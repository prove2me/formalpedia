-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0789
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:48:22.184317+00:00
-- url     : https://prove2.me/submissions/1712089f-1892-4c85-b879-63f625d6a16e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 141726618 ≤ n < 141906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 141727868 1250 141726618 141726623
    0x1090510062c0c0f040509070903210507030c080c060a0501050f06090d06090c120c06030e030a0207031529150a021504080d02030a0c0f03020c030904020328020d0506100804 76
    0x10009070405001c0307002c1d005e650240800402040041c18014000740c82860b01d131104581c454200c078000d01c41202d02920840400d520b5803a0b252800105a82c11205500001401c41e0204428840c0ca101d03807008100d01882944203800004842d4140f00801070048840c40b584e61280c401003000d810305403911030f84611030702d9006c1008592581d462401d41104103480d00507510300d0321040000d60600a0b92200341045445a403020082c3c61100610580c0341d20465809001680c01002e003080018403c00700c0f00280218100009a142d042807940312280b80c100324003220300b0085040c4604286400030010213180d54100c03141d80f0301151000302075219070810340000d007603507442000501170201e40c00444e800c11040c40000c5540349081644030004290000003000060f484000b020744645c028070846140c900d010006605040d103110400000c0d600081ca8015000c084012504020104031440c452840d00c41d0000340e1071f907100039845011110014201480740d0300e894400741d103c0e60441ca031950020f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 141729118 1250 141727868 141727891
    0xa0204050a09050f0109060510030b041211070915141e011e051b030f1206041b0915081b07050a0b01080a020306011208031801090510062c 61
    0x25590301001000703282c07402d4082c3c03060003400804151514103610003081144144800c00a5444000000c0309017a0140001000c007034007040402c1c082000c040d61240080782d9481c01c0c0d40f4600344c02002c43c1c00d140b41c1d58030960899880b5918401441440c0102401420303107201001144920345000a40c500880040c2c14a4800c44000c000c43c00d900c42d941220071410415260106643e20031801022136001c8540080401c2e8654181010141d0120031034240c8039600040a080c0a80c0d01c0603a400f03010058180365001c0e2360352908251000c0d180c041c40b05102c0054a42558a03440d048407600100c0e00b01c0004002c01510004210580008611782000d852442d40e5042d00c454080c98943c3c9003a08000b000350101c900003000003030044001034800314444c42a4107807146c50340d889550061804182c54000d10482d0140000384007119515011481d003114000041440107454851505005641482001303103900c401c0180000701c90021501d041003001c004414888c0c242c10030a01005401400154151 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 141730368 1250 141729118 141729121
    0x20114030c04060c1110110d0207060e04180506090610081f050a18050115051f032301091a011d130207060e0303040201081807030201050a110607021605040903020a020405 75
    0x10182c5500c441c004000761041446c03c0305a03201030112036030112540c2051080040c1080503d101140120440351a5150414649040c6003000003502552000b0440f14130a13a40810111700c0c2080024007d008030000782c4003608040c80c150b500c4001c40e400c00c0c00560300c000200380480041c100e0b09001c0c0705c41030700c001509865844d8564060842907510f42c600c0032741000e640042c010194042404040030451003d5400d59580500c5401200700c00c05000f00040c10300d501004034007c1c1c10411000f41c44294029401020107105003040f0000c1e000080b05c0d50b5100c0001c01068600300c0c2400200c2000d0a24041000603001501d0100000840440c002e0b00641903c09240d413003501590030711640648140004c201a4424a41d650012a816800074000340d001c22100d1040780540586004000040c02c0c402d401d5400548240c1d00c16040c1030100400786441a1110100b441b1603030140d481a4003501b11090004814106407010781c10113845186000c41010000e0380008284001c940e05443c0441c09 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 141731618 1250 141730368 141730373
    0x22811030a0c031b1101030605030d20150703020301060f080603061521010b1003050c1204030e04050103060b0307051504120f02032d030a08040609020409120c020114030c04060c 78
    0x5101c0281e12080c2500e40b09600b4004101080d101700b04105000c1c0c3c0c0822110365a030041664800012070500081958540101a074003000104064900a403500701d4900300c190000c0714040442c1110710300000307540400148050b0340e11030103030041c001c0146805151402c107100000e407200c0015092403443c0b0449900455242c40d1900e1144070020a855807814094040d1910b0380600070504440b40b0484c185000544164002d1207140d02a00a10b0003650811456a4248c081d03448050415000d016160704004410707074032805102c0c003852140c1c80115141c006031080c940361078042c3c0c000602c683c07132020804000e03076080c605070350031035004c5e0504020350003003410550000040350742d0183d05402501040011140c4200b10100d803005821200ba1b80c400d000c1001c10b1716405101c41c0716001a082001107008901035400030f21503180001c00020b640f001c942d07205003041d0080740c8141d02046060030000290344c1c10020031012602c2c01d11080e031a500c1c22203100c41741442140240c100740701140480034103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 141732868 1250 141731618 141731627
    0xc070305100218030a081e090901090f0b0f06030a090f0203010c090e010f0608040209041b0e06040b010309021503040804080318150a02060a0203130204022811030a0c03 74
    0x464002040c0c03004003100d80019070195201080120303041055680a83c0705080c0000c5858103260415411401c1118198810300300040c44601030360007002c18081110700d5a01c0c0703803800d4000d0183d0480000c4180b00c51046d0702c04d49020614081c400d81c0c052014844039143c60080300c0d8411307440d8000180c02401803030913010080d03904001940540c60302d04201d8020350000785980c10b4510904c0707048116070b41c45504ad05200d005004080016002c0c00216005007081c1c20320303a0304079100e6941d850f0302403928804079002f01120fa00103138500e40400c0901c40941858491102d980b4803e1805100407403068000c54030032450361a58200c6084004009818800607009840180c1400020b81707a4850344902c0038542407848411161050001c051040c000741c41440c111180f8803d140c000e0700e010340e5107008610094000a00031040503030694040c500690780d510041180390504940780680801616160281c1c542c8a01c1200c01e000250403072400001c000010744030300d0402480d05d4071a81c6101c5c0303002c44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 141734118 1250 141732868 141732883
    0xf19030606030213031e0b0a05070306050607030527030313050418020306040f0302010b0613060909060620010605130203100902030c04030b070c020901080c041113030212012309011515050c 83
    0x600e00611f18040c0300c4450f01c5034018502840c0160303401d0114640390010416144a81e0381c00130081102001a1000e803650194005040341c06d200402600350030a0300481d0541d4450806041d00c0d100c040c00c10b1016242034810301012140b503507111020700b0115408a40da905000e04041e24061034403034101c08261007500902c845c070030060203040e1503c1540c1e1440b400f0780100d008070f8003c81c214410104910403070740300d0741040b240f071035494101150f103001c8062070141d60b6848034480d554030741c28081030319224204200d0360081303195401640c1b40380c101c810b00030000c1c2d540c0021340500e004100340714043e40c60b1000d4909480c0c120b080c5500302d4031884e509542c0c146550038005d420611040000800e403001050100001205580c14000300c1c5004640703000714400c07c1e659204290080100b8800340c101600d50f00c103100c88880000428008a401c0800a0014041c1c000240c420280c100200b81c80e082c080d42461031852109811020304110281d56807840c05104001002000302d0700500c0c04be0200306c0e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 141735368 1250 141734118 141734123
    0x9020f0d060b04030605010504020a0509090415020408071a070506041509170c0105250c0206122d040f081602090106020c010921060e030f19030606030213031e 70
    0x20000035640c0c2e82000003580041c4001d44a03e49000b0001625007814002c0b110101110303902d40385010181400c0002c0f10382d0292040d2034590490b28808484100341c402040540118001480c3c81d0340b07086203019041044801e2900da105041c88000300040c40010a0b5401c44d80c0500c1010582ca901d00d24a0b0040c03c5107440079040101c0700103107109409102c4000c1030601b41d000000d000941d28005a0001001c04c81c5801014441c11210000c40e0b41c8202c0440138043d01c010302c03840c640050582880010003064880e88207440b1a41c04226901c2404020b8804680084c0310f101640c0c6042d48a00a4801403250b010740321240c006039140b8400110886054210360080804010b0350b12000000d40d01c52007007200030f01103601c3e500e000c5804180c02c90300034404400108032004203802c070360f02d0340080c210b0a50444043e00c0240410041080124041c00c2461100404911034803469a0018140c501c140d00442c2070520410003148104295011042030702d8000d03203040c4000080c0c0001e249500540c1001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 141736618 1250 141735368 141735371
    0x10e03040e0c0c030f070b0106030606030e0709020a0215040515070903120806130c080f06040209090636060a06030209031b030c0d140c011b1209030803010305010519020901020709020f0d 82
    0x901041f4030060002e0503243e150340c017007264540b501d0701038044420480c02500f2031341c803ca0040201c4c01d250740003040f01c00311071b20544155000c11400300340000b40c20740d002c40c0e01d80c0003800500351400c4599140303070b400410740c80c02c490340d6072964031140a146442181c140c2000a0300000600e01d80780e280300e400415095403403c125909400000401c10074042d01c05110341048400843c0442c03620303000f51440400020040191500c422040000e00ea0020011140d081101d500d0540c41d202c0a000b00d0114964010400800386072000030000e00161940010042c1803051126501c19100002c100007034001c49030709440380555440011b40781c41d40190002d5400040800c5440410881492083d090a042d9040740c6030013600302c00542d503095a03403107041842c001030314031a0085a8184900000145241040c035441c548a8440e052030340d00c240c000380c0e0503039150014010a001d0b03040b00c0301c101d050499011801d1007040c81c0003c1d101c41651045600103900414121002c1200b03600b1621824440c020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 141737868 1250 141736618 141736627
    0x11070206040806060321120604090605130303270b07180609050a0b0c061315061205100c0906030e07090c030603050f0334060c11010e03040e0c0c030f 66
    0x5607203689600413125280203002d08071101c03501044011030140e490219500d69410300d440c2c0541030345d03000d100a101ea0340c460344074070f140c401041607417050a00420421030861400282130030080c042e03450340031300742c1038414201c01200341000c4545284011954030105080c034503151000d080320503c0340c00d0710040d40015481400180d15402140070421a02c05039400d41300c0c3c036034410525216010724450310320301d0307080000018104080d80a60001c03140c4100d02c45a2542248003031241160b40d80d410001000346070000380401d0010400c2143c11006124000f8815075801c2c0c40000c00003c0385200b864145526004425815a001c1c4001c50203008101e10401400200c0c030001005080b50f840161003c0c090744914680030240070003152840c0c0e080304422580da14226500e22a0301062012844001c400d200300000090304a0040403002403580d50740d0105804003da0540c2103804258003451240d0041000b0452112282c0c06154001150b41c0303c4c0707407502c0c50070b03040f24110b10031614a000c02200008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 141739118 1250 141737868 141737879
    0x2090108010507020d030608100903090e040c030209010506091f03020c060412080106020304150e0f1008190212040b06030f030307090306060b0304050a12050f0409021902030901050307031107020604 87
    0x1030102c2e10a074034990840c2d290520071001038049994501480b201d40d0003042008805214642121600c1c038424506203011594502c45990310070000d580498403070355000301c00c20540c40c10b000b410380584000c454140ca0031304041d0000f42c0c08001d44121b0780300d203c80800f01c000718174066410380742c220800d4010307039400d8501440e240148402d000141c80105085800104801c0d10010513101650300c09903640100c0a021002a180c82e428070b8201ca43c088204001e0280c96102c0c1d101c0b032448080c9070f8662070f20034107085e50303500400c210030113419161038814001ea5801415600503203030419000701e844880c036103521000c6404d12034101880700c107a10000080c0044240d02c02d42c000110380c02513a0401486840302d402200510050798054103076844003141030085108000258040c0c0d04905100d483c00122400500031b039006503110142850380400c1182c1071504403400711203400d0680c80514a0454180001707066801b000d04900e08041d942d0326800c0c0781c941d205003218440c3e9001031034642c465903a113 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 141740368 1250 141739118 141739121
    0x10e030d0c0210111e100e0d020c030c240f040b130e1b0a022e0f0209090f1012080c0f0c010816030f1b0801120c0b03130209010801 58
    0x4a0040780207861890030203c4a510800e000f0511a40390070150180c441000382400b03c81c81118400c03240b034003c501211545105a03c1032a030401d03184000b4013120408040080d06021130080d0043c0241c006901c8581581c0d038601b40d02d0340722101000a01020009441e00c20141d0140307101c0300d605034400080204000741a90b01500c0e81b60706034520304030a61344590a00c03200503407c7d46d400c80904105e028404807030f80d40401410200c5186d10441d0480074280d070410648210012800d245441283d009400380107039400f0324030302c8050084043d0710b00ba00034004a05101401000600c0407042407000c1840046120381c000014036940c1114029a61242800c000c641e0005544101501c1110302448112401283d401d41c4000140c4503030b4955601c03401480402c81010001c401059900c1c0c3e00103200c0740c080e100d00354280107254030f0805000c9965001401201c4181c100d231090840707865544002034020300081040d19100001641c0b80e48403000c102080c1841a0310013503101079110001b040e00e8205 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 141741618 1250 141740368 141740387
    0x60e130b010807080d0338032a010e0303070f060204050901050f0f0f04110d05010303110a05100218181b070b04020f06090a090506040c030e060411010e030d 69
    0x19580d0290300381da0719060300b6603070819403044542d00d8014070248101750b030180c0e01c03100700d4060342c071850307250000f5041c2e1007864802c40d030384022549010b045008206003800c008103020082c0f0b01c0714508039020b0300d262088006400d01300e194100700c2c108805030322075201441907034030171603002444140d500c841d80351180c043e400500495006061403400090b40c3c0c03400b42205043c4d030201904440b0300100c410184100b9070001c0c1b8034190055140c00c094403079502a00d004119040c1d19440000b1554150300e001818050000f545010560040300100041a404150703801701c143c803150016650540401400700035031072a074050b5031040d1460041e0165080002d040741c41410440c60881011440718181100e07402060405000103801500082c0182465484404110001406c60742003503041c0000412048080c2c001444260721901400360758145070140011444050400340b10040080c18960381d200c030001c0c0701600e08461051810301070b9002d2801410211400303001d0715400140070310090a904031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 141742868 1250 141741618 141741623
    0x12040302010c031a090606130303120c08071e020c090106170708070e0405060d020607080d0501060e221d1501091109010c06020f0d0902030f01200d060e13 68
    0x20700d480303201d0a0b480b07413042032841e42c0c5080580709254561018444c1091000b000c06403c00c40810003078426102034100d5000442c40fa0380c0d142c5202441c0d80b40d44041e14000d80141040c0001e100c14015603540084900300c65884406469810584100301203244c04032040700c95401c005100000304503c1e40c0141e000a0b126141c61107807025032150802202c02000444040000943d001445101890b0940199410ad4002000e03654211b040d81c00144030b5a0040a0464110000243e40b0b504007103a40200380c014601400e154a1411441000c03074070842d402550b60001019081c04020040080e83c8174014080880b082a0240301c40d4884080e940e401202c420403802540c50000560b0851034003814008054a00b681410312480700f00540c0c2e50300388604104e498039005c1c01541d020701d00e034001420801c03262100100724002d0500515060001404402c0391a03410154028041c25030f281400328000450003003642d0350000c1c00d4221008020b01c0e04541c00b10201201806090900700508502c92070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 141744118 1250 141742868 141742871
    0x90b0706021e07052e090302030712031b0207120b040618030302040f17030a0e010c150209010e03061501180e09030c011b0f0c060b090a0e01050705070c050d060608031204030201 78
    0x11419651800d20860001d10340440c844045e4445008400b50010168a40f01c0c0c01182d0070488103a0710048030300500d00034500083d51b41d4000d04031700150420318014414072070000d452400d0610345800129a48030700041d101010318000300f010400903034040915108040300d6500c005003d803800901a501c5441003440a1841c20740c00300300e19000d1044034480f03140350001135103001d0b01c6c00780c1070758080080c246642c180f1207402120b1022a4460000610126208400507a40d0100900162a8990348075059010b03030301c24420800700b8020600c0a000c1d80e10b003401e0540d44074030002c5603880c41d81101e8114080c9582a03d09120490b1000400740c103021481c0c6c0700a001000c148840888001071106840d40021410b11145120b5401010000300b454041c880203d5484034003000702d02d14000035a50381225580c5e42d64405010a4203110b4035402401c02c3c0340180c07400d041510303100110225401020f105016107204041005030f90f920031002885140242c1c0c1c1c4516002c0b16140e50104100c0e000c0d005075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 141745368 1250 141744118 141744133
    0x4120b07020d02070b03040b0406140901090209010e0622020f0a020109021806100e01051e07061a03030406030e0c0d030c050c03030a080c0a0c05030d020702180601090b0706021e0705 80
    0x40b800404c0650648091003101e508660f00c03a20707a43d0b1030001c0940159074566981071030600600134103c4180c403800012002040f00c41a0384188040038105a0002d140041fa40050202c03d95030000c041141e52104680c5c0120804082c994500920138240c02242e005070000e420400682c064105111880c002c86048080c1708030061402c10f0700c0c500310b4607294014804140c104103a4015800000080010716109081c58015150551a1219418485c00c3d010002c1184020499940078070a2041c484125045138003034a900801e6983c06140510018144c9481e01c080744410100a03840c0c0400e07008201d10308041e410708020340400811182038849005251071036502e820700100325028110075944038030a568030000500d8094005901c12400c001b555103610004c07510400c0078000c11f0b56450001a5240b40070710401040320094490036020016040030000e540c0e0b08136100400300d911222030140d5840c1c081c80c10390000c1c4505466120182d203041c4095410b048624040c1c12900c1c41081114041d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 141746618 1250 141745368 141745393
    0x100b130501060c03051b06010b1b07030302070b071e0f03110c090a052211010e040b030a0b0414060109140c030f06100203041a0c0c01090e061504120b0702 68
    0x2034600900815010464803000000020701c40d02c001c012101960416a001d401d004aa41d0b041c081d003a8408004c07107102241d4900582031900342c3c102c2810a4000404440f49580d070040d49031038142c4103000102e0400b00f003d60500c1a01d21080c40e4044041a80d038a4200103454281903561849806030001002206541076a020000303613101803401c01012800a640c400309a140680001801340d048903800d80e40e620341344214441784401c128411410102d9074203045c000140340c143c00701d41c0d0510560400c0718400d8aa100400c0b03446900381c1151280c0c25a60b0f0780c1c10407441101220306030010500c11107000003003509031548000080e0300c24400d052295101e51003401c4160100b52030010080181c0400b241152500200f140c0210889005503410103581b16080751a110515143c2588010000340c1200c0f40c43c0113000b0400c00703850909100b420141014000c9058050042425014480260191140034051004c1d00c0080101030225035090703041d458100d03012502503540030058415040b4040c0ad = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 141747868 1250 141746618 141746621
    0x170f01020f180604030c05040902040b130b01081e0f060102030c0a0303020409110903030d09020f180610112509180311070501020a11040902040e0a0510021c0b01090503100b13 77
    0x312034008040e40074047c20319080100901c0d860404070303031150350f82c03454030259198002006602081000d0015840601070001740c48044000e129030b60300d20741040642190350300046200e801c2102d220740e40c0326a5071118010703071131807250026480651044d00b11802c1055415001401070301c0071140d0601a0617442c01c1c005641c0d01410545030703031603003041c0440030380c40c441a8040300c2d2990004141a84841c404000300714124266051458a869039808000550030014602d0714071185a10b06410404a60784200382c484403103a506103200c040801134460505a002c890301c019110f61101042a031200780c54001140c800124118041040a80d04d141105800700c0c000003115010b80203454007903599170300c52214000300c1d441d5641c03040d070701c9880c007001d40c44501c144c0f4882d0701100010b042d0b0300f105052042c50a07402280300500103004020700c01c4032082c0300d0359010200c10480c40124680b44500300503640b90000341c0045406105800720140304079456040300c1c0d40e94070156a2440a403079003446900 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 141749118 1250 141747868 141747877
    0x3190902010f120f0203090c090c130509041703010b190f090909020a1e061403070c0308070c05010c0305150406140906060d050f0709150801170f01020f1806 69
    0x2408070700d8440c000c800e4240100505011048007481c00610052900207a13401c0360010760700e40020f640504d00d021031318100704210070342000507010f020341443c3c5014124044d1814034050980210b4880001c5020007000300c2040c1c25136224520b8640e100d40e181d075902440f6400151840003444032000e0342d0007901d402050501c80520942d43c8421480d42860b01d680042c0050131400c0360440024080007a00101f1650880b00382c0d640e03680c07407203034a6241103002802c1b0071142c8650142501d0030028003452a0300a0514443c95526084c001171303690303c4840031b0b60013400e8104040c00650070300a1606507207034154007040c400c00c90140d0020380250000d050000302c0314607002c1d000d051540025280b0706840c180b42215404200100041d141030605056802034800c01d9070301d0540000c40400740709120b50000fa02a01529560f43c010492140c0c1140061160301c043c8504083e10b050301c01003140e6200d0605c0303d41140071825000f90f6440d0015120710900794445c01ca180207500c0c041c03050400600e400407c88 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 141750368 1250 141749118 141749123
    0x2040b06120c09270a02090a0b040308040801060b03090312060d08030403020a0201080a0e030f160503070b100e0c0a030c030b1203040509100602061801060e0c0702120106060f0c0501090203060903031909 89
    0xf508545d46000c002c074020742c0a84d041d6544402104400202045041d006001451040c66407540f075614180d1150f0941c0c1c02c035040010520801d20411411038000400c2d160821468180068561103002c0031400c8040c52250107003101b5000010082855000503c09204c24030031703a02c111050740c802c611902116000c03e408445900208500162824440c01506016500c1007134614200c2041c1d0701d2915561200320b00712507070000f00f401c0101010703881800100030704a1200e440c0c598071301458032050034030504001000381075036110800750440c07007603000e0720904401a00541003100440c0580d6681c3e04541b081c00c0c03055540000191107189040000402c0b076215400400c02c0303480310001481340300740c18030b004e0703195650311080050b0b4a410501194040d191403050140e03103003114018482c2680000d00c1401c003680c103100c070030040035500c0035000060100720314251140300d41ca442c080b405040c2000020b50f06205402c180424868040000c60007401541c050081407070f2060004800c0d9210000003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 141751618 1250 141750368 141750439
    0x10203090d06050621061902040609180f0e07030506090f21070b010b07120e0a06111009110109090605060a05031909110a0603051302040b06120c09 65
    0x1803600140b03694200d1508a14010240c1c52041c020b401742c8018140450b61078000c5074803000c00d122800e8080f2202c0c80446001c110150700d05030a0240141c035086403803040502104a41600703420b005100e0b400f125007070618020034040c2e0107410f08895590031050005a40320b02070a408610400710008030003401c3d0142c0d0028141380120080903e548400c4c2c1802c1001800040082400060f1000440d81c040d003134400a031a1103000d941480c220700424071440b0002c1c08501c03100201706544a12091007111094070740319210001524500e4103107410405908071007420090103400f0408800a00d0b210001e080e41c40e4039029640300e8586082e00d036540714268012100300003c130795061054005560204000031a5188010801400c6007110b01c8100c4c10780398482c030340451540700c0c5880003030a401402030f440c0138000ca041651800140c1007901d41c0003071083c1c0d902c1101e001c0c40d403110030030358841c19200b200003c03c0e4945980714041079030251600380d224501d0138017000b04007002001c0352034841010702030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 141752868 1250 141751618 141751639
    0x11401090b0a0f0909050f060f01061b051c200102040603150f03081b06040f030201050c0901081303030603050706392a0303030e010501080a050d030b0112050a020a090501020309 78
    0x1c0300010b003c018000d1b035050140b00706141601c202081441e000d030900c1442c1e041d6a40c0b42c960300402440c05980c2e0101d00d440145401004100c000454a6294441448046513902180390a680e0308500780d400882600e5280340719448050306501500454041e910140a00f408070008010960341900401d050707036100c51403d1000c6101c0502810302c800c2030600e54107401d10046121850808211012a82c040410a0043c1010307428000c1e00c0d0070166801000d4105000000082c00d500070080c1402c030300030110000312041c94426002600217640243c20344160036224030000703103503040604040f5603c4d0340c0d003142541c6140c4142117034140d803003624030b1031481d00d0025521840500142c034030010300d801c80c041c5040a806007243d507810045100e41c60002340720210300a00c50a603101688650440d801c07802000c070100d103022404114501852400080034503102d0f005031111403d000342d900059207004100801005a07500030a01406140c4071014460365030401207070b891182038146a00080707000c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 141754118 1250 141752868 141752879
    0x504031707140307212001091a070906080103080301032003070602010c02190b0c0304030909060609080c31140903090a060806030d110102070203011401090b0a0f 71
    0x1503030464550110348940c0c5409010b49900008030342540310182c060300700066620810100481444030560030b007000c4840f132100c40d03a01800038034095008050415102e42d00500080080d40b042804030791040ca14107503090083d003003101c1c00070b040f80d0b40c0300440d9a075170b00480c09600070040b0074100c9a0100750949541e0a59680e00c200f20729a8403c04035403a800010380702140ea0074004407004e072001394000100134000ba14020301d804c0d201c00c031120003886038418503030209000800241d03005407000c03800307a03598480303103800c07169404150300054001e45480c40c04104694400d92520455030500304490940803200200010101001c00c4181042c0c030b03200c8102d08070140c05001c0401c43d8140c003400102071607003913000c0d800c264089843c42001e4000280e241d080f4984015800c0c00f8105614100c0c83e40c3c80c000380802d6584030401d110300c1c14002c0e0030b5110a5246025011100d0300c50740038000340820707030030070090010340b000070301984462a050003130010710340c01c0000d00305044540c04408441c0c6175140c40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 141755368 1250 141754118 141754133
    0x3110103020705150403050a03060509060906300607030509011b0e011404121209140f270a0e03090f04200c060123010e010305061c050c031606050403 66
    0x30b640844081c02640f1070506000b9000301900d104600a8a8060391040075620050031101c0d141c0040e4411403400e01400760603261082c801c0e6010740301340c03000e06400000748859038400400170303100703620348403030f03480c01c00d40c1d001e0108000303010300c0b07482d14188040c0c0c5078503034900e080ea03103403e0107202c800c2c420984444500707114407038070b40e8500d030103050200403611039903082545507019402c020304041d08060b00508100b170006d900b001d804010700c0c1054449080482d99008020400c51b501c1c483e4142c04048030a941d2a144018803003801d6105002c0c40d035401628184822100b110400340c040c0c905000c02c0c1400380040100d03950200003d00e2072032108901d204100050002e429032a101099442c0c0380c0010400b040010411213035600000c007995851300244458441a6500031141c0d404100cc0f4144c290341c002c0e0000c07040b60800d0034041a25030300c000101c0c00407103020001000303100115101c1802c1c80070102d49c0c581401e50a41c00e82e102192071042c4180315804602ca0000080c90400080000c519039 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 141756618 1250 141755368 141755377
    0x82a1e01210609060512010203070210020c1c110601050a180906020c010203040311010e0109020a03020405190c030605030c030706020a080f07151b03050f1b0d02310311010302 77
    0xc0c01c40080d41261070361059400c489458201e50140c0d40e45910511103131616040084451803528025841d45c03408084c025103840050742640040c82d0007044000c8a200b0600c88040c8c05a40c088001c0c84c03080c001a401031200c000340b800c600040c042c080000c01c89081c0100c240c016100f0919110101090088040c0c0092130050030079680c00b90300b40103401441d803084c002180914040d50381e00c0424442c140f0182e0846001c4180040260b2501460100607158a0300d4007044940490300001c1c1c0766034943c0c0e020a80c24005000d000e41c80c1c945100c0e01441c94041d4048000d40c2c40513000c441c90908103005040d0389452501841025a200400c0d00c1c001424000c010912580103034005c5040400325964800e0200444060b542c0d0300b51221034031480c50a984005080303140c000c0c81e0900c85070810708001341502e0000303004950344c3c000c3e100c1e120200c0070074401107a440710401401155035030324642004600c90030030381a00b0b420380d00000e10800d613403180348401d500352a003107030884a040c4070500043d0000c0d0310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 141757868 1250 141756618 141756647
    0x70f05010f26100e01080607030905030918090d090e040206071b0905014e02090109020304060b0d0305190c06020703020d030b04140105041104082a1e01 67
    0x241041c0141d541c0c80d90b510744405021807101078089401d114818001000254110301201c240080040240307520000300150090310909000540314882e00740241184146079040703820114030004400d451101d0488030303104031007030760507100707240300005040740c03400042d2190301841c0d0501404580580386c810000c00040784140440c0c9612507018034011600c1900381d000000040d81c460040250b4487c00080301840000318124405242c03c03400d0094420340c5c1c0c0001c4e8240c403c00f03606561080a00b5259112200790020980144c940e56128010701940c81184e0403541a07082032070300e0b80541081c44860560f03a500d9155141041140076070340c803001c181070350710904000361800301c14041078a0748001e018260099001d44a0342c0c03505131014055801d100303540340c001c138a060044e81c0b03001ca08c0e0042c0b5040d15011107000c01c03500d40a200462845c0540c0c4c00003036a41c020b000c10000c041c7d4003c0c00c00e250901014160703100d038241c10820403140d5200b00302c104100341840d04a46a044d84500c91800e4240c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 141759118 1250 141757868 141757877
    0x1c020d0905090a090f03030b0405010f03050d110f10060819031403040201030f0e0a06050108030415030b030304030c06050304050c06030f01090b1210060e100f0e1902030f0612070f05010f 82
    0x40341c0c1c0d11840178032440d480c0f0590111b0b640b5519940c3c103051900496000d4402c01c005144128615500c0d01e0369080b20407610020810b074040302d000c0140080c0030072400080d203001142d07030100a05110030010035452250540a03c00c01c5c02d140710345076001c803181603503d42581714038000c8404c050404000d41d0009008904160340e460000962145502c108000510003600424003401175240c1002240c02c103801800c07650344144002c00c5014003c2c840f00ca2107420901d0301003140700f42800801c2c61401640c000601c8030800000211742158084083c620030b500620803108500380a03002d003d51780c03109840303042c845038080005103c0c0701c0c09a04969124030300501403a10300c05031015458104071000e0030300c5800b42e40701c0c0020440e000449083c6070b006a038407002c2480c0e1619000c00c1044d441258420700c031020380910f00182010780b05003034034814900316020a41d5a4942030388454075940c001c40d40684100422205480c104030009040340584505010030014282890010b50f81030400101010411 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 141760368 1250 141759118 141759131
    0x60f0703020a021012050a060302030606010c020307120b040b0f0c0f0f130b03070311160b0c0f03150114090a030618060f0f050f0f04030c0c0e091c020d0905090a 71
    0x42c1c445032030a0801c43c55680d102c00120701760920640540d14040d0076031500c0d50428600f1f0001d6a8003080b1603401c0700003420109692402480030030b007021481c1e4069181d06142c13004080c288a1214481d62049118071190720302562501d070742520b2788d101920014840e50082c0302c0100034003420310082c6810502014200c0c1030032081410307058540310b0b642101d01c0705100030040c00042c68060180668500c060001c40f0f04042e1403011017a0798401410001c1d06000003003001c2a11800507404803000d01d044814259540e142c00624042c024a460022500103410001d2598406200c9002e95010400090007220003901e1a1510000340c00c1c0054000c5050780c08088110000d0f00758422725600b0590980c001c00c004000c002c0460407275400505010141c1102d50401c41e09001c1100703015486545810900840151030900007126841d41d001203071014040400d0010072803000598940b05d00368030340510249105104101c0c0c0b0f440c00500580045080220203010340d1422100c1280d00000c824000140c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 141761618 1250 141760368 141760373
    0x70602040b0a09050a08010b01080f1b0a03050609070f020616090801230a02030402130c0302090402040303170714040e04050a050607080a11070201090504050709080106140a080c060f0703020a 84
    0x542d102c100803030041a820001044a41855407042c801480c41a00811144080d500043c140c10001480d14450b4040040009e403800c10045011451140d0600301e00c0d2a020414405001450700740c03803051080c05060002400548540030030350465410b5409096603444412008505031075a80e1508140003904401160300c0c0000d104841030715610b0380341d02c030100441040d1400301900207414040c6050041007040b01580715402d44030040c04100c14001203005440c1c00890080c0074100040340d000740002800003d140c3e01819954111034a0200880c2607254100c01b82c500c0b0715150401e40440409000030001c0b07524032107a9541c001d008038243d505440d401da441c907092072000c640c0440401d55241c01d001101d01c0d1441440c51012003a82c50900d494050340000e011040743e48507640c4071b81d40311800102554801c00c00c41005044101c028060a0340b1805035940403100c028540307020f2481340400041300780b000108210b1088000d803585161240f100b002c00c003540c0c03114a0503402c1d4800c00c03c00500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 141762868 1250 141761618 141761639
    0xd0207051f0603031b02011b0503041805070f02010c12150f170d020f0604081b0a0c1a07020a06230412060e0604050c0910080a060906051806010b07060204 68
    0x10081d8004400251060a41c50701502c03072004d1005454082848820050060760448800c00d1781b22005044070004e401d140c80d03d43d00e10b200325006410050000c40e540c8461030019001540164459125034013002d0071450b08134202c1d0080c1040000050a2160018140c499540300c0ea900b0104403403034107403080d111503c2a00c1c65031580e00407024007255504200c94064144940202503132244041c0c060403903000700380c940c1d0310320141002d020440e00185138020403000920944c100300041c0107888a040c6a0b09202c41070090a03c1821500e95003c1d0000e1035082c01c45003100c1120754010a1248070300e08000c0c04a8030203605912040164860000301040c001141c0003030300c010180d5a83ca021492154642501030701e40041c2000702c00e40c844400c0c080000c07000701d001c1d0145141992179210039520300380d44a441da00c259201280e24007903182c0d8081888180e41100101a014030300611941d00e511401120410703076101c1e95003258000d00014003003404544001c10501d40503030780150526440310705404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 141764118 1250 141762868 141762913
    0x6080102130906050d1a070c0f140705010c0b0a0207030224010510030e030a0e060f0c06010f080303010506030109090501060509070503070801081902040b1f051308070501050d020705 80
    0x60301c1182011041080801030301442d40035090540e4046841c52095440b032030721411030791545108007403610019903200e214000041945070415111075401038142085100e60300f0750741c0c1e441414000d03280040f485500503502d0000061340312600781d0342d40d660419000c0081d0803043d0304804602441100480340980c01a1401d000c161040305043d0651608081041c1e81e0350101d58a400c0c50300300700072620f507440040250b400712851800c108041d02480c40c00114103104191080d44000404522054000c3c0002041c0781171f00e0841420405184d21140c2c41c1d82d59001c01d101e41c80e030041040005109034915504200c84c6548904004614281c6840c00920048421513506002882c04010040c556512100309401802d240c4040c0402c9038602143c8403503401d2600f0084e0103582c132040e6010040d03c0e1200c8500c1120b00d0840e80f0910511203a42c01000381d807000d1000c071084518948045036070300340410300030201c0310161900b5141c03017007180760000a900034200549090143d4409095a030310300d010ba90 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 141765368 1250 141764118 141764137
    0x30e0307170607110d050414030c09010902040e0108120403031b0b13021008090d0c0f0b0a0e07060f02030322020d030302030916080d18170a0b0c0a081906080102 71
    0x14850380c070f04040003d0140d1101e000084040c0d01100c10b070817900d41c0010840d816a050000c480e0030350489140401d06c1c0001d10030309550851400c200006148080787d001d0000d403640b141043d441c99a036813001d41c0d554051a20340c100e00140401040001a0040d1440300d58002007429405c4035440b103880b16a05444120380000c3c091a0100b010011481d2410410b00d8040580c00d0158007414200d41031687ca0340c0640c011028040741400900c00c0c040003010780e1801c2540010074440902d0303c60840030113050321040c0005244a01c01d03000c580203004000a01000200d9070007907045a50341030360b60204115400f03000d03100352640c010850250315006010640070f800380e100540c2d41d0a003046200d10b00b1000c080d490280c40d04000092000030404a44200c0c041040e1030185000c1e0030710501c80b15130414582c80240301130321204509010040101e01080c21b0b900910b40d16485940d0070100c800f036881607080000014503039200003016200030694425520514100009071540c03105601030890f881140c04 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 141766618 1250 141765368 141765373
    0x20a05100902090105180c0a0507050f0f0f1b0d0f0f110a0515040302041a1207030201031b0c0f0302030906070804030c0f0315020c0a080a0305070305071b030e030717 73
    0x207100307504003640b11038014042501c40e50821100c888541c0c2c0801d00c058508072060310006101c0c001f561041c0190740c60340b600f100c15101502030300f280e0a640ca0030f49180407401401648036002a40764041460301d1001d110700e2003180000100402c1140740000400101d078481d86414111000c589604082100b10344038510f420070402c4a40700b08180811194021032040600b02102801c116100d0305450860340d064030045540c0c1085107074407480c244d034080c00c035400405808c00200c81400010b0302e201264000c0c0c030108000b031035004800440d03012410209011955400e044400a80902c0c020a042c5002e841030380d00b46040070000800690100f0001e81e100da40200341801400031030f030070b40001005902c2c220800c1c1491903940c0050100981d20001901b6408500044407030300904c248602e060b801001280d41d5200b0b100090014a4255140c5001a10300000908514025604025085075501035012003003040d58040310b19842d40a5000d4045c0104c64000854a1071980103800f440f11a802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 141767868 1250 141766618 141766631
    0x50717060f010b2104020a030204090803010315050708012612070302010b0301200c0f07031a1315020a050f040605040303021002030403080612010b03060420011e0e01020a0510 77
    0x40300720010041c0c0000b1200d9034100554410b0202038140060100e00b482d03604080e40e540c42c000074580380c29030750001c1c1d001820607c40b88108031a80b4011410389109040301c461012417943c20004175002100d850000c00d80410050003020403424501910400030200d40640c1c02e81141441d0501c43c0c2440503043d25a4040341d44004c258080c0603002003460260001c020207102d45a41c1080c02c5107403400a04000e10005070003404c00e02c203000e0081134031b03e40400c4803003150f5649002c1c9840300c0010f0f0640b00b25a07010300818583c0704603140003210340360030008058055040005100080d03101a106206200301001000c0c881c0091402500041c00320f62105600c0d149541170290415402c00305150065104004000000b50028440c0350016410b80c2c08000001d950903000e401000d600f2050b0350f062103020100410084001c26051201c1c003044030445028400d0320043d10303020801d02c0450203c4010103101030401c0d1140c0143d07202c0b8201441129100c80b2162110780c00c0108000403000710a03203440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 141769118 1250 141767868 141767881
    0x1b140c011422230709050702060402180405070605030c070c032a06050301031704090906050405100b0112050405010912120507050306030c040906240509150604030f05071706 76
    0x1140101901c100c4a82c10500a20700e50300c4103141203000d0607003418080c03003060000034200100132420141150910402c000d0070503e001a41d501d034100c5e4108c3c031881420034460ba08070b03162081180903d5000c001002d2181c100102551755804c001c2c054607502e0401d2280001241d00d0f403001d1802036001d03184c1014002c005010314400d418800e1411020403222100410283c0c1e48481101e04413604110182d40c40200400c200300a446142d0180206509103034403a002e01526600c241d00542c40303003046030098a0558001c5080d1040444442e01081503034505440804460704100c0e44035218500025a2030040e0b81c1d6056403a04201d484000181036251920100d202d602c610341c0c100896080850851520100082d9130740c4040004c2402152500014010410140c01800501d8030706240c10201100c0140100941e123841c1c0701c0d6a103d0034404010075501508072041c04060040507241d03d2a040c150345600b4203203203020b94126024801c4090000d8039005400110f2400100c15024100d5820100e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 141770368 1250 141769118 141769141
    0x3110c0a0e040305030a021903150510020a060e0c060a0807030b030c060d0c0216060c0b06040603111002070b16110a0503100c0c020d030e0109091b140c0114 69
    0x110201401060400030030321500450880315035000d6031500d45255a40e1341d411548010f406400107481685d8240301450607043e030181c0100d540c100c0c08a113618029650341c070400c0030140071b00d00b854001d60860034204ac081030f0b00c0c0d000404404080b030304070f690000c1180c000c10600e50010300c044000420150030700c9400356043c001c1c19100f01c03003140105400c0c45c001000411521411301c1084419559203468103045000340004540c10745a003401c100f8040e0754400292116221520444060301c008000a401c1e2a00d88500e0060720340091031003041200383c400348801108001040c905500c519080001d100034194020700c4041d1382c0e8400d07091078032460701c1c2905a00c220315161902c6001041424032a68500060661195040303590120b42c040c0580b009848803400303d540130f90030800800c44002419000898200308003401c1c0d0325001402c1e60b8003044c50807100c10281ca18100d040c20588244064032641c540d400700b0100c1c02180d4982202404c00908407807201a030720315089000403c0000c2103500c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 141771618 1250 141770368 141770383
    0x902150d150b03061806030c040c0f020f060c0f09060d0c09050f0111060c03070c05061e0c03011202010509060f0309070f0501020309011209080c0d0302120a06030308060409080f070311 81
    0x91254890644c101140014100007000417034403110302d902c000003450707a6420130030003259647c05042048000c0405c400109440c800080302000b520483e00382404100000500302d11135600d10507864101407a803a4181d02d15840450120740c4410705101c5902140700038802c4000202030307900d858255520700b8050010708104900300c40c0c14804810a403d900103000304e451540040010035207650b82d9140b178021f03582c0c0090543d01070424802d0b64100403441c0007115504001041000701072245540300381030040e007440309000b42d0f00341c100e00e0080b031001075000d5400b41c00d43c103000078411400c1c000b000141c081d046d081201c5001c450b0344108003c00c80c43d80085103442c003a120a2000d940b07850034540002e4075041c4244150812260303152072583c2072100840558103c4076480c02034516008403044004d000c1d400140d51410a48410b00100340030202b184074600449500d600c07200400d5131134004000c01000c50700f100362a20b0804002985c0c4ca901c400c40100b022500ca0b4030f40c010082604003406160002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 141772868 1250 141771618 141771629
    0x170c07090f0b0d11131107080d05010e0705070f03091a0a030b030303010b120603150708150604031515030c12051902031207170a110c0409030e040902150d15 69
    0x2c07004103000030034604401c0f6500104145d40360150300070a411180004e11144d0402074201d03c01042040811110a0083c801c2d40b00d01541403149903200c410b584031081c0306a8482000c20b808004e05400030380515000b00c4840d000e401d100046903550046070300840c24440e4010560000041c1e008502d81d0140302c0c21000c4001a0003c0d4150360506c0c852403154071a5221904a0f06819000200c031580e04118a600c0320510303400c5620750f82072000b07018000ca0416100d441d1102039849421509060540c02c0d80d00f129045a1100807007003a40c1e005000a140b0740220781e4401003030420100c003007005c85005000403c8400b500f000f41d1041401c0003410700e043e078484082240d007403462100c0941d0300007881d481c030340c2146c00e0410341e1002c25181040d600880085a4001010040b400c00c4c5031700d41040d0740b10383c1d002c0e0003002e81d1000b150b03020400c021955440801008180b658400707000d0703410158883c1c01040c1c030107800e134060100c03001e070003280d150455124038a4807510386804140c400c0820072071300300400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 141774118 1250 141772868 141772879
    0x15030b0a060608060f12150414030c0c0d06090b19060501020606100522080a150e0604060b0f06040b03010528230409050601030203010c0903020d170c07090f0b 70
    0x500b00b8a006203e0080030b0300c16440789280c410600b109544d80b111060300c54000c071040301d07818110b020000b403220304100c905542c0c3c0405c5200e004250301d030100c11207500c0c90103400900010b032240c9040120b4800294005c0d02c0c1c0b40c3e80e51070401c001899200c9480e0045880140725001c081c4114501c606454840e0400d904542141e018410903403243c40000b81421054102603840340c0f1180c44648040c5203180c0450340d803c0744100b001900e0200814a850785500403a910204860010209000d035040480c541003241e02407030005021130000d41c85000700090003020350b002c1e1b113098400074002d80c201d038000e641b100e840040100150f1070000b029007900d0142c844081d41c489070925a10b00d150300e031441417003180d0861400d1340140340500441c40d4a01c880c001c0040140002504015136074000900049010b5881d000c07555901a0003540100c044a5005018041c8a02c2d25501c2c0d01c5607403030580c40c800000700c0c02e101802c203e4505115030005841c107410006a260314043c088800e60700c1941c0e20902a2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 141775368 1250 141774118 141774131
    0x12150915050a2007060b06030a020c0105010902360d060e0d080105060301090c090902041206060519050d050f011404050c0a060503060108040201090333020412030c0c030615030b0a 79
    0xd10707007840c5184080c910244003139113625542c10b040000c3d20480b0701036680102d000080003060030b0b01c0d901070b00d91042130f50001c000750380c1c0319134111b03040780b0a00c00121000801b0b200904800386501140c18400004003080848400d02a00070034260304494074100c03111030f212003c080700d4240800090703e140380c43c1c3c07421490b02d502d08404a89544018010155025205c2a80011250155031345400410614008540c4e071503a401c88181d40032a11002143c00794101000003950f1f250007881c0b0742071700c00c02c00c50003500e480c0740c0020001c180da5511000c4810f0b0080c41140403012000b07103e601229541c083e82d40080c5c1c40e062400c1824500f00d80919440f440300c0701014010f1541c04800e681c2d010f042828907034030b66201c9000594417511035600061075103008400e42c80d96500355a994031514000e5070140d40c954600d80c901e5500f80d020740e000303c0b41d9041c007810f440c0f40402d01c03e00007a900355010b45580445580c6035101e440039500448200b282505941d02c040003002250224507034000342120040250 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 141776618 1250 141775368 141775391
    0x1e051809150d031e0f03150609060e030a060906020903060c070c050f03390a03020303161b0602060708070201020c070308090303120a060501020c0306010f12150915050a 74
    0x205841c180a05000d01d000380001c1d420140195940d40122040c4514488803105008000f00038a020124600010b420304403c1c045d0605070000f18404c0e00e0813a2600003d030313400c14104552010181241d542c3c5441074450b0b41003c9441c1c3d100341b000c114051032000da40c5004d8a01030629100c0050801c0341c43c0e180c1001200045001c1c41d2000c01503440c00c83d42c103101d15000d00b0000b03181c00789407c019904980380755011079400e8401e411200d60900c0903491210101c03207200821040000780c0c0700194141c1c00030000c2d0303c6c4511403502110240fa1040e8145540140801c101101d480820303000603001d42d02070418481843d40110791f145c0e001650344000d510f0461625034058850a81e48401000190080744c4000766940c10f01c16500d810110b1212040380340b80010803100505184e20942e40503001d600a00d880074100410000e05a41d02500d42c3c140c883c0c40c1100d1800d90718540c41d41a941c0074140040034000c412130b80981c0e00038602aa00803202c0030300309100c2c0011034401515020035140b900c1d180501 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 141777868 1250 141776618 141776641
    0x40b060d03050913091704050a03060e0f030c06070914030a0b06060f0a02010b0906010207080607050d060e0f0a0b03060709060305090a020a0f030308070305060105070609031e051809 80
    0x90040040d00c1180c000091403600b59164000c80384043e500c6044250316584404603a8001400b80740944100d01d071080301c500700316985201b2805041e800822010080c00402c074190000354181c0d10003000c807002c8008194003d170650700a0440d58100d81c0001c1d003070242c540c0c1e2014080c030245c030021440030040081c020029541d00c2d10490010000c1e1001400140c1c0c690740c20086c5da0810001d00c040c4c40e03690000b075000a00811403520402d100303600b0342c00031450552002560000303503a60f401c018070b2103481c0c100e810384003030300304c80300c00072485403103000201e90400d100c602e06000d40070030b81c9500c449041100b4a4026620000340d81d5020768040710800a0341540640d01070102d502c02d0400007016118081e1480c141070b295000a500004038000003e0300700703209801001183d003c1d9480b010311b9140c1c060107c060b110162440360000380244980030214000f0303802072500d244a81481c00503481e40700f8406408000c80351201001c00c4010601500d00c080800e00c0040307a04045038180003924083e0308850 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 141779118 1250 141777868 141777871
    0x60702100b011e09030c090905060f0601050702120f1c0809011a1c0b0106020a031404030f111f020105091203010b0301060804050312010b0d060e090604020909010f0204090903030e06040b 82
    0x55001d0f030902001482a405000300e41c01468000c0305030409a0b40310302d40c5101900701100216558481c0c140050402d003a01c0144a006400507554180b5002d00d42d020882c0d20482c004c110400f501071064914100c0408000c0512401c03200c0c02030000c1c1c03600400c13020309000c80007802207245034142440f0504000b2083c1410000103811902c03025681044094400390701c91003036000304480001000410010b400040020106210303a4030804000440700f0b0310b1029001d01c2c80014094500400c2a100048044a004900070b0001c2d01c000425007401652070404540c0c0c684200250f5941c0051210008003844801d0032050345811403860b5503d0090202d0300340c401489407508000d00303800800c04000f000e00444400f80c100da510f04000d9612441d04240550001003138900c00751502000041c034101091245d03216400140c0600780bc0c0d43c4507020b0110540005007901001c2d540c8440e8001181d9940c4054405003440d0500011100624038001d01242d0340e565a803180c952107002044000382c00e8030100d5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 141780368 1250 141779118 141779147
    0x60b0108091507020c03030f040f06110c0918030a08060112060b040504150312090e0f0412030b0316031103010e010b0d0609050304050a0e04060b0a1203051e0c060702100b01 76
    0x10110781d9140d108030705040b810302600c0d03450b000c005242c800d5080230001508c02d44120300d0008100c03c1c1d45d450203070341020306103124031502d80003a80641c0252801041c1550b001449991803c0b540381207030a1542160700c11520a004940310748284059942d1090703803d0360385c8055540070040d603400c06100e00081d001361300c2003501c43c5460b03501d018170940c01c42910302e00860344221448802c0e1b0403070300c010780b500c1e20324000d0031641c00c009030010b0381c81c925040c01c8500603900007202d0074001d800d07210101e020300f0b0881b5a5581501c03c0c900b1002c411980e400580380158000c00c405a142102d210805080d1000f40c0b54600e4141e04210640d001d65075001d8a103440c10754881400103410860380340890850185900080c1d000c1900d8400250f1491006000c41c422841940200404281002040a11029030080030342c212045ca030076000280c0101e00500c14003c030040001c00a08840b02d00d49856400803103501c03070b10f41101d41400240742d010891039034501c0f070f502da0a010084c808000241a40300d0301803c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 141781618 1250 141780368 141780403
    0x203130f05030903070e0703050702011a01030209150a050c060a1a01231314040e100b0a09020a0c150513060903180f0f0e06060d0507050c100603060b010809 69
    0x201001c00208204803408a0005000c0c1c851803982d486c45046000011a030b001d012905000016020f288103210301e81c10203448040c2c03545076030000c60046000b90422000320381c008240c20b0b4074044110461000d04860106a034440341d40d484005122030800c0b90241200d00303a00d082c85010018408070800c1c404460f502880c001d00841c81045092a503800007001015907000001031441d000880c000c0904240d9001d14554209050224140b004580d0314504007842c80d0840c100d2903e64480c0c071303080075209074801040e180c0c44c00e407102e046100301d03803040c04500c02003a16115090204100d880b004602c83c014041c2c100402d2503d0a100341c0e800e01c2c81e040080801d5594407040c0d0405000b850241e025142c0100020030700e684035400c808008020340917005942c0701800380041c00c3c0c00b03043c100300d00c121406000a81001002510000030348000340182042c400240210412994200160042680c1b0500082802d0b461410070108403034082001d5030400146200300020100d00140e90030035071824203e03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 141782868 1250 141781618 141781643
    0x3060f0f0e060d0f0c0608010519090209010306051503041a190b010c06091101020601090209030c1309080f070c0b070b04151b0207090605010306032a0506040312090603020313 77
    0x10300e035182940008000300c41350503042c01032182d4220fa000075200030791030f584000c0e62203100f040b60713180d04803140503102951000c091140c0d900980141440b103c06040c040b03400c585403c00212010008503a070034130020301004000600a0404400c8485552120403110b6030508004041140c00744444450025442e2141c9007526441400c1d6001100d401071000c1089072501d20340010504a030300e40850051080400102e90305155108a03010b20300024010100c445103442030240d00c51810804481042e80c40038504086076800d03005201350a5a0302503199a501c0602e4505864000c64100c0d8125404c1401003070002015001e0481d08550890502962010071040b00005002c072030303000c0e64058011800006040e900050440309654030040144000d949a100460446180d1712000d401300c0c0f10a401c20061450a210880c14030000040341c81d1801d44401c003040d250390050b4400c4440c421200301c00b8419a5000080b032003d081a840e003940b46040c1000c05222040e034120014120724207451 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 141784118 1250 141782868 141782881
    0x316123f110a141b090c03041a070507150506010c020d14030415090605070b040b060d050714040e060705030f0c0903160915030308010b0f0405090708010305120703080403050306040b12070603060f0f0e 88
    0x220b980c203109d400010b8003451400c0d040080040d0070800d0200c0f403180074510380c42c040c10300078010310b4803600c41a0750390001c1a0b031a40030400e6102410b58240c071040c40c10000c00e15000707424802000a400a014203108510782100001d01002d51984038108005050207030000150210700c01a03001500043e4008050301c0b62000038481d0001c5100c0200136100305000015a00041007106c100303000d0881e01000803c5440710410f40307850084078898005a02000040c401e00010011150810254a4258100f50032107010034038245601c0b0410381d1500c0d06ccc00c0c0402402a09024009aa501e0240480780071441e540d0050a003020601825030415400f003445000515840c068400030701c0001c1404009040c821406002d8580078003054070789028203941300780c441003c00102d4a21035030544d14080700b03a4a0340c4040b20903420103054241d00ca61124080c1074241c0e00c16a004590390242d0021340a042d1a00401504845450340002d041c2c80c400b800070080d03185058010002c032140c80a5500d41941c804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 141785368 1250 141784118 141784133
    0x1809110909010b1906120911010c030903170d0f0c090b090102030903070905090c0904051009030c05060a050a0605010912020d020316123f110a141b090c0304 69
    0xc41080b03030404401d01c061340003482007803162003c40e02c007500d84658818646030700c0000d9803140741010303061100d0404625000c1d48104000203505000e454840703040b030303140e9581e0310055600d4203004218210102e0300c4000c03051544180c00040c8141c60003040038901c4008058015039080c49400101c00300400c6861440c1d000f8401c0360070011004058481e40c80e142d40c03580000b00f80c2611403c0c6a80320308286d00c0854103241000c240960741180c01440610311803040c681c041c04607980c0c100e00304106055004001001048000d01a4850304408280ca14001e00c0d41c00132a2015446141040210071081001b000460585107840d90159036642c2504d20500220340307041e03c460300b1005003c1504170700244071000039203018080d500c1410501a142d15080105104001900c038112010a4030400041151210902c41030b4074030160030034843c11004c8411883c1440d9008200751201c818035480d8203900001404914400b20319583e100c000c81200001080c0c010f4070042c941890300388000040f40034054072 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 141786618 1250 141785368 141785381
    0xc060910081f09090611161104020f070303090210180b07050c060309150a0203010b030a0504050a150c110a0c3003050d050708060f10050706050a06180911090901 71
    0x402481c0b29225a2240b407000144858101135420520348503100c0040c030543c0040741d085554841d40c2d66082d0840d6100d4049180c00800c2280e4815400c010b48031030f1890010161001c98040c4d1000202c01d070460040c00350041548403400d040080c480681c00c80b1012520368141a00c50038a9003a866520500e465490208203002c040d5010001000708815644001406e1090040280000109494030340395042a0300080c080d000038200c041c00020b589025690240384c0c440d000f1011203281031050344503942c40e154800c0c40c83e6016a1600020300300303a40c101d00581f2424140d10010214107440c2d840e41042c582140c000d0f150340070395041402110003103450809410800018041940c4e030014034002d0800e60103220401d40d080d0071f000000e044039014010382441100c01600c2e1840d1046204200035034268000070100030f1210521010340410140d104051003140001e2000940c282482044040800710b13244101c10307542862200030004240d080c0700c21001e0713815a18002e10b0b4903400e0866024008 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 141787868 1250 141786618 141786661
    0x50102041e05010f0215130303020d05010b0c010c0504120305030711030a0314010510020a11061201030c0603060e070c0209060a03050307120801080f0304050f0607050f0705030c06091008 82
    0x1900701c180c5085084500040101c0d80242c840c0c1c2c1c160480500b090b6100d1095801d1240200300501c00982c401e1038444050002c5442071500601c2d1003002c6500d8012100e007a0846807208030080342403c61f03050248100c1449183c50300301a07007070914102411244403500703030000b0304101b0040081035a8a00413946e0254580311507080c1c9403118050709005000300a62040c1c070690700f015400002c0c5604060b580c002d1125080c2c0d02911001010f43c03500f0243c40fa405501035040601000302d6620781500101441c0a180700f810b22035170003464508010141c410f2900442c803141d024130701340070495402042c901d44503a03056800b4001a075846000a10310840c1e0b1340b01908502001070b00307804108200e00d0707000852000f40c86550950742c942c7c2c0724694400070450f4110706130740204400e00c0350f407825840f4a2040f00d4000c015501d002019a43d550403c4094511040950f20500c001d20680c60140540121200e09540c040e0600d43d40710001090348070b201036070100f03002009000c0307000643d000b0490b01c135584 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 141789118 1250 141787868 141787889
    0x70507050d021c03110d111515031b09060f01080a09030c0215071a061e0301020c030c0304060201111801032c0f19080906250c091a0105041205010204 66
    0x42e6541005443c3c3e00420f017100381e05008600c403004c1013a020744210b003184407040c0c0c0104044034840c182c04000302400b4040e074800f80c440d009149d100d60b40810480d61010741c840c5084c14040c5080052020a41c000b4060501c61700f003d8900380d076035990110006910201145011544114904050724140d0505030080d4003d0075101c030800003001c01130028000184140401035494040390b82e07900d0103038029148a50b00191210b0840e82a4141c8405900c44000007400149802d485180742841c503800842014a40d81003c02c0801c070850b02031250440d055440d0039001d10303050303d8202d018a4400c100c507940381456602c20002c9481c440e0341100301420141a011181284402e07a14165030301d80c00b80c001c5107103101d00b41c1203801c481d07030410390340462552005c0f40303d051044000410005800407510082089040d0b5134003d140490398119070340702802000e45158140c20565010142c0300c0342c000310030030500d01107502e100340e9a10100300d808031942d0054043c41c4060515050380a8826a8400c10412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 141790368 1250 141789118 141789169
    0x60804020d08040f0b2502060f07020f09090a03020d020106060c1e140102091318030305070c0c03060615110a0b0a1d0309031515010503071e0c050c030102070507050d02 74
    0x400c0640c0102046940c40c1c0e140808440007046c0684505c2c0c000384000d410120600444008001001c00b40800300d100410b4034000008400209141410417689603041e5846101c0200c10306070180f00702c21303083c2c2983c4000c1c02034904003030020b4407001c442d01c0b0041c01010500340d103020311090588a020002d901048280d56040005103850103500200e452610502034008154903900841c800e0300d0782492040c1c5451294040d50300e0550080c1001001e0320b06000004103c00d00103603107003076a030b0051407041c01d001500d6800d04800308400c424540546040c08180c0e1103e050f81c80d400941909103940c8200040c2080e6161000c00025141c1c1c007a110003000001c91003800310140110103048d40540a0b8102e402c0080d40d00c08031141190709507954400d20b00c10b002c3c040c1c03095220b28019540440c0c50f00b012001204080309101420201e004694002503001400d282001810712015000c079008400075400d10040b40ca4060312001c0a101c0c6034418880b0000d00011521151103c5003501c01010051120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 141791618 1250 141790368 141790379
    0x703031116110406050a091104080d0c06060506121807050d061a0603130b1f090b0109060f020c010302071b0b0a090902040b04060f0306050a0602150f01060804020d08040f 75
    0x45121501c8116084140440c1181e40750510b40b207503100720b50000784200c000a01d001010b40040100b100403040e0010100804070380704c0420004031000c054140c6d81c000c1c0c0107101c2d080400449207c1d80001d84281410001213906101415015800c228503040240190b091200740503d0b240301540b01036001004c40160301c0c05c0c464a588aa00000c0303e10001d04400b44002e004c02c4040c1c071007107540c01110020704116601191442e80916800030700c0088440d22400c1a58480b03510300d0895010b00350244d115185202c103540d000321500b00500545c20301d143c0340445003602a44440300300c218203040550116009041c404104040c0c5654404c1e0139403551305949030030f41d0220766805a0035000c0400c4000d08000380c4032045100716800c46040c0400e0500701820328000312289107196200208054443c0c1c1d0204642d641d00700044000c0009800a000da42214650614040d40c01403804110441050040081a401000d042c1c0e100d541101c20000500307941c64810254090341d04007003203402c0c503104045903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 141792868 1250 141791618 141791647
    0x90b011203030f0605010912031206030f03020c030c03100c0c060e0616020d050f0a03090b1513140105190305030408030304031103090102070504180f0614071701030807030311 77
    0x80740650b805120350750825003008152660780c8070b50f80c0000e1070f0040c10005a80b17251000039401d84645000710845408040003030a07500c03190426107030070790000c40d400304240e0104a4108042c2099018100119000001a854130600c031030380022141c41d1400b9481f4544140030024500f46e00100c1003000b1250040020b0381d401044810100483c0d00303140c403689440c00000e02441e941c0345603584514151103800e5809071900050019014180c543c0307c0840043c040000d054890300d4924008810b003080395040100c1c05042601c0f48281d6840d28000500325603140040e68107454055a4030701883c0450f000914064000358409861800049404107101c8030102c015406103009940d00f4134100642e02585881c4c1c07041448942c0540c1c008402041a410b06401001501c0742a01d03140503c101e0315200c45000c00e070780da41c08030380b142ea65504c0b18401d80c0907610010341000390341c0b6003646c4003074500020ba000e40406000260100c900410703100105403180e04845d100f03141074003d4a44603146007a501e032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 141794118 1250 141792868 141792899
    0x30c0702030f0d17010b07171615150308030f04230f16080c040c02031b16080d230d0c020604020306010603020a0509210102070b01090c0203030402010c0209070201090b01 75
    0x38801c05013030208040c8585400e4140c40c5004c0741c5e20b2800c1c0c05036a40005404035581410b400e0003040c000388000c1425160282d10460140518544440c2201c014500b292144040605c07071240a0509001245910054a82c022400e11110b100c1c2e8031182005102c01c2d0320001500c2c0845195580d4144010003ca01c940d0f84070804000c031850074030101e060590100903805442c0380741e0b0000d9092000b40c642900004501013081c0192454144006ca0303241ea0f02038000031012040d8040718241500c51150760b4600020610300014000b840c1c26587c1c020300106a418020803150034825000604c02100d02c2191034041d080c5c0000c002d821080003000c0c0d143c16080f00c060b84240104070001070114028001c8510f0001075036551490071494a00300b0104c0c0204500c050b21901880c3c1071040303407041c01d10042503c18018148000b90b580340c8a686000d440c0701c049201c0c01c40d0014001e000050b40c1000a0b02d0700307664100c070308030020364400b81c0407401800303035130350181064422400014141c42c034043c211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 141795368 1250 141794118 141794143
    0x90a020402030c1e12060d11151c0c020601030b0a0b030a030804050f010c02071208070803130c0f15110c0d111801050a03020105030405030c010504110f0301090f08030c0702030f 78
    0x52491310b040d0f40700204540600c681d101407401d0360000188244c40e12905150725280b02c0d20440003c1c0820002281d000c502d021030140e6170150000b102d801803104000224140303200314205000c04200448005d4490006100082c10500002c003c14410000d541004400b034201030101c0d240303000d0f5424020401176081d6400d03200d5005440c8004c0c5000303018001c01070401e1084c0c0061106034507005011280640a071003d80344240c041c804540029200c40003503000d1402c003070551551100070b0611a03030f03440b00340d4880c5226044038001040700c5c0e5008442224410000e040c44074040c0074400445003400c3c1c00090040c5d0041642c4404401c001603d103056103c604151640240e030f903805460314000d07801c280545540030001c00720810042d8403500007164020f00c50383c203983c204004c41e500c032030965006588c200c0e10340030b8141c10000c1c3e500f8140503407880a10100c00038808103116032150714a4421806000d4400341c030000000700f0500300c1c0f0040b0f51841d503010701100ca4040c2980c085a48034235191901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 141796618 1250 141795368 141795397
    0x180a0812070507020d0b0711010f0902031606020624030129040c02121b0a0f03030c0806060304060903110714180402090c090d080409020c060f01060207030308090a020402030c 77
    0x810030707140c41075041e1000716501405030210350b240e544403202d05000041400c0304000815850300134100007030151440c400e0300c01e440403514034260310405082100000b040f54000d640050b04000643e40054031a8200c004040c807003030754214411038048030340580041107400d50b0800f0035a03030f00304c1910f00c0c3d240070030761f0440000c05030300b4a003108200c181c4220b01d59000050b80410042e20950030310000600044842c0a0858802800c29460504011501390140c405184030103000041c10b8040c0a0045400c002e071400721200c1c6042000030b149404041e0010306900e95401d0180101401200081d680e54bd40d0404c5622243d5144006002c20002c8401e46000c4c044c039030301c103541c0c800c0304a01c05d50050f54020030840300c90f6a00c0d0800a9190400f0303042aa00c4a40c0d501007602040e041001080600b651444c0540d44011402416181c040003034001c213803ca00e050010002c05a020440c1070550b50b241c64050079544500b42c03510316090058002a600c54400001e004c0340c0d5a924006103c0c0c0f43c4035220 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 141797868 1250 141796618 141796621
    0x7080109020a090612060510020f120304120804020a0e010b0706150608060108090102070c0303050a023f040b0406020f1b010e040b04020c060a24030812180a0812 71
    0x1501400d901414001d42c02051000109000150103840322811019100c2c500040460351003000039002c040400010b00983c014140925039200280f011301c003513265038889a85503050031760310200049140740d105010003500d100070904654a08030303520001c0060001c5004503584524001105900888049800300d00e040c40349000c460034040d0000844219440e0414140d6405c401551072800044c86002c265600b04581000914115044c001640c040d81d80c890b11031900da0700c00b0780f40c43e000403074100c40324100c2016641c500d01c007502d800342520700c039400100520b82801810320450107a07410140c1c501001103004030300c0d294000b0300656004282e00840364420a03d9002003040c0c8081c001e424005040310b50a1842400d09400001402101900c0140b0740001080807600703080c01a02d00c2c81d41c26840b60218084d07010b2220403000070110900226003040d18661314045a8403c50903070242960144000501c2c1c13079640d0348405040100c400a45400c0d01e010303d09a80c1c0c0741e200c28405911075282c0c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 141799118 1250 141797868 141797879
    0x1005070e090c0d0b06040b0a03050601110f10020c07030b0411041b020709020a0507020913050106050102010b1c0611041d1501020a030c06022a0705030307120c02010e090708070801 79
    0x1d080d8040c9a100321001e1620365103001950141038070f4000e00f6000b42c0104400030714007030804e009042c000455900060142003000005003440c90041a0141c10f0780402c12001c3c040401065510081e9103d6030016660280d102c0ca0301d04111644d030016045c030810504000c01c0c820303a164404207140d0211410001e8100c00401c80400150006003440141e00c21582031091021960003000d41c66010302782681040c415a0009031811011a104410304a0010f44941042400d0145602400342400240410600080821052007440c41224001c0d12070003c40d8080c4a01da90103020000385000c10300342e5440e261048000303101040c001e90129006e07460002000045103001ea1444084168090107080010352000c03507642210302019541d055080048074903104214180a5014a0b51170b65142c821003080b0b809400c2c481c05905c640d010f0707002080340100061070182c0410f000c40745801c0034a501451400100c4a088529511a0700403104009001c02140c004020078400d4480b41c3e2010502c0c0e0300c2b030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 141800368 1250 141799118 141799129
    0x90c03060911190e01090306020c0c100908031204021504060c0c0603060308040b0d110a020d020f0706080c0d0e0102070b0603011508061824060a12080d0b121005070e 73
    0x10028405204060354001d451070311810465207801360524000414940ba5214a0100d03801083d400103d60301008101159080119488821400741c0c00c240c58183c0c58002c296131030f8466104240d00d11601c94000504541e142480c07131f40d000184c150b1303461f01d541d2981406058920011825500b01000c00800a00e90b8403900603441500e5000c08407505007442c11114032403e4015203c0c1010081c0ca40351445a19078102c8054a84d4000c035500a007000780740404040c0c00c11250702e200c4d4800b50410a41441410f4015082982080703c44480580c1c2e0411924640001c168141e80390300154000070300802808031031241d0303030301605086008015107542c0098083d421031162241c6c0e000c0380c02200000303110700402e81c00388205030740d10300a030b40c040c0c2c4112440c06c022210080c004074000e01e0f15806c1c0505820103061450140c02d6154200c20310006548464000740140e01750007030701030b44594071440241c6985061a5440c0f00900842e00c204031410880006090101c400000107409444105a603103040b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 141801618 1250 141800368 141800377
    0x31e050a0305030601120c120f1b0e0d0c0b04030c060305070f0f0e0315040b1b0702061806030907030624090c1103040e01230310090309090c03060911 66
    0x10100400e00008140e8041d100d03030700020011414040031043c04d8020980c603004011044603581c0d2107200030710544100d08101c1e14060008c82155160202541c1389031240c19503c500c0e04550300340224404000000a50700310004000100380541e00315001500030244400340c0140c905c0342001381754064444004800700c8204840081c0081d4070610840c90407030043c041ca40c1d0040a46c50100019501c41c8040391501107021000c8024001d03000400c402d008009203250b412030040e240c40c202030800040000058080d5a8019200750b1001a0311068021043c40c2002001c0c0c026241c10744038549220f01c651222030510013580c010b410440500400c2100703061107440500c4c03c00320340c02440d0805010760300a1869a401c3c600340152500c603507046d106c0c100f010300014011420515002c0d0f042c801900c40d8207490200ca0280e441805144140ba80e50205910700701010340100001c0550b00360030112494610f903486885c0705450005410309443d4150050700c00c1e20843c110502c03404040c0010a400c0d0302c40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 141802868 1250 141801618 141801623
    0x7020d1a100e1611010605041814070302010f03050705090d1202010f27080d02130f0506040b04030803130206040909020a12021c0f050114062805060a0203190801031e 73
    0x14455295800f035070081c15502d0800f1008000054213175101c8003c1022920000c40d041c542c0c03034a4036030100411540300d101c4502190403401400085186034006842ca150340000d070401e15485074000340ca540d110384184c2e007040b42d0041c0001280003442c1410069080c0e05641c0300015402d2240c411040d00180c000c07540f040c2c1d842d07030720340318203c58107004603d0418a0090859140100f08040c0d8852181760025001d25203039000d480040f649011540005490968440c501410341400200060700c0350005031001c480e04495201d64075941c0b850011815501038000950041003c5400309564000b0b80c4036640035442601c1203502da07621410195801c04d64148001c0d4044030103501d00b00100380550903202c034640f10300b8540b250079407550745260941d05c02c2c80151150755904800c01c03186140800c8a0015694518140d001701864070740c100d808070741680240e60280300c0005030100ba40e882041100c101d800c00c40440c1d5552038103102300816100302032000307440100c1072810048109002801c40141c19a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 141804118 1250 141802868 141802891
    0xf01080c01120603050303041109150607060c02010b0a060302030a111305010c0f1a0a0b010c020112110c0102040801061403070e010612020409051006080c12060607020d1a100e 77
    0x14034001110800da0101082c02d0301622020300000141080020714041c511840002d5019000001072112600004000300e2130445031a0261000d038076640102c0340e1068108501003450345822600740d000d0443c0d000c0850f040351914400003810b42e0306901035401a400351009010324500040e041d1000e004118a4908540c1143d00800040d030244200c1d40780140700d001306018017241c0c0d84400003955560800c0c0d5500549000410444a03814440c405010409081111140036103800007003802c0c2207142c4070503007599034204284642d40e0314001e0f145d2000b0004029503542e51103d203000e01030075061140d01c81404402864104a24020030f05000f518101000c850940e07180c90421155194185145000c1a50801c800b103640101c0e809821f1007050f41101c1c82c5144c0340340050043c41040010300c4400d5400042c40104880c84a200604d0740111081300d00940f12111400080c02500100400400b540308200440010b00850140988200d1035034080c0c1c88030942e5552030b861807507811103040610301d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 141805368 1250 141804118 141804133
    0x80a110d0306060210050405070f0315051006080f0a020d0207060204030506160c12030b130b030d0518090c1201032a030308010e100e07020a0606050303040501080609091914060f0108 80
    0x31700c825840345070700500940440300450355405004801803043e42098a0100038ac110901c0040a40e009003900300000002e00c000303280c54042d000381340304800750040d652942240c3c007203411510f0640640c0c8181090702d00440da5000729280000096100e0b21080f1001d0240000003201d0411b4901d80e0031101403d5182c00540000640d44e200c4042111641d40c400c0c5950341d08000469226900706401f016110080061200400400c141c94407066090240c20803408100348995203400c02000c48076000305603009a0700351242d54180c140d50186448400290b900f00300000b05200382c10391040f001c291102a81c03140401c03542121b00c0f1100da03600016020480f810010440c00390351450304d690184181081c00c000c1c9464030200c0c008804140e03030101c01a4020040d8038248081c03031013024000e0000320011841c2c14546000a003c20704d005099030700c201c90b04c03400504100c1061150030002840ea080c2500503c4030744c606114021050394040700c1d00d200340000640541e0151052606a980c03500051444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 141806618 1250 141805368 141805393
    0x30e0108041412031905070f050717280507050606010e030a0210020f0f03040305070e0403110a06090b0901050601080c0d0608100516020a0b22080a110d03060602 71
    0x1800680116004402e080b20b81c0b20040301031001c00540500e6401c110350f00d04110312014101174020880c401c60a1920051281080c0c101118995985082c1807a6844032818108403040c80c0d128002c003240d8000006100000c2c0328840700401b000402200d04802400c0303000b00459450250300d0006046a010f0000701c5e003158014101202c1071030000b000c60355040c0c0e1719070204101c42c90441d2000050b82c80003e80c010070f00010301024090a1030500103500b01451b40d252280c0d5211907102e07008003803d1000c042014503202d0041b400040010301c040307503000c00c1c903031515a00811898800755182485800490710301c10042c000c1c14041c401c142d4a200700d039110b8024074440740c1d0001f0f44240d203c075500d0400080701401030250002e90442c0840000d40c52914010040d800d0003151503140864220310110070028100d8141650400d41c00c1c0303001c59500b400e50f030f000b00d080b0400d0383d0098062900440c2c0310300407aa001020700e02c46a444e80585042a0b818001503055030035602440c00540c02101030700b9039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 141807868 1250 141806618 141806627
    0x13080609150f10030501020a020609061806010b0d020c150a050606030105060304120203300f090d05210a09110913021302040e0403090801112b0f1a0307080703030e01 73
    0xc200c40c8940900c03c80a99a035101e508903130002d081803000d07806c010200f01c9030350030905c20142d002090a00603640f03039141c200081c0d2a0101401034444111001c40c5001c035080040e03041c0d400e220034030011100e640b08003183d0210088412030306110391b0f030300f88000520345040503001c0c0c078101d50700900b039141982c5072940c81c050200c518601c00c1c01180b00600031403401c680002400f080510b217058a80c040c40c440307605190302c0400001c0c09044641405001e015056000203a440103080b500d04d04113450380c40001074454034400e101d0507841180713000401e10007150815400407411521400800480f030343e8070070510264400c21540718001e040c03815064009428089180d0480300305120006144c03c0e140c41d4001c984403030584055000a454040a004080c030134450160b600040c20b11550400030f420350030b100c140001508070712600d0200040d020320340e45c180e08401007403104410180182002e9100314840b004100d07112510034070a5110004180e100030880c1ca040d00d03050354030700407800c95a01c01900e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 141809118 1250 141807868 141807871
    0xc08030702250306060b030915072606010e0a0303080c0a050f070605090f061b0705010f0c020f1002030f01030305090d140606040c030b090601180b13080609150f 71
    0x3540103a161a410b0300b00040b4004804035026200a103000d810350904800f10b46480d00401c0c3c2c4030200304180542d8000008400608918050071704003e60744641c021142140c2c0f0b600d02d03c401d0343c42140014240701d811140c2c184142000c5ea02d100103038100c802006010440b034070014000c6641c00c40803c0721504410010703c0c0d0105281031031440e0451018050640c0e600c50b0500b545e10079519003d001e080c450601100e4031000c005801000e039810700c045c151464003000840b1803480074001030b03104100318080d040303010404901c0400b006860703481403019480f032074031150307000c0170f80030b804592154400d40d4400c1e60b00030b2212514900c038607030850707030261050f60044c4c940c0d56202e20003010800c000b07000b00b44511041302815010f01221b040800c1400241c6801c000d400c3e060500b00b0070803145544810f10030a5100e802440c2c00c4030881ca0384200040c8400c06d940000e40c05020004203a0115241100040d007151581070071600c041c1c4d07950000030388862600381c1c086541111000850b050044515249 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 141810368 1250 141809118 141809131
    0x10020a0201120e01150815010f180216050a0609020f01050f1917010906090b040207020112050c090312030907090b1c020303130603140711030a03050a09020a0f081c0c0803 75
    0x1401280100340100c6561040d48501b91a40c448008120b0307e000d08410b4600625406032103070300c03d5060005402d0581c0c4103d0004d040142e012500d246c10b1802d60007040c0d440c580042c140c03400003005042481c042d1045031b8050340518803a80301124035520440c125062011401e6126007003902200502250b050450400b2040200409aa132008031043d0a0b481c0201480d65000452f103140c84d03190030680721030742070b0107100380d206000040250b6004106a1300c03800c81c2c1000061156a51014038615008038941c440c1c051003020348401a043c4030b4001140504c80c0941150640c03982c0d60141070076180b00821440d04007480309420f03041c109980060740c103103510040a403070405d03070510308894111545074440400a600c03401c3c0583c000121a400c580c02c46210701d401038a040d21152002d90341e2007125050020550340d000044e2200c50194848548558010054440541e5810700d03040e5450050180080b14002c10711140c0038106030311880320b201501900e61680c400b4054071881030540004000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 141811618 1250 141810368 141810371
    0x1020607050c07053d0306081203010605090a0f14010813030905060f0c03160210030c080c07020406030b090105160c0c06120e0a2d11100512040b0610020a0201120e01 73
    0x11038101001941035403004403980030178510105900c1c4001002d940300c0c4d0b07100d2800754210010681e40c00d8003903000c40e815112141000c0b6900e83d4001f012440307103600c0b68400e001e03402d900310700407030200341b01c01400d000c040d4241d80b80e03426501d807445560030985803944000d0200749101020000780c28840050300b80b50f041499402e0801001200711402c40e40490b4162840440008501086140002039046501128a4108414001c080c8050712410004d80303604078441022a61408541d65500071101442e4001c03d00012414072068440c0a0001075409103041d001c0782550701c0e1075500c0362000c59045608140c003215810300d04001580c101a0f4407803803a074102c1e1509850243e5000420601280a09c03401c103042806462540d41c403000c9000d846144001d0250704030318800304401c060022000d02c0e0490f06069104c540800540e40f40c8114410034008140c0503082209020f4050307641d5110b80c1e0306961142c0d810240d001c00700d8440c010310f01d000b404030768a6101020160041c1d0300600c103070b0721003400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 141812868 1250 141811618 141811669
    0x30518060103060606080f100504050a0e10050a180c03080702120a050a0c1e0b090d0b0a0905070905040b361f0e071a09040e010b01020607050c0705 65
    0x21250804800340c00a0721100c0e01c07203100300026940100c5460740007031104a289200d040003032003035030240020f00c92588182d40f290007090b40c2c54510341c00414282c240000300e802c00f44140e41000c003d01401c8803d803c0080c907000c40c5184440c4481d0440c001780d648041650000b60850b0b4401c172a58105603030907a00111011031022114604001050380c0354010001000d40281c0c80c504402503016640007524a45c0c1c105050a80280c00091413405488419900c80e88850b40701002c10004500c0903800b800314019201848800303e00c0fa4030204a181c018001d403108113464104a10603108240c0f001090360581d1380c0015030600f03020045038803183d080b070036100c0704561014041c0c40060995400764131a400000b8000304500c8100c0900942c507200f14014088409280140d9032106190312a00e5603a00b120030215240300c804004580c60188010401c018284c0e1070102c160003803108150341c2d80984114408102e190780907200755280840e8100082240c2810001401045007411030040100d50f83c031134 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 141814118 1250 141812868 141812911
    0x3190c030807050109120504260a0605190f0504080304060f140901020918221b06030603050c0a050616111e0a0b0403050601030b181e1204080d0305 65
    0x90070b280e4060000072501c400e407810b044240c071009010300c109000041208200400321031031400710703003d80c10848041102003503c00e40d0914a036a10000d028a1510082000c0403214452840102c461400100107060043c00324404550007a076004d49296803d00c0081c000030082c3e000306400e0148074a000c035066480c1ea16140c0c24800075121044981d4002c182807a06040444112402c0310342c07181d5007035050404404043e6545030b0302080110b40d89080c0028420b018280500c05c1d55180302804018040e540c2e80300c014010711050000300c2c0da5009514a130100352504900810035250014000c07481c21840d00e42c02c100501da2a001120008299050080240d41e645032020074880301b44286491075500d5420000e82d8000c942003e002e4100602044c400300720001540c6065079400321015900d520365041c0c003a154a02050b117111a071044013000c820f040d01c5803000800c1034503404c003140d610020368a0740d2900390082d402078610980c0700341c80241c1040c0c1310313402207900070702072a48400004d940c05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 141815368 1250 141814118 141814133
    0xc0c05011103071112070201110712030203031023040c030e0303010308030115170a0b040b030f01060312050702060d0b0f12010c0f0f1b050c040204140a050f03190c03 73
    0x44500c0700259034044104030600340c00c807041c010002c0c0400d003d000001141c80f0701d60b9182c0200c1c6006410403403044400130050000308031403000303405404062001c1a0741807070000d40d41e80c000c0300d2100280d6400440050110340d41d00340d030062941031035840c0310090504000d000042c10622101c0c8c0805440320f0a10100e100c040c401140a03600a09040d0f64070f60401c002c1112241c20513800408000c507254501e140440007d4140741c100c04061404a0300303045110004000d05641c0000f10f6060007082c26040701180c055002008a900c03443c0c1d100510b480e2032000351114001c541e006034001400300402402c02010341c0c01000d000a00405600b00d0130501c50124421a0001503000c4445c0c1d51444100d0b142c0b90003c044c40c00e0142117160001c2141b111400003401c406821440c10f1003801e032040031904105041c445086007030700280045448980c0d0300409a8400f8001d40c034076000d045403200200340d600300016070b80203801002d03004105a0b04a040068091b40c03280b401a120032b0000c180100c00507015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 141816618 1250 141815368 141815381
    0x6130915050303090607030302030405010b1002010b010f0e300303040f1a04020607080903100e03070606122102010207051b0118140607030c0f0b010f090c0801090c0c0501 75
    0x44040004408041641900d228412a04450300c2503000380500030540c0e0f9083d00f1541c03e40c0d4586400340c1c42e43c03103601c1d01034054460b000740c07036501601d071084408031035074150b00c1030341c07801c0003640c4034008420000c206464217520b010f1680d401005880e60200c09004d0441040f00314980c01800034402d4008105440c03c43e0426101140c41d56032005141c814011b1450814a400b1402604440103080c9980041c03420b103d60607004180da00f021940c00341c942d50a0200082007211401c05000404071510f90380d480380d214800464031075140180100740400305903461009a43d1062112200036048600854551301da4000303181150740030041c0e8070008505100c040012144900c000340c040c2a44030001d8100e000b102004809220540320130409518031079011003c5200503501c1969418507824121a43d648140340a007821007a50002020014a512414100d9040c0c0c09941303005912060300c0b50070b4a1480d6012000510b43c18018002c0e44e20030f91040000c1252410901c1c0f0801c2256603c07400d5640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 141817868 1250 141816618 141816629
    0x211014181b0118080a0b10050f0d0303090b010b041a0903340b0a030b100e090702070e13120203030f0402010f091805011502070513111c0911010305090a110613 70
    0x20517201c2e020821500d0f9171682280c140f220300001103042c034000c070700507020044d8031510036070041a102c82810b019501c109541c2c0c1d0007261440d038542c0c4a992584040d480341c0310301ca540010603900e84143c1000482950b01400780100036100084c03031859251110030384101c8441b804503160081d80300c2d0300c2c480c8190400030600400d015884084108000c2c0803200c50290700c90050301d1003280340621907404421280751040c01c986ea034500b0340355943c041380f0b420315a0b00082c0070404410140700400200c05540105984a07400003161900103090881e180c1c0401e135144203e058440d00420f005600410301d02100840c54540044955510400b607034810034008100c03484507507038000501928a001400014906041c0020301c942480d1001040b44802d10805042015554400100c02d4064017800c0703404101508a10510242004140c1e1004240c03040c0b044450b054607001119295020303002e000d106201c074201412010038551114000c4604501c490340e8090000c0100607864444001200302502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 141819118 1250 141817868 141817873
    0x509040219170f15040312090c0f03050319030603080301090f140a0b040b0f011202030604020c0706080f060409020a0b030411040608010b090604060e0105211014181b011808 76
    0x464030f030540760810300c40fa45210080b43c1a0820072002c00d4000265601405500400207170040c07071810b0801a0110390380040d0000d20110700000b0904c44000050074003a9041c1482050504000d14150112081c6220040019000380300401c840090f95009494040d44000046080381585800000d56401100d90000715a551030b04030880303007854031454681600556a04401d02c81e00d00010b4101e00f00901e000501940001c0013803960344954064440d8403400300f085400850b201c10028120b036404652020048041c100080d44510b4940618440b490700500b9170203420b810700400742e52a51000f030040d6114064682050b00c1d5845511034440149140000080e0401c50b450400904510151416104908080080c400d4850040f481411500100e46142c2008085150040307624011000c040140c040c00d003910f1001c0240d0742284c50408000d100440c0a0359800940f039559840d005110442903110502d908042c15040c07281c264020414148035000b4160a07140100e082c1e9143c0181c0031030b4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 141820368 1250 141819118 141819133
    0x30a09080d02010b0f120c03062a09011205090102071424090601141f0e011e020c13020d020715050601050309190f060c020705030f07050904021917 65
    0x501c0070758210300d8184000c0c00412204000174040c051441d031010310848001d06c2180e49140c08000761500c1280c080d050320010b10300401d0410f0306101c800e60303603000c8941a11040c41c045011038102c82000c0c0703058540c0f400d00105540000c0080c000101050b4245d90b003000303c000843c010b1400011007412601c0213100940c0001103c433000c02400500190404212040c4802500c0c04520075041d02d8900106951007902c40d00000c4941006035902c04400ca10004031600c03140d80070340000b02404c02030700eaa00c038480014880f000d41c040408070b024016000007401c84403d14043c9004a21078045020160910102c0d98000007240c2c050182110f414083c900c01001005140c00707403541c487e5003400d0450035407a1988250b0f0b210841c41e0450491125070b00c2c0d44030f0412520010840a5540201b0100903510b61003070083c1d6103844a01401d80703c0c3c4036480c1c181011a10024420f0103891028000c0c440588442c0d082c40704e2090500c0303250199030b8000d0004103915040c040034a200d00c8000f0001c0404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 141821618 1250 141820368 141820379
    0x9090a06180b06091207030803070203070309151d01032405030705010305041a1902040e04170a12020c0106030204050f040303201621020d18080619060305030a09 71
    0x4919403070514a40c03035007050a601195940c0e002078030030000c01618061400044080c22034242145904001c01c0118044107120000c4d9000014105582c803079219400c0709500c8106005200c084c41d0070000000f146d100d100451944c1010000c8030074481814046090f4011200282c120712076205804001845550304208910302040010014202809d0801003400c0940b1a10764090320000031041e43c0c90001e01050014408034144217036481c0a41046442d5034a607524401010001d84003905c02900100000c0041a04036040304c807002ea080d162a903400410441e1000650882e41144010b07550783e030740010158540d80500342c45030001250500e12840d1a10b00a011188422160169042c0420301601c0e400361240803152a1803100c204020000003034030b0044500e0015088001d404000c0150350300d02603070005000c00305040f054580104412004003c2003d8002610034042d01c3d074441e40103d0044108070010038040001c64401040c09500c0361601031030366014840e0000040c8188000b04807 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 141822868 1250 141821618 141821639
    0x110907050d0609180f080f1606052401030b0d020306010303020c1c02090c07060906091110050702102003040b04030c0519050405060301141e06091b0304030509090a06 73
    0x902801e480030840904040480b0001010f000f01c010082c00c01948118140300306caa05460b515860401d045694100d2211000410540140c0840d5202e0400c0c011908440c0100c40c041122004106100424022080110060001460103030342000580740b03e100580c0303050240d40d01843c06600140030480c03150b418094804440d0440e4240128640003c000581da5025110340081c52a002940c6440490074214001c1c02d8100d4000c01c003500d020f0700e00082202a40d054550a07400302d460b40d40c000c2e41010283ea19208544000354001c0084810704045802040745103200301c000703200e615091201cbd074882072540e403064210b0070f40d44901260400400c1342c002950703c040c2005031b501619030300c1d230140c05104181150080034403903926840015030300e450035444044840440410340c40c15081410118550210f0407145102e60320350a40000d080e820000e100c2c602510240801c6841c1c034a40c03180c100450b0304043d000318100902008002c27480c0d60740d8580c2ea0302903448818002100b5140c519241d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 141824118 1250 141822868 141822881
    0x100501080c06070302070e0604020c0a030804020123040b070807290105120d03050612071d090a030219020d060903050309010e0105010b0901030f4115010c110907050d 73
    0xb482a841004503400095010518000b160301d040541c00c2d00d5120000054064010280b400700c03280300e4695034205040d8441d03d4180100d0003a200c400c2007020f01421036000c031580c2954005005402c001c01c000c4a180c0300000d101190103152040d060061030b50700d1891105019103101a04540002001e000a07020036140d401481d08583c014482000c02050a449441c0a0216014141c0d2040000d1094592103600c108030080c00c01521a21911000d40107154003071380050350761900034000050f011040024400020701d030140c00070b01104403c14451100b40346060001ca0300720072410402070010720107004000305a131003074444641303910304004170f1400c403800036100d0040340c2c1c102001084000c1c40001240d402240030300c0d01048803a2035000d030b80060002100c04804228000c1140000740062451105042800d100803101c008840034507240c0c03800065544002c8403502d0b254070703401d941c040c0012600461040c1003281000c1040c1000500c410822200d08010940004088851210a10501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 141825368 1250 141824118 141824143
    0x60b0913020108060d021906120213120c03020303040b09130902010e1003020f0d1b0c020f040e0109050a150e1209101407050c010909021e160510050108 67
    0x204514039202824840c50110448082c0c1480402c0d000304149413500c030070800d42190007a000c00401090710f14a4441c141113032140d9000180c906420050248060003120520062803440e810203a007801802800501109000c0b2401d0614600020040e101400508010b044018250383c41e50044400c0c0040b8071458511035100a1038245d500c0c00503a00300e10601145541503405c0c3d01010f90240c4242c0080c440c940c001000c82c0c002045010580010744c1203032080040c3c14441030344481c9503401c191440f18210400030f43c00140c0c01c50360310aa090603402141c00044c4075001246c02c4000303494060a151240c2025541c10b02072424210181c1500d024250b041c090070360051071203048091007054035004240d5402c1c4603500510800d0602845200c607480c9500407034a55a50700c0d40e2500e4403965079140601e4031408196243c10008a03003919100781d60340a4844d59541a1004580307500018aa00c071030450000d0800c08907810001c1082080716041e40d0260940008680d418440d4403484c001825488 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 141826618 1250 141825368 141825379
    0x607170d0f06150e031f020d0e0c03240105010c0f0210020c09010506070503030a0902030a3807020309010c150f0603060f0b031e0114070c03110106050a0b03060402070b0f0103060b 79
    0x2490401d440004509074445800c4802c20b858145486c0140301a05c1400c0040561a0070024031200c20440400c200354010011812100528940000803042410392207041c184e030708d0644010030a950048650030091441031003104c4d040541c0354001480180d0900a04005038070170714521201d410a40a1907014003400c9a1141c103242c190754070160349210090030407490541700c0d1108030854400300058900180e014004108a410500340c580340e6010109c40041c0e005121046034601e84060314102c0e01440c4581d0140d4030b007400b4480103650000da0400111441c81e0807918901e281071851007010201001204042010381c80d60a1540a94038590320b41d00150f4540351860342c4503a000034041d40c0e4803000101e0f0b10b809141d110b640c80d0044c01c550001100403110b070802c104074140d100c2903100e0142e209455510400d0800e044250072104c150284030f40245002d5400c0c812007802c08084c60380464000c0000d80341c0451980c07411a4107105917140000c21040740c0c018010044180201110141c060f140d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 141827868 1250 141826618 141826637
    0x150e0c010806040e190804081203160801060f0807120f02040302030f030c1e070807090c0210110a120219020a020109120b0103150e1605010f05090607170d0f0615 71
    0x604c03071340352040010048070354050410788104000c0d4600584000380360700c2050740e90307004151043d111558000c42e862005100182d0007100710074004e09985041c1d070429a43c11000d80ca54000c140c031410b00203040d800a100220101c02d2521105000b64980440c04e1200507031101d02c0c604c141440c00c04591035070780d01c6400c1481451034800c1e00288400c0d0840b40854220030f0726400c03011590800015030490201401450008502e100381a080100380007401d0b422940c41034900740c40c400446601d14924410001d0402c401c1c60814030070440ca8030201c0003280c4c0140350402d940c42c403000b8004404074420261700032141003000c0d5a0010140c80061500006c042c21707640e115640c02c603030880140401002e0b050035070b0031b042012040341e0007072303035000c5888044034031941e040e25104080a616100f003074000790061444000301842031003513130610100581414200451540c84240079940e100300260700760402d0200c0b001e00c03801070081c0085021007070f000143e0389082006060f075000144101400340702168a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 141829118 1250 141827868 141827891
    0xc030601031119090501080615040c020c06030c16050d0f09080c060d0905010504060f060501050c1207060b0910180e1c0905040e030301080d0807020d0804150e0c01080604 75
    0x112035a000030455580c202515400c0203e2412540c6420110700b041ca050300104440c01e00250444c021400c0c00c09200014540c1c20820040c0c5280c04003140058014820110903810a10003443e04010003416050400c00c44030301d4030591500c4001d040d1840d03449584040f00039500078549800c01412032514001480c2012210707545c0301404902240181c000086051560290368055003040742c0c0b10f00240310034101400c00d900a05012020f91500514240000440c0d6000c0c804480414007044054015502944214045070f040324078240c94290311205480f0b02d42e916200f04501c03480840000000d01030410750a43d1840040e40d40710510549403800c12898608000350486003030003002036904122180480c2240c40d40d005601980d0001c0c24440e02055620000c0040c506a81d90740c0103c9a0300d41003040c040780c0e189000d42d400000b503000242c403480380504c150300c07140c0d02501400d06070100342d807103240348000c44850810482d00c3d81c10012542d5103541e446810641c020300c0840b4140016106803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 141830368 1250 141829118 141829133
    0xa0506090126100e03030907060203160201140705030a1106090705010905040903120c0302042408010e15090c0a020c030c03100f110f0705060a1107121707020c030c03060103 76
    0x303006111007401040c1e004070b491080008100032144450103000e546481d03440f0a03583d4000741c409010714010b00e40003007080c4d0b01c0041610600010408a09070034202c030740040d1442e9070342c80e0002c4403203d010426540442c40c2000108440c01d22640c58485445c1001d01007400c0c44000381c03d03498641c118050401850b80e01c20110429510115800541080d0b5480d00b995410880362160391007500700b03100c61000c1c6405074003502c01c840c02c0803900c1c400c1c08800c40d03010301100440403400740032416100040c00100d910940e1203501a00e041b81d1614508107074000681100c40442d02c92680b20800915898025414420007100074010703030061903406c0401c4d0000351194407250b81800825520f001d06801680c040d040b1101c210740e0011034a0b0366001041d00414107500204043d54035116041c0850f910300b0b0940b1a00d803c9034481d494003420189a56580403941c4c60f149600c000300800e00c00311040b5500210070303050060354181c0041c00018241c1c414103092001000109110381c0002d001000403c2c0311 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 141831618 1250 141830368 141830399
    0x606170a020304120e03010b0a030c0501030e0c060a03110f030f0a1a0d061a091008071e0308030a140a0905010c1701120c030507030605271b1f05030a05060901 70
    0x780c00e000540885d50808a4018940c2440740c0f50300418104002085c04507e0107138030b0540704284d9050216000d8004403d544600c0c030b000240d0068802c1002d40610ae200c0c1e40800058407584801d50300d40941900002c80c541c0098038116400900b200620000600521446903907030040f140c11010006000001402c44c14071700000741085880d0780d030f200700106030034030707071a481120040031402c00d070030000840d12500b40d02d0300604800344645000414051024008080107617000c114031003149042d82d843d03040e107400c003400024440c4d482c4d280c100c688011228010f40b0510414400007007851650805600f5110350719140d07801d20554449041441c00c81180d047e040d503a080c00d494010010714580040800e00d154400343c103500500201004200781c50300414002c005d4800c50710a0f00013103070103600e2801400c280401c150f82c00b004c1c9440020440400038404000000d0a119401503040844035000401442c0300b40040c000000b080400c048912546030002402e60b0315025942c144950945d61801 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 141832868 1250 141831618 141831653
    0xf05041a0117060406080106060c0210090b1b01020d0c02030c06070f170603100e1e1c0e0a03050f0c04061e180908190e01020a03090909030e040606170a020304 70
    0x4042c0006400e036100d07504182d0060040f00d008108031540c0303c1008120815040c4200e20481174003040004a621454200301610542ca05c8680f0b46009070000c1d5419141f110009a11035400b4080405405120311414417230b120036802a40c1e441c110454098100500200b0100c10300409400c81c41d02554891100c240002c592042c140c1c0c03030f03200c100002c0c8ca070041038a07680d5481810000518400000030412025440a003141c0000b03090700c0660003a00e87d0350002502c215140c081015190383c500ca10040480480d007d0000d81c2d980e500d03604c0340360400612008061959010501006613824240f16140040c111a0441100c698881044c6202014607100742e83c05010303c09002c07882407090b42d01116482d81d20111140d0b84580d01d030b100041c00e400e004075840111b1200b00f0754002e02d50001c110540d01940c10f9980c0d0751014200b0b0303850001031050617002e13020402c0c4004203a4250b03d661013910b01419454580407085404040704040142c001410241824018030502c40050b0701a10142d20461 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 141834118 1250 141832868 141832907
    0x3110c10361d090c0438091b090d02040b0a060f0e0904020a0608070219060603020114030609040b0c0702150d181a0c0d0c0e010813030c080918010f05041a01 69
    0x2800400015100b0342c2d403000031815100d100100401c95031b80c251840d802e104040d18480110381e10110924441c40f0810031110340e095041200c8400d518102400c000464030040002a1400c4044045a1031072416004070000c24a420b0000070060340042500c0943c200444030320b00d2034a401e0380895010140c0d8400d010500003400046044140240301c4803a9011240d1302e1840703540b55504150300900302034442640418500c0342e00f074110030025021031303100b554007800789c851540311552281400c0380c0042442c0c09080e403c0c80654016960482c071000f04202d01c1c0d02280d105c1c519810030b50115a1340c5a80746600302046002c1c1c0e00001c1c031004d000711003120030000e04801c1e40d654185503011481090048500341c2d00d0141c510640a42001841140d03c1081e62000780700d9440719039451081c980703614044c0101d411103519100081e00c0c1401080741400c050411042c402040c1c1003040100b00a8010317110507200103000380014101485403219005603d01c203903c07246080c90002c1e2800140900700412030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 141835368 1250 141834118 141834131
    0xa12150b0f0304050f0a0507140a0b090f01020f0a060204051e03060103120c02060a020a061d03121902130e061e04090507030b1303110c10361d090c04 66
    0x2c20710070141d401c1300007004e45880c905203241c40368850f5224000c21003414180300c927070b40c01410440c01707440507501e084400c6440e044080301003282c10360861821a0441c4214120480c1541d402d1241404442c842c00000d41c840741402c0c104802035070038420982041200207480705181c2e9002030001d0450340c1004c4500804402e120048a0051007050040d411213000a03000d420b1980c00100c504030b80c0e0203540c0030030154034140c0500f50701201d410071140c400c0e0b1003400310019541103a40941d0302b205020401c11045010b1000c80070030fa0300100c3d0070804a41c43c8080070010907582c0786080d07901200840d00c071100d01c0e286801d101625104102400c4c015aa55803103541001020085503010315044907115241c2c0c64402c806e03480d07880140c003041340000c00038500d00c09110400507481d6a0f168008003600f0f00c03605c1d40e0300115461a00b60030790500312000b0100107005600c0d000910031510240c013150840c030034180241c0400d040c02055040101c85c0700b6804104c204440410b046100010844010621 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 141836618 1250 141835368 141835373
    0x703080406060302100804030e0d050c01031806050108010b010906030b0a0e061206091b0406030f06050601170106120c0c05120a0210140702010c0207030b010b0f0f0a12150b0f0304 79
    0x14640d903000290030580c42d90350341095a820402d203520480c1f02340d27140c0040380c00900502c0b11034129450003c0c02c0381c4c05420016042e60282d003110b5500030004007030262010a0b51680c0f002d449007a07000308041d96644601c1e034401d50307000015201604841c20140302000f2035401103112441c042c42960440b03260000443c01d642c3d0380003220071103c1c80000c1100d0560421443c0507465410001c10300520baa160300d01c6040724146070190340d04507034018100841402d866207a01001e08030085c04d1604000340425095105402146154041d01d0250703180d1410512a03542c0320125503003821403106000c0c0020040001a0300052100900100307401015200d80c8924800e0740b52070002400c080a16040800b041102600c03100314070312030001c40d4002d10206a06900c01e0340c8842c1c0754040074084510480060209a40441c020040340c440e043c0c20780d140802d12641a215a0030440c03251002840c20b0b00014405807940c020140c80008202488601070b10b8001956454420ba0743d024840640c00b0000506 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 141837868 1250 141836618 141836621
    0xb01021504120c02130b01081503060f0a09020307090501080c0d050a150e030408010b03060f01031709060708070503030a0501080d0905090606160305041503050c09061605011d060c07080703080406 86
    0x60340c0a00341e1100e00c0c241c110b504003c0c08070061007d002840f084005405500350146400c2480f0f0090081e00c0b131034840344510b00c40c407000104400d107510340b01d0540d100181c40030050398006012020000580d9418281842e060054080d9028460000c102d0701e000401c401040c1c2e441410741c4108c030251030390000380960b0b01902e900c40d048c002a000c017041c00101d418040d00000c00c8401c040b0280c503d5941c0b08440c284040d01c080c0000303040711f00192000c050002414008102c6e000c001881d0b41d090611507500d12109502108007125250000700500100120b5800f810b80500b201c00003404200300b58040c000d044c144e140c0b140600c00c0358050b02184003a11240203d032181746030b8514400400c00340e400c1c054029802032140e0b180711075404420280007442441403500038511501c0d07003860904010b04001c000e8200342601c81c0b21480c4034803074600245092280352800c0d9003850280020700c1c140e04209051a50042980040000421049002803151000c6858031079160900d41c40f00d840305c2c1050300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 141839118 1250 141837868 141837887
    0x4090201031119090b03040503040e150a06050d0c0e01080c090a05030307080a14070203071214060106120b0d020901090e0a0b0708060f1c06020d0b031009020102010b0102150412 78
    0x100c40c40790004806485064003e035902404859840360040b2a6079588203243c144400c0302e01038802d8109000500414888102058205000400300c0703815092003000116240e00c90362203080802c00004803440e4029040c058a4605050b03400c01420226443d4006000c6603c020240030100e040010300030102d68807000500050400070741101c0c0c40b9001c9240a100541c4034442d08808900844d000c404900e100030102c9040a5015003e060380519143c0d81003508020854200c480841001c008030a04400b0844107000f848a5580d0810000f01051004111480840d0f504c0c003420b0b1001c051009a03e68107102d5045841150000568070404c0c0413860901c0300001c00203080c85003000c14400b0256024119071300841003100e4031400c0c8445141000001e100c070020320990a00b6540826002c45e240e5070141c40721024007400400d410800c031000030f092040e4441a1a041641c8401807415035a091050141a80c020b0000300903080a4486041184100134401401145030400e4800300910031203641 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 141840368 1250 141839118 141839141
    0x712030e1906060303200706050d0b040203040b150a1a0307020304030b07051309051504050c0d110c120a1b05032109010f020901050a08060a050307030f050c030102030c04050409020103 81
    0x1e4011440038a841c40180005200c04e9000828a2055191640f803004200200d481a0001801514a490001d884940121780703050310080e80c5007038888080e255400118401c6102d890480c1c010318207003100e1420b03595200740740c0b406205210400d20140304441c0000d6000f981c4100460389984d01c0c500128a035100c2d03038000030b007145440010300610a42040c007811200700109080c40485072194901000c4410485d0761007080f030030300e202f040105d0a06907c21900a41c4100c142e03442d2003c03080090781139452500a4480581c0000307014841e046003030104030850441200b10300c1c54243e440740002c200c246401e43c00e035030107086981c40707408219017001100d0140c40300d10000100d40b8034031121100c01500441d840c0950b0750030708072400308117800b0f88212070003084161100c5042c2100d04038200d8003c0cad801000b0300c1d0021545003002c03c26503401c00c200c5008511400c0c1e4090322910525110b800c2803152240107001e1b0b801401403043d407949000566041e244281e800150350301d40d5000480280c010040c02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 141841618 1250 141840368 141840403
    0x80123090f070b040801050c1201290c0d120506100f02010204030b0f18070b04140316080a120206010303020c120312090c0102010b0603041502070c0801021c0c050712030e 75
    0x8840c0c0c0b030303c0007034001c50741007900030482d565429118070704c18421241c441259940081c01484030003032408102e40030804801703003120b400302d030646000525880400c62040320f501003400540305c036a10850407005e0102240d4184600d003801000300700e079111581c01c0c520038030030a4003001c8220361007581a28002d503041020040e0908007040304101028096a0300d2154250f03000000520007000181202180c0c010716040b0f1500d0701c1c004d03aa00c84001c2401d001035140c09020071034031034820034001c450081c0130070f08003070001c3c50440c1c5484210003100c03400342c40554100c40010008240c002c03d206100c07040c1a910301908103004005907040d8868114540100e409010030303c2110100000e400c1c08040e42030b0002c000c0300c0b01e418100141d03408111401020ba604210441e143c41200750050035a0324490444482e1444c0c513a40c00070300b0390304546000303070642c400544070791b80600e8180542c0401954900f010b0349480307580d441d545d810b106590300150925858200b044820f0000b0490130b9404d0030b03210361 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 141842868 1250 141841618 141841633
    0x913050114010f0203030702071e0308030901020a09050a080d1b120e0306010614030a0c03150e0f07140901320414030129010507020d1209080123090f 66
    0x101c021101a000e0250b00243e541110101c0e414000070889019540d260000c00101389020400200d2001d0141030b08100e060a02d0b0001c00540d0400c061070285418800150b10b850a0401c028400f580c43d078000c601ca13014a18007002044000714440301c03c82c80d03e00c2c14034102100e0040a094280504400a0100a21520b03005000c0e50214074881803c00840075203029990b1007404660b03020b02881f01c1e400c500303400c0020a00d40720441c0d0024140440c141404289510041007102d0800d03440d03401000c2d5403421000f080170804491080301d90100c0135040044070030212910072022409101459414002c441d03001a4015680e9039000340606d0222403942c01000058207200081c0d0054490340141c1ea4025891703044d6854103002c0c25002c0c0c0c5000025440820010560344240d6100302a1141400401c0104a000d82c6a0019060340140aa0b00c803030303003003184040c00070b0100016520151850345408402090300481c00c2104c3d412041c184051501c40d1210406e40307003011260b031030b41c0c1c2461003007c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 141844118 1250 141842868 141842879
    0xf0c0b1c1d15041a0702030403060e0105071b110406090c0306050f0d0b07121a01080906060105040b0c03090904060501260703150b03010c030510060509060306010509130501 76
    0x1606191411411032041c025603014452446070042034084091154000d580206400d1074441049580030740078400e02403c103800b00c0c15401042d4800d541000041e000001d00b030051280a0203901c01e0460544003c003c2441d100c00014104500b03810840314a4060b18480340034801c1280342d02400c103d0080c020050350740d80320801001401010003007000b10342041000151803904501c658811080604101424001c40c3e643c2000703000c0050120003400f050360300520003800b80e8070602c02040c05140001c0a40000d2030000f508001700180007c01d10351100040090a0364810192030403039106500032911140c00e04e06050960090040b550340050050b0b0800080c0000c41e00030074101c940482865059603010300c009010a040d00040141e1030307005180c00c20000e600c07004440d8404103008070004400c10504000303400d445104041400003034480c018022061540e40901c0024280380c10910b1500303203e0070126800e804001c0c240344c11b0200101da181c0303007030312421404035401851450800032980c550 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 141845368 1250 141844118 141844147
    0x30c03060c0a090e040807030807090314030706050f1b0c0705030303041a0c0703050703050901030905030d05010314010605030c0609010318080c011103041e110d0602030619060c0f0c0b 81
    0x802d80014110075000160464080719a6020b241c012545030300c0c2c071701030751001e80750402d0190258042200e882c4000002c00d25a54501c840c81c1d580030b000e50390341d44850505205481000d4540301c0b00322a9803040c42000c01600d4401800c0d5001c0e85a895251001e0104d185c1c20002203602958143c000001000304000c2011105a981c0003501601c03107460f02c400848856500860700d0040110f00c0c104042c40110380220003411600b44145404240054680c0e281421a00020140d11456441d80014420022000641030724001d40710001c1203101c0c9400c00080d40d40c0c0b00c421155015000002b0240d41c3da0b403080c1c1040c03420488062140d503c6003102c1c94000940d40c05510001d0240d40f811560079501c2d4880804c41c0c2c0100e40000c040d044d16100212880c070010030303c01e4102e804800f0308140f0421501d0700940d281c06540102c00042e107a25140080c80703020f422038080305400441d0201c2c1840480d400c0000240c9242e0481d5825500d102c107032810905888003500081e0040d03001185542e001c0e841d1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 141846618 1250 141845368 141845377
    0x405100807110313080712020109140f040e0f010609181b0509040c1e05180a06030605070c050111040e1b161113050411010309080910020106030507080609070e0402030c03060c 77
    0x417000c560850740d40707054444102c0101740b80240020100c0700100031004012881e0703000c90358010b01c5a69221900700009003218504082880d1070b8000f000480e180079030a12031a0000d01d8541030500003840d48880003204400b82a10060199154179a140c03c5400c080a8140280501070201886400c286c14140c492b1a00317880381540c0c0341c00c45070607503d45261480355101150b1010b0f0032284e03240100004170007041c2c002003111034015994a07001000c154103018243c02080a6110400182280d052007400c2d01d407000300c0c0b0360081c0d5003003000b004096884008a80e00c000351005051480411102007105446038298030f6480440401040040c0f00e043e90324112800c0c0100c0310380c003072403081c6141207003655400c0307a028000300800004160103501036046046000d200e04001c61030480c2c0c1d0f83c00540f18100b070480240050b95503c4c824010403904000b0880500b0307840300148460b1910003c1c456940d62280540c5601400e00341c046011900c00700600c80c0b0054005080c1c81d013520b489040303204c15400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 141847868 1250 141846618 141846629
    0x806030f07060804060902012106140105040e0c0306030a0c09060e061c06020c07050409080a081b0406140c0a05160510050403061a090a021e0405100807110313 70
    0x1559000c00341a44000940354110740c450340703480082d0759658a80c00000d0508000a07818080041d003201e0080d00b400640307507038000c441c803030019440d42030250243c2141c6282090505029003000306101c40400644055032000d04103209070394036070f03c00010a042601e240001043c001c007240000c907190f4412703005401036032000031005086030764282c10041013040b141c081080c1c0039200348040010885030340003459a04015800c455907165035101203400ca54050320140d54007403000c1420a0703466804a640c5402204c001c0e00031240c0720564902d201a0300c02c0e88102420f00c040c29280e14400709101003901d150a072824190354452005080941d10350b85044010a4049400750b804610340ca0240e010074442051591030030b00303280c1142d035068014010032107440400e07440c102141c121a42d540400522419406101580740e82d210111840c0c02410712203040c102d41400c2c4006d0081d03072219500c1e0000b12005207081441b60305e03142d000b1348030007036250260f0a050000003107401090303038000c021908491 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 141849118 1250 141847868 141847873
    0xf1d0a051c0521030601080a0209120a050c01050301050618040b04050403030b040e06010b250c080a03030c1704020d1401020a18150f05030a0e01090b2403060a0c1806080603 76
    0x104810205500100120701d0002e81c03c40c248007142c8994840c1403070035070020150f50014640444800000c1d03c00c1e10580e1502203039403041c0c12100800c1014808402907100c282040c1d4150b5040400040450203401000381c2c1c101c05141c484d00301c641d55500311092071040a04100603900309418014042d1008022440c003490070b060b007030615a0000078030035040f603200700c09060a00200618800c2d40c030003420054246505145030740070119500812180043c41214000c02840b9042c1c9800b9080c1e40c0080ea006c030501188246905640002003185680720b5030440351030702c50041c036250052182d04400c501d00d2081d1f2012840440b500d0308030711950281c49c03000310010f00481c0e48074504440c41d2840480c0380e002401c8001e80448142c014400b40d60403c4500c6030109540b4418141c41d400c6408440e000d6070100150300070f00c20218620b2059144c02000031502c5401c03030f0412000b080e03a03050080c0012062950340c0660951161145240c1ca0000742a15031408509a460f800101070440903600948a070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 141850368 1250 141849118 141849133
    0x605030618010e0705092806080903070201020a080304051603081c0504021e0105070614070f1d090a020c0a12020c0a030506040b040f14010c0f0f1d0a051c05 69
    0x61040007801030490b0003440e00400d86603138000c001c032401e80011034010381000452210301a901085c25041d032032440d86030220164186420340007003d0440203442c1e141c164008100140150340d001c140340b0a020342042e40c1d95a641c0351071402e680f80580d000da08103001c3d40c002c000801040b00b140b0007401040b8410480e9100100e04545040c200c0e1400e440c0254003010121403500d42c402c150a440c0c2902e5014100300d41003001c192160000c3d98030100c17411040b13001d0042080246900403c089807681440d01e003112070084d40c3c07044c00002b00b00071803406200701ca0b4140028645101c0d601146d5948202c2426144204820f14007030500950305150301001d802020080019410560a58070031650890000c16050b1035039201e540c44200050010744e10310001e0748a22001c2005400c3c3c803005503056500005005450381d0004044580c5000380c4020456840c0c4140d0100ba441886051070085450300815001d0b0440d000441d80d192a0380060f801002d1483c001c0c0c500c025409001505a005106480c5070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 141851618 1250 141850368 141850399
    0x13050a0f060905040504030e0310050124080a0e0705030f10060b0c0a030e0f0a150833060412120305100f0303051b120403020a140108070f020106030c06050306 70
    0x4203082802408001601000104240d2510b5001aa0030600a0800e80340640c103600c0400d041050112040c140300343c58400400551490482c171214040e0700003031001c1840d00c007103c01030888a024280c0f151690311603400903000002400018005c0c070000f0304a5541008107040340b525500c41c0c243c4c1800d0301e80703450750004081d40c00740c0449103aa042d4001401121000e6034043e1032040300d0040380354118000ba0552299a2a205001000780a2500280500d00e20180005003501c10080c01c4254500304040c059030320b040d018203000012503a80d00c0700007014401c4000300d030850160381d10500600520061a4081c0081d01168881c040035940d028000e90b959041d01c525075450a125000d40d0300d800304801c1011900c1075003e440c0d44104000724896030b02007081c001e0702c0c000025442d0b0401082c00074003001140780110440c0c0090244143c03407408010030000180084a000b4565800c1c03001a100c801c120610070342c000f0b0065684014000c81d51a201c4000800343d810845a0b1400390303c101410404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 141852868 1250 141851618 141851639
    0x1a10030c080105040503040614040504060f030b0603010b010f0e220e16030b0703020d0b040507090914010e01030b070c050f06041713030311030f030f150a03050a080f040b13050a 78
    0x2013a074125004500d454600720044aaa90b15a00003c003203000a210216081c0d5590050b0b0009014070f00b48000803508604020f41c03802d030060b051030320980c5440f604020a0341c00c110611040c240ba4207215200450501c041340d0010f442840e219001142d00302035642d4003485601023103200c0c40d190210780c0180c0c01001220004220f074000541444856000070392818402d400400c0701140e0b0703040218040d500b0001242c1680d4087d9800008900a80420700a60030300703125500c140c0c0032085901242e07500d088500b6138074103410300010700192800343c0010082c074001e804410031254410219140700f40308840321502c54205480c125030203c04a01446504808842540c0a2031024114003030060b146070b50070344501611517204609400280f09068038110098003a41c41500040460b919034a059074891f0440301c900b90344a0b00c58901350001f400403840000d411600d00f41d11034401a5982040400c81d244c41c01603a000c814802c0300006c004e90802c100280c41c1044801c1614031100c102c0d00d0b46451075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 141854118 1250 141852868 141852871
    0x10c0f020a03050f031005100908010c0309080706111216120509030313050712050a060f0221040602041a070204060e070f051602060f07260702010503041a10030c080105 74
    0x4000903070600100820410032402503806c49145045017582039511070110f0b103c2c040740160140880d002400030004540217020703c903500c030070a14003042082003031307581c0b114a03010f03078940540903076599010700910000c500d0454500606185000300ca51410802800300c0412030400c400000308a0f06403120064403034007941c3e02990019000e10300b07590340c110740c0303180c1145050010340b111b20464030000707020303080404181a000d000b0000707003a0080040c200b40e0113407040070b0007100745c1a10400841c6c041c81e00c28003018010291400b444841c540729424640302070302031504800110302c0c3c0c41c007041e1030740041f507002883c1d414800e440502c42d01e42d552214050081d022100c2c0d0001c07890503000101ca036482400100759052000d4407060003040a500460043d402c211040341e0490400120b50050100f01034000c0d14411244503100d00702c50400d0165440c2e4062072000074144400400410b04020000c00804105a6000720241351481e101c031001120503060302c4140c4050513007d1001c52020018040d45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 141855368 1250 141854118 141854123
    0x40b030a0c0206061e15030903090a0f0f05010c17040603060504050604050402090c070303020d0f061a030112030c24020a030f0b211006030f0b0c07030e090a0617010c0f020a 76
    0x2240d400b101910f420340c0329030b488030303070b1ba800300c00300c6000c40c000b03000c3c040554011003080b002181c84106000502c00d41c131489420035a9449240c4100b0000b1500940304001502c00c20700c0c01340558003582c500b02088504800046c4401c0c0740100d00400c0c807a5040c0d0201c2c00f285c404403000d0065840310020f009c101c450070b803800781d0003034499000030b0030f401d446200403c9010301c6858018a49090044c502e02110b14002061442d1520380004020600c89669110303840401c0401c80c0d461549002d20a40e0003200f030040003003d01030380030080403e10811001c0c006c142940e80b11070b102d290441d50b9114009522030004040800e1901c800081d41844e14491560211070150544001c0340e003c3c1c0d0440034402140040d0b001034401c010f1800c01d022228002d8400441c03180080d05050100752070000b003a604000e007280307808a4140510310200381d0212110303184060543c2c517090180c8402e800030000e00525001004c3c9901c00102034040e13000305500010201c01c00d43d42d460440000c5000c100e0b100c0d40303e0b0ba0301 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 141856618 1250 141855368 141855379
    0xf0b070518040b01120501030606170f030d09020604090219090f0b03040f0519080702010221030a0b1306060504080607080c070b071809050a2d09050a020402040b030a0c020606 77
    0x1101d01820264480c0d2080c45050610b451081026003c08040d10800d07001200c200d61554000c00041c894101c0382c00b0300490b179002508850680024240da20b025220050b500d0740c1c2c892501d0025500c462045070040d00ea02d079805d554400e2840483d003c20380d5076a40d18000117986c500c0000b0303500f50750031052081d035a496552501c0c54a464669140c006c04821040e64107001d070000c4080480001c010ba400c40305d11481d9016156001400007a041403080c4069441c0e46040ca40c100010303180c9101203070f90100f40d44d1000100c01c2d001e0f101140c4880e0450307105030306252820502007080ca0300301000d4130860b240901110025614038400b1601c914017a0f604100c0e11a081c01103e00043d6101022503001140d4035105008542107e104024110f540e4003442c0916914018080010224002d05001c01e001040582a4141e6094005018102d00300e100043d503907a036a0b54000c010f8280b0103034290b960000d0041d0b456a44800038a00b40b40c2c070680d00a240c0c0340c50004500c1c2d0143c00450040c0c443c1800812 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 141857868 1250 141856618 141856657
    0x5130b09030309041d0703030c12180608042102010603021e06040302060f0705121b07030305090123030103110a0602010c090302101b0606090e1c03020c0f01090f0b0705 74
    0x240000740444010308014820a81c45e08142c0000800c041001140a940c403161112041d0401c0c07a84d50118540e40070401038201d03072006888880b40d286104440651908004a6989007810340340000044040d04c0107a10081220b80b80590540243d420b4038021100b85490b20009482a81240520807240b41c01038800d0000300301500d0310102411131100e03502041c03071500c50726960345402d0a44122920350241d0002c28411502c0814010101481c070007407004241150642e2409401405503c200c581040b616a03260401d000400c0010700028491061441d280c1d40c50b49004031601c0d80d600c01c114001d1145010018120384140103a207100030150312840f152504580038032486030301424150080c00803006280c40f2004195540020841c0a608009005810300c42204140c480300f8100b00610b5101360300007050001c1b1046503030300c4104036003001a038806131f0022080c00c2c0202c0700e50f000519440c000081c01132100710307503003122807600c03442180d5440c1d521020300340d511740541c41c88584403072800f06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 141859118 1250 141857868 141857887
    0x3040b0a0905030d06060c060509010203060f06030a0e061317031003020d02040b0d0b010302091303140a02011d0313050103050c070b100f0306060e0703050402030604110d0c030305130b090303 84
    0x38040c1d59824041c0e0103aa14000159005109039481c45d0f001000203240c01441c0c00610640c0e1040361717007041c2800001d6245050160000d00e0007020900c030385101d12400000b0130303e260301a03884941d0216182c402c4d61101d1802014101c4045528113084d66060301c01c0318081d01039001d2004a9114041345c110f00294541550248000c0c00b900100c100c0e00310f80c0d03484403a08030b82c4e43d0413000d42409101d01c107000c480d5811441404a040d102030003400105510b80404000607401c1100c001105a2f107030380860703d4000e4071030200e001d4200c80408500e10070016940c8601c00381e000c40200a4220100e4450907100d6442004604941c41101c22902610051159500054040103681d0b0044c21214002c1540c5441e5001040806415070085a0f4543c0d10241080940c422010017076210f5410300301001145815008651034510060000709204c0010042c44503958408200c0e480954110040c84440c035201c0c1b401a040d1380c44410303480c0d140400741c500055103c0c422412601c0d040705c0a0080c6050080c02c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 141860368 1250 141859118 141859121
    0x15010f0206010b0a050f2b06050f010513050402031f0e04030c0212070e090f1605010c12021c030b091510120e03070812180303220b01080105060a090203040b0a 70
    0x2920001080400c2200480c0940b06d00090303c1c401c0c030ba01160790410b0140300c840b0362000d0846150302801c43d00b0400c00f00417941c0c81001e180a4a0400c3c2040c41e552000c40d41d104580c59050303009654000d1000c014007220007440301c03545900000c2111b0181c120740c0c4a00134200c0c03098040724010001400640d480005080810010300c42c00d00c404211003504d522050407128420b0b04031000001d50b0700052a500701000f08001041c840713031070042d0403044141403000007010000c25202c0a000d9146910452424a10030001e210602c0a4009201d130500d0803444018027602900086911a44020000c2000004000c007079400c0c2501c001c014072400f0355903400c15540b40303030081600700405680c0d0280e001f004800703200811059205030120f40d80c1d0340d15000d07004642040076110384002554620940c47c03843c400000c680e00a140c11a114507124122480d1544c40c010b4650018000704c80c1200000e00750005400c514024030049500700d14054032206108100c4c04120707030181400354401c0c04541c03440e105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 141861618 1250 141860368 141860377
    0xa06120f051509060603010f1103010501030b010903060507081005120a02040c03110705011b08010609030305031009021b010501120f0b070212030403020c010216050f042c01020315010f0206010b 85
    0x95081d01c2d070451280da8401282c050807a2442e48903002001000701310300e803e22401c05010b9540d001005110f4400100d00558001400703854117041c0d0b540c62084880e801800c40038011548010240032515081100600f44076007954144462549080c000c5182d26143c200300c100c0c43c03014002442c1028080e0200700182c48122140401c1c0340c0d8030008035048208210003001464011400811510805a00d0b181d440003040b07095002c201c080c1005101c4190300500300400c80740c02d440c001f42c80c0c2c0c950007000340300107000354403c4121520001c3d010712641990f90003038401c10f5040008101e10b13aa0342c42940420100c4034070080065039019611340000300c074600040d40100d150301c1113410200070b020945410b82d1041c0d0b070503405079220083e0301d0030940c0d04001d515040544001802e11161030000440c400c2040690020f00c110b88070030f07660f210704c8031031a203164540c0700c00400e0001115600641c98001e520a036002c41030200034910624095010f10815540c01405600038099a8078010b64401160070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 141862868 1250 141861618 141861623
    0x1409031b0a05060d090506010e04020306010303120209040618050105031605090a020d110c070f0303200a020301060605070201021501050d0206070f061b0f0201060303021009020d06060e010302090a06120f 89
    0x80c007000218150301e602c00030340010b5022140001c0c01c584030f404c00340d1905a0507030007403d085401d1010040180c50114105044075810300307107000103124420342c0341c001c0e0003921a100c0e0418502000019021511484440e1543e00c0500c00c2000740d89030810305031034601400c3d086000000a50b4100324904007010400d520040c0d014005027000e0f4541d1005066961048541800748004200018002020300550300141820151303848007d146940151400d42d04a004800c0444e411010710003116050100d84001c1e0350040081002540fa880c001e044c541042c078080c0e0051041000289203506c0450f03409058800041c51400880c00c0e80d806c01080368084101202c03412009101c02d00001e5840c020980d08181c85042d003e11074040303070002084030f91000019011a81840708c20004213401048100c61a10214400f2400811b01c0c000715000c10007508c4001d0255151000c001a00002144164140ca00c00c071900c00040e207411400c0405d646090294401c25108802c540b03002680c3c429030101540d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 141864118 1250 141862868 141862879
    0x507081e0c09210a030503041502251b08160801020c10110f0f0301050f03150103030f0509090f01080105010602030c19030e030f010f180c050d080f0a020c011409031b 73
    0xb03007143e00309040c045246030032404030301c0220900080198011608401a101c010110305002d46100c21250b00c02d645500e00030190502e20b0510203011010758413034414441d801e80d4241041c1c1c0ea1143c40d594100c2c148640f81e1003241c128011034000e506000b12004150071030010110303100306141507401808000740c2c041485108001c4181c01400c00301c06440d00741d64407400706450703624090070302100010f009942c030300c240c101c0c40d179000100d1a00000d1606581c4c1501e0319404007440c00c081034030117100e4a81a039500128003403c00c8800031025035518181d03941c0d0740080c08140d03654130003a0303902d0040040a0500781c01171301c0407420000303d210007c20720f24043d1401e4070f4100c001c0000b0a080c45954800c85985944410400d115051075000d202501d000018101494100c00d4076092440c14450042c50301c2282149400d2080c449107005403101d1070b11211b102d55072465082d101a65a10700a901c6d980030a000166850b0142c210301e041e2426a80d019003d03002d1120850714004403001c10441c80c070b500c203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 141865368 1250 141864118 141864169
    0x70c15020a050909010602150f0408031305010f0207110f0a061d0411071109070e0a17030702060c060103120302030106120c020f0105010f0e0c0301270e010507081e0c09 74
    0x15500c0c401030070300800658008d00300350349002184910180c0c0080102e81c080322390206200000e000d140c1166409641009204001c10507440c1c500e025114a0b00c0303400c03843e400410110240900180022700002003140d040c60316143e01c1c07052046064052040300041200c2c47c1c5031800c160101d030050b0646140061001038914110301e0b1401d403c2e08980426164010007004010361400d00d030001a8120201d41010b80305400e07244006141c031040c6001300e420b00e0000d40c10000b1a25420420f442c40703150b0050180d0b4450428102440e5110b10900c0141c52a40c81c40306c913481900e02920807281a0b9210360360307801c40789019105100c0a080858460400c5203c0d18000c0e6002c8a401e109844c040c00c12601d05c003440d180b402c1c00b240c20740c40c00603000c41d046c008200010080e4003020010400464070326241e03000c15101c142110030003020314101070b0300c0369403c040800241d035611040700d40c49801d02c107000b45c1081c1c00c4810f001540400464100743d44e010200300031409841c06002d402c0301031141c80300503c0103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 141866618 1250 141865368 141865387
    0x5030c01050a02280302061b0f070f1e02012303130302030c0a200102121608040801060603020415020f0604020108130503040803031e04030504060309061b0206040b070c15020a05 78
    0x40d034040c08a80544c225a50f43d600c010554140702864116002c28100c0b584245c8007501400c242c480c4141f0401514800541501040f80800c45090659000700c1c5120740c01900043c07202c0c820a20010032070018080c12140d41c4601803030070f9191b440042880c8114190f60b5498404244462040415020340c40240031419072114100030300494107107e804000800c006100404842e02c2c056160903040d508420466a804e802d0003003505c0800340c21312040f01c1051440d041c80740452251b5006000d055003400750101d14190160000d208642d455450100228102a000c90310b55540040703070f8401d0380080d0702080140d88a89403080d0400310340601c515440c1159600c1c4c914662080d4042c114030317040481002000c0e84404580e0303803084602c0e2041502440c01c2c5d170340180780c3d1040340140b105140c0d60380d4800d030601c010b0f94003c5807494000782283e0041d04013540081d69444080310100c8400e42150f00040c0440e1050064210055000b5901d482111038501360601a412040940301000801d00c00501c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 141867868 1250 141866618 141866653
    0x30120160c0e04110f060a170a0e120c0c0103020306100305070201020904021b07080d050f0c0a020607051509011503020d02040f11042d0302131b09091505030c01050a02 74
    0x314440c0f95000c442013a014244403000481e0402140701d050203005072800076230003100c022040c8031500c4401000e0354941c402d0740700505000d484942184036101c1c20940c0320000c5001041d001f0f05120442e4087c0b020705004500740e10048602035084004d03062500324a40c001e4001c160015000d000250402e1003807804101241c01c02460502a040104001c071030407441403000002a000e44800382441c0d1922410107006807069442c080051200004c00c1c00b61003105010304408281c0c01000260b031001241055641c409680940c210003615140208050950520510b92030141c01400a980700d841e5070208250440b2000702039030400d40740e0f040c501d20755405114034040c940c2140305681d11182050f01c4101c2c008107880740c00c0940b5000000074a11003c15410440441c0d0b0704840c43e8524403907018090025002903104162100442c3d0109404e0036002240703402a07a00c026800c0040710f403c2d0701402d00401d402c1c8966a003580110f5401001075218030f00038800d03102c0354011603403848441210f222 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 141869118 1250 141867868 141867871
    0x102070315020703080c0c03191205010303110d0f09050424062001180b13061d0f070b030103030e060708030103080712180611070503060c09030120160c0e 68
    0x8a903260b0000b012400c161700302c4a026000f21041c03188509102900c6d00d003603503904c90460302003890703103003007001ca0101407044c641e2255440e600003003848503581da850080c00002e510702410031140251622102800d125100c07444480b01280d40d2500d01da031512041c0401404440c002c440784020000141c08032901e504105c0c00148070650b160301006803070301010300d6102d4480361280c0c000d07410700c10080900403810000040c0e054000824010b541c94030441c107a41003c0400340200100d0401041b455191110254801a244d844080d200c4c05a110a0715036101d007500e0252101c0d40d04240018000b0901ca051541d044042c06403116140c840c0b00d442e007050720340090340b0455800d01c000460b0810000c061510340a4072040d03052000b01d00c14038007032601030200503000d00d504110317001e05140b14841c81000701d20018107024041e520300c1d00b05000d00f60b00c1680442c1d5418040e41c01d001102003010b0680300f00218140d6030a6040e420034441601c9129070714a03039801134403550411100840da510010101c80d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 141870368 1250 141869118 141869153
    0x60702040914070e0c0316031415030609010c081305010b03030315040b040902010e0f190b03040c0b0406050403030c030e060d02030f0f0105030d03020d1d0a030e09041101080601020703 81
    0x50260102e0403048070b10308281c0742c11a40203030f64181e0500080c103450b4026a50401016401c244070041822011002041d6075280c1c42007030b90841061000c61031b41088685034040059094442503038541144d582a04d88200014000a0b120000950740301c0c481808100103a00c00c10020469400e00f40c00039255070829111001c00750750201c580c0d103a6180c14030803600c001d80242d505001c0c0218075000030303003003240d240034450050508120141c420399602c0024460381488504039004917480796201021074000700d50445908881a1010400700000000d8800702c42203903640610b0b00d0b042d907800312030141f01c1c240100d060042d904400612a40d445003d081202c44000b00103869160400f002050500c01411201e1040d082000520850720082a241c002441d282000b69850000c03042c81c600804404c0d0074100039210003a070300840703810041070602d0800e00a5803501410b4032740d2410003840d0b400c190740c010000003601a1810295014055103507200c01e050069511031640c0e40c40d201092403000181 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 141871618 1250 141870368 141870383
    0x30606030503310605030402011403150103050603152802040603050901151a130801020a080f0f06010519051b01061508010311060705030408010e0303040b0612060a05060607020409 79
    0x25a10030751943c841d119102c82c0c1620b406401100b8044040114a9580160b004101c1c000001509690003404110a00e000140704c01d0740c0c91901100542d40404103c511030700185c100804100c003072400040554288140c214040007d031206820b00722a451001c00e1030762115005030701c1c0c0c4d000f00760502c0640000c20241c0c40108080c0742151031a801c440e015030704001c021b9411001030280024a05c010040912220307081c1d5910003420480110b400c036a54421003096000103100c200c11548050030038040c03640030700450513031303222042d100b90302070403c8803618000350050104540f180c003001d9000305002440d0401d0740c031703181082d030207550103420301300d60940703940e4450314101b011070302c070601e8150304160501d8800c0b640c0d411669100d01519882507560300c541700c00b044c01d04c140f1a00780100c034010506407000b0440550700035860781d140d0f001110240c9142300c0d000001903d41c14941c001c07074a00a0700c40b018103013070340ea640740c0d6000034040a441607030404811301400340161240d1080c074101d607000381c0c2d8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 141872868 1250 141871618 141871627
    0x60c0c090203070905090703020403080c010903110f0c04020901052203030206150f06130e010608010302030c060424021c02010204290f0a0c060603080913150302041104030606030503 80
    0x41818440146a200c01422481002001002ca600903003450603600c1c1210035402035107812508070041d025135000a44451400248040c3c000815440300c2c0c851846130311015292900b80307031100c7c0c8810035901411a650003440a105803490f143e8010501008141071090a00303450200c5c05121180308540a01c0301e6015400500900d43c0400980f0360014038030040200305400c94021a0100c010b030850680a1800401c660781c0f00b419410101024048250040c0c1e49582d488900500301c002c20310041e4003038040d001888203e03040c810704450540e0060320081c2c400030341d007030003c203c00701111001c882107018034542c08a00d260107104100c401202503001689660416089010b00c85d081d0442c03174480b40c3d01540c00118603421000307803201425002c16480d21400301c603105499420741a03000908052a00c0004002c010130344014000d0000d090314100f80309082c401d40b4504071100c07510200801c4805a01c200f0052500d500142880000c01c102181440d5480c5d0300c2109480050308105d405810205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 141874118 1250 141872868 141872873
    0x30b1602100209010f120f05090703060b0a0f0608090c060d230f040f03111c230f0a05040302030607080603060708040f08090303090d12030c0c39060c 66
    0x400c5070081003500d48110b26001d1450000b81501804188600500c1a442e0080d02460b41d203070700041c0740616510341440b407403904c00412038541da0706010440d60903180400c0000d0a081c001c44d4241940c41d400d846940140c1000c0703040e44c00312002080c0c85242c0c0310f8000a00d086480310300181c99010307014074010501c0700d01c403180c6440f4060208102c400080c1c9103420808800d03c2090051703085070304506402d1650a25042c2151540200101c20741c00348203000306101000101a2052850070361540c0c0c000027030303a0307001c1103c0c190199040500010403007804284403007060200201070903c03c41c2895032406035240c7c0420f0910300304607845404550404200119800d0512285600400300d1425403620b10f0181d40d0100c0d40180040f028101ca031002c5407030001e58404100701c0c0c409190040802c00d02d803201c0d01c1d00044405070030750307400d0020703040c4035941880314051350a400806a200c0f0401441c0e207507401c0401c46e9038030410120340715411080014040c400e0021400c001500f42070342d03440c500b0300c90350 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 141875368 1250 141874118 141874123
    0x3010f150e0405030a0c0804030c0e060108090c0a0506090a081207050105010b0a050f07020d05150901060f18050408120c07060c0e060d0b03030c07091d1216060204030b1602 76
    0x540c0219a03000c0075004100009201000f100c402c0030980c10442e44002c0c03281007680036801143c100606c0b0f802c10b8800413420300f4100c03c10600c1088240e80d448019680c0300c00c00c50b142c02d106528a034100b200303104240214074049001c1d1680d11006000164403540c0c4819803490014070402c500c851340e00000324042408000e0103440d014100324221189020005000140300748101c821100c10100003092003c11941d4068245030025084400c850240b41122827610034880d00b070303d203d6842e42c030b8518005420407041030088200d0b42100055581e142e004841503024003c001c1c401c55441c0410008060000b108201d0b040c081c0000c0c00b0306039240d0155103084412226420b5820045c400c407088200c1e561f0761101c044038007480018802007900d05d0b040f000310f855070042d001c2c00c0c0158051003402050030215940305c54141e06000c08190000d4506c5003480f510f0355120b401288500004200c02c40c0c4502680c002920000d204043c014038140e501e407600800c801003034034548001da803401c00c40020544d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 141876618 1250 141875368 141875411
    0x12130519080d03020306060f0304140105160e09090c0a1203020d0201021611030a050d020123060102030a110307080a09060f090509012615092406150903010f 69
    0x290610140d62908015403150b9400d00c0c0340010081680000004d4200c0d00d9072403d80791603400740c21080e40c81c0e09003032030005043c11488803035a00c0c0398a401c0014051440f0381c102e440020546464190204031000c09000001400410760390003886481815821501d07001e004038003c1010030054840784507545002420036074030b6607452003168010b002d000309554110000200700c47c1d100680c0000c04225001080c103000603460042c244d80103a921001381d480c1c041d00112040355640d01c00c0300c0c5003021a18240c2d180803094801500580c130a0111940030381c018202600b0400d000c5049a0900015a9860083d54094401c1c0740005200203070802c00c03640c008502d581c0c0341029040411380981003a0115050240501c2540e540c10320f16400542d800250300d40c1b291a20510138251160b2402e0101303a1041200145c035810b80500c030b40314032401410743c01090324011141150286803241c881e0b00400030307451420f0000035036064013001051000e0b5024030030040301042081020032003850148200c00762000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 141877868 1250 141876618 141876649
    0xe120102071b1d090706030b0310060e010f0f2103090e072303040f08030a020f03150a0e07081317070501060509060d03020a02060f04120602190507120809121305 71
    0x3c00c0d03003030059041d00821240c0603035038107160001d490500140024546000c1018244080c0c2c40c0c801c01182090302c0722199070582e60780044d80c200e460740d50203403180780508910a490120030981c3c103499540e07400d000c511030f0160180c9080050079440d0805000c2c0c81c00161512408074a14015141401d010007001d18100000c000c8880d0440c509a00c40403000e807025680284051000000250700282c00d5050703484d5070102d01c1c011902d83ca400e400e241200100b580784144103140c99940041d5050200d0b5005214064903940e0940d207468101000440070f8140382c0407a4100d407500040380714030f459000507006c810302400010038840e00d84028003031003810241c041c034001c4100440d03075000f00341c000a20014a9505544060b80c0301114030082d0164040e540041040c6040c4c58100024800c04c0d4002d400c052210203c00d002d42215181d060314184903840c0002d00d242d00b212000301740c0b280146a0700380d102c580c407029102070210350b22204815030304c502c0700c04050303480c0107405100034205120f800c42d040c2c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 141879118 1250 141877868 141877919
    0x120406030212100509061005160309080114060a090b010c080703052d070b13060204240914100e04061e0815010e070207030605041119060e120102071b 66
    0x14148400301e8490700c5e008007100d0260407004032000c169441a400c94508004040e0100032100b10b51034010700c60005c0b4458a41250b0032f044014600300001490507025650013840350801c10319000c11080682184140c032414044d22400007004125103c00a0034014403c3ea03e080e901c402c0c14200681419010001440c602080e100c484803c5002c2801c5520064001d111030b0101e907114500d900c1c00a001d4007006005c540082070000e803000e10100341c80c85000203005441c082004824084800c5801c3d4400c1c2c2c9000c111a00c001c01d410300348140030804c1603134540f528a03070611a050204003034601c3c1d944081d61404d81c0b480078082000c01d4401c8c0b4400391004030003410003c1c4984499001c0701c10180248038080f000000482c903640c1c0200300702401194401c0050100385801e08000580e20b00e00400d590084200c586910714401501a0401c181d44158541c07083d501464028005c00600000f8850250341d0308022407070120f00c070000e84000d4035408880024032141041d60f50841c1825203100c114131749 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 141880368 1250 141879118 141879151
    0x3040f091406033a020d2a06050712091506050f09010303110304080d020c04110c0a08090a080109050705010e030307110919020a08010317041a0c120406030212 70
    0x40d41c0114048900420500606a0000c00f850b542d0350031140300e10f0b1200303c0c460070010940c2c240341c001c1050f8584400e0f603200c01809000240904010443c0d094004008600b401f40071400680158009030b000286860040900b940450500003100e038042000d84030a00040c90541c1150074501420020304815203003106101034020200340c180006001c000d05021403421030103209001041520300410381082215040544240080d40328600042d00e01c0c001ca04010391042008020001c0700e180c44481d00040080703601544801055422500c14141c0c02007a458000910076824041c088046020f01e010b0603e00d4902000540340003038065605000360001c2c04840c012400c4141201300c001341c251394458099032a280000100303502901501c40ca284041070142400d98000040e9060f28815299040f1440900d80c510089024074420501000d03d043c251001c9000c4040140c407424080c08201c2d00d445006104031401074200e81c221400103903000c1140480040e41051b060f0308184814514240c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 141881618 1250 141880368 141880381
    0x40513060c0516080d0b0303030c03040b0105090103120f030b0a0801020c0c0d0f03030b13020a030510080f0d1202070206030103030c11040615050a0c020a060c0510020a020303010510020a020303040f0914 89
    0x2840f50300307400a04084404100071048a8140d0041c01c4820030050036a0782c0c03442c003443c00c440c1d07641055074203031070842c80c1100215050030200b0203541a01e030402c08243c0c42240c624801c0322041c0384036050500305611a01d51484507201e030b4040c4405800a00300250302e45911a92261a0501c0030541a204070122080030001c00e00da980ca02c0c1c1460f0301441d0106051780d071400807070a42181042e041800034400a0340c80c0306507500da40070394041c405600e04400860f0351280155610601c0c460700c0d003400d4010080ca985090b0217281000c1c0c048070300c1440982043c400e50001122a0000d80c0141c0c0440d280314a03081c1005800c150783c0d001010b0880f0f00f000f1023800c205070503400800381049441485000103100c44070750f02410444100507402404450702a443d400002e207205540301c0704a601740700310040440700303200a00999000d00d14580c000c0d411a071804041101201a41d2072074801e600031080742e0009038030280001d0000d01520099010304e1450003641c0800c54200e01c1001007102e2518061240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 141882868 1250 141881618 141881647
    0x207030906081333090803010501030914030f0316090807061d0301050c0d0e010b0d02010c0c03050607051306050c0714040605030105091605030d08010501031a040513060c05 76
    0x2915a2454000b49603a250712001c9010386410001400304201c00d090313a40d100131948881045103034400c0c0c408049000701000c120580d00242d10042c4a04c2062006006a500c258410b00005001d4071080c00000d60300440c81e800e5600182c44400d40000010400a40c007000e2070b80c40d5941404c80c0b4214035081d140034426074035580d00d0b00890040103449441d10588108115007000d0841c4018001c00c01d41c144540030a03d41d51206071800320103420300034036a10441c4184078610b0003090241c144070010342c4aa00446000d480b03003404132201110000302101062041004900c00d40c403d440e4290784180e0104200b00000e185d5000200304103003008154209100400c106045407083c09488500c00ca042001074090304030741d08420303095841c140c00c01000d200e00003802a07103a03200c03800c3c04190580f035400741520317192201d1021380407030703d41d40c010001c0354401d520020101403410051142240c1da0400281629010713943c0382000d01f4103060241c1844018800d43e10103101c181052803421610607841d90b0f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 141884118 1250 141882868 141882887
    0x1111606060806130809040f0c0903060b12030d020a03020c0313060206060d030e09040303110d0609051005011407050129040c03050912160615090b060304020f061e0d140a020703 78
    0x10548000441e200f01140c58a4120329008010241d0a020360001d4007270060000c1c00b00c0c4070984101d07003090031118160030700c096038601e009102009507290101c0381d50200043e44c0034040840c02c040d402c05c010140d0b048244080c1c10b060340710305040c5140700c0c80c01c40000d19001014086610410143d0101b00009411261811031014180e64184995596003030950080c0100703420301031032a0002491a0b40c025041c0c1c8481c080c0d444400341082a0f0b20b5130880e5010010450040c0c41c049040c1100c1d4081660712180504103e500c503100200f41c0307544020348011001c01200b40311211071000c54102d41030b890140240720a1217607514040200340344c4001203d54900b9882d41d910300c00c0700d0000d100840c26017901458040c0c0380d00001e0038040d405400500ca4882d403001c0c4111072501c0e2404213001024607007441240c0c042da400400c070b0003520f20b20008100b030950120002000a0f8004608582c8442010010f0b01401c681480000340c03020111a00803034003070b002000309005600c104005d00010303070000382c01e9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 141885368 1250 141884118 141884123
    0x6030c04060815100e0102100902150d02041802030103060b0301050f060d0311060108060405190c0302011412190f0603020a030b041b03120f022a01020111160606080613 74
    0x10202600d5024140010f0240b103c2015000480503030600c007181e13000b44501052040a900f15840c41101d5010791040307034007481009601c448001303484e000c6900ca040c05060b100318611001494181d0312000b44040400c40b00c0c0702a615900400108107129841c460514000001d4000b030043e40782003003480d0011140141810b02c202e04148131034041c940324200411035040702c0b000300c400a584444441c0e41c1d8410480c0e040b0303041e00c10380b6000300502e6081c0860382c40741c80d070000381940424210350055070240540c030041820395106000701c0c425a400d20503802c0c012600307150108141c41034411800d05a03074580710148801801c1884c00c100503100e010201b130449400c21003c001c2c3d600c591400c10100d01c481e144054140da0024404800c0c0090000c41c0c1e20460304c5034030703804840d021a901c181c0e103480c8108112202e900403900e102187d0001000b00c1c0300c82e688144000540758030782c001451001c0c2c01001c10003011540c078a41000c1000001d100c0d0801608a0fa0014403c80c0b81c02c401d00d0a1903044031200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 141886618 1250 141885368 141885377
    0x5100e1911030606010203070b01090c03140f040c080a020a030206030604020c16240f030902040b0d031e090509040f020f060309062707050409080403020918070506030c0406 76
    0x14014a110510006109110340140c508154900782000001d041c000707440c0d20b01c40e006850105010350300001c1201e04441d440040000c1e60307841e11510b40300400c1c22a43c00750030305454075803a8203003220040042d0321490320702c0ca8103400350405003810080805a50003200e91030344141e5190000d0707035602282000700ca5049500a550750340300e00103d0f010740142d0014a80c680301d00d5000111031300ea15803000c800d5a54422087c5aa102c0044506844140068040c00426242c42e940c0d8003040c07090f002513240c1d50002d040400c3c11010a004a0080800d6001c10744c0003540950100c011a0030303045e0350038103a20780b501c1c101e41400e0504c1d001070300030705c4c1c054401446e54000448040c1103444802244a8040b0010b024036124a80802e5258a50340100e500c00340300304403044181000c0c0c80300040c0903188a41c240040003076500300001c1c00002c009101082e030328500148800001a560560ba06105802511103015003c00c500700711454020390f500094840c4e1700520800c07a403800f0000656043b201107182 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 141887868 1250 141886618 141886631
    0xa0c0b060604080304030b010602060c07020a15090f090b011101050402031218040f090303141b0a18060f0801080d0806061b0109030509030c190306020307051b010902090c070510 78
    0xc2081c81140e01c80b1003e400040b0340042403040700903c05040b1215038003541d0380396480700e07401c088610a560000b9400f0110348030a205000c009a103511342b92a103401d102009a03143c2e194030400480c80e511181306180c42c0c1da40028039591110103000d421010308020710407030034907500281d219510700ea040c158500e07011030b4649a2080790080008070300f801410410000903001241c401a151346a400c0d804a400c242200d082c40c1800124144942c4a100414a0907050b50070138041c550710101c0540100025054a00c40c01c0e95941c410100600081d1907002900c6a00e81000e451580140d0045040e41c0001c180a060b95070000c0d0080d03840803007103800f1a916801c00c602071030702d000310f141c40a060f5071800c84030b242019003180082952070300460403203480c002620200b0070540c50b0386200c0315421302e03881c1040000030040d8020f15000003445c00d200741008110544107140f0030343d60308007102c10381d1210401d40035800c0004140e9040040115810b20b00300340d41c1c0b00e050f511955428000300444d501e84 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 141889118 1250 141887868 141887881
    0x4060b03060f090c03120f070f0f030302130b120708130b09070f06090b0a030c030f0207300e040b0102011b03141302030a020d020f0d0b04060b03030313060b0a0e07180b0a0c0b 77
    0x9a204030114ad000da0860303900000b50800900030342020750040b0740303012294404149004a501941d100c8403000070703140340310b0345d42c42e0040f90380e0390b006450f060075441c2c00c0d00c6580024007a501228403076501c3c6001804c00a15240c007811680030290b11007010300070b00d0310f4240400c00b00102201c01140301410040346496105404400a080d40200500a2440455100d0030401000340c40c0c4004d20b910396901c1c407400e00b00c483c2c445414600c440035402003501d24001c0c1c04030b030916401140090b0710500000882004c1c50390a441420441465180042e07038803004032a00366950302130b9076084840000902c1038a15660f000c29500e803031240c80070b0f1041403208250310441d034601441801e556000f400c106c130f50740f0451410380441d520940342107601d00e04000700b032191410000240c911039044030743c0030403440c040c40d101c4000411301d0408907904000d041030b0201c0c2c00b5000300b04a41c041d5000c0d5070b070b071041c08166058840c0e00603503940000185103404c0161402d559070003c0110861604800312607495110003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 141890368 1250 141889118 141889133
    0xc040812031312020609010b01020610060309020f040204030317070e060406121e230609180102090904080403021801081e0304030213050601080a0203041a04060b03060f090c03120f07 80
    0x904018500c3d00c2a0b040c64001c2c941c007060082c0a684068024030400c40c44100680c1c5a00e02106c085800c0c82c5111020490240320b80c010110180c001f170425a40c0f4030840010a090f64002d800c1680410020041c9116a100d2540b03820350105640c64920070700941480090030910803440740904104500904030b084000c1d56005803550b1041508030501c0e50b0350100e40302c4c041c00d0901d41080c0c110a5102c291440ea00401d2400340c81600b00501510316036031407900300c3d030f1399820120804000359070911038019240c40d4948c002e80134a0081681d60f4503030b85140704100c4c005206c030240d0b0f40c12888a1004001590000070a441c46a81c0c0340b100c88050054001301910b140500d503c060351201005141400314901075101600558081e41d0b101c016079540311804042e440305035002000c4588106130070107041400d150f03241e0050710600c0701054a9070f5400001e45810010344d18208140f80010034840300d03030803c0111540d00071054018106a0210190fa6850380c010004040c2400394005070440070449030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 141891618 1250 141890368 141890401
    0xa2c030a020907020f0a03090f090204080604080a050708031302100e10110a020904060905060903040308270603090f0705010e0901050f01051207020c0103050a02090d11060d060306090b0c04081203 86
    0x171401c03146560300d80c0c1401064101e65101e109101079800c40d000c15440043e0003183c00355000d000060000352101d07a1020790700d501c50080041006014413003a0700181c0c281d0002d40c0203031030003d154684501e81d0300400c0030b080350000c1e00d80288503c0580898064076402a52880d140f20360030f2050450044041e003609040400100a6000012104200400195034000103065001302c1c111180340d520040ea240d40da104500020303000800500c804148007070350f010100b14075645010b11400c044004004520705810555064515401959443d50381000810900e03000340300900c0c0050f045031851010506a903010300916002d038000c802c1201c0e00f079004104440345050003149039002c918044400030344500d00c628030540064100000f0175610a11802079130802900104400b0b440d1005990f4130200c60a13558620b50001010301031880141420301c03035480114000c80740800c007826189020040c007480101190001241030209100300240090030280340c241540761285d0b280c0b6607082c07a00d003a014 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 141892868 1250 141891618 141891643
    0xf060e010212040c080d02030f03190203280c0504090f0b0907050a020105071e08070306180204031b0e070c0302011b11060f09030901031d030a2c030a02090702 70
    0x68010b85620103400440e100740d00071540c8655440e29000f0090310b450204048000603802800f005545080850085405c4101c4000184c00c01e40000030035010fa81040b603a424141411071508410141400d6041141d40c0380b5040400101c144004090300c280590b0155260103a520b02149844450030703405250701c20700080001550b46001040240143c0c05448128010350030100400c007000c0c001c2c680b062010310540c80036010504464421210040010540005c00d620303201c0001d030a0714024401280055600030250307645055043c014400f00840c021f02003101c644000800c01c00c0b000c8c0f2500c9810030b0b00c0b4a04100383c0381841c24100c3c0901800c1710a0f012840300c40c0001c08440d500000d0110403403c0400995060f075075440882c110300d480c115064034203a041008090346075846a44030860558082542d0103002c40700100191035508540b214030086444003540c03080c4001040c240240d440399400d402d505011000e40403d454501e00d2100034010003c00d404141050300901ca003004486 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 141894118 1250 141892868 141892871
    0x1502160e1302031f0219020613060902030c13020c0f06010302030a0f080d0203010f09050108011406090702070f0b03011707030503040501031a040c021c0f0c020f0103060e07030b030706110a0f060e01 87
    0x42c200074410000d41c0510203407400e211b250560039492070300116500303109845102c2d00307000e01c11050b11980068902450201ea05016480c050440b03543ca80c001c429035100141c9006031075084c06108a403915030328070340100081c2e00c030100410060b600022504202d60303000b504695001c3d0780c2d01d000ea9003801a503103400301c810b00100005c503010001e584c0c3d0208945c4040030601c4aa45d841e501c2500f2100e0b02030001c20340c5011100020303050304001d52950b8000e030340ca1040300d03182c9558154514880045812141d4080e400000410201514000302d910309810a00a488030700e1441d51036581d00d02c40e61040c581415142c0311900b4000c841c01031000025500500144103040000d80000d440b06240c80300c00c43d00c0030581c00e0401000e80b041d030080c18012080c0c0c43e43c40c620701d515020040c01424070703803400741015120070b80450110440c4000c0340c01405141c03030108940903e241010700300301d12600040100050040210485400001d1051100c3d0b023101020a147d602800c082010b000d1010149842e036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 141895368 1250 141894118 141894163
    0x71706161707030f060e06060304060c0504090c0e04140f0103060b0105090a080607020601090b0307050409140a0b090f0a0c05013606030e070e180f071502160e130203 73
    0x383e8054000649601c4503050401a02d030300d0700703d14011a80d0581d0455081542440002d00180f1a640209001c0343e013410251b04155072004000f0559069014502c00122140c100c618035041900070f0322440c210a144242041c034008060704004141440040c080f507858818100aa9000b4000c0703511480000e49540e030384c00d4860340c0e43c596a090035110100184195000002d10001d03c0c0b0480e1100c880040107045254900390402000c0c00d51810f081e2400d01d560100c1003400f200400c5590180c1340310321196482c0780b401c1c240681c100302e4a0344103520725800c8002c0d85400107513800252000e0300d600b400c043d92005180005c8280c14101141d6010001041002101101c050030040004969503950180841034030904403513101d000703d11902c9180b20405001c98002d5100b000b50032000c0300280c0840e0607010006501c00d00c1d000242d030105000240b40400013100740d9042c04682c04c80e00400402d00000b500e880c082c0c00410600801d00d40c107501004451f4000c5640620101030a00b01c03801503403c50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 141896618 1250 141895368 141895381
    0xb0901050105220b070c170a03020705060901090902040e0f0c0306030a060903050c12030612010b03070506070f1205031501030b010206070f050c06010807052103090409060b030f0f0717061617 84
    0x511618058503208400d02607c0c1d4002c190001847c48000b0351640c058603103e441d0606000181c4c110700c0c03034141405085035001c50607101c5840680300410901d84c4145640c100903010300440740c40500b00c0c004202d400c10411040d40c90008145100950013200000c80c040716040448290049000700f034498011a04202002121480950700440040f102881700050540b103141c00c03105580510790701900240010441032501e030000c1c1103480e00800804013109256a01d14009101200e40c00001c600d005c4280460341d201c2000c00404c650080c2402c012403468600080d40d2660000c104c0742c1048a00712006000910610613280100700c0901110099610b0388400d40e226400c901619006a039202d5402c003610502c1c0640c1d002000191010318600136032907080c48003404103d98144d841c40d440d00b90b12141e94030700300f04006040312034030301912844a0780c0c900b0505200c4c05611442001e40d6440c504521440041005a040003800081c0c0d800c4d000002d5090341d000c0744640b2a150510400010840b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 141897868 1250 141896618 141896633
    0x40510092304020c06130606080a0b150103020f1207200307201306051305010b030a0e0718050f160e062508030f09011506050705010b1e040b0901050105220b07 70
    0x12641f00742400d000301a10f4a81c001e82c2c5110114001d03100000e07020209114201c011007080188006240243c9000180304c00001d403680301c1c84902c0018181035042084d40c50b0706c544540d540d083c01c500318600141907104216900d000e5440003500d03280000041050040c0041600c5441000c040d1402440c0c03c0d40b407801200800035849194040c040e84500c0c2c0e800518180301b0541a26140488075041d1b0f20b5881984008115059035841248103030440452500d0703015030f11664000080c403020440740b901740f801c440c0ca8000a800c800902d00c180e440fa601c12a00700043c902c242000383c4100f51909210504120014181483c1c800030780d5000401da0300303105040340154814160b1801c0500340e602c030f900c1b4140c00c0768000701a0028855078168248a964803500c0188441070140380003090401840001411709004104000e01070000341a9103002c40c141070086c5409003408030b46010b00382d0301d4000060020b2260400305650320825501d03040c520710f402c03038608003e408680c00203503c8444602d454070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 141899118 1250 141897868 141897901
    0x904030917251a0f16080409050f01090b3a020a0602010905120c0a0308090114180705060705060a02070812150f0d0c03140316050102040510092304020c06 68
    0x45000f05190b42071440d030002007044880b1101c03c10f8003941385c4001c00e02c601011075010035040b40c424104000c002580c1a06005450107169058440e40c0c09500d07154003002110311100304140181d80c9a0288035803000c11002c080403442079480c06c1d440c1200c820b648042210743d5100002e40c000002140403a44903815400001c4061080084074001c880d1548242802e008415841240340c0c0301000c13010010307120b09100d03604030384c46000204107142240401c01d400401250b1038a0500c05840484040d401c8c20041a4018982038071050b28103401505e07002e03100c120040808200343d8000610f002000609030032224040e10b080c9824409042443c41d071400c2503038084001d880340e00500324100e0300c0d242c60144400619841500c003181541313107541d4680c02c005101540d0f1701c980024040d80d540c180302d43c4240e00300184500001607a50707042c1310030810304200a0003c0d03c01c01c00701e1001440441d070583c285608810244131031090706400e450001780030307109070302d5102c0070f5000e08410721503081d86030034154 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 141900368 1250 141899118 141899129
    0xe070806010801060501050304050a120e180603073003140c060a060b12040b04021306030b01051002010b0901120c090903051305120d05090312070b07030506090403091725 75
    0x1307200742c07562000115000d0206842c0540aa00200d0071080014482410240804903d040c01801041c0201c005501790b0041400000001c040d8020800a441c2c18840d0030f01030031001c208284aa030ac1201c8a45240c0c102842e55520105e0441202c0181806056a019049007031481c907607550008120310b61300d9940c151480c10310103052440c04160030000304103840d200060020104055030329526803c9080b0001b4000baa0065007404100820b0b500c50302428000d140540c12803c190b501d40020b00650340300c610807160440e4504010390030b05a0f0340108513411250440400c4401042d03505200500300f185500007074540c0d28200c0c5080070140c0040213403109082d0130b059042855912007e001d00c030030120170021882d03046180e803190824020000703000d40a00c0034040b0303582407902281c603400c0d5a018500a4504240300c0c02040000c651500500c1d501c07110076034035070146041c02d6801400413943c600805104051245041c485070034100a80500c14900d80300101c0740503250000c40c8514485801030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 141901618 1250 141900368 141900371
    0x80106020304030210051b0d0504050f03151f09061214010501030b1f0e13150903080c071509061e0207110907090305030a1713050a060b03010e070806010801 69
    0x80050022050381c080741d40290400100f80c3c0d20a400711107541c061304000c0340003500e01e00c4a50b80c1100c101f040079922003ca40f10180d540e07044c2420008110a9006124440d510085404540840041000f6007003100702d048031a00d60070b03031160f07503941d4040398100909003803408000245820344603041040b40e074010f032000000c10240160081c02ea50003404064030910780700700450062001080046401d101c3e021401d501192540c03d140c081200643d401e25428054402401c02d210b005841c2260924661a042052a0041d94046c0441d04000c001209014001c1180400d0200b0000d2075810344600d02010400908103160100007003031311800c43c10310b1003180d5000f955014014400c03640e070b594001101b078440308924401c0118034031000b0061b2082200c583d41c00000628100302034040d1604c0340e15003501145403c8008194500d004210310b070080c59492005000c0360000c0340305101c182e00903a0100e4052148000309025200c800c9406105200790100040c00b44c1c804580a41600c610303200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 141902868 1250 141901618 141901621
    0x30420060a020606060f0705120301061704030903110604081507020f011a04020a09050a170606010306051e0f0d0609140604080d0209191d0601110d030b0612040c0608 73
    0xa00c051070049241001c0503a0041c0e010070424a850805811107280d44403603503160007456030ba100c2c2083c01ea5400001d0140c0701200501440750400401c800c40104505802e480c0d140a48008201031641e21000c2c1000382c5080c0031411503242c42c1d0854018050300c00c202e502440c00420b4000d83c40c502126144014000e6000c0b0498005040c001c1c2c04100c1114003008580c1e001d50401c200003944810089010301104100c001590f89070200c50310003c0040404480e44402c4840c40780b410542c00820b1241010f00d0800c0c1404540e81f02002403400384003a8195401c050242d2011401075410341c80300c168041584100a810001c1d5904841e031030740e100f0f80660b180c014405000c42c1c0d41d20010f80e4000e2a0f41b409108a0744c0300039140d806040045801071040d038800704044943e14079500545c1110180c662584108106a02d00c4040c882e00301c8028a081d14141d0751400c3c6582d02c3d468010038900803d40c80340d504001c6a0f4503c410b032004412042070502d0f09050601d440c07130700540d543c422540031640301c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 141904118 1250 141902868 141902933
    0xc030903100501080d320c011103010f09021303050601140a0905060603011502010605042a02160504090606030203010c080106140a05030c0f0d0c050a1d03190212030304 74
    0xa00350480c1e80440040510f802040001d03600d160b08840076032000b0f11400c6140c264030100f00500702e040c806c2a140b40391748648400e8401d0035189d664281515141040004101440c440092101129078021005844000c82c2c8610251281c6961020380030744141400410701c110444010303040b050040b00d0407480c0d140d451003000140c61044902d80c0d809030080c4010400c41840680d0300380719502078400010f180f40c1302c8001408031504000b42240b9450f6440281383c0c0d400c000369103142c8003d4203000904119243c2e0700c510340182c819000f0607024613142c401500c200580d9400520140d6070003402030142124074100200411424800e04000a05954101809001050131607209049580d035041c0385540b04c03124081c46521040c20007842090801400035400b00510445d103a28145030b407095910b0000d803c0080c20010014041030708080c05030b44201e0308d0755001030384001001909801c1210a01a07000082902c08598204800350100008102c100103a503806c150700101107a60f419140c03150350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 141905368 1250 141904118 141904121
    0xe0d0302031f0302030309060a120c02030d0c390602030112020306010e07050702010c03111e0609030c03040509060117040506060907030509032d0c03042c07030c03110c03090310 78
    0x30f120203501600104250b0a907424084018801541c946c20213054103841800c3d2041103c481024840050b000420a2000d02084d4018943c0d103109500d00750029246481c030303802c090211070a02281d040e070088032007040715040604448413141c0046046446c0e6a48100104104113210341c02c03482802514004114a180000070b1070180100d0f903030702806e0440b181c1c01560f654004400c00d5003803010014280089200400101e007000c141c8003580100d500401200e00e14000e00179102d000c43ea0014400e107000d042c07001040d2800c40310100c6880d480c54450000603210310184400c0c510241c001041048144100000d0701400b0b0942661044d05079600c61200320221001590212595013080103040002626004100001c0e00744000c61500c9441500da620600d0380030210740d43c2c403508086000c000208c0d812800440c0412002094405070310941c40d030084c5104000c2010f0141681c400141411034480d80c8844540b0035400704e01c9035071384240c0e03201d80c1d540c1c2c00400f842803081c4100d040c40402c0b030000703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 141906474 1106 141905368 141905431
    0x6020f07030801050a05061c1506050a02070503030703050304060e010b0402030a061e030b07120e0a030915030608100c030b0604061e02030c030a05030a0e0d030203 72
    0x324075002c0c0440405a00c81c900c51000301c80d0412071500c0388801c4a000da0100d00704151440201c298030401131400302e50fa1128200c5144001c00c0642c0c0107030061030304070895001c07502c0040d40d038010542c0e02e00c00d045000340061010b00202d8006030540c0c220b00380c41482c840001c00c5d010004004202203800890b00310001c01d0702c1d542e04016007940e80e00e00c17001c070b070141b0950078035094295100c3c00f000c2c030005800e02080080032107008004501030362003503031250004420754940d80302600f80180741c0c01c018000d900080041481d81e07413185020348030715000c43e480d60f00500081a020141000100300490070042856240c082080303da0b500c03180204094941038403000404840b00c030740344040754003002c94003040d5403040100e465480c40020030b444032803e552a1442d82c81e600e800070a4060040b000781d200b060f219102c02141500d802d5006140700d018050240c1c2d0841d503c0c043c006000804 = true := by decide +kernel

theorem cover : BRFrame.Cov 141726618 141906474 := by
  have h0 := BRFrame.cov_init 141726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 141726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 141726618 ≤ n) (h2 : n < 141906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
