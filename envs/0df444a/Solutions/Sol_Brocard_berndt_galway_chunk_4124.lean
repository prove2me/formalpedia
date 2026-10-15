-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:38:32.97098+00:00
-- url     : https://prove2.me/submissions/b94b29bc-5c18-42b0-a66f-8cc470b0e14c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 741546762 ≤ n < 741726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 741548012 1250 741546762 741546779
    0x30115080a320708011b1d150a030903080711100f060b040f030b0c07020f0105073806030d09060804030210110304110d0b070309060b281d131109040b01 67
    0x100401941c14600301444c010340c016034081d880c09802d81140d60070040f102140307c04110103a000000c030500201e404503c98055070743c56481541482e011b941c0300111078890701d9003aa541a812a9180401d4200b100340c04001d02032908442c90501105800240482e906e1240382c1041d04242c00a00700d201e4422010002c0c48903a5a000d038111002581d0b0b54078110b641d900140e140c2402e080d250b8103100c0c0c00704075441408924840c40495070500c1d112420369500281e00c601004815600d5a605461104041b07152801c3c005900c00d0b054142c0d44545080c1c0e82400020751b64508014000c40c1140b15198100e100e080b0240a4410540d886c0040541c480c2850718005003c070001d0858603001e02181d80031407010600c20083d40e0f411242c241030010780c80116042c0135000d02014440179070001201400c402401c144016a00c007200d15464003400d00d29103030b644004190401d8601500c0050900000c03a200c09030480d981100386116800d03054a4040100202d96030080c00ca805603210300d1240c0c010024400f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 741549262 1250 741548012 741548021
    0x18050603180f0f0a2405040605070207090b030c0411070f05030306010806270604060b0403051506090106020604030f11100e0c01090b030a0504050f1506030115080a32070801 76
    0x444000151051503c0c854429540c2c43c1c555001400e1981d00911860040580300c3c1580e01140c1a500c042c885850b1900700b42e0007401c019940d08005100703400c00001e40c0e403420b100d440342c403c1005002d0007100000c03c04000c0903080c0d85594601d018000c004010006524003029032420f0702c00d401440e124a0607200240803810000e010900580007c880c119110501503034001c10400901950007217a00c5050108000307103483d400000030844000350100502c0780020b140b1459210780880104199101004e220314400203128440242e4450000300f00020301541894029074014a0841e0b041c1d200b003a103807031400d003940101f0380c115652219032181a42050180c0000c00001382000001c40c0e292646150702448004c054880041c0c1e41d602103820440240580042901d2200071107540074000c40c0c201b000d144043c0c81592280d880c109104d0207640c0070b919031504864801000c1c03ca030000c6030f185e01c402401c48540c40e0265040c4000b808503c240350350030300b14003101e02400074031006090252349400c5a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 741550512 1250 741549262 741549283
    0x61b1b040501210b091c020102120a09080a05090d23060109021e0c0106034b02010e1219051b100f0905060a0327050d1805060318 57
    0x2800340c2106a0080f01c0d0450600d0a225401041c058299076200718007400c12520000400d0030080719194245c0c00303603054014160815251482060586505d88684212000d2200040808905106401c0480e000c1d90180407040030141142d9180356003075032101c04040e00b101c106211a40340d202c881180e20810030215000d0312001d0000c62900d403842d0410301c90300c052049610041d00d0000341443d8003100c20b42026000b16404003104503401d601c03900c990064250f00643d04103100d205684081d4018014030f0301f4441c2c86c0d0510181c0c80e80b2040340c0045801d0075a01a6040d0000440b1201d07000700c020800403010b083c1000ba80c2d400d100845031816a040501d0404802800c000c258103401681c3d89011858040c00070608007403c560340d101000750780303007100350340030300d0340000081081000c00b03401d038201d01e140200004006183c0d0b4103802c0c1c4034440301d0503058080c000c3c1c0e01032503103031107828010612001030810319001035030080e42d100c00040456008585170495034545e0255046862020850024803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 741551762 1250 741550512 741550529
    0xb18010c0314061203091f080c131406160308070e01030b0915030f030a0309030f11070e09030c030c030c06060307080c010c0312150609050d08040302061b1b040501 72
    0x7903440030360036004640d1018240d80e04c510760962481241e40130800c111040c14801400c0040c0c00303e02e20107038038400c009454003a80814459000101840c1680c012280341440c3d000c40c041c401c070704008441c08029a80d2450981218007042038500060207540f0000e1098801d41c0e801c0920310b40709000401d0229209080c50516081c8a1080c03819a60641841d5101c0c0508030311421091000000900d44243d4001030036490000044081c4070300d40c5500000c0c440c1e802a00c908074800511a0200c50808507080810003d4010380403d103d182d18600c5010303040800c18003140d00303044441c1c010a04580c40140b00a0a681c00010503601c411028000a41e01c013504030b002c0c100b420303e0a070b840b0344c40d0942641c8144c10802c1e66007902040500640c0e404140340b81d0002e08110071360114011540c840041d000b0300001c41d044000003d020300d8440510b1080c180d00000d05401c15140d90300717108864200c003850b09110000303c00d02c580c4c07071b08003001440c64040c02a00640c84071400d0006010403201e06800003e072 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 741553012 1250 741551762 741551771
    0x409080d050a0c03200307020a1e1703040317040311012d02030402090a02131d061806030a060e19080d0e0118030e0406051908151614070b18010c03 65
    0x20720f03e40c45c0c80146141075407241d91694a5491407000c0382030441c42d078001070a0f5149409420401d01859120302c0d4610700c11170010fa82004007413150440c50108a0f00100022100d51055000d03404003104581c11510a04080342160312a41c0c00030300b0b543c1c201d1550175500c0f130382c8201203540d01d0a000c1c48240d091200f0200714036605142d004603050580c02400e1132040303600003c005000d10300701e210010040031030881107140005140603c0810301400c3d62082e11802c1c80e42c41c0c00580c0c4074403070b80b15409158020020710200c8101e41c0e079000a45066140000c45000c0c600c010040c82460544003010030303205607500c3e6980d0051181c100d0031110401407400c140d80c500090070312003406030600341e102103800d810811481d42c1c02e440010050310303090b00215041098071107050074482c40c00010030103440d40074003924441e072107840394610313179042c103d03280225142007015000c0150300a462040305c0100b60500b0610780300c1c164981c001e482200740c4500011740340c40641c03a108450284558800a21246030a01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 741554262 1250 741553012 741553031
    0x30b040b010507200a0605040303080603010515010e21010902120a0203030706111c0b120a1a180303040c0e06090709091802030f1b010503070507110409080d050a0c03 73
    0xa042c0d0292180051014042c19070004644200085041c20700400801d0018400e403104002481a0401c1c030040340402c698401090503880c040c092a845200c1000800c1d2075103141d03000450308070004003c250b4104208440c0c80740c103c20b0f0b41d120769203807560340d000200301c102036481071224140407000c4203016030b000f400c55100142d6010080310310181c5c0045003c581411011034400f298030806100d400320304000c3e5000340618005801410249100311652056075440d05080303511005481c1000302400c050b06c0d1540c4880d20b00240207904141f05028503034a46469280701c82c0786500554055a0030020004100300c21505000d807035920482c140c4660f032041c101094054100d424600a401c04280c4075880002e801d0f0340a80280515500241191030102c442044680c8905004841030540d8080e481030307424550194044902441142e83d03920301d48141a01c0764017001c0c44812600303511a0310780840502042070900904a0414805d0002456040c02c83c2c40313201b2100040d80120a1509001021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 741555512 1250 741554262 741554267
    0x6020c060403120c110907020d08010506040e0109050a0b090916170613060b1c0b01090207030f0e18011d0a05010f12050322210b0621030c010b01030b040b01 69
    0x903d0118603400c1c0f40c1400310580c901a034000403000b99207030304180c18004200c4810340c0090000300000050325450502c1c1d0300c1c0d00600000c0d03c5180241c44881c0d00c8407004200e040f1035980003680c01160043c0c0050382e0640f80000802c8280103840390500e5030b0054281240341400b003152100101501c4100a60703200582403002d0300c8540080081012450a9800c0c030701b0310130740d40c0001750800c500400c4001036103e036840904e6514400311055510150800000c5003401c018405c40d03070003542580310070701200c0c80214221510342e01e0011060b0030000101c41c1031120307010850302c1d501801c11001c082c800d4245126401e400050010155a410703401c10004211350810b50200d40161031071000150f83c090074a041c20761940c0b1506000400b500c00400c003c0b100f00015544210580b581c040b00c0715a006600c001c0c0d80c0486e02d1908000e0023212004002c40c0c1ca030f2819180900d0400880d00641d80380e140300b0744027141550403162000c441070b51144e00c0b0303904660303240c85003040403c804c903410402404103a000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 741556762 1250 741555512 741555533
    0x606080412050a08010b1b0d051e030402010212130801140a0c0201060b0415050f031302031b06030a0e010b03010903020d030c051204060518030f040f23130b0a0f06020c060403 77
    0x7100350380000058403017115403000b40790706044000602200c4c001200c5c0000201590300240328030610310181800329280f8a0ad00c070407a40903d4050740101080c00103416007000703541c852048001204465440018030940a028a030347c001101c00030070072240742101c0d00805503110700e0715000031640b400300140494050901503a06507800c400300000c23517152051003540c8501c150081c043c80d1000210401c040c02c110303054080301c0c140c0700758283c80c0c88150b0640c188400984008486038032050a00024910809541c8109054504c450000c40c0062600c408603003103400c80703102540140c02c241d842800c0c0c642c050103410b1002c0f1040c40c1c918a0084604103030301e18402c1c0a00001d0410303848002007914240c522a500f104211040e0a4980c2d40082d122000300a0b4800d2249a9400c40074030070004036060081d071302c2c141407820328070803403901d0b8584820000030903003049130528203e59584c05601c3c80d44411000001400000310a05101401d03e403000c0d24140c20440014802d0804102c28400540030030f10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 741558012 1250 741556762 741556769
    0x50071403070201022502040e120d0213090c032406050d0b03070513020a0e0a12020d02040626011109010f0f0c0b040614010f1406090d05010606080412050a0801 70
    0x415100c1e01c50510881c0603115410303041d00650082003180500181118160401610864041000c60350f0b801c2999241c0d924846007801101052142800d400100e070002c010803a903545407004d4441d2904d0b448011510340501d0f14002035580c220082e080004a0000d08282c214030b000c40001a14000d401080c500c83c0d4600c02c0f555545456040d44603032420020369007e80b01c002e01380850003214508000094004442c0b1100042070305443c2409802c0400d800025904120a0481300030056000e01221000c0303e103040743c1286da80c0d0340015144003030351610303600b00d01c2d0a51000f071141e0290151a00750350010f0350340d049020b800c110203407040e03070451100307041d03d007250500c50401c0d2404e010a0310410581100a0000c9138048204410065640d210341a1160050101020f81e43ca41d4295180c05455000c0e080d40c2c3d9040f400307480202e2074190302070525003800900500522810740c1e501400c0da0056401000458a0741c1c050104101246c0000515003c035403a003a400d00c1c60506004260b10010320 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 741559262 1250 741558012 741558047
    0x90109060806061b030c010507081509040f03030915150e01050628020309031207030305091609020d06030203070e01080d08060d08030703090c0e0709091a045007 71
    0x9001c444d1030014825a071100e83c0d4000200400c1c503112001500b01c18080310076004d00c40030500b4815446ca40310015030700454000c0f18015080a00e076400b50001c2412030019601c00250705c142c00c1c00c8036001e00070351a0380140c40b64102071141c034100e106800f251060300240d20480081c01f45404401e80c1007485580311900603911804140f440c00240d046204101e20150140103141d0115007003841c1c0802810401d1181d0b40412551780c1c0d000390b40b51512020038490180420060382041141c0254000c1c07c205184280d0000e841c07036076540000c1c41c003030f03140e4000306690900c9001005800000d01c07034007000040b203013408629843c2080000b11000701082008200300701c04030124000901ca80d0120306e0181d4040d28500301c80361180c5d8803100f05d2004503109000210003070350214419200d4060b4044442d00d1400e1900d1403003032041040003501d08200480f0b80604401014a01c4008103601d402e9041c4035140e40d043c3d40c4070301e00080302030315180d4140d40c64140e41000a00c810964024404c560080810 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 741560512 1250 741559262 741559297
    0x140a0e0613020a170408340b0618011d10060509130f0e0604060609140f0c120f0601030c030e0c0d080c011118030c0916021e0309010906080606 63
    0xf03c405583c00b007003542848003041c0d400b4040008000e4841c00802d00240007410319000c0d80d00e444417013454a0b551218440741303451003605000006441c25184c5801601c0100707042251717000d4003d000703903036142607100c170310505010508100e50b076030401c06960f0018a40009440b040d800c2000241c510701c20505824010f05044080d6286041158030104110b500001d003031001000504085984000a0340c040e00d03003a01e48840040d02152600c5090a50300c04000020840c0d0b999803512a40c0329030041400c1c0c403480c001c0081e40ca4a1000c041001d00c601d120500c2d000b15414001d000600f10782200c0c0ca0300c002d041c64001a440d0949001500d041c81c02012a064181180301e071138000014091403d1589107903007400c12004050194401030442c0c0c107d0103203002e0040c0c0c80c18003010b50300d094001a1540016a0502003981e600c0600d403904100b100d01d0049a40880380805a5240484190142c441d19000070440d00e05540e80000860010b00d440d2138070341024240303980000c4c030382d2042d502c00450f1114030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 741561762 1250 741560512 741560527
    0x3020715030f051603050f13150908070c030b01120c090e01150602010f0f051308160209070e10030606020c0d05070e04050d080c0a0207090506010c0c140a0e061302 72
    0x1e03003151900b0070a40c0018481810040d0310310061503001910b6402181c24400080e0820b1102c4e1465441020303141c008180c81c0030640c98104c8561822614110702d95104d0101c10041020040205156840790900700c0c201031840c107001c061408181c0201140d070424128281c0030a2031640d604e01901c4030340c00b002885200030800c80703004206810064190108104000a0305034041d844458011403500061011040003d0007000301c034000c42e000c00c1c003040e590300100042146040505101c03014111091102030003600014441ca0044510100042001c85000003074102501802010102400d040c401c141c00c181019488040e4010031038001c0303c900c01072030140201000000000c11144542e101c0341e0800c0d0400075150782ca110103200100e03501d00049003501b0310103802c4030560656540541513940c100884040070b40800380005041200d14114080402d078405a03c400400210a1180c840001441031040ca452164485401d41811104114680d10b4102400c1d646510466005955060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 741563012 1250 741561762 741561767
    0x120a020304050d05090d1b1a04051c050322090615120e0a02210c010c0b061e030303130302330615030f10050904050307020d06020d020f090a050102060403020715 71
    0x6c0c000c801500c8420381c2c031603841d280030b242c504640645e0305a4181c00034001c0c4d44282c490442c8540d104064101070303608058041764420100d912109441030003940e241c402c14004502441174500e400600b0300444c01d0303081010711134070f11610f001030451840c691851404480c02504c04007250015410071500c03803141e01000070b0300b8000800041d9009003415400c611101c081d8107c00d050841d06010b034030031410030108030742c002c00710f00d06100d601c8040509155241002d00c046a2194070724004425a005120280e569060000d10712030300d0342418054035902c0ba410001c1c03604c60405900a07402c2560311250f50764141c032070085259a2408450030400752580008181d0641081d90384031041c04002c03051090030354122042c48d0044a103980c1c00307071a5076110000c004000806030b5000f0015403003040700d14014200382c80c190030310b58081d00c0018204000307001540185d078880780c161115244000303905401d80c9050074003100504000e20061130f040c038080d90041e5813030030b10b13000304200e507109005402000751 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 741564262 1250 741563012 741563029
    0x6040c120b0a1203030506030f060420010513030f0b07050306030a06020304211806050a0912020d140a0c1d1314070b07050f1606030905010b03010c05120a020304050d0509 75
    0x3d140310712030614401ca050080041400ba45d41c03038030170f0040454124488400003000c6002d00c0d00283c01915814528032a200c1c450000c109482c1031050078008820303100d840c0551007008500803a00261440c6e4140342c030040001000f40a10148041441803119035100002d14030160303030f8418401a9291214244940f41414100c1001d0621010200c0f07060710300d91000480094529070415120036a440e090240c5044c050140c800b400210100c0007013004040b4010111040c60000c8c000011422640e1940501c0b180c0e101a40c40c01a403020000c141002401c01c500340062031380703019540c80149824021008510f0180c20260300748007800c403103428010014290445010300d07404582805560b00202d08040c2c20001040d101da02400340e050700d1180b00403409030180b94448803108040f9090071350540040440d84415145503580d05141803050314244100d1071200001e86605031262411120074045d000000c012207200740c014400c0c03100240740090500c401b100341e030030015249c001c00c401150052 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 741565512 1250 741564262 741564269
    0x3020c0411040e01031b0608130f1103010e0c010e06040f0306020715020a090501030f02121803042112090f03421d0a02090a0b0d1a06040c120b0a 64
    0x3d40a0000000c01602c00310007064003910440340100b6654401d1700341c0e100f4004440c500e40c44d070580300072000002c0501e404e80e00360f1482083c1d0f541c0e8032000e6601090840328900c50780e14041e4002d901500d2550307040404042c0100046400341e29080c200a0380d02c2c0042014400104003d8010600d0020000e280e8020221003a0709101192104100031340100104594880d141c040303403900d143d01502d0840c13402101d5419030181c80c400099218180c8210020803c040403011501042c00041540031490101c85406003240c0301c0e481e011541401d16880c41b00d0601045024007400e01d6007041800e004101d00c4045a810a2000c416618005c642d203440490700781840d03099000e064108107140c002400c018990f012080020060748000c0504000c924105840e5462607502c0100140014500a16440d5200701403e03000f280c80701a00010a600640840b0121400310310115588610198401c405501040c211414849440104400b800e04840c11784055052911420440400c2d180c810b00c86004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 741566762 1250 741565512 741565529
    0xe09030f130302090709030803162006150405270309040c020312060a060509040b0409390b030105100c020307141906200f1903030e060403020c041104 66
    0x101c0100d40c1d8180110409800708a10622241000c940240c1c82102e100042d41d90000780103295841d0803090243c204119141c1a003000350300c21070341c07402d00444403604554403a4000148580d04049000c07403c4580020000760003249808108824943c0e1842c1c406408030680000c45080b072a42d425080c11803003012581c40d046400e00700010700003036000006040100401140c8480c640b00c0004104400700f881c0f2419000610134070540b07182c0c1c80c003035003c50100701004000103501130306c03940c607000142c0b50784042c496203c01c4181403401c06a08699201c04004000301d00c110000e042040c800711602040c01034501521124114652160040404c2c6507065001000c4400300d582d29014001e8034142d64404500440012280140d41603440001c03d00f030751700684a01c10084040284d60582580101c03040620b845849d00c00c0359104014451186880c00904410b00c0783c006604018040da003005c00c9248095100d14108004268003180011f20300c1e000b15801324030015008030f228110700540d0400c502 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 741568012 1250 741566762 741566767
    0x40617060319050c04090c052d04020d0609090302010c12150311031509012004050901120507030f12091d04080a11120a09080a031b060e01020309010c090b0406090e09030f 75
    0x141f144003403400c4100c40301201d01c4d64491408038496140c038400c9216100981803810541c00d158602900904200000070703c0000d40c4964070403d102c00d480c2c1c1d55000b070300581d550f002c0340c10a8942c4062500c0c0d4588454005200c1c4515001c8080805201c40c400600220031030900702e181f503601803154001e80400d16800b40d0003810301e511260b008010144501e00040600328031521038070b01c00c80587d012614001d082030266031030440307028141d0f104840111894004c51a001c00002c0c001e8441e510301034040c1c401c900d1281c01c02030340504903030107030740000c00030545469100104003080c03c5807940c010752104001c1e44425248100380c17044548007601200701d0140a503d1610700f0740c00009030a03042e07107540c1d030426490f584104454441d02e1150000c0e0001b5450702c0302d054100840f81c02d040c1e00d10300c50b032000681030710000340c01400c80e002900d40301d403030341d454807840100c050b402038918010b071140b244c0d080d2400b4503010700a4400e010b1440f070201c400d0303c0507000503000c034824020748030184c1840c96101d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741569262 1250 741568012 741568031
    0x602030c1605010501050307090c09090c0e03030d060504140610111006031b0e070c120c0606060509030c041a0405040c0f0b1b061308030402130f02040617060319050c04 74
    0x5010705406d0150300e000303114014002402d1152402904098503050305c0301c407440b60400441d08054440031503402c01784141800c030158035031010401418556003061000500c60b08040802c4181c85250014800c45094070041c400389549544580000c5421424118841c800000b06281004880c003080f50f461850020300000740903050303404000d00c0c0d0b010703180c03210003548411741c0c1501d140c400c7c0ca5403000928034891442c001008941e6400488030241080a41480300b9950b40040e10081d0b00000d0019901059003d02814104005441c00d00d08540510000d900181d12444890255104a20503616800442c0900078028081406049480300600c115925039400d0038031070f0b06c481c0d1000700c807840f0b900c062540b0043c00315146000300300443e03850780c0c1c0c0d61140d141c03903155400141c0107070780c40340310b1403803c0c000340c911842418811450004050780325490100003400300781820f40381a42c2102108108460741d03802155418030040280c5004450009034213000b4a4114418512904585000b1604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 741570512 1250 741569262 741569273
    0xa0f09050d09060210090c060c03020703050102031006110d0e010302071a040501021c0c0f0c03020f0f1006080102041404180813051203190f03090f0624120602030c16 73
    0x3d440c51034003101c0074081d2100c040021600100c1010301880b015940c24046030b4412800d8000c200c0c02441203d1941e61039480302401c9074000d0b558041c612030b45540400c1110340100320040701381d403440c014103880c01d04481e0160004450100c450b0401d940003801100708600070018221a070a9088080103901e020720b400c074000d510550301c0c0c45119100094003041b008603400340e0300d842c40340c42c0d07940c00c100c0350b102d5019586552500000c40550040700003480000004001c02d003100e050090043c0502e1344c0d440c40c0c00c4101d0340c440d00041d0301a401000b091007055076001c19000114426500000c2891404030b240c6c108250420004140c1c40e00014462a078500841f001003ea81e022100705402990303490600b03580740720703c0c00912100f079644525951424001c0c49508402105401e01043d00411341c0d403040c020781c2c0e6410044912558980125014034450341c1c01c03d02d600c10262401c00454104290440100c6803040000d0802d41c0000000e60b41c006800c0a580c42000000b0030400a80c00a00d0328 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 741571762 1250 741570512 741570527
    0x150522060809010c08010b090d0f0c091404030f080408040518060406080c0f210703210801060c142104030c050f010c0609050c0604032618120c0d080a090603140a0f09050d 75
    0x1100c42d95818030b80c000e02cdc400b80d01341c041c500030355068890323005441000f6002c2d078150350000c0041e24000401d200000f01916090f042012051070640c00040380e1806508001c00c03245a60420340041d44594101880e540b128241240207000454079845031201480c50070060703204440359420140640c40d40002000185111500000040b0a1180c06c44000d007008851510003440741000203003084c082100400e0511041081300260a02a40c00141140603807407800c0c1403105441d002c0c0c1c440003d0401c00d00c0f0390b40074200b001d4501250300012103c0020002008414401d2015129507620703078400041000c00c10004508c0a0081c0c0800e44540d52030400c08058070030801c005001c656240811b54240c4100e5044400c004ca154410303540c000080300038803a12918094207001d40307200f40c0329150303580e558155030422040c2c4205000b550300c02c482e20000341001d603182e11403024103041c0200581c1e0030071941040c03030744001d511000041c2c14400700460720286c180042c0140c114080c13030843c0034074140c3c0041c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 741573012 1250 741571762 741571769
    0xa060b0a05190e09070e0316060f110a020609061c060906050405060102011509020f0c0a06020720010210020f070611030a24150522060809010c08010b090d0f0c 70
    0x200306100ba078503008161040384419118070342c064a0b03040010760715801840c1070106081d000d005c6404020603285000f41c2026250081c41c080340c4444041402140d110000c004030042c040c0186c4101b00c0c8680c0400d455000b2020305070304c00d5202081580300c031a1011031400035230240c508188041c0c0d030359807402d00040416000e0280918205000079000e94014010101000c408202c80d42d805840c2c140a08002d4000c080d003c1e40f580d030108025044aa0f0400800000740e001d002d00503075514003480c242d010b00091685c0e680826203c000d061005a030045400000341d0001c01c80940d54284d05250410310b446003c5c4000d04c200e01d04010110302190b030030003451040700031107070400980c0d035100644074a040201c0400c0c2004c44240006100c0341110000b140551091400c0031814101e000d0040c003040c003a40d14007001007030341c0c00c1c104004607544030050680001064000300002d003140140100b2491050003030184c1d0350b0b4000b81e9028541c44401801400700d42004244d8000a40ca24001d0441480c510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 741574262 1250 741573012 741573037
    0x3040b0712050c19021b060913140105210607050a0c12080912070203031c060e130210030207020f01140d111207140d0b01120c02010207201005030a060b0a05 69
    0x110944c0300d0a000090300d4001c940d600d40110940074014007048561f034040b81a80b90001c1c00f02001403050702c02c1c2c1c06108499020387e41c0081896050109008a003024000220030340c124490855891503c00300d42960808224605a55680d411410035100ba99041d80c00800741c010b0700f00c92243c0c2036840510240284080004d5490300480a0b0324400f490054107400703541034100700b100303038281d414000b41007010040800c804218290b40e540b1841c6482c40445043e01c546c41c02d0b891010071450100c86d11000d03c42d603401e01b107007004607a40106030710707a0345a150039052111800c2a180c0400c032403c107441d1400120203003070180140c0105040c03c1500501c12580c0814240c5001c034031180c0c01000d0341c00d8182c144540203400d001e480f580b480040d180d002055410700100e5008120311041d140103c044040103a0005a59100d043c82c0c220020300303c0300c1d10400c18100d42480e52545a4075901110b803000c040d03285c41a281c1c3c40d40292413000b4043d96200010b00c2d00d00103100401c8a4100001e0003c401c10308 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 741575512 1250 741574262 741574297
    0x1505060406060207180e0c0405190e0706050f031e1006020f0c0634060209091807050d140703030801050a0b070c060f0309151e1103040b0712050c 64
    0x282c1e81030741e40380713001d00408603001d541044000c02c00269a11800400c80c03100c089416a02e100c00200c0c00300c410030b880445004283d00162030700c4500c240140d0210800b40c0f001810803a2070058010b02c54051010301c5203140c4000400f2880440300c43c014201e4a818802c0b1f0a0b800d410858054802c5030f065210b01400341c09002c401d064400307800b15807620341d264007902607458410410f56440840c410703001c46003001020243d50700003c20301003d800ca0310b02d100d0320780169034103200410044c0c1024020038480304141184500385c042c00c004541c0008849007681c10741c050310a285052116142031281000c003902c00c40200005040d030001149040300c500751621891a601c500b0711030143d106580001e4500042c42c402044003510400d0000304c44c410034540010320f01c2c0c1595075421810340c848828a150f94985210180d0b0b030500d440ca02564201001c01008954030842023080c0300d01000748042c110030120360004440a000c2c1504001c0956061010030013840c1006505116801802d244841c28450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 741576762 1250 741575512 741575519
    0x5190801140603090c0d020d120f08150a06030c2a0218070912030e0303030a240302010c12110312010602010b0108041110050c070e06041b08040b0a091505060406 71
    0x40307040f40c0c002d03900c85019050b034000c810240004180751010483c2c02c402c41c500c240012030403031403c4400c00030441e95009a82008594001c001c0480179002251075801c00c0d0100b515550b494001c0022100a401e0106550810590659801940e0000704010301c00c0e40c60441c00c01000356807507211051003220841d2071401c054418a10380c62044540b81d000c94440d80301800040518400d80091a12910f070004400c1c448502281c03c41d0010b61310205000d80f1414140142d2881c0711030080c0d41a00a40e0b40402e039441e60300002d0441003440c1000c0c01d601c4400d04488940751241c02501d5035011010101e07603550a43c07404081905d1400d1003404010f5181060410341d6602c2902464015500040036400d44013104040001074540290780c08240101000300d0454203600740100d800900d06c030419500c0c01c0c03802500b0701c02602c10b02402c1070310b41c90300b410b03211482542051032160881e0304003d801c90159229008840100b2003079034058240582c0c640d04003101a02d94000320302c00d0400761000e01c6490f56 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 741578012 1250 741576762 741576769
    0x4050c0403030504030f0501060b210705030c180a12050f010f090c270c18050307062a020603040b010323060c2a150c0306030307030e010519080114 65
    0x14070300008000810400c41007012604440e000b20495019000014503d03548016019140d0b0101c0c0050000203440203813040074456002500f0303800b09803030400901d540303444035908030395210b41c3c05050b2116504000d119803940304c2d00220000303031080061620041e0b0543c10126510310f060003c42400d5802c005100b40c40c101c80d4002d41109a50101e0304941103801c0941d0100354107541d021504258100c06d0728048518814007030422400d02549507004001d40351041003414414541000307002398000b0504000790f5034801c4140c558034001f46200c211750001c081c0004036090702444040d500c0760000c0180000c0c080301d544058101c174801c1c41c024400369041100071001c890f8201034043c49812210000d2030000f5180002c000d51005403203140158030b4030008104210241c0c080139201c6602032a94040740006251b00c1c1a0010340304154a4250300d854000243c0d07134450f068001b030400100465601499008505031203d6050081015007001d10303880000344a4842440307401d07210851400f01018a06 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 741579262 1250 741578012 741578017
    0x70206040507081c0e030c18180115030b090a05070f0e07020a0b0f2a0a0315081f09120e010f03060302130b060f0a030f0b01030e031e090a1404050c 65
    0x890a184e00303c026000c041c098a161444c4103036141c15015a912000da1959002400c60340705c0340c51200302c1c850342031020400b00e582c06600a605010b030300d8129101f440c41400c0c003001c802c40b40c0c0964400c01a55803441e40da41480d00e00c440051440c421520301040140c0889464001e892220a10041c60f13543c242e002c0341c0d118003098003d0130602d55200483e50603100540125840404040501080f1480e44103524020b00d070110003074010a4042001020303107a0601441c0740300000c030000c107540079043c10780540c0c46c3c020388e001d00702e20702d9089801680000225000114a01e400811102d090414000042c00e0240b070200d115001031182c0303c1d5036480c1402489228266600940710f070507805600711205006110720461030340e01290920041701c0b00850b8000400b00e201c215500400c0009045541c84140c940000f82681854281861800254000026902e00d40202000c00c281900303c0a81c0c9000c42c8582001c05400581940300801e80345d074180000c070390000303040d103080105035903106c2d82e13803841d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 741580512 1250 741579262 741579283
    0x51002122d09120a05090405070e0a0603020306010e04051303140f0d090218041203050a05060f010f0314010f0509010803042403020904050114040b0d231507020604050708 75
    0x41d0400409500c58801c1045036224031107100700c3c0c585041c01c40344450a60000c14001c00003890004c0d4081e01c0f81418046d01d40c00010b203090072900844040001076190a103402800200b60340440002c0396603200d4130301c142c0d424401401c1004241800c07824055107403502502500422039050413596121080404c41e41c5034545510460f04140940200002034540d0102c02c1e032b41309a100c1e020b103900700b001029490059200c3c0320798607030100348800023805a510080510034114078200800416460351b10813212151400d01c0d21003606412000e00381c1c000c1144003080a080710f80c0c00e002190250b100c0c036403c41541c1080320030340b40c50b0381e892004507941e114500404a924114401c00c10f42c1d115070042d06409074605043c094100241080840c04940003688040700241070b000a10540c1c2c20a445a11428241a61001c05007107140c2c5601e0486011040001c0702940000340c450b0b600762051001c4240e1584042466005050980300296555015030301039485003d503620000d003242c80084c80f075954 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 741581762 1250 741580512 741580561
    0x30f15030d1d18060316060801030b040201120507030e280206090d0b07080a0c030506010206010605181507031704030806040903053001050d0f020f04020705100212 72
    0x441d445004200c40100011040d04400c492000320003005694102101040070700549440c161480c1c28010145040c102550908900c0f81d121420b100880c0e208000d107054940200c2c3d1118603031110300c0100c0301d0059400e44088010b10786428810903d5050b00034046841007002201c503090600c0d200540c05920030008050100d44800d000401070078824081c0400c0f900c02480100e52901c1074960214038081280c0800000707003240d0030000580340604c11910010a9132404010302d2405000103561503d044c000c42d0240207010841c030b480b003101d03013140c1202000082c100414410b81d4407242e807201c0d00080021004120702c451083c0c1070058624481b4400c64140da9803583c691507038400e000040090a20136010400204100d441ca100b1381e902c0e411a81c11000358811000441c00062804054183c028038891490103207030750f0201d0710380240e501180c0d4040300c0420a0034a40d4000a009118404005200d4044c0c0403050a850344c00e5409400a44034410700c030180c90359030b40d00f8440003034000d5009400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 741583012 1250 741581762 741581773
    0x103121701140316080c0a0e0403080a1a0a12020f04020a1205040519050a02011701050d03051c050c030a06091107030f02012417120a050f0f0f030f1503 67
    0x4800c0042c10307500714242e000e01079401100103003c00341e2059200341c104d500d0640c040c11007113030b40f406c1560510f0b00a150303c05a00d44142030950300100300030400380c141c0724515240e003844a40d581c0c055407000c04c031010082c00d6a101c0c683d01c811804000c01a00026031164000e80440c40d240d08250085440d100d03102e41da480e400c0303100307031242000416006d0700c00e40d01072142c41d847c07641004e02500c0c0081c030140918020710102c4014400104101c921410400702e00e00407800403c000e80b10003e607140c0d40c3e6494100b580e19541d20030300280248130000510040182005c0500c002c0046e418000e40c06111441001e0140301d45602040c01a5032141d00090500a810894640401d2080090904022241c400410803103100280c0609400b100100904117211000003086034051030500c41004808030f5029201411104a084140740035003684207003400000180105031a0f0001d045418078420000c040e500c422032101c20000235001190f14903419140040400c06039184008034040c0703c08024000c11 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 741584262 1250 741583012 741583019
    0xf0b10050307180e0c090403140403020603070306170106050108060d0206190504030c170d0806120d050a090e0c03270703060606110102131401091a0c06060a0b04030b06010908010c080103121701 85
    0x109c0e15081c50000c5071403210300384400b10042e030b1441c1c0154001c500695011a1150601d14a44240004100d40d4100b980c50448200003e2360001015540584116403884003142c05002080385807040300707015165441d04c618101c446681108c081c0080e00d000f1030585081c2d03a19141046904581c5c1d040041003035001710b4400c181613104003480c3d80d02c100d018000c46440c00060388801c3c034001d010340d1001e01003980450450900ca074044c110b9070040940340c070985290309007906202d00714400600340f0b4440f48010107202c0040035004002c0c6640401d200102e0720655501d04141e0020810f0b801424005250710260201c400c034140252074105c44141c1d4103035903840c0350198a001d9248910380341418040b45031000940090703400c10ba98851521a400290782d0b0701e030f07080050f042c8800280b165100340382001e001d1003040305100944041d2940003d9280d102d450b07000040ea041d500030381c0300ca2600c1d800c040c0c0240d185a80301c840581205c1c840c000c910804001e229061700c42e0302941d0500d4804090560041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 741585512 1250 741584262 741584267
    0x40318080601210602030403030f051005090c070807051b0a09020405010806010f090506070b0a050a090b0a0207170a050a140406120f0f110a0e06070f0b10050307180e0c090403 77
    0x110b646030380303100005843c0c00d0786644200a9810407a0103402003076840c19001d229440382e0040e1a0300650403c0888400d50030b040000d80341d280041c0516000c0880800e085080001c107404454440b0307003000c01c44620b107804030031989004503140d13102c80c05141c00110000e8078401030b000f502e041d5241615035141e03568580004482402c07003046d000c0100b08550000181039103404005202c03040c041d180c49641d82c9041c100c21802d94002520040c000d42c6071040b882c01143e20402c0b02600300e00500c40159035000c05003003000490070340c0b50000702810000140b0020313103a0400300405000c0ca40307881c0c602046803940c0c141c0030306020302d10450380811280c1420b5103006403240c1c01141022000c850002d10721718a003040710b007103480e55009420318a10015000d42c00507017041c0c030203810001c1111198642403a0340c3e24a2040d84036480001c01204000700402e4101d10120f402402800c409400c6900c043e644100781aa042e18440300c01c51510b20f043c040041302d0f10b020618210b81036001e0300c50351303280c0c40e1603504 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 741586762 1250 741585512 741585539
    0x110403110105040f030308040615060e0a1409040803360c0d2a080f07031a010b0d1e0e0c1008090a320a0204050a0b0a0308030702010e010204030605040318080601 71
    0xc450a035683c8070020030000ba02090b60010b00615030301c44cc5020fa00c84180320303c42c542900f0400201091038152059035589101d5180e209600031242610303a11240d5a802c3c00042e607075840110705d200ca66580b5180480b4083c9023101c5e0350043d0484070704140c1d0000f071011103070040501419210034400d0f031040c43d006600302c100c18024803640022080d582c400102d410960b40d04580d4207240c001101c10003d00c81c00d04202d1074204000c440b41605545004410111840340c10592100b0a450300340c00701d04c0c4015101c0d1444460094001030040c5120b28000641781c10840d6130580c880c11090702c103540081d104d080c0b814440d0218500400c41c0d202240c032000c03401400200d00b40c0d1000050610049c02403442500c1a44017012040100f0403860148100800d071600208019603051030328010420707035540e145041c0126504106c000741daa4445030b6049016142e50343c880501c560000500100304450f5034840b52045009944806a0403507881c401c030110f8540d40b0900e00c20b90f008000500060100710f40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 741588012 1250 741586762 741586771
    0x31303050c0304170610080f0601060e0f100305011a0405130f23100611190c05040e1b061201140316080c0a14010203070f06020409110403110105040f030308 69
    0xc0b43d0529940e041000400c100705580c00115410210034003005814411a45c0041c00035000a86012039840000c00c0c0d4a40341403186c50100584021804402e03118a6082c405040011740f00c43c00300b541113580a80504800e206130603800c240f40f00d240354412190701c1560300381c547c0100503500d2000d26108210241c190001c3c03601505070784010300031034182c00c40c0740f002206000c0384205060b841c00c0e0800c0340b5035000c1503210344144240d80c0800501d034080403400410484942c00d441040b0412030400c3c807a5001140c0055030400d14000101d100d40c0000203204c058102c00289903034103000c80302c050003a1805800340440720490080010700c52001d0b098901c10700214050300321401c03400c40017081c1a00140640c0003075015002401840242e040a0ba1b40c10040d19803d41c500010164200c0001c1d600c0c07041034405001ca00b18410fa440800c640c0750102e5000303080180003032011040d002c10300052a440b42c80125001c2c01110f0715040c20b940900305580458040501c18031029255403426900490000c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 741589262 1250 741588012 741588037
    0x150203040608060a0f0602160510050307050c070b0a03060801150b1608071b06030c09030819020f010603051c09050d1e0c0915090509060106230304030c0b01050603130305 75
    0x12030100c0c00417081180031009043c154000c0800000000341c092030740c025600228003c203a400e407155401c80c1c0020880342c00949a00e0015601c00d081c0072407909085030350f040003481000004000c440540c0c1034000c10160394001000700950300e11001d000303d0300043c034402c0805000d800c0c840d4a1500207a4105402d41c1ca002e01041458a10269190700005520214006007088002c005029155040c0b00300d10a180d01403c180d04009d0668403005441e02829184800c0400c4c2c140c141c05c02c45100b40a0621001034800080c08441c1d10380c03800329200c0d0340302c5200d4801c400d5602103211419204258490031514040d02000c841c81d00350f2507640040c040160312110202070a071050700021204050320000b049038040015190040c0fa20380d1030210100d600c48140503081c03c09001100d01e0209000f411180c1c2c45c10300461040c0071030503894100d000600001d0490002100300020702d031f04031001c60f000d603224601514680ea00c40302003000074041503503a11807128240c44064002400341d030003080d00340e0707100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 741590512 1250 741589262 741589279
    0x1080c040f0519020a3506030c22110408060a0b0307150e0d0f0609050631030903050d0810060f020309101b0f02120f0d0c020a03060501080a0c15020304060806 70
    0x241881b9400c0c40700440c0d5080c8160b9041500d4558626180458100e40c2c00c90180c1a0207903000005015010442c02001345000d00d0100030111440f0b0f944040205d401f1501d2407500d0b280c0d2884401e0f10f4420840d02d0340101410f1038581102c03032401081050640700101c4110400d0b06200344219000542e00f100c83e81c010707403005115804501001c02e400c40c583c3c443c03440072a040070180342003414202d02074845050801074a030035502d2140500340301c103051104071580505451150504489181130383e070002d0038900540d582c0744a2194802c42c214418580c603819600c82c556150400c650294500400d440103070010b001d00e80e15840d2080c8804d140d0b081c036242110700804000044000804083c100f220300301c00c0854080304600b000d0070703a107504022500141060703030203090310340386c503039403005400030402c50003410000843d550301c1a0300b000b95070804020401da40c1c5032100d42d60f584120084c01c1c1d860301c80c0040c0028188407101090500c1308060303070165041c94600807080da510400600700740d42c80341c5403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 741591762 1250 741590512 741590537
    0x2e02130504020f19091206090203010603060207050a061506120c030603060f0905010f0203130b0403020f030d0c020f060411060d1e1418060f06030f0601080c040f0519020a 75
    0x1107001420050040c4000140e0f070390134a01e160f00652608080040c00d0009003141003001c400118810740d10b03940c20400105a10b011803001900410164000030b01c0342c0c5c07000c07900c84244100007450318100762003408104441e544010b451548840213204110000351050442110f40038641c00a085000f201c3c1004141103449030b4078903040c0d07034910103003000c556a00d081c080140f00c802d00600301c1c0074210715402c40c51801c2c10a80090543c0105102070540500e1101080030940b0811000111020a005503900e880d845000c0c800039262100c503040040c130500b03005000c0c0c00b0001c40c1c4035010f141d0003094007640e0409038080c400542c00c240c010525103559015142c0c05070441030241ca0700c01f240311000080501a840703e00f03160a601030445100c1d00c0d07043d0f58028140c000000d502d070b08142850b003411030310b030394440c0080e20303203800c00c07480305260300030f8500000d01444000b441e8542c212003140e090140d07106c0721241e1409c5400403100c4001c05024001000343c0800c0c00d5000302000da50900d07081005040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 741593012 1250 741591762 741591769
    0x320103020c0c1002010510170d0f120908040e06120601030b0621030d060f0609030221100b120d201203090d090509012304150b0c2e021305 61
    0x1d220a540f0090303512031040000000302c0c1030481002d0b1035580408100d4848003021545d44030361f242085024030914940142c03849000741005114001d880000b44051081880c001c3e11a420902c5800000702c007030fa01160007440c2c04411a04801d4403403006040a80c0b031619642540440030389515040300550020701c0c0f020881e1710001e464580107038000c40d0382e41004c0c201c103012108240d03c00010300e01d04c030006020705070303011203c032040701d804a030500c0520801042115200fa61a03c507001c542c490021004072420082d0490400a541105c203003a829410f920040d41707544905080c0310004243e014080910117248411400c2a8440401c1f2110100c648454203100d03482901d1254a0307502525040e04144d078400c01403005007070b040d141c890701940351003d030183c02e0b2001c21450301c02224840c1d4660780c1d80c0783c591104d614140070290450444c2d030744450780d07002c6900c4039420030910b0040729491482a001e88401242444219559000384241d07990200029001044401c444100954000a2969 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 741594262 1250 741593012 741593029
    0x2704060b12010302030f0c090403030c1419090e010b0a0507060b030307030810050d0c14150d0f0f140106110f010c0f021c020304050d020f031204320103020c0c 70
    0x2001101c10108950541c0109840c0c003160049007002644520701c0c0c058980c4032100803d400640c182000303c0c21305a10719054a1904a401110424400102c8e6201c14603c500100707850029540d25100b14081d280d0a016085070400d02800000c8a0100f0140d60303201d00c128001c0074510300909000070031001c06070020782507078002d410980000b02000706000c00c002e60b8440000007070400b110b402c1100d0840d41d5901100f80c501d4441c1c2c0348001200240a042c944402c0b40317503a9201c803101280f96440840c0c6045c0d400510940442c880507030710305891102c408106101754202c01c421f600e281400c503813130000c0880d001c0414a827a21154000c1d4458032450903000d0013480e00d42c90850b103d2241942c0751407002031810500c0e60003030307030700d03607035041101c5012a0044100c90a0b140191134901d0b40b21102d00105101c0842050310356050320908007042e252024600142007661040750100c2c2005010381c0d5060349130100f0107442065184d003454541259070090b0300924515510105503014041914001000f03203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 741595512 1250 741594262 741594277
    0x801061b0c0b03010b09100c03080604052502031c06050d08130f0b04061713020f0409052b050a12180605040308042a05040e010b0d060b01080a022704060b 68
    0x100f00806c5188180c0390051a03101150b880d480c1a4404206540f401010b010011f00114000c503a62000314982c43d6540c1c110340f1968440d21400203403100500c400071740d03070750000604125040c14100c6961013446a4080c0c070701102d40090455031144015100c1035107c2c2d1140ea800824083e03080000981e03080f4204058008200c0d2841803a01e41b490840080c10180080d030080309211202401c000d1003010541c0c45043c041d80503a02d1585880b02000440c000346000100542140304541c26482d0011515001c0780700000b84008810702208031280981d25801280e5006000c01c401c0701d40c40b403c50b0b100c1e900c0311941d8107103c0744141d48445107032034a0b07080742d009450960000c1d4039001004140400c03003d082c480d003a8a1820340200701140040c034041100280210340c8966140e035501440860250000d183c1008010904515200c10707142184c000d0031500c1c0d60360f010032115400039980b1081842514201a6480300341c4540c3d021003a0004620b050107450254420350b140e2020843d080701c071b0090b0150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 741596762 1250 741595512 741595529
    0xc0c0a140d020d14270406031b050d1a07021204060302071a0c07060b0609030105180106090203070905130e0105011707080105150132070b070801061b0c0b0301 70
    0x7003284450083c1003103110b54400c010702c41118807407110402c1d088201c0340443c1c0c806002c0c10880903c00c0c195440c00d2501000140d0142c00c204020050140c4940d5030401c81d90941045061907980300c00344508000114006040741c08241d41c4490844004020190b001d0100d2050301c02c0989400f03d40750480c0c0041d00800d0010381e000c510082000b005000c1c2031010038207403d00c181e040c42c080c00c0311180d610882c8002011a500c0e24802c110742d4981c14260303035144a0003002480b50340390145a5242820000c0e0301070400d50b00302100092421191f1003103e0041d001c560b40c02200350b00702418415000c401540103e0404c0c0e0724087c00000171801e10415002c0c21200700c9600813003003200c88142c0b1b410603640004030705034900010711400d404c0c017081140d4a07034800e0030b05a42207405078008505420901c0e0000043c8034a111440c180103101e1001800101c0c81150303030394000d448001040f6141f500034005d540c0402d103020010b900c1729001c03010f020b10091151009040980c0c5862003044950001c1e80207203503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 741598012 1250 741596762 741596773
    0x1009030b0a140604200d090c030308040506070509101103280e030106050a031716080a03051614180d0f020f091e1306020c0c04050105010f02060c0c0a14 67
    0x14a90020000c05400850807603080c0130340303440b0402c00c0508140f01300c03007001d145c10001a103181403940d640015507032507044007040c44403079607904001c1c041c454200c400f11014040d960000b41d1460081e416030303a003800b01070031130740d40903140140c10f582058400c0c03600d041c540300901c50014155a04602c0c0d4100c10042d82d107146550410460140040c1000d084941c402e13410001c0910007910f52140c0c0108036038202c1d070805000710031180341008600c20390304070702c4203039600d0000801801040d80051a903041a540d0421040d0f40320701e68079643c80c9020304540c00090500103c018400325000250000210f0300d41d019a03030307445102c00101400b10602c0c044030b401207185407a070294640000742040c10501030740c0190a40ca801c21400fa0000d1412800c0a0101945404150894845441a00d034240d000a0455803045001c100640d10107200030403e104500340f20001c0703019440340030441c000381d1450b002070400e40c03652080d1540680120f410440c00344600c1c881140400d45503051134841c803e00c40060f11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 741599262 1250 741598012 741598031
    0x101209030201150602010207030e0d0318082107080a030f0605030a030207050a15021c0e31060501050f280804030f020703020604140102010b09151804020f1009030b0a 73
    0x1860204654404c006592041c403444020035000b880840c02d520044606c04448801c9182c2a14184100004c1c0109100380366008156048001655900090102352400d04621401c600c103545104082000300303034032800c0c850b95402c503000e608800c8401031440e1010483e0b90700c850201e840c0c1090380900342c006911010003040305040400c2840003400303c5410b8a000c00980302000b0b940c0d50000e50b580c846001500703048a46651041100600c0c6000041014060a50001c8074001d2143c0c0200d110b0388050b5003270000010543c40d0702c200c50071140103855450602c405200030710841d800200e010300e000342145040010716001012140703170104094039280c003981000d04009081c042000e03000f0040d50311001c02030015980741001d44040b150007041e091240004c0e00c004070f01401595080c0d039040b0f21040306104050b070b17041040c02d00904040d02d003918040030f03110080392680000e840c040d4000400034400e21040c14808024101c080060800000403680d950310070350042030880342d01036550703926032100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 741600512 1250 741599262 741599291
    0x12010f050906040c050118080717100516050f0409020d02070b0a090804030825200f0904020906180403050904060b03160302030703110c0106060305010605040311101209030201 77
    0x80d504440c0850040841c0d14281d55040c08910b4136024940c1403141c100610005c444141500e4400303408250700355003840d40e4030440f0a00c41195883d003040c4502481001104104807849040c1c450110305c540180d820039007017025211540000c4040d40080c008000100d40701039180010a0781c8104003800603501c0c50281811700e04950f015081750703285414000c1c81c83c040b0342400d080e501a217422074500d82e520000d41241d4003444012032107600040101011040c180900e00d81c21180d030000e110040d0103541c20900810120a040d43c400c2c6610100900105000d0304114000603170244c0054a450010182d003802403210950464084001450000b00c2c0c2c4640d0074580101c100506c1000a0740781542044112030010040d800c849008050340800001c032030a1180d0803060301404201086640c580305003020a018103864081c0c107010906000001410340d11600072281140c3d004528010790440c040c0411140600440c5c0c00010080a450140b24001c564490004018800e4000251101c15901070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 741601762 1250 741600512 741600521
    0xb010302090916030b0a0209030109122316030903020603040b041a0601020a0308071404030c090e0624180c130e061e13050103200301020f04090207030e12010f 70
    0xb10091a0402516000d02d0303410801d103103060b240d0106150300955100e1464100901a9599107a855800c0583c200e050009000070852600440d580703400e4090002102c144e4265140140001301110801c09420108100d00000780ea9500c2860820811a541c0c0c000846941040d54152590460b0000b070200304240724004400d90f603c0d81143e6000c0d8a02500086e40395104048060141314400000405c142e06c1443d0802c0b000c5800030a0544403a2139040034021814140202040c103450440b240d120500b000070218800c8080e030304410042d1200c0006420302d510207400254100480c460342c9150a5070003001c1c1d620844580e503800b0346500d0b80003414400010b080c2e00500302c0112382c50a01006441d59046881c02c40100e2060035008040000800c000c010840d082c40c0c0b00ca46000d002000b00b08018070885064501e0002411801c61480c003054200e2089000c031015220301004100459803954002e0680b09001e4201b411680341c4200200381803c01031001c41086035500d95003024180f08903c207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 741603012 1250 741601762 741601771
    0x609070f0e0117100f2c191e08071104060515070f02030a050a170f0d0e0102070c0b19091503021c02040f32010e0d0206070b01030209 59
    0x1040e940040c6081609070310308106000b02268001055500618a48100a80b251031410b110701041641061a032100043ca2249106ea1088415141d1080300854801c1610011003d21024102840c141000d4440c0c1c0185540c0c01c032038161303403811446c1244900500070b119a074010488559556801d117010007681c0190320b10207100d0b41c50020140b0903911400320100034404006985942c8404a013010313070010104c0340000f503140c41a8003201042210100e0389070021481006100c60004c91002c181495000d12043e1510401082c017251022905540045585440400c001440d00080e034990582d503040701e412240303400c1c3c1c0000303039110355800d0346803c0c0d4006a100c2c80c005a4290074030200c0080c000921000008154020400d2140b0318062030410412202c05c050441d502c07581c0340101107041180e072140704100b014844c80300410341903100c441c0c2038204111808018901031440107440304010b044189070400103d8098200686a0070010200303940a1180003040d0740c9035104200c443c140041 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 741604262 1250 741603012 741603029
    0x30c0f0b040b161d061606061d040510090c180e0d020a030207050409020a0b070f0308220303050c0d0f0219021612030509040507030b03010b0f150705030f0408060907 73
    0x60f00f0505a580710300c640034030b45202010480b03c021110001032550180c3c1c4420481240f1a140140800a440d0700560864016001c0c0102828040800003004401140c0c00380c4980c004e00820001d16115500110200b40f03d0f01d00c59400e40d80320441485003c1c04002c00c0d0381c08580c0c902716040381c17260400030500850003520007090310181381d540080d15445144203d81c020740d00c400306c2c0011076039400c0000000d41660010192240000e082c5405c60490482d000d501141d030000105444034031006180203501e04c012140502d403045660100d009120081ca046080300040c0929029090072b4000c054145164240258407088020040c2c5001d01c0032010210070b55100000d024140f1000301041800c50b10308042d94058803000d820150b80a01c030743c8440a6005107048104000690541e2104041202c00d030001c01000230300e4018807111050120450354030444943c44209040c40080003011424400c0c41581e042c0002c140d801006034010360441020754120004114016404000b220b008001e103c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 741605512 1250 741604262 741604291
    0xb09040624110d020a0b04050c0411180f1503060103090b09030a020c03070e040b07030e15070201050a27020d060237050d022503020d110c1309030c0f0b040b 69
    0x3c1c28060740e102c130b541000400b41b0426800003024014180300c080c02e09440034100b840800041c2d4662081940704c803d406595a940600700880c60403c840a282c0003280541000c202004209080d900c54200400c1581010f44900070031001410405d22107010b5440c103001542c5401e84502c001c1c1c00c000c180150b80d4043d41c000c1108100c0c18064035986d54206400c61740040c210345800d002200600003106100f01c0ca4868011074102449103845060310843e8944d00070003040e1620520003007952038508108216030000800d546040030341e0315001000c0e1340f00920040742c1c3c40d00c907035a21090b80c01c10f02c000c40300098011003640302d0900b445e0303944440040d42c880c040000c000d0420041d04030b0080c40c1916040315404180b84903030650030142c80c0402e460354901204c2c0e2410614000395240c2c81c0d035600741c1c0080c0a021710307164030f031800180b03020803020001e06088030800b900500380b00612030000164200b1480e0200400418580e440e400c0d0280c4c02111943c0d910b1800f030401321650300c0003520910038426030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 741606762 1250 741605512 741605533
    0x3010e121903092018010b0301060912020f01050d18140601050105070b040b07050408030d060f05043e040609090c0518010f0302040807091d0a0305040b0904062411 72
    0x90510445138140041c801c0308030444001c049000d1000c00a18190a22444800401c3c0ca40020b4051030480b00c056940082650b21145844280a0081402900100685a00a000c1d80600701134400800c480200080b0722601c4c800010040060440982c0c85030340035031316465840f00520042c0d01601d401c1c20010329026950b901c85d022208010001b42c0a044440b01248409101d5000ca400420080c42102e4036a00801c181c03200070580d038803405140d660000000143c0f801e2a00070900c01c2c0c0440900c000c2d0503400c5084130310251003210102403441d040c4140c10440052204060700c060020f66035140d00fa182840c0c440760484001e00d2544c01840801d101000003a41030034101c1024140c28a030071502c0e284401400c0d03003c0c4c042c2e030708440d2441c021f00d6000f10760348030b16a202000d481d0380008108038540131901d030181c03295592500540050002c0105000004503079004126408001d400080e020340e48410b02d03d1201c120076034440507a41c00706501d01000760b00052080b40c203820710029045c0c400d00d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 741608012 1250 741606762 741606773
    0x92d0118021c0302030909070201053403050612011e050f0f011232120c06010621050106030207020111010605060306010e010c050f0a02010207080c0306060d0203010e12190309 77
    0x1c5060b0150001e40c031540c00300351007070050780c49200c0c1c06041d1701c81c03504061078068040d04048511000b0424054074486c0c15018407160408840034409101c18012070784074040b07000d010002e2032550000401203035600da03010240309021501181075814100c00740c0d41030300c4606036031000e407040c907000203a402440713441000d40c01003604613150940c00008500b403603d080c1c412299140718400c1c070228910307400c440f440076006080c410b21b80004c0641e8820171040801700b080340620004195250312480040c01131500480602081349a01002c13040440440040c0d0703400d0b00c000b60400c7c40084e0700030440204558001c400f04500080c044024001e203410840498524000106a141081413042900700d440c0d0003101007406144e080421b1710b000e40705900c04141d4488010742c04a00611807540c1c000348100000c2030b02c0910b44030003005001651949420884100c01030031003030f80e055689005510300c1080c100480c0c00003406a40301e103900d45130f402e06220220210485040e05140c2840c800000150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 741609262 1250 741608012 741608029
    0x20070b1e091f0f14090705120c0405090f030c010f0c03020717030604060306021b0f070602070311040608030d0b1c020a0911071502070b1003020612092d011802 70
    0x14182d80500d03a18000340c5840c1009000c4408500c1c404074074140380c0c42200b10100d22082e208080030402c03641095503070b9007806181011000c540034a500403180100152405070005900321660a00702c5250034035031120b941c00d40c0d102d591800c01d42e80d9540e00c10011113502e4060707039940e80900d05046090004a0711089002003c030342e001800341c031000002401d607540d02d038071030300c0a1900f048045495544c0510800300300703858100c0c080c0300751168801c00c17950424009034450540d0706030341c082d1440511b123503102a00c1400d0348102590290715041e000c14011401c002800c03001d002e50102055540c5911309100707940c5241d1480304500d01d44001d064001d6102d81d01c03140d0844040c0d41000486c0085000071010314059039070010145110709600089841498014110036801102182d203540c40e00d054a40c042c1c480c0c0e01c40203400400501540070074660368104641c1c03180c1883c059940b40c14255a80c01c0c040c1c0d080648031820704c8103000e03411500c200d0074800c5400e04011220111340008060300040c1858 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 741610512 1250 741609262 741609283
    0x10222081c02070b040905150a030c0b070807140c0109091a19150c0303050901090b160e04060602160b0c07051009080a140606090f0a20070b1e09 64
    0xd00e500c0803004800d80b003080150002c00d05410b1aa89442c1c66003440e1025000546804140440594000500d8074050250004580d40141070980051910f254102e242d04503041c03e079100001030000101140d00704084d03e14000d40c10019088103c034250000d04000c5140c0c01200d0200d10b0325200804800c2c84040c00d072641d0008680d900c10005d400d60100e4020706d416040201000d00c10360103503100c41e4100c0e840340c199a1180e2400d200755900d89440d00c0c00c0300d601002c0903104065280100d0460808920401440b0b04141741030300840490b0f03000300d4282d446551051006030b10180d03640d9410032001000a004d800f52a034583e103001d601243c21584e66425000e441d10890078001203c40030ba000740415402099240180d402c100341c00d00340500349002c2c410340b142560142e40000703610351409100d21446100780c0c08064000e629010420001401e904e818a00c0d0140304d445500126002040070388256031140322500c10340c2c0703448806499221f42103000303038030591020400e002c034042d40130503005400e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 741611762 1250 741610512 741610543
    0x9030901032a08090d0c03020703060b01050d050c04080f2103070c2103060b0304030f080c0705010608010c1e0203030703050c040506071202010510051e0312030901022208 75
    0x10420b01425900c4030548020781002d1010085009803201c039000182d00c0e1107a40a0401d85821807006031041c1d61400160100a0042c0c00001080c40000c0080d4054130310711006140c05800d000e070210080085920544903c180440c01090822600208210801e44000b0480192000080d8a04200d91445058006100004001c00020401481014540903498200e88010b84100d20001a5000b1151041c500c00000741404004140c242401e000c5030b0280d41d05944404011000550450341d103540681580084502000002c020400c00d00424000e071518400016641c440c0c19006411a84c032800340019804000b41c4040e2025004016030360b00651a05002c44c080c1d03101c8665258074400c03a0441e549c01240814284184801c0b915a0142820b031a00200816200c20407900401c040501c25181e0020b030540700d40c50342c40034050300c1e00d1500e080070341100c480018120304c0821a030070407070f10404140c1d408641481c54080241250b40049403440300b40c1c3c115420450459107072990403001400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 741613012 1250 741611762 741611771
    0xe0f090403112406010801060813020a0803220e0f0a050702011b08160923040f1d010b040c1704030c05070f06020606030610050d0c050d11040c02060903090103 70
    0x285400b0701c0c02c1050703001c50a0b050740c0300d10804903820515a000812102032001c1504006407055009109440c141c500b203440d01c44140d510028400e0401c0c84882c403c80c1c00030034000001074965020005800c1502c0b071420359804044080540f40700038603503070303000c1c00080d12400107201020b5005200c641d0000c20f81000801c035a03031444400e82c05401c09048000d40d0f4076100d41030341212640300800c030340030381204040590660300e42c403012140c0c54900e000c0c40501c41e00943c4081c41c00d104850041c1404031001c2c0002c00c96142e08a44c601c1100c0d4a144007030035804003a403c08810070002c1c8948404d06004031000c010705160712000410565414140c55503000381d80d800701d8103240c0540418001d461344401104d16441d1210303540c015501c060700c1444058030500e00800e10914003c198188115100070415038480c2c03418080007901d80002c2c07000d031500c0c6091000801c490702d5540500c04603d001d0200030700c0385a9450140030440d4a0144d01100b15006001800000342c80401118103403c424030780441c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 741614262 1250 741613012 741613021
    0x62310050f0c07171902212d10090b01050105030a090f080903070f3b04051b030c0114130801020304060603030201060501050a05030f1003021c0c060e0f09 68
    0x901034895007941c98000e20407600000b40450942c010054501c01c01350648910b130914950304440d9540c5c0c0d50000b907202c45004e40d100884036070111100320303041d080d004440c07110070400f030b08044a0024003034100e4040b40411001000010800501d250a180761408000064a5464005000c4010301465041010000100c0d10711600e40c2c0040c240280c02c80130309818441545412000d5034405401107009004254002900d4512a0042e008854420000c844a500b0500b0801550f0001380c1581d107d030030b00d41800c134000f00080040148901c0c030420003401c1c007010102081e203a0780f95100c4003070b1007070f80003581145a6076404900c640d003c41000304030503120300306440b0082c100c17101904031500350743c400b10400c028084250008022a40642c008004503034891004480c036208141c140130200b0410000306000000d910f150070703030202c00881c0f80c0001c1600e0743e00007905091000030440f51140c1707820050b02408405420301004004a04001d02c1c05010b10b000f0030840015544514402c89240000a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 741615512 1250 741614262 741614287
    0x412050f090310090c0503010614060304020102070f080a0501050c2d0d02070b011e05400903020709180b060d0b0c0d0f02070b1815090106231005 64
    0x72960700c040142a61451402c1c44a41d41c02480c110700c0540b1180c4c03030031030006100c1c14103209134400e49040308484a26010742500b4401141e0003d0002c0341144a8242d00003220510b9080c007a000c2c0c484400501034500321810000c0c00d6501c007030490900caa80c2042030614000034416500e21841009100801d0840e099003191200d00804100f402203e0001070b1200811604800c4c4a0588040f681d0f07806440624031141d40c070a882030700840e90020312103142801168600550301e070504500898603150455428604a0906005580c904105031100141c40030960107218040140050b010100034100b00ba651007188003003c860080e0410400f03802048032501c031101100807907a084803800d1268142800e2603030403544032045180c48186810f90101c1020400d00843d0f0300c0981103144080c090300c803003802001c10100c50012090612800203062040341d0340724101da1041600f07500000e81c242c508407e002c0c2c110030401368180c2c2240603800c1c0c1540c9a440404d0070620070f1321850455210325645454 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 741616762 1250 741615512 741615517
    0x190b090f0403030e030309031b070303080c13081f0b0d0209180102040b040605040e0f0f160e0d050d23040312050d1107061a0307060807051611090f0412050f 69
    0x18034580d804000108111440c0010003450b1912800718044c0405440e03241460701d4074104d020007800500b1079000b0071545d001725405080b40fc560038180760251a65207244a00d003142030302c00c043c2c0c0c40d10203028184a9542c1071181e00c00501c0150b428540c600a15800100b100f100140480580690180c0c10003d59109505580282481c503280c2030f592a12030402a20b01c0c0c02c0f503c5440f44181d4a48005202c8001c0b14011a0242c1002d410814040e00d50200c00c00c481841000c18104025100c0d000d84855902ca401d1803003018000d001034030b0700c50003044004000c80f60300b44583c00142c5011500007800c0d800c0ba0226401c498024080070f110041904040340d80307200d4139514101550a01500a0904070208020180c640c0720b10070803c0303a8014519107242e00e403100ba40c1d0641c10f4000420070490a4010400c19600080601c0c2051130051000c0f511504140542000d039089440e04030604c3d11810010325a07508207610f144213040615140e51442d10101000808108106000c50120300c0701e801d0303505 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 741618012 1250 741616762 741616781
    0x12050c09090103140610080703020609060d0f06320402030a0b061318060803090d0204150815150915010905130c020714010203040b1b0a0803190b090f040303 69
    0x4041d00756900c0c10704120141841000212a00030032000c10100b0310601c46010440e10487c028041c0c451464080003403035000000031075000081084208060700481c41011700c11110301c0000903005041c06040440500b400e11071994680503a00111942001f44d0030a00b140a0116030143c2c2e81e80d9041c2ea0a0080c0282e0011284c00100215045a000290384001c0e01540d03a41c1e60344c962201e841451034019641c6e2445000402c2e00200222406420b003800e40c03609150024002065640d515070361801c0c128801d03400036201e07801900300d4101d043c1d103421030035401130800541504186042d40002c3c00190000d480c0ba000307040031200c00303070b041d90160280b10006e10f0003c04003000481906c007880050320784030030b0100050042c00030204e0529102910a007600034180d00440c01e05003001030281c5030b41c0c441040c07007501c100c220041000c15181000b264100c244203030082078590800424556501584040b007121190401c45510090744845017a00d80c000c05c0c210300380290b522582015401040c0c03401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 741619262 1250 741618012 741618019
    0x7020303091f0807170103020126070f021005010311090a0f0f0204031a07091a0f190801090603120c030e030f1b06070c050907110609010603031b0312050c09 69
    0x41150001c0050100c86180040c803d4445144640d99200c040780e40655028480304000131950043c005540709001c102940c03250f00d503841550420960031b11001c0c00003201d5600c0002d55488040b2909a4103007c01c05034609200e07070070301c119415a5110244001d40248035401a8a803d0000f440000d481c1c0288051030400c1e20100402000b582c0404044d6019010907034505140d01120724005801401480c49488150349a407803880c00d1440104501c5117030714940741891014000ca032681403815005166004400100d01e00401c40c0440141145d0700581c082200985011020400720b50800816001c0d910307245007490a843d02840c0c19122214440040d64061181c43e21112081d9030009858074038141c600d59441c920b400103130030000d5510504200611a280c0f200d000c10450070150314540d0403200030300740000f02401e01d040e554a400c0b012500501969156882001410b80006100f203450300c03002040d2001c003d00e9103024282a544000503024140e8603000110204040810b4820a00b40107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 741620512 1250 741619262 741619279
    0x3030304110613030b180615120a020306010f0801050612030f070c090e01050105041b1b05030c06070216090e031206420301080706140403062901030e10020702030309 73
    0x341020f011141044900306416846ca9242c83e18503500000c40c2446241410440c40346081808240a144003000c440704015100780314034a00103076000e10080b4080c065115116010380d2a00906a003592400b51201d8000c8a900180c3c0b11001000b000f222544070300500340996070491490140404400d5510605e01039150502088003400103401881c1211012034060004c608078080440c2c0d44045100080c1c0030038844840303044d040103d064501c003442d004c0c2d030a03a4140074501c1c45150500b03034100c40c0400140c10030380c00100c083c516000c2140240102000402c9211400c2010b246d0324030070740d49441208110040054a2580c0e50410318451004400e10038140c070110400004a41242d1040d601071a800013100034040040700c41a00c1c102c0710740c600203040312898040141d0312000204d02000603540d0403c40480070540c54020f0064138402c4010452541d8030800959600103035500c2c15504142c01c001207119100000110504110b1500c0801680c907001c5100207071443c0315035900550802c1d8403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 741621762 1250 741620512 741620519
    0x3120216091d01020901200c1915020706051b07170d0230030702120304030801152c1f0503240105040e130c03151a03030304110613 58
    0x2030b044519104941c0e1601240801d8407084079081c0d002d03400707003180001ca0900c2089400c03e010300035030228884140c2a00c442074070b1840480c0000e5501e5140a85c7d0b040c1462040007a10524825101e101e081407001c0c06200e814103a00a0841c410798400d240030611010004500c044240725a200502009001c01181b18403c101c207500c400c1c443c8904070141c001c100c06503102c5840310b0200c03030080b081280e0241d902280880364865a4001a1601c1c08601c1a030b12445103040a450096000d1b900035201d401a540c0750484801d60b11440145030400c000703820112000824190000d4240741000000301c040206450010a01203d100d409116110890258864600703410600541c0100d4000c00d1040a07285000072402d008911485031900040303080000b0001905040c0a9035006040c43c00c030f042c00040d05403200085044c00da00700741c0307100180380c24400c62250305100e446c0240d5403140300c2460230350740100000c2e100e010040c8041c0c01c80340c01003040c1d00f00e51f40b4502128810703400a41c0c40b840d49907c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 741623012 1250 741621762 741621779
    0x1f02010e07030507180b060406050f04171006080a0317070e09270304210c052e170c0304140d051c090803071103160807050601090908030103120216 65
    0xc4c2c51041e8440c0b20300410030fa07030391101d6600032070522000c00f400c401d107400d01c0d042c0f0445865002c0e5503c500f00c82c00c01d00002c1440c0301d0a200c0b28456541880040c4402c200d001d02010807200716901110f01a0f0160a11400003a00710742810071803000401d04c00e485954810f001c3e2091304140c0c01095100e10540201304010fa4034810040c4c00000038555a00403440e40c004143d542d2089000b60701e0b00b049412390f001d46102c2c411aa85070540c0c440d0120f00385c40d0784d0395004240080c0300b40c00ba0301580d40e44c1c034a044c2170f4803a01040b1031403c0341d81498003075a84c000303071500d40410700c00152040050301400400502488800005c43d46c00d005184200d445d0388058110040c2503130002c16180032114840c0da640545031503540035102889411000c0303070749151100c200944080c1d481010f0100030740810b120450700196006001c0740000d000b6007103aa550101c03860003a08000050300700040d51842c100103407003c55a10426a810340f07a1000c0d890180040b1800140d00c0c00400d00350310120005500c0d0040391721170 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 741624262 1250 741623012 741623023
    0x90703060510121107020310021804020406110c090c09010507061112040b07140a0804060f0e0c09010e010806011205030403020a0b04030302011a03210702030604030e03060108010b1f02010e070305 86
    0x1031900360204601c00c1d241d00913070f204d4403c5000c080e42c10780c4440000145100e166008008410100ca5070003440c03601346010a00341d821076485180881c1113030400c014101c50512818160352812603031894240342c203000140050051941d0326040141c00f0078a2010441c090b4407600d0b442c025a24000c2e2100b0400d402901e000d0011034040310346a1121022941d1280130318030400c03000402c0c40f4001d090104c1c5020403030b07078840c0040c400d40781191520300c409800203882c070810001c550f50f280507201c15441c0000788244540107a10024012103408010080081c0108582d41507491480d03412401c0f10690500c80d03c0d5006540000e0350000a070580014000195001401100d02c00c0d0024800007030680c0340070103420283c1a01580640202d00300a10b0b4940760f2003c100d0b020307a840d01d00e5040076515008645003181c125070881c0480e6071901d5044241c60104501030040c85a14004c1c0595800003000c18942c05058200304040b85c20b41007440d003624006c2d0801c550014880003100d02155aa090032980c13007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 741625512 1250 741624262 741624287
    0x20a020a1a041203091a060117070504170f06010e06180f15011b110a03080d02030618010b07022412150f1f030612060b0102100911090703060510 64
    0x503c004020511110b00a014040000e43c0040a81003000b0401c907811b030582c0c000a020a040140451903049080b041c003071354070b00400c020384e40c4645507404c05a0b8000000c149030304078041d5601100d141000c070100000e10314191101383c500b003503803038541380003280303100c408958000c1c1d118170b84c10100400084c0c02254541700310b040721075149400718040700654007030b4007640d541160740c5148070310b807000304405040120060001410f0881070650b2a01c41650302e03040380c840105840e8000048c880d007864103042001d03000c90441c00800b850b516150700c07146507124106000307004200050990b07144070305050b40c4808040380b8854a07695555031140003204003108480310a102101c1200c0d14803641084440d0001c0070303d02810741c140581c8800c1c03440c510031200b00507140c100b40d10350f040482d82200e40d5000c450300034420b00d00410841043c000281c200f100080e0030920303042c1341000c4140841d0095041e000b00c6030b0140c417003034902e40b240c0d401180905a203030005504030303054142000350f40740c0c01058100c0c00f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 741626762 1250 741625512 741625523
    0x10020d080109050103050604141c03150509160f0e0d06050703110c030a051c06150201050a0b1c0510051e011211011b020a0314060f0c0a03020a020a1a04 67
    0x20380e88408115044a400307005c00f40c1103900c1500050001088000c903582101d8414080750700845803500c0c0d4107080c1c1950410000044e8503032011544102d81c403800040541401c0350313190890320380131240100b040c611307071110b60400c180d1000000350309000e066044144070000d00324180c01c40380c900701000078000a0b00c180340083c1c90103100c403210701821019540c4621683c00030b58a0041d1100d821035254220500e06020002c114101006c08840b5200342c80007401091010034a00720f80710b00103402c4030001800142114103003201d4144503601c91250b510301001303001c60100d494440b410018a07006440c20412a11403401091003002c2c0b101003900000514a55210002a82c840c0d01c040024001540014070f080501d405920041d8003c1d4030400110414652080025505400013143c18030154415210a402050b00351003a0034140509903104001c0405a800c07400c0c0440988628480c080c0803401301070380482c9200ca0940f092001c200300a81002030302214003600038603000201015182244d1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 741628012 1250 741626762 741626777
    0x11406030f0106030308060f130905011b0f0c020d08120705030a0c05070203060606030c0f030f0a0c1d010503150a03080d14131b0506160b01170a1104060510020d 71
    0x146140c14000d40003601d515a40c6c1c103000307031502e106100d810601d05e0742859000b41d0384000c0d186c3c9042540310308030030240980300214403031020340740281c020410307042d00d0020050903860705000701da049205129080e90548000e950082c09040140043c001c07401c46144025611051020041d070180140d406002200310401a03d17900c0303542520f140c49400ca000717400d0342001d40020b07002e14100b005154003c0003684458500745a5030b205200d00c0d4400c4460340c21080d200c0c0148880c40f041d40c030a80d2220401d41c201115414401d1507003104d14050f003aa002e042001c0040010540c030710150000d19421000750061442399100d140c00c2d8503d401c4240301d080c80358034110800c031007429000c03031140c0a040402ca82890840c0c1c2501c0f442e048161060420701c3c00203105030300140380c0e2251402008400780c14075141c030480c041c0c1d1405400f041c1c4180c0c0f1407503c00b16014a80303400c05801040d00c1c1000b42d4001c6400c0029411400403c010f0300c60355008a43c412001c945450702d082d00459103003400b80300d81c2c0d100ea8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 741629262 1250 741628012 741628033
    0xb12010903080907241404030501020d110c0307060c120908030406110f1e250606050f010e0f1906020607020c040917070c030816020a0902161b030501140603 69
    0x160b803029217104d81440d00d4900803580901040307840c2131a2542041e0f20701074080001e0000f10380d149902540c4126407a07940041d02000703406591048200095036441c0080c42c208443c0030b0541d40703010301a0041c04032a07640160710a180d0040e0403071202c80f040c501d01844030196600744107050f034008940c142d81070740c18600e10007000003400d8101d85480000c117200c1c900300784400d080d00300a10411340112a0103803042090340700142d03108043c0781200c40e11043d00d400c46a01032030080250398803584800d002d80000290045240e03000034100d05140030540700186540c01c8e038800a01540c03900310107000455040f85021441310b80c08214203204050a80840d01c44031212000d1104031012107a000c2e000800014800c000c084c0d20304010440180110505140507450742c450507260b0303000c245403e0503480030820744011401d2900c00b00c0000d2800502c02c5061070703222014100d02c0c2c6000200145001000e4051700040b00100002002843d0424002c20059090051500e00c1c52016640d03140b00307204490303450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 741630512 1250 741629262 741629281
    0x70603110306032d030f03010303030b031b0607020a150509090106020d0c0305181e040f0515060306011b06021209031309050907170a1e0f080703030b1201090308 71
    0xc1c0d024140260003401800f407800040360400c0c0109000314021408185401c0c00142c080025203444002d0000e455541d526514000c1c0c129925038042c00e01940000301c10071010000359102c100310b0402a1500c2c6e542d104244001000c5400030381060640403008501500e085032310001070121306505860070803040e42c07075000599489109244000010fa02406008000f912a10290001c8041288400c94015200b00050040e180340b91b0410303484403490007030301200c0c41c2900810340c180000010400c06030502003207092780d88014101c01170140c9400804540e503a4231810340300c82d80a04161056000341c106240210203540214588001030074110302003140c00001100b1280c80c3c3d1498201d003040301d0301d0300b44214007400e0028480750050091440020b010300441240181c40c0061402600b090070140c580059460900e084e40101b03040d1010201000404071941c0501c22034121840c1350305d604103898110702524452028982109034100300403d18001500712002240c461b4031804441c0d41c402000c17 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 741631762 1250 741630512 741630517
    0x906021224011202070b070e0306070905061801020f07030609020a0906181d150412020109020a0605030a060308070b040c0603020313021e042a0f08040201030f1b0207060311 76
    0xe41c40c40c62220195a08550b005800b0041070f0b48040c803000d428a1056140e80c04151801c9582c5d0b030200d01d030442c10341901d18040c0503883d071001c0c143c10028025420000452940e0040a800c10860200f400d840d20b2240c0c02000314801441c240001c031001d658803841c001c1c019000c0c0000490040380205000306a1070940c0c0680000e03683d03020b4129040300c44140003603003d081120201c0071225024250790340702d140240440000220440401d2690342494904542d20001d000d52150840e49400b07461401a55144407040c00c491a91604603182e40715451440c00810150b400244088000100369040000bd14038041c4650700882d010303204290344600a81c10380c801100c0c4c203046000046074610044c0f500100c0329039000601e600f40441003181c0c01c0428100e4011903016060b03910810720341543c2903c810648840c0121610b400860b001d402d031809400a2005000241071540340d41500c4071440e139951100107080f01c1825004910002400069203440150040e540002c0c02c0100544040c0b609404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 741633012 1250 741631762 741631801
    0x10b030d12020d110a26010308030c030405010e031602103b150c06090a02011218020a060f0905042306010c08030108160e040c141309060212 62
    0xa0303a40554100c1e9104400950041d01c0380c200c01990f80d074004020b060b40030058501c5190075240d5648003a0b482c00510146010b243c01014051340c0c1600500015661800b540d81119010703c01c980c4984a80c039140c0d001d451140405d40c1d07a440045807072020a40d070300e402c0d5240d65000b625004080002000115100c8c0d201d114032100801081044031110742144074854851282e4880e6026892000030028020907000c07148241c0c07035000480ca07080804014815240c0016800008002c000d4240c3e0018200d00e800d4011002503a50780c0c0d40b04d000303808019140c1140340e030740200214280c50715464003414006021400200082840e00c0c0814181004d01c00e10100140d4420a81e0701400c01c00801030741e504008202d9410490710010b0710b000107036450b0295010704218406089440300400c150714424070503900006050701010300780710108006d85040d5064800c120311040300d101480000c19181c00090001a82c0d203031800788514107001d15075010307018480d4444071a82494440c51000000d100c203041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 741634262 1250 741633012 741633017
    0xc0d0501170c060a0c05010f0e070609121b0e071d060f04030206131e0806161d03071206051b12011e0e04030807020f0706020705130609050c040602010b030d 69
    0x342c00c07411803419070301030014281e2600d49481d07085a1581e985080d919483e00d01e03034881c0d403188401c103a900701c00d10903100640028508a40c040d441c00c1c290300c0d03168400c4040030b4265213408140c00310f4200c04601901c00b91031000c0007182d40c0c0c02d055400a0113050000300343c144488003114046880e261200031542c1c1c5004042d885800c090030340d005c10100340c1c001c00344403042107544000000e500400051880d1818040e540300e895441c98410814284400200041c0b076a1081000030418160000300e00402040004c3e0001409800100420701e44405074111400c0903c0c550021410406a60030203803251719030700443c21100c0e60000d4400918000c04400b40e280600c12030040c05010080c10400014840f51244101c0e0569511500345030084265002e4001031034437820000c1240d0100103c1c42d89611400013030401901d4108003d494172180e0050910a510080240588a0312500064003030030720340c4010401030401c083d20340c010303600a00c01c040140d42005410fa00600d804509400d201c1d440c4c4c3c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 741635512 1250 741634262 741634273
    0x703050a0513121b060809120d2007052e18140c3609010b0607110f3a06020406020a03020712260712200105040f0f14060c0d050117 58
    0x814101c1059003250b80303e60b9280380e07900540e0a620150403040040790140e500f49a42c0c07102a420201e041070134443c035010880103615012081e01243c40c16540640c0c25140737000900c0c400b00c907540301d8004603000008e0884544652040c0300c04002103860038414004640c5c5180b0341d603400c82084c15404409941401245100c80c551842000d18281d059024030403800015424000100090036504601402d4410130301206402440b81070458a2094207241100c0408218180008124040c11681580078040030142026003540a01c801000301c4141d02640664440c2d8035050700950b1944105401ea00510400070005003152501c0c00c0ba59045400c040801c46080c0d4038000c02200c2c40e800407940000c00740410000c030129200400c81c0c00d00007000c0e61041a460200c19040f075100e60045c1c0040004d03403405003400300040b0201606402164851480c0e650729801c0d040c0300070704508002c54603c2e640181420840040149030043c100001c522204000030f9072aa0102010368107250050045580700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 741636762 1250 741635512 741635533
    0x8010302030307030804031404150f0219060c030b060d0e150f07030902010c0f0b09070602010e100c09030b0a020703180608060d0203030d020408010219050703050a0513121b060809 79
    0x2440170158442c1c024185010040400440400d02c0e5000341d10080c50505121381307003c9225480031400c0400303029880100b0492100030780c051100205010000c000750750f2404000409401390704107680d044401001541c580e028050800003804860703019801c04c2c021010143c0311086c04104960244055010b04501035035181780c264000d10f907861003030f4140000c450110000030085c01040541d50320a4a62540e0360410300c0707429141910310341010081da4104030b8258441c40c000640f4502e601e4010801085548001c0c900340d0710500e144c1c1000d0300c145c4411007005140c91403a0000d041c00362113959103401030001c146071850900c1c00c9020f01000515981c0c0403c800340f4000310200f103150300044c1582d03d051190b00f0030b40700702d80c4182d011640366500425000740414140903641000f199a05100b0f01d0b107060340c3c0c1c0061032407103198a5013061000c0486c0c0c0e80c00024044400202038141c028000000d881541052107c2820700d101132903086d40b113410041030092184803018054030702e0710000d200d810031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 741638012 1250 741636762 741636767
    0x706020a110a120b06030307020d050102120c0f180d020a0e04050c040614040507120509070806100e011505040b0403062a0f0c2a030510020a0c140f0a030809010c0801030203030703 79
    0x18050905c6034544070a001c69000b41e80c4003006461070510a200050340c44800e204055440f000043c402c1c41c8000007400446c4885030401c084501052000890b215810004400a80c03407036809100a0b420045802c4003060301081130310002d010f0740c0240103c40c04060031000f00300a840c0d03607025003c07000f05070799072552107070070302d03411058101d01541005c0085208003e0800111082100c40c440703250701210041040c1c00c01401019049100d2243c0078a5460408a206581c61018460700000941c4640c907039012510030000d48020301100085181d80d2903480c1000009840422900034100214038011022000000058078079450107132905411580000c80c2580c000e28040390554600307200b1102c81d540400518140000001107103119035510f07045041c07061800d03045965414119104201041441d5001502c01e490143d0200d100c40614605118160034142051030542032849001044020907412508941c03144042d100208403005018104032003021007172002a40581040282c1c001092 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 741639262 1250 741638012 741638033
    0x1060f0501112a13050c04140a030c080114070c17030c04030807050f061609050d0204091a060123071b0314031312050d1d030706020a110a12 62
    0xa000e003d461003608940303c215502c55104a41e211550207a42031200c030b51910901000103042c9203d000c0240d07207000c1049034124842d0b802a115140c0b4a001c40998940e1046d4800c2e01441c4c1c001d0320700503840c2c0d48100f200d0203480400700590003c40f0242c009902140708189103401c464008015248160442d41440d02951000d4902d0031001c20030000840426402801000000d2060004050103100070800ca801c0c04030160240569841d0344212586d40355100148000761207088850144040103480081c00500d00c41100905144500302d010080d80c50340b41c2d40c140305010a8884000e1000d80210000c50203404403408242e0040600110001c40c0320f040b29000513204c0b0410340000745403079884040c0c001e03c98000c005100c0d0300c00100c1e2400c820b80300380f40c48002c04805030180341c1c640480d03454139140c200c0c06000d50b040050b44850700b404040e031321340d4401c0101c4003c1c0941d001c0c242c803070b000207446d030300300d0b10080e26024446201030545051642c00c18045840340814034a15021541d5103410301d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 741640512 1250 741639262 741639287
    0x60d0c090503010c0e0406050108090d05090402120406050403080c04060f030203091908130e0103031407050c102607020c222d060620120d06031401060f0501 69
    0x8200c019010800740c03070912590140c0c1d400e030340300c40d0703803442d00c41040005941864010504001c0420309006101c100084c50070b140c0041e031b04180f51640f02220200e4008d0144c964211170f1020351b4001d01c01032001541c040f5025501a540d01112035031820f45048840c4214800c000c00a0b40540c01541624425400346400c6240c201c280da4081e4030b982c2d104d10324040d045809803040a00041e81d2140c0302076143c0c0700b100600366803507143c0c025071450320041d00c0041d11f80030a2803026400a64401001000c3c01207031030855006098002d02d020094008106041c02604000807000200100b00ca08111a600317522401680d8001c0030b220460b003041c0a1842100d6100c0141110307200c558941005007030241802854161070340310990340b0b20120740614042e017500c60341e400c2c925201c0c0070710110307500c01d521042d5040d543c08000c2c070301240d8030b1606160404940068040e542c006ca4428903041581d044081260700034001c00301e00d9102d584485003211114801d90110031803010701042035500130482d594a1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 741641762 1250 741640512 741640517
    0xb100207060c0c121a010f0321120504060518010603020a03140f0106060f090512060a0b0a0503031c0b18040f14010e150a0b0a03080309031b16050609060d0c 69
    0x182eaa942008046418000e030417680b21910000c1030300e6042c0142401401000a84040da8282c1d00c0e54442100700d00b45000b541d0482e000740482d0141d0107001d5401c14a070341143c20003c100c42e1603d030402e10011304050721010301c0a20f5009810691090500403142134a800900c031303054903440d40c0d0f02c00c0390b200c01203107100440380590a03401c1c5d01e01c003003032050b40e0080406072981850b80078100310083c656921500264400d0075070148200340e42c040014044c1e03018002d0080002c100040340c0024241000903400070741e25200000f146c0a6007000d0000d0365004940c005420312039030740100100040f90ba10740701259646000d42001801003178a18004030a014001c61802c000710444a94090030b40d4458544011164803800556200040780c0f40c62590060307078818104081310f074403000103a26100c0342c8000b0f0049400803011900c0518107004450301c0da000e02280c562400d0368809102e40750001a12812000044050002540c0c1401e204880c0c0c2240b000f842c2c1450091440301160040010b901c4036401c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 741643012 1250 741641762 741641783
    0x2805042612124201090617060103050a0e1603110f01020a1e170909180c0d050f06040c08160312120b030706031a0d0203030f1608070807060b100207060c 67
    0x81c154952031081c1d5a0440408080d414143c060014101506551000342001501c0014254113940204c05d0b64200c1003d10b400705080c4c603610b010344060a041c207801003942c01081c50f07516131080080160f000300d034421200d4400708500941002030941d0740c40d8600d4056044202040c000031003800045419560320380c04100710f16840d441d0540c5246040041c4425034034005290b01240c5801c401e0340b41d0010341c20320181215140c03640b01d681ca03101e0101846000e8100c01d00500c08014080c405051002c418804552152505080600b0144800d11552680e0f0299515000001005480040569422096003090348604000c00c40301c0b000003024800081e40d41351509006980e0a00040c0014010ba540100d2001c04c8005424103e15180e882140b04114400c0c1d03030b20050301c0c04810f46406041030300740c507519498014443c00396443c051000a0a407140080c40300c1c20440002d0243c58014010501001406205024004a106044452009a88016000c00c801441103400d800e44601c030703525400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 741644262 1250 741643012 741643081
    0x503030a350f040b0a0b01140a0215070504031a0103240209100e04060501020c10140c030301030302100e150f09070306020d0204051203280504261212 66
    0x81d6104015152100c00154500c144824001c0442001d0f4001301403080c05c1040c080070100180907104a1500c01d040c800c008a01c00f4581c40c004e000e60f0550398940b00300c4110a24020800515941c8140022180070341c02450900d4095000c1181c41d05995002c196060781c0d46040e031001c0b1094003000d1512090319002c2040303180c0c68582410040f01841c01e522000f01c801160020002610900d41089045500c951282e5160b5031f00c98517441641025403e24a15082c190b131240584e5114501240c031035071000200020802d50300051076400700c680031804010700902c080d150740e11081d07810094001d00407130102054400b44003010450300046000c040350720141d030f0f03942c44c581070b80c20060050a0341d90340030408004608109004408011000d8040c51030940903445c01c03014945c0540150200c0848080e901d0551800f42040300e0143c15107034088140701d0b40500f2040b41d01e1110003156051401101d40341c05c030000000050394002c414840b000001640d41c1d424080f02d401c8407140e000d0b0180403142c80c42 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 741645512 1250 741644262 741644357
    0x3601180c292a010605040b10050405060d02090904030c03030617060a0b030705130504110f0108152209050d090f05090a020f070f030906020c060412210e010201060503030a 75
    0x1503000d141030b4030010901519107810002203c0811b000c86024646d1032540e20141c0d0b600404a40c1035482c1140c2a81c1c0304c0000b140644000d00403904075541015401e0140805d1542105000c5011403082c0d5007031004940324000404a042140800700309a80a40301041c905a00c0390462403001d071000d000c82e0421652040011403411001100c518034564810a2001380185091143c14500d030680d80803c18440000008020400c002d01c4107100c42c0014501d4900d0303940e05800d0052a84c1d401b01c411540039048040d0800070315540748221005e114601c13080ca012401820640e01700c800d80010307250240d10b01028000755120090000709190b41c201301c0907900790051000b800800b402103104100450b40703850090f201590940040302954030849104096503146000c96055940300e0000c524411002d1138060620440541e0b260b1058514926a000c5a030b4803c462500e6490240e0090240a6603142456200c0c4140d40c1d546002501c440317015130951401d51806101446800380f00145150031440f46c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 741646762 1250 741645512 741645577
    0x3040203160902070312020301150c17070303050f0603150a0e07081903020f011109060c0a0b070206160c0203031b10020d0606030c083601180c29 64
    0x10b482e800e81c0820310600307050388040105130414828004514650401f20b8140040991803104010001c4d4110100c08002d404060406441000d0002c5900d40000740b8014003c0c00e02141e1485101000f00001612460005480c3c04060070b103800f076441549071150441d015215148000e0610710a0a070002150881040500e05840120421281c46425458003d04145200e80f035a10540c0c1404c01044070316007164100c072143c0384102d80996550011030003050070580d8445000d000001090104082140c0114103284684108094446606100c45059074025840840650160b205200220391500c5070115043ca0224a07404c60b180c140458030640c042c5e03440303103581e42d00c0941c41d10800c2094903050301a81c044290030742480d000740d150000c038620b06981d480c4c18a01210200c50010fa641800f25406082040c0e6050020b011148040e9400103104600c403c0c11030f10f980581c00c00080900d8000070b003102c141d442d495115100c44440c1481041900078291038001301e11418101d0f40600c000c100f8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 741648012 1250 741646762 741646769
    0xa02130626090c0a0e012706051c02040b060f030f2a0c070f031e020105040909050114131a0411120f16140603040f050a05060f16140304020316 63
    0x3094140403c5044c8841140294004900380c0480c10040c400b00c441d10019103078103444803181040c0c21000201031030140c04154009500a99130107518a51004609080d1800310700079581442a000e8000600038248180c07030321084034070f0080c0003040c00c20042048458001c400c0c1c80181540e2420b44035203c02044025032242144440094083d000a40611056002304644e2488072201803454031654402c0ca41200c1e5880703034050301d80008045a008000341c4001d07201ca50b8082001c00381501d00395008042084e450343d54041c8030780002d50610f40101c104c1c21200e61100503025064450780c0e524005500c041c10450310904030340f90381e00e260386035424182c035080030190003080c00d9582010b841d814003009a40260400c0c5841c1000e005445201c2c070380c070030f164a00740d514681c2c030780d20b0f400d0072010300440c900000c106004000c0303408240070001500b44d015444003448076031541ca0300c1036500b406064003c1c0902c040760307100e030040c030100c129030001e958018005811303a04170f400350a41c2c0300341e076089940 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 741649262 1250 741648012 741648031
    0x4020d14060a0e1b0904150c030c0e060f090603040302010612030504060e0d122f0304060807050301141c12110c060310090504080705150f0a02130626 66
    0x1010481e22500c5401a03c10000800000d4040211100d00e03035120220048410f82c050102880820100200700c3c00e03030190034100313210422048480000040c01b0b030101f040d200c4009406003140466034074102049490210542c140a4a0000e0580070f010307203500028015001c2d03558440002680702040380c103034009648603aaa0030313074680c00c0950140183c035596100300d014404031444c0300002651420011074a10340c40c01c2c40411000070000011881c000040010502d5444c0151146541c0b0000060410b0319000c2e22a80060780d280b680c1107075a408240700b1400701e2004140c00c441e01d414030150a158241c4180041d400501e0384d40c99580e03e000c4014042d000240384c184250b0021071040c441400c0c0705800320b441c541340d42440c030225103410b0301a000d01e100c0e55541c1e0002c9010085c0d80002c841030540c3c03002c1618440300314980010200c030012518085100202000514040364520032512113036031081204400b207040210840c2e407282812120134101c500e2504144c202046000c69910aa0008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 741650512 1250 741649262 741649273
    0x612162a3905151602040216140d1418041a0402160b06040b010206042d03080106020d0f021c0e13020c011103010609030312021215030d1404060804020d14 68
    0x181401a04218900a0b243e104020711880081001d000942601a6012100940c0300e01c5803102c9400038241c118001001c0d10103035603c000752540d01080f501d00b25440360b10389135124400522903428901c0340e028405070451150410758564506680b1854520844503070100b8003840b4175003c90100e0f44000c03040004401129086801c00100c1e10009603c818262414000c1c4e925050000c0d646282c050310040c00100b04654107003000151178543c55541a03d000300e00c0c500a410305020301000c00a00800f40180510408111004d006007240780071030420707138014102c102000b4015100440c0d00f0075040104040701981d074055a4510444055045103040016607915100c07204500311150f000102c20802d5040c001004040d4024035510b08aa81506203202083c210780d0b8000000d11640015105d00e04010303003400000e02410301c080d130a07840241c00302c504141e0140d0040d6010000b00d400403c50340e01c204014018503125405564202d03201800c12489500039507030b81407000701c00c2c1c1d00d04005540013 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 741651762 1250 741650512 741650519
    0x120304030c060e0102090607080d0f09140d08060109170a0c17191a0a02190f0e0d0c05011107080a03021624030b0612162a39 55
    0x10303c01c0005074820322000b1854000114086070711070041c83e030081c2488402040361003850000b50006000741d00c50080822020441e45040d150f042060b0844607000e00c20308c5c01318907590f4058401036000341c0c030584403e00d00303c0c50401c10780c90000c14005003841902500503280c0000b6001c2a051020348000280f803140740041402c0c007840e201d5000541201080411480000b20307880744803000600343c0804031440c1c590348075102e96010340304401003a2102c1c04244580040c2d1a4024009000c11260360f0b1034500410003001040b0080c003103217a001d001c2d0f0421103010032031503001d5901c401c6c8030450f110503500f04030360341c4044500b44000c901e02500541c0140082081180f45c126250016101d46408040b18180c2a002d1701c090b4101d44001200341651085100255910030041d15514103541c40c0c0040c041c64807540050100e102400c00c440800c400f41c4565076071050307400000d8003601c00300d182440c3e080d0441e1910950b44214480e00d603101d421003244181c42c1c1c031200c440c0700b03258070581080d111003614 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 741653012 1250 741651762 741651773
    0x170f091506060a080601090b03040501050708060d021f120908132c0a1d1005070903030c0b040c1e050a0e01210212030d050406060806040203031b120304030c 69
    0x100200c204441552004104840da509000d5a005500601d8400b61540c2e0300d50059a107000c1d1904146d007801008010041001015040f81e846901503545404550300c444060008001d07508100030350010001841c6410820b01d01880a00c510031403501c0c00c0ea41c601c50030103e089800c0b1903415a0070400004403040702c26a801c0094008042c8011001d40305c50215064200030100d044444d0302c5141d0f504080391041e91150045c0e00c41c4015a00c0c2c0c001c030912129640d554801540d440720995034101000210420f000b0341e00ca400701ca0700340e100d5090545a55550703504003080108222805001c141c804a200d200ca1403600c00c02c155200c0c000b200250428080002807003203944020311581c0d0450052101248043c02c83c5200304421800d141c103040d0503c0020a041900c8990f40005d1201103031030904410103400c858040c6006030401c212094450500d10345407901118041e405034410070004489003101502c9500c00c184484c250b40320401110911800c56006440c154006502c6080c000107001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 741654262 1250 741653012 741653023
    0x1e050c18011d19020d1506020a020f0a0b070201080c1b0d080a0627060b0d0f060b070203030f0a051207110f010e06060f04021e0705190803040b0601170f09 68
    0x20410b1030107005a01e808806a0b01d00c071242022101c040ba00401c4500455003550003084020b10541d4202c041141c480d40c00035610000706405900c10003101e0140403ca042a41000043c0d0700c1a003091440c0641e20340055900c00c1c000b0f800c800f040c41c0d0400600b40e8064801041c00d14000155014060506880c50010b00c3d05201a11030100c0901d010b202304400c0d200c292904050b0131312182c1d14142c0b5000e1041080c01840c0c581d2080c420804005800c10b00541540e100c14210320500401f00092500e410680b111401060002034156008225000c501000b0f00d000e00141250351401a14040304400c05146003c41554001c0203d40d410380c84000240c401d000410240d19480c000308000d00980030215910007015005c180524480d015005880c0c50703640494001d06112144080c0a94038201900915404104161401d001d18090140900d00c041c81044803e5000400e9500b1078469440308480341c50b018229074140302c4550140d011400750700d13100f14802d5500590680d100c0c58480801c60518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 741655512 1250 741654262 741654299
    0x9030905090f250507030c0f051c0201060801020f0301050402071e0305070308070e0d030f0c1a1e161808010c11010e070f03150e0303150a0b071e050c1801 68
    0x3c07040300c4110003c1c95408801d0b1800f07280c0514201c00300d429182410b001004548a0207031450080e041a0040a200801101c0c40e060b4a80e000b0050075130381708952801c034002e035500040301900810040282e49010f8016144040c05036031107000c0000d18901c9001031000b080e5040740421008102c080a064120003a01d42c00351444c105028401c01c0c8400103010403400800007420701c40c4a2040d100e0300c501c07541d4640303502548691100c240001d40240810700321030491b6a0340308010a4a1a42c50301e4000000150185c02101442c00341e8125030102500e00c5059071b5a62074030000f42d6000040c0c014405d0094040c140641e881e0002c40c501d0030b0310702c0790030346a9050300307181564400042003080c01405000710041fa074010003001c022005507034202018103d850002c45041c0301c04424030000b030002d207903d0256140d049a0080c0e0056071400b6607000c9011b0b80304050b10850200411840345920000301100c0548204203442d060824400024145080115403007590444400184006004034000042e070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 741656762 1250 741655512 741655561
    0x3070b0411060c030a030914010c0e0307080d080c0901020c0604030305120a0b22150e09010c171609091a030f06090a03051b0304030602030f0a05070f0309030905090f 73
    0x2c00b90405015503503889060941806c2583c1c8514910038414400a008003039103c20009000a0020050041003610060240341c0301e800307007505c006030101d00010518896605a00c0382c0e03c1c0356540d45120005504082100760541c011142c2a4002c1c1d035512004001541c4a40c880307544442e44020a45109803004100003911844e000e400f40d0150b0710f2026042c0c020b44003c0d01807811060b07100020000d005800c400d40006480c149010a01144014015200710f1841000700118454044216080141c20094100d00c00c0003e0100d240031f068100f10390080070035400c0015044da5a0217008045030104119510742e0b00e14502c060180d86800d00c0440f0101c1907103002060542007515587d030301c80c850305a0040030f000001803154071200e100200a0310601405040d0f0b5113aa603030303081540280d8000c1f1002000010f0b02000145140c6080c4982030003000707243e40303900c64450141015401020519410b60070b005003210300041f55030b203c1548600c284c00061224030130f424400300e02c004100c101d030f010161 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 741658012 1250 741656762 741656767
    0x8011b180302032e0c20060114060706150f05040c032313051c110a030e010809010b090405100510140609060c010e06010609061103180f0303070b041106 67
    0x96903001400c0d06180130030039082d603200d144400b01c1000c20340d680b042007089a41094003a00081d5049111858840e001081c80c203c4d020903161455101c400034080e201c401c3d00c084040101600f041c5000d8400c1c075105070740024081074007540440e00c1ca1401d0388440c5216030081030a010500b481e004071180c0140a0806110313a140071040101d002e400103100c0000245080c0001d024400c0d500300009446401c402940d41c0001109103c156014050b11042e010440300092104031040008881503c590140d8a1084211220f001101c0700400a001d104856481324180305c3c039070380c039580c069000e64407441c01000d04803681410340040d07506c010a1004012155042040034107903800100641d03032411940300e69290228000580c0368090403007681039561820b9a40000342c040040c420341690b0140c1c503242d814a40e2954125030786448260880250782041c000c0d00e4011124901258900314000c081c14401c05000340400c3c5550042d403030550f0301908100c20302c400c1c4201064452514107090300d943e813 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 741659262 1250 741658012 741658019
    0x3040609020a0f061b031e02100b0a03030f0804081b1c0809060c070c090501090e010f0e15040203011407020d031b1b060603171803030304020a120c08011b18 69
    0x4000d01c205480302c41c07902c5c28900e2984209442800c0c1e02c9441616130401c030152441c00c0c0c0d4020350756180300e013680c002a80345c4807a0015501d09520514101c83d8196101c06940c0c40070101217812601c050b0007140e50050900030000d0841003510100e00091910008010004040c02103664011051818205002c000d0052150701e900101d0303060380c0304400301c1e0035030741c0c1c0e24203031400c42ca5901e070962096680ca440c24002142403100c5420104144921500a00083d02841d080a080320f6100c0b00c5a041e9a00c00d081c0d010640c11100c0c4425401400100002443c0102840b80c48071400c0469a040040e004101c1091500c0d03094450346407040036209544170300b00c0c4210700203441110a06460300442c0110041d010400000f50030ac3c00246620000c40200c800d41c200c000200e640001c00b4900240506400402080c1000000d4920070798004004091151620814510b00c1d00100302c01d8540000015012407442d909016a00c5003c0100222075071030654240020181481350080c6030140da01210200b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 741660512 1250 741659262 741659267
    0x150b0f0903060a050f06100507080414030c09070e120109050607030c022803110f01060602010b010e1806100908010e030304030e0f0a0b1804060305070f0b040e0c0702010c050303040609020a0f06 85
    0x1720750041c426960360b05050740c90030054400703009903140100b0782c0d0400100410a040451403a00c085003081d000c6442071606c810401070300640868120b400548400c3c4000d0541c034019160001c10003a62000207592a00385e00e45a00b002821511040480d84850050003800e604010b8039400350800c0755102076500c88401c0d440412140e982c400b400704413102d1007414802c86c040c89011321180c1017000802140e903030740b4400303070190421400031408101c40b42d21400b114101020552a81003000744682125a0703024200042114660041d01c03c20400c070b5001302d5003007024030444003400d100d00c0085440e460070746001080304603c1560140105a0300060601540710b5440c4901554144140c207500d80b00103071340103201c48034800b6500380d115080c04400020300201080b04020388056110340a1019206d240310700c030521a5200b1000303401200e4000506440d0010042c0c03080300c7c41403500b103e04401540302d031407954205a60582e0303c596a004408114034110300d60100524002890303000503071610710003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 741661762 1250 741660512 741660541
    0x1e02040b07261207171e0903040513020a0203070c0905040219030b060d02040b030a1a01080a0f08030402130f020307030f1104060e030709020318070b040b0409150b0f0903060a05 78
    0x50b983c800c2d120034042a490f600500c81c50491815a01c0e4400d9039142070031003c141c00243d82941c40d40d540e059004100c80c1540401101d09075000034041ea0a05984c011601d0000d520440017a01140070a120a80c00078030340e02410380052a032401d020410b4201401009030190b0f40e40340c10074003000c02ca0380420000300c4009a0552111042356810b070240c11038000b24000e07080b0700105c039a00d40900307920002041540ca0914000c103c00820816980e030b02d07203285075600d40510b24040c1500b040f80103c20000b598040055910a20182c4000c1034880000090810381d10359002c01743d10303140c01008100280c0c0d07040c030440040222010082c000308044e000e0001451049025600810800d141072a0054030704110040c010900a10115a6440d000c0b10044282a03010011512070084110008114103c2c1d025038041c1e8030800c10f25460b040c40e0904210050469440040da4151490f10021b40c920f0404003810691044001d40c6039102105000c00d81084001010075110030720b0941805030301e40500c03a2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 741663012 1250 741661762 741661777
    0x20f06060f1903050106270c0804080717041805060405040c0513021b03090a0b0301050907050a0c14030a1403010f06050a0c05030d0b01080702150a1e02040b0726 71
    0x206207800c2010b000001c890505240c0001e8150360034200001044130303210654810080c0f00b50b05246080381c0c1036076840203036103500c0100c500041c103603004140400d40510007489810301ca00016040034280b4118130246030042d90101d4045030341c0c111802d0300c1040b03a010b5950312803811181000640307030640d260308520768140682806034400d07620801d40c001e05941142d0800c0c60605c086440c0d902c8140245540354010f1401e02d024003900b50000600e000e081099a058400c0203080c0485990307031800854007a00888d5100701000303145020000460030302072489440c8400600599070340c603004c50024110742444507002c0d0400300100010000b20342d0131154001503800c1c07440c0090b41c0d25100c2034212003002c0c0740e440203816404002558030b40040c0b95405941c07041030a0329160804c0c0d48003103042c3e0b00d0702d12405803c00780d0a404000103801c11070359809154442480c82d104560380c60300d201c41504903001508488591103000030200309000c44600000b0403001654019014007805000495032400b4a10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 741664262 1250 741663012 741663019
    0x4171f0e070311150f0c0d02060702061f0b07030c2a0302150f2d09062b09080d05010f1a071113090201031a0a0e0a0905010516020f06060f 61
    0x110521080d681c90500031101e041c022206511500803200301061640120401b214078800e0301c0b01081c1130750020410038400d0215401a2201c0d580d07081d0700c0e0170745007081403200d000424807040c013048500424010380b101901a0340c80b5005891240b800d40441c41d8522000b00100c1d4000029100000c0c60404c0b0038196641500d00c030204520007881e074000c60252000110076000b020030700d07140c0000101104c0882190080590300300c2c00110385c154010f031042e5544150042d00402600300102601d54422040d13590142c400b8901b18900400342048034041501124114000110b9080e880c80c1da00845014010713012450b903036589071588550070000ca16041000d81c24021601c54180309511001c8450301c3c00c080c02c6e480052411071089001030413400380c100c0c0800e144c0144030140c40410070000041c41d4018201d074044a0503d0f0300700007066001000e180c0f005440b00070600004500b0301400d4092a016800822254040c100c06801c12440c0391100302c050348100b0401c40941d6a0110743c80c08108140d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 741665512 1250 741664262 741664283
    0xa0605010819150e04030c120801030c0b07050705030d0f0801140901061b060f091a060f060c0a020d1407120b01120f061e0b0604030f02040b0604171f0e0703 69
    0x15010720f4203003520b94404002266214200411b0640014044240030310800d1046000400d01100f40d810000030301000d41103020170002800030f500004010080d0364000d070b0849883c1c0da81c5200107464403c2480c0c800000505e405580d0b01460740041a26000d0030040d1507401d8441c220002141414505200718003c0088210742144945000f05100048541204040c060040c1108456020300b031082002c81d500036071182655001e00c54001d40d54000c41e80145131115a039102c4040000c2901b200c400f48007540121155100166078808000720b9981c800c1c005085840850368945050925035440090b64a6841180c60001005070548a040d90131800314182c055041f400c1c20034100840820091102c0d20b8011182c402c040900c140c06110345d1845000c1c0000014030060000310f014034031000306507040e0f1280ca20014a05a0400101d141019080314100b0f513480300280c0b07043c005264040c43e10f030040d405140c0201034001c1c0c0310000c1c0700c5480c01406400714888150741d0700c0096100180811015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 741666762 1250 741665512 741665531
    0xb03160302062a0a030203040f050102240901021c060501030c050a0e01031d0609210906030a050a022a0c040504020d1b15030f060f0807030807020307050d0302060a0605010819 77
    0x103101d00c0b0f00f4500d591011030b01002c00510740070b90b895000380601e5030032214020740041d15620014400201d07a00d08400b8048000d040002c81c0300d50100074104407425502403120108200b213292036402e09000c0c8200c00b00f400c52421001400b229903400140c82002000c01841902d1074102c0c09114854900381f83c000b0740700c0720318030314800c2c5050b90520583c45400707098140012031800082403c1d03070003e031104410415a41003c015075610034250b00c2d940000c414000100c00700507652100384c1c8846440409403801003e4403444540040c1046850407004500c2c0c86007401c2071080050019001c000c0c1c60400c140d05051700000d030700085104e8000c100b04d150310107102c03440c91544c8414001305892282285032060003c005806802c2c0310300c035900301c1c0380f41200000f5001b4400c15290100c506100141c800182191503104650b40803000a0f07826106a0200048030303141c0b01180c4a90500030340c054091030500007203c9081e100c0d99804a8100049141401211503d4901c0814180103c160020303a030b955 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 741668012 1250 741666762 741666817
    0x12090317090f0a20010203270612041103011508070303030f0e0715121a04050601123201061403090102090303032701090203030319061205030c100204060503040f110a090b0316030206 80
    0x5068400200050301d0b81030008000780c1d05400030a81c1c330210001d0103a00300c0b2030f00350300a14070248110300a5510000c41040403034069800781075440003c07540410581b1a164041e8034041c003030750084102420b600d200d01e508650161a001c450f4109030024403071100e034081a6548160701a400b075224a5840c004035040d40c1c090012400c540d00e02141c1400444410300b2203542a0035200000865103440345464401202c8403580e99050b2074072a105d8489c84001d14440380041e0b04002c00805a40d0740c200024101030b98204051485081c20790341500060300d01401030104880d6800b0100500c0e0b05010000d80140e4002c810350b90300094240c046100040c0b00b8940c0c0014290b9a0b0111040c040320020810a101c0084020044000d1000480f040d04101848450882c441c92044500091041c00458009200746200544290055850200d04088540011020480f944c40504d4680d5a1019001d02d820240541d240b04c51048440c448454516004a80340d8443d13180d002c540c100030101420100702 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 741669262 1250 741668012 741668017
    0x250c23101101150807080706050306030712170f0307030e0f100b01210207110109140f010c0602120103050709060e0f04080f1912090317090f0a200102032706 69
    0x450f40340f903d281e01569071856503210038080c050b2107414010000041442805501224041e55000c1c0042010600d0b020000d1094031203030500300d400b03210304a040c20401300600c0141003180b11101005607623041059001e0111840d036001c0c00003940092070b000181d0040801c80b41c2e000c1d15210307008183d181959004803020039810360201e0ba403c00c0446000d8054100c1c1d800750040a00c914000020304981c0001034030406820b2040d2487c030310b8000c100c141d80c5d0410300d50201c1016018108440303070710020354035034003a80c02c440b01003161a80108010002c2c40710400c0742c840100166142000210305240307000b0f480d9400102500c803c0340f0008049810040c103035049800320f854002d001c548420218000e07003001001011441c000900c4618501032103c100d01c19894140d6150300c515090402e282084480d0f490020100e451600400fa001d2980901c20712940641a11484114020b003800c000c0030790040c00c040c5003060441d80117002e5988441000c1e2440d01c0c3c042d140c3c1c8800880b0002000c005103251 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 741670512 1250 741669262 741669281
    0x717060f0a1d0601090c0305060a060f020a020a030b070806060319150806012606130f02040902041b030f0606091e0305010c030605040e0105091002250c23101101 71
    0x15200022038120b90032000c50140d05032604c2c82024032001c50100811002d41d482551000c0d8030031a42c1c00c04000322030050741c8444840d61540151280460310781c0008002c0c1d01ca50f402902c00d41c503443d04103c038541d88540119440042100d030941507081038520700300f015403100340c9002003640d2040e4448503400301084101c018401a130454000b580c4485440c80c60f000d02c600101c1040b80c4052140e02c840d800450308920074500c1b40040380600c281504c1d41502c08980010070390b0400e40e103440c0320340580c840d80150082d051802140171408104054010100c415454001d10454030340541805180d071b204149108490410401c41c1c00740c2d10007149038804613120b07440184590b20300481c01c50750b15055080714084403412138040200c4003a00c450302d42078640855841c88581c1002c0c0e80c050042c411680604040700704a510b80809024461084400421180003520b140101d200b04206031000054030368095031004051032200610080410410b83d05a00300380c00f4050310340070154414000f503010580c0d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 741671762 1250 741670512 741670541
    0xa0314040803180f070303020304050108070e01050304020f0f04050a0e2404020609061c15120c210c0902090906180a0f0f0903090e07020a080301140a12140717060f0a 73
    0x1175566407801035a26449442103d01040a5500003507980e8002c0700d0024900106071140c80c510b585a900b0804000410030443e54003000c00098042d036904d45104451141c0c00c3c01d0f800154500c000c2504900d04a60b00c001510717003603480c01c2c2c81703601d425956901c1c0c0d40291b41520b000c3cad192481d00c00040c2142c014802665000741210003c817202e034940d07402a004401e9500060603080391101e88100c00f0400e00c0c1d40140c9a010300c1c480c00c00c600c1d03a013640780111510300244152460042651054100f14181c0d0100b2074640c0c010840000901e800c2c8429904904204c0b18545080244038a0a40141c1c0c02060421110342c0d80c605000020555002050803090300082041440514a0081e00c5042c8034090070349030320303011400540094000a0180c40a54000040500f5603281000200e0502c41d07009400b41c1091000100149003600c043c1c0c161402031258643e1010a94402c2c001480c1450983c059024500000b941020814001c03d549400101e0380c0c0703204c9125541d402001001c1c01e00303410034010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 741673012 1250 741671762 741671773
    0x122304271e1a090106021902120307031701090903020604080904020d050c03040b09010b010c0f060f11191704061d0d0309060b030d14220b0a0314040803180f 69
    0x8110881c0d8010300b40058240307040300b440c1000d9000d00c1100300c000d0143c9005a03011003100014400381c1d4010000b03561006100201c000f603401a141e01b55005440124049000801c03001c0300f8650031001940907029400b81001103001e181c400a680b03c201410141182a000500800580b540d0301151050a02c10100b40000e0500314015000c980c02160296200314110f0003041b003600040c0074112007200140c1d1040075101c000e4035a0042c403009284200d92580d668044280405035030702036401c102c00012480e946510342c19905480c0003141a0b034080400410030f41001d9008948880160841d400c41030000302d524120ba10345442046600060071a807044283c1c50740040d9054100c031885a00c01c1000380700f1080008103059840e443c545403000858407011442c4140503206002e04042004a1800c0d980c0d081d520078000034116458110f5912100e000940000a40d01405041c0711816480340d030000e00d00d0700341c907009110702000e001c0000b8000754007280c09004074204005071407801c000c0300b543c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 741674262 1250 741673012 741673061
    0x5060a030902030a0b070f02070e151201110702011e020d11030918150301110307080423150708060f060a0e03031902010e060705120a020712230427 65
    0x8145c0101c0320880003942034044140300a201054040888007400d0803d038680c3c1b601c50180881d800d100700303a150050307c14045103025880c02d01403100f8040b0080340050399220107000048c14140c148511b03004511060f40e51304100c50f40040c403045003000310b160492540c0800c0c000c160452080d045070650041c03d00958408a4012409560046050241d004010b103806001d2600782c1d2056844040c070b114007800000c8000380520099a0b2240c800d0190062940070320b000c550160721a03510041041d0701c08802013900d00260901c068200f452070429090a280600006003903501745e009050044201107104505a400354010b0603480d00014180c907190b00c6003421440ca100018a1180c0056003406440c420f50a07001c200c00d8002e00c519510180740582107407000401c50710192000d00d03019420401c2a0118900341c3c00200e000085568203c0003007051802c115030140e004c46100101d2004000c10400380d0f510003081070300c41c04405a000120034900c9100e000414441b80301c010154403000c80207 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 741675512 1250 741674262 741674273
    0x90807050f01060603061505070209090f0f1c030209100c022b0b060d0803071b0b04060c08060906101101020714160e1005010818030f12091605060a030902030a 70
    0x3c038181c3d2402c0da42007020665030485100e100d05420b20032000f08408120a5000d401c00c0b904055002c0c8110084600b0303a2000003040c3d19000c1d200ca880c40a540041c030ba035044600c00d0a0280381c01140c985070550500b44030303100149201d1010910b10040c8000c010b03121085440f144002d20195800000541007d9440110682d1030345d200c890844094030a8400202a480c0030081c40900c1c0d07402104090466940c2481510140042202c00f50100012407101000420300f4000506c914400d00010420362031801018008250251800d031042c41c1e0f400c104032850711407a071020703199070003454000c4600d0365031030325140240310781000940001d034a4030310399040302c0d4002110341054500b40c50300b8a039682c0e61801d00c0d00811003900c2c5800d0a11140a003000300e580702c0d0140e10340111309800130010040700550340a2840d030003403441c228028008500200d22040ca2a6a1980f05641034007400d80000e00382e543c800401154010746101c2d11010880c20301052107a805007134025400b07000c5998039146070a00c0e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 741676762 1250 741675512 741675521
    0x30412030c090522023405031c020409020403030f1e14251b060c15050601051c0507020d0e0612190903020615060c10020f09030610050307081609090807050f01 70
    0x980038904014100d4036200305c1b031441b004411741010240d8100190805041d00305030100c2c6510401d00d400f03000100301c3c00300ca440108019803103900c601c183c000c40d03e200540701a0000d0720042290000b03500c0c150026400803071140c100715007007000301d940c0c5440181080004c0013581603207504102c0c10109800304440704042c80021f107815081c010103146e0b076440444040d00000e41c01031542195024601781e00310702e034004a41000050501a0406003003200003101400750041c681a420b8603034090288543e0107012515102e4014580803001c481850027003103903441740c034401544494003000020fa0755109015180344452800b0802d00000c886403d0080d0380d064103070703005418880580000c0d001440c045040340ca540c452000a02680392a002813140250450641030b10000c004000074140303660705022481c41940e0351960105100d0500041c14580000c50304441ca040c0c2c82540187d0002c03028002c2c090803a483e6400216250801d4500700d0124050848010810301c21907041100b10b6906422 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 741678012 1250 741676762 741676807
    0x3061201060b220812090a05041a041d1b0d050a05061006050901020c04050727031a1e13171206150a0c0812010803030412030c09052202 60
    0x400c2040c10143c189032500a282c80c400c882d0a039224400c1c045c003404850000d4200c0c10300052120340d4041e035900101d4191884504500e02c0800c0c4c818461226107841c1c07144406022940005000c0310307061250465440701e0403102d4041d07030500c5010040346640c8294405c00040d610009503280c0707150381c2c600300c2c0e90381000341c4540c58603060104e408071300c00344140c0c1540d4070a5016401024051021020b20000784005414001000b440354040030303140c81c400022140d45400c840349060f0841c0b40d030600005503200d05000d850300300103040034031a441e4207203501d40c000900807006034407064a58000c036840c6240e880c0802400c101c41c0540c40f00104003c0c1002d48100394044000007102c1d43d810040090121400b0a9080c4024040c400030400d6803250101c5521288620f003154503100c850442e00306402d000368460713280b80d800001004100590580c4900504481d814280180e030b84014000d070113100c580c090240203102c09420038925441800154051251000045645410925040d4a03041c941103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 741679262 1250 741678012 741678037
    0x20d0e150a2912160b07020316030c03120c050a06060311032d070306110915071a06180412090e0c0d150e0109020d050a09020f010503061201060b 64
    0x803007a0803a03002d00445800191480301d401c05020202e1000c100a0b0080b15290360704500c00c1e04010b20009074040d02280c040c2c080203200d95140d1040d481010728001240c01c50540c6243e0000c1c003000002c030141b8103902929800400c1d45144a5240d10454040d17018800141c01e0b0700c83d03500710000707025407544880c2c1034074001c0c084003c034001c010003030582d1303003107152880c0f4105002220782080c02c18508500d9440180f03031700151420195280c44403c2690360344804036000c5400010341599900e09040d010600000c0d90301980e0804c210b6071a82414000b0840c010002e01350201c002131503554960b61600c100d90300700b506a008070300301401d00060201600420074040f40c54400d011800019400074140708029951040d841c00724008010b41c098811031109150200b0103007c0402c0200d14200443c0c080e0021800061f201c0500d18429400c1e55000b400381c1104a2a00070841c000d0303202d8070002c00310001e007824003a580e62107840224903010341040403a000d9529284000c1808610400109180c0741d085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 741680512 1250 741679262 741679271
    0xf030a0c0509010c02190519170f0a08070804030204050406090507060201021218070803070b06130b010c0201031a030a0b0610030c0c0f021f0c030f0503060a09020d0e150a 75
    0x108001d486601c1007504050119101c184c9600c01440c00b41190881c881e00c965610200580e160b0100c0c165421246484104d16400c646c1408a240342c01e4914182c80101c0e002440710004001e450b03507c0701a03c54026020040001d0f41c40b0a2068101c101c03801141d001d802008149070506055009181121007200c860080d868009031041c814000e960100e5200e6004407000d8640c40000b089000c03030300186201500941e100001c40d12002e102802420f4040e04407004246403003001c00003205980c2075110081c03450400303800c030f540e68055151251660b080c2000610b880d13061038101001d000b2002c403140e140c030803100610204440d005e241d500624043d41c4040c0500030b94001503003540e00381c002840015016075041c41c0820358940545945a0000d0414280542000303104008103980081080c0401d0040503400300709584410010641081e9142050a60510318005816030040e071044501044c2c010403032503030711441c950003a08030040107003c07550754009014030804048070840e07003442042c2c46c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 741681762 1250 741680512 741680531
    0x1804050f0130050604150509030a050f0903070503030408010b0102060a0506030606130f0204030b070e0114030c0703020106080102030708041a0106020606010c0302010b1216092f0f0f030a 82
    0xc0c0340035030594150305000c485060318103001401e814903072129032042c880c41c06001c00100d107040c084240607601584031103980100300203030881641d00150907211142d104021040700c1980c40f60549505883c0310310350603910b1880c00c000034038041c1c854001d00d901d030000007400a9401d00561008820160030b80903190160390700e01c0108201d400440d00660107812a600049940c40d00200600f41c0380180d038070002c1d086881c14091000c030f0300160401c9485407581e500340f008568120704070614109013480e00303100881078510004554000501781103590000400c41e4400c1500039080b070405030540800031500c07441c00b2600100000c42c1034809503042202e0402686148080b43c10041c140d030100c3d0020320301919030500460f135480c4010029002c42d540d600c02c4120035690200c540451500c060000c04100d480da0410031360070f400c242e00602e0224544914082000180034106211110901030707021b60203101000e80c0006d10445030101c07200c1000248005548609502a6005000d099000c2000140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 741683012 1250 741681762 741681781
    0xe0106060e1e18090307020a09020702010905010e0f0d2604060905010c020d02331206120a153c0e0f0f060603061018020d060b180405 59
    0x11840d0450342090082c104640e80180790b003040080030401402200304943c9280c10f0180502040c0d80350501c0f6000012032205524100403114003425901c5011454041d1720f0340080c20001c1d540c4102410f001c0250303840340542c3e072100c24800005401070940045501c0a1070b1080ea074881d40500031040c03d140244003d8048942e2041c0e81c299080da440d5801c0080c24040113441c1c850b42a0000c903030041c80f201d40000141c94440940d2030081c07030501155042041e600041c4981c81c3c02c0003800300721303c009000d08002e80041c2040e054000106584106140c0110b00c2103509050800201411107604680c1c0707200400d8555011000000822070000c452600000c941c55400072104444480705944501d1480c1d50042c0b5440000c0c4056030004170344404603100081c074182120f6072085074950b0455000c02c9082d06090001d80c0d88500c0e20070000100b02e05150314bd80d580081c2101c1134650681c049040f91102d0501c0d8001c802a040c00b0004035254591079204801c01140d20744071500036410000401c100d00d8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 741684262 1250 741683012 741683027
    0xf0439051206070c17040b04122a031112060720070b04060f110d0c0c080309010c0b10051908010f0e0d050f0d050a050103120e0f01120b1002010e010606 67
    0x141d02d64880746006002d17140e05403e106981c8125500c0b00b03017000b00060840500300103000620700455544814401410401c0001c1a48082c0014440043d000c00281e036403c400e0000a5039808000f0401860034203001c1000003c42901d0342d1080e10925051060994105242c802c2844d040d000c0501a9034500e000e41e45c850040b4032984003960741c06c0c402071103100e004071a800103142c15440d02071113240445524516040c1c0c842c8600c030200c5c040c08660020b0001501108003e0010900154602080100001c103841a10324000d0002d410745d2010400900214072010020a4010300f0450307040089003d1061b2000c82e4400c3c540d0a40c42e11a084400b5040d0f8001c01c4102502c41c009000c50f0a9030010603503140c1d110440390150075200300a404850107291240740c0c051100c001000802d5819807808111030519003400c00e00f80011500088120b40c1c5101c03007003c00390404e180c00070140c00034003886406000d4103002e9541c001444d68041c3c005950550012464942100c001c0c081d0a41d1100c003a41d005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 741685512 1250 741684262 741684271
    0x90f0504020907140901030b121b030d0e100c0f05331618170606150c030306040216060c0305040510060b19170106020c030d080f0439051206 62
    0x444d062000920542c000d9111a0b40c0c4403018200502c0100007803c41400c140326002140510584031204409a041c03c0140d6048003c3e0b07402c001d484200c212002601807501e403031305c1c0005c01214807250810000002044281e89611034100c2e210f40070000d6440500c4c1e42c0040c8202c080c004c081e180c5984091072142d099000e844039019800003408403190441e485882d5081086e40d0282d0700031b0000d651307080c00a05942c00d2244030003a24007410080104009000c1845030440364900600c00f2a00c0140084203ca800c080220360050741d41d1105807400d206043c80f6000601240d1a01c08000c40c1260580c01c401d00c81ca101e80161a10301009070600001c4403074a0058510240003448034030f440f0651541580720301c050504060f29a154112072034020034000360028001600074201000050030200500e0b416900c16040c10900b40c60301c0208407890040041004c0c04070920404000700e02c440c0445c01c05804034140c854810468a90714641c10425000d2050f280140d621010260a118020074110f008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 741686762 1250 741685512 741685547
    0x6110f040b120a27050c0a03050115080d1719060603050a0e4b070807060302041206230a02070b0a0605010806010c1e061d1209060c07090f0504020907 66
    0x1152110406000801c4c420700101c2c3c0a22031403810f408203176280002c6000646c80350f400890410591802298200d0301e0f50b100ca56164404a81c00c40754a80007008038016200c0601c1c6c03403146556070450a02ea0700307071080308107171040d181000120302d150303054002c3c034070074604100184013540c40081e1803617840500b444100030804014108452054800044640507440003450544000880d03421000115104451407100e074407408040140703d00030f20009000301981c0c00c045007031030301d0300c420701d4840b80034008010a059a940500c0c0114071204501803814500c0c0604140c3c240307084002400254403000741511804c1c003880020f601c154060003498140c0d503040c1c0d10701c0c3c05600c8110040d2151114581c04031003283c1250041074128841c980c1e4402890b0044101003042e000102906140a000c0b03011520941c101e0030306084010331b0541100c5000704140e46203544d410704100598200146904200700c0a402c3c0b60200003820555081503000300c0c000c543c02511604c1e5007030103a0b40701c40c00c0740d0854035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 741688012 1250 741686762 741686801
    0xb1912110d0c06031515230309030304020111072402030c100c1704020a060c140d030203040210020604020a05011409090c0405040e031c090609021003050f06010c020d06110f040b120a 80
    0x2507803203441e44c6003000d4001c3c0c440d94607d01500a40500d81d401c00c0b01c1c0c1800540c004805c000030756910000040c4420a50005410315a040ca40d44105104442903005481d000d21200b040135107200f081150000b038048001d03603402201c40541c21000d84800b006160000702044a800000c1c0304014a0307a0007254010138a00120b440c104040d80e80404501c020303194014440c040071042482400480a0152156070040c1e4901c0d0a10400031f80c0c3e03100107a10000c55002d08200001600d1710389811007075400c00d081c404030f2050040746401e4607203c1d00c680f6030342115024090108940c2c64001900640e1421281031281c14404002c1e90303501d0040441c14551030182c81958180002142c0c40071ba07141c1e00902c00850140095004141c1e0280420700240c0060b03918002c10400e03000021855810503000d190035401c44c525500041c401042c5824060502d0380e68498081381c095001c0211690303080d07540915520350f55034011058054001ca0318118182d04d410001030501e0100b841140c400b54049031070001c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 741689262 1250 741688012 741688049
    0xb07080901152105060a0c2318030708010c020624010f180306020a26010510180e01180b09040c120f15020d0b1912110d0c060315 57
    0x4022908208500820180d9144100302107803050101600c00c4024140c00301d410f6030347c550010030510903140751101c0d11100c11a000485241d02c0700307d4011405100041c011800c4180c0003d06060081d84913840d01d600e00032481c003100b03401003440ba02c25818915980c9800020721401500c464096a06074001806160070380c0d1101c2c060790700442100c96140c020880c150f05c958074003007241c0c0080e00314804900c0700b00381c038041d0081c0c5031194124518040c2d0045002d51401c400f1403840f02e0300f05046030501488500d01648190b004185500401c00c02c0d0f6503010a59481603004084144941110b40303050500360207003844c2c2400824940610740c802041143d1601d4140d45260f4003010f031400b21219a4100b40c2c01c00442d540c45403c10584c1d45e040030040c0c0d02e1b130780c01201c070b0200d0340849040c07401100110304e008142108510244111005040d86840c4240031345041c100c0891504203450b0f00c40e0b02c8000000510081c60030704c02c144c0d60350341c030204528450035805412242c098842e400d0280c400740c040d04c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 741690512 1250 741689262 741689279
    0x603010207051c050d060603091101030c050406050d11070812090601050a1205010e0607030c090801051302060f160602070614040b0c090a03020d0b16140405091509040b0708090115 79
    0xe420100013450410f04105408809500355030441c1e002d8000a61524501c6080c000d04c500000c58504090808001c4402449006070560085104000501c4400720f000304e40215070350010604003070516241e03696504a40742854084d004416491140f031051000107000c0d050005006050b914014040c103043da103800c06d4658180ca484104039884c0d500c61040041684082200360300402541d01d001c6451003202500a01a28456100d0049607040509005606140c40ca45102c3c1d190103403a4a80d0b11440e5405a007024401d0850f41405490315010030014403900364068070896110704014003a9803142042e880c09a60300340c4020349808004030204007001d0000000340300003030000e80742c181d02994a030001207803d003031004213641a00a210420840d00091420a6024901407c00d080001d5404990583c54000c0b0701401d40a60055030101d80e0031003020100001107240244110260b261905d03203030f1102c58041e59104003151215000c40c1c209001030090407610080b06846180e56440c00d22071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 741691762 1250 741690512 741690553
    0x10807090c0e0301180201020105070509060d0c1115060405160e010e0a1e08010c0f1707020c090a0207020301060b030c1e04050a06020714010521180d09080105060301020705 76
    0x507414007040507640d101c10344083c0961110300302803074080d450525060002a0940d28018071207170811208001602041c1c0e01d000030745103400341814000410401030b03031007511950300c1200f115401e4826601402204c450000f00e25201e41c400f07075010304c10f580b034040a030103402c0e0404c0c9468002c50314500908041c1d500c03d04240c0243d110041021346002d030703625183c042e989140c1041c00301e000a15a400d00012909002d070b031047c00075520300b940319203070315401c02020b071002c2c0008500703502120008100c01c00d100700441030382580014410600c605003664810300030340c4440d00c00ca00175400d0940000b0411210b80c00da074814000d83c152940703041c4c07814840e18108141c1050360200d55009000109803070321440040c0010704031980007010708504048205241080d00314189042001c1084400104000192001d105a51103030720051151101014649502000d003415200391145c0108560360300d500000840c229040f42000304880d84401082c1800d070b1007a07540185c840e502081d03840c03810010a040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 741693012 1250 741691762 741691781
    0x10f0608092b0e0a0608010e0712050c04031109042303040915031b0810050705160302010519091128120b280203060a050301060b0703140301080709 65
    0x90b5048820441640400080c034488441410420340040d20029074008220001d011400c80380445151303d00000100890f01c1405100707000311502001c284094003402d501001e0804407042070120789009003d56502d500188030944c2d030410180d02a00403410078141140c000c60300034581d000c41484124150b014214120341003041403004001c0090001141d106404c0c45070014990120080d01d1800d00040c0010084c40c82a0941c0d00340a00f006104030020b00c9241c0262400c1010034641e81e41c4400b50b4250051202801200c045145c00108150b4107500c198495103c11204000c2070400b252071004407010307080e00819405941d0040900c40c6000c81d40b00f03410303060824021061080038690300b50101201e03444400024000701c2d03c03004002c412040d02d40c0c400d0920440c44824000202c01c64111480440c0c100c9507942e000001c100c1135110162180d000c2c0c44003034000d210a03a0344600301d11903a400701505900154081d01a50160700c0420100e80c101e6010000500013a410b108280b0010903881c40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 741694262 1250 741693012 741693031
    0x720010f051608131403190b04020d08160516060e040b240315012f0f0d110c03070f0b0d06180b01020f0d140715060e160503010f0608 59
    0x98814002074410001800c0d6403011807400c44da154039082040041c0800d07142524801d402c50518400303d240600b202d001c6880d000401015980c03118000308402c2c0c200c60348050050000000e0001c0c8030b480e4074401e82580b0b03103d4030882c1c003500d002c90100545224075000324000101e0105070190949000e400c865058a401010011060742040480301c3c6031105800301d90004002008010200000c113060036001102800d060220307003202d96000b040800d40110080912888101031103641a04100010140c1149011141c152210203005008910310540b5080c0074807541c1c912560030305010400c041124000100c0400590400f01140c0880d001051030740d5070580d0f6007a0002d01e40440b60030314094414115400201514070f1800242025119002e0b41102e6100e20303003030035206510075000070406403c801a181c1f6003045203000c03504581041841d0740d0700b504212f400b00d010904800800d010702490414102442290ba005a649000c24400d1034005402c0030010080d650080c1122503002d02181b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 741695512 1250 741694262 741694297
    0xb04060b0a170d031505090a0f05101e05010f080c270405060409081b0114090d080108010e100e251802070c03020d05031204080720010f05 61
    0x2140d070080c2194040c1800c400303800c02040c5955410300c0401d400c0341a51800344103540c00c0d42c0c110022010240308842c002c94070400001d100f1142a405003080b2807503824103004c0f41c00c10701110500440c0314003407551428800c008407100c510b4002c5480081340d8040e140c0c0ba40b0709120744816a04a40d00a040c1c0c44108410080c10140600c0e0302450606e15009841e020010340c0c0340380600088880c0186882e014070320f458001f03004192010142c0343c86114030700d410140c0640a03c041805013034203050948070070300440180200f4820106480c007120844d59a004441d0380d0725442c0a00f6204030f00f0500da1250805503903143c071042d0329008a4140d00e809011103450080344180190a0011041158032b10304811100b40041c0e8001010807008041241c81582040e80c540c4410845007094840207104501c007a03901000c004091042e9066000c0074185004189002d0524060581c081a0100c411000d140d00e400207001e45c1c0d41000aa104060392925001c17650f0507802d031060340c0145400303224000d02 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 741696762 1250 741695512 741695531
    0x80c040c0c141b0103020a200102071407030311030715111c061e0302090f060121050a0f020403051c050c010c0504050a3015020c0105040302061b070b0406 68
    0x2e03030480b54142d1111030300405408898840640d008200f50211604060040103d580b074203600030404c0d41a500d07440143c41036814030032102402840740300707801400b5040031074181c022103901042c2001280c2c0a42c4805c500b8500c00c9045a4403403140c01d00081c84085c461150384414881e0380e100c1c0500168030898540303400400d400401c107a4410046500e143c68580d103061004142d00b0180740307200c101c054990000355042d640001c84a800007003141e070040318050005203440e84251001400c141200341c40f40300c00c0d441c1da500c4001615040702e40c1040b0030b00f04440306091b200280300721021070b1b070002e014120034043c101c80e0510300e202410b0a14100042409030022500082c4034120b0315443c1a00c030540e80d1840d040900c56507148030f501a0302e9054041c00d07804c0d91b011030000b9007540c00021201d4060901c207585054007144403a0803502c00e00350320101d10881103c3c0c0540c020b0340940d0117502121150356550320141000001c0c0e8880700b000010a004070400206a9926283c1181c401c04010a1540c0f5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 741698012 1250 741696762 741696773
    0x9080d380319020d0f0602040b18040c11120f1308060103060c05270d050d090e0606070309060807090b031e15030c010c0305070530030c04061101020c0d031a0a080c040c0c 75
    0x4c01e080c1f00305041c80a06001c2e4510380b0740b0800720450003034107114010700038031620dd41c1c03201d90060011880140006588a2242c0020120b40c0e882100320307402074030240c9a182d8076644d030a00b40800c4540d5482d110205200301d00580540b120800d140c054041d16600c0d007400342c042000b038030032a01c4e0840d9001c64100d001601c2803000c08a0215503640f0742500f64600300880408100180c81603001d01d00c10000c401c080faa00456000c142c41e10ba0030440c0079900c0d40c0340d04175552041035000340e550810200500c1403810b0500041c038940303c28800030b8640c03525059001e44075100e08030441e55155000c000c107250301e035000301041c06000380242449802c0940503110603080010140f10170b4484103a403c000e10350050b02c240ea05401464490f4880d045180841c0b001e0b94510440c01407a05000ea0a0700038890900309404407a9100c50100a8510b0440c6a02000d030140030710003c010122005010504450309202d1541070455280b078004110045020040c4402400441d1a5404010511441001091 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 741699262 1250 741698012 741698017
    0x80604110d0201200105090d1d0d020607050d020c01030b33040909050303010e090307050d1b14010621020303030a0b041104060503040309050409080d380319020d0f0602040b 76
    0x80c0e0000000c51180341c01f03400a030418001140e01e40c2070040e0303240100c88005078407040020481081d01c42c0c01e070140640c000a1458090b0318001811032091072400740b0850780c0400c3c031b447c40c03a20a8070140108548101001200011115140c0c20000340410030704c00fa4048410088101250079880740c6000d40701d035a050f090780d0003244143d680b94000001008030419001c441c03580301d00380c0005107080200c01e680b010384541c000819036081180404a03590784070949400c00c0101e950102941d05981c4030038280a0203040d81e4031804503401047e04a0018612018a40c4c3c862594000c014525598a0f1003410005001952030b15421a41d1510008510584070004201400d5962506500d03842e09260080228a841d001603005904054101000807541c1e019202a03174600d8002050010001618049506040c2056418656072901c4820901c011503040003074890305505840907083c2e110b52032000003244440080d00a000c03400d02002240c1c8484940940038401c1c071002d86003c0c1e42d00000030864 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 741700512 1250 741699262 741699317
    0xc040b0711190e1e01080312271e01060f0515090a1806091e05091501140a09050c0f181504090506040c05030a090f0209040501050f01080604110d0201 66
    0x20380c010030601038500000820301c4d442c0000c89007480450741c14002071070303240c0c0150243d00400103844008a82605e0a03911006219900e40e41400050103206001c030703903690364000e18802492145050100110740600402e029104611205841c452410041c0b082007072400301015507024090100c2e1206594540d03440c00140500030790b8070640c4544d4002e0000300e0304d141c2d20000301145060b180c00c41c0540c2440e481d52020105030b01c0000c055a811401e142001c1c044204548121000310010402c607506580c0300f001340c101070300c4103545982c8800b000c10032101b0542d5440e107450340074041d004000b0b900b580100707040000c80000b00c0e000f840841c00725a00c0307815140b91110326800031400f80b010040d0351003020f500c17800840b0103010407001480007403d01e10020b840495040c1e00c07190b108080c80545589400b185074003134000e110034540307800c1042c020b08003a034814605803110350001071618000602c0c5401107401845800c40d40841c0810040206105d031001c90504c0700809100ca0071503400f007030b03042c01c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 741701762 1250 741700512 741700529
    0x5100305070813050705010c030318151d2805160302040b031522020904060c0207062610050301020c0a03020c060a080c03060f030d0f080c040b071119 66
    0x107400c041c1c0000d00b12120041590703e42c81803405450740894800038510084410a0030301040c09419400c0803805441c00580382d118000061160204001561801682c0c0d00080d40b400c114146140c41318400b00800c45e0160200c5a00541007016040c803110710b40d2481e40145c04032207919001c03640d211802c00144151900d80b929101c0010411760800d40031b034850319142100036068000d0009031079040000f01900c90700703a030f80c941400100c080c0b100c1d504c0c800e40d09400400c038507000d2510345007507005040c401101d9401401225800100980074141072070b58461900102005038800f980c1c90940428000c0261401011b4244006410b803004e1006040ba83c07800340c06489035540e14103002e4134002c07021031428041c0408000200b20550f0001402d03400c102c1c0321002035070300c1e102d000003d40340f00b1000e001316038180a0801480781498011000000c00b11311034a031983c1310340d0361a518410350b0007148280403051800700601000a1441a1822502c0300003c200c1113003411582030030700084106400c225031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 741703012 1250 741701762 741701771
    0x1d150907020f0d0309030f080601020f070801092a030615030f08090301060803040b090d1703010b120606090603040b041a190f09050c011b02041e0c020607051909051003 74
    0x2080b40c00348100e00301d2160505090091350720640c0d0041c011450315094004201c0c0500200790b4a030301c24044054400c4d0b01000300c40240344c592030311500805aaa80c11603001d00c100041e885074260f49a55150706c81d802c102030552041c9142c485c44007030031031600207603903080355042c0100020356228995956540140e20040c1c54010710014103003140e01c2da4200d80310320350091100b081403460900403510f0a6070191030f480c1d504801860107122207900240c940103114004130012584110324009403a150340c3c800300e018aa500c440e01841401d1040d41003040c0c00040c1000000c010403c10007900340c0143c07050303000c3d0340c3c901192214085103240c1660f00c000350440101d03c92021498074080c030b40c0c007616003400030460b0a034039a0350b4560f921844030312075052004501243c2e1050a40640c1c020704160054000c0c00701507401c2d004080c030202c00d68445a0040c0c5010f8801c0401f91002802611032035460301c07820f160642648048070840002030f02d00c4100300c40600c001c1926241d0702038014803980c4681740801d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 741704262 1250 741703012 741703033
    0xf0c0910050c10090b06060a0201060b04090506010f080c040e04110904080901120b09060d05160f092304240207061b0c05030f0310031b1503061d15090702 68
    0x2818011000380b00040035052284c280b0105840e100d200c0d03040482154030300d0303840006070710590240045030300180d040980854002141050340d00030600c02ca509136649401100c2241c42a1580842605c0d42c40092030705120500603900b0981d40d0355041400307019501d4041c3c81000008243c40340480b41190f0890000c07440b4070495030008480c060710244440c0034404d1409030030200303c0c9030f03100803c01d070702c6540d400f001070040c801d081c00044160012005041c0c0c400e0b84903142c0840030b080603c200c028040c5480c0100729915000252126090403100340024107071140d440e40031b4038404070a4004c00c54400320840601420003407004101040c0700390360200e9001e415186508080c1d0300080c1d81ca0038088800800000038401004030f412005101201517140d4a071900703807104254842e00b0041051b000c4250701441440a006040100c80c0181d8010090340541c64044007680c14912600b60b542c440031400d10181c00d40d941045600441c0d040741840e00c3e40c04000011a0740790160b0f030000142e0407014810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 741705512 1250 741704262 741704287
    0xc03020607141219050a0209030a120912110310020315040902030705100c05070501110a03050d0603020607032102130314010f090c06030b1e12100509030a030506030a0b0f0c091005 79
    0xc50740000c1b203035000c6080c581600c0100e9181d9a01c1c102c0100f280100b0021500403e00a42c44040900001d00c01680941058902040007840158080c1e20038412100140d003220390380c2c022a480b42d00300d410946840940c8004bc00003810440c40101d9050183c0c000c0407585803645d00c018000c446050b80c452070301c0b50030303400c0890034031186402c640d0400c000c1c0140b0000030980082c1e4000d6039545890031a50f01e00f034101040e0020400741d00000d5011000027014400c0c1039000071030b03900c9650400c00041c018042d000d9803034202c0c440c040c6488150308480c0380800c00301c0c0e80c4030750319201486030b8000414488800c500d040304448000400301ca00e1041880103002d02030b407620031102542c40139031300c00c00b00c03861070010f81280d40c0d9040303413043c49264030080c40042102c5c2803040100d0140404014091400c111801c0c0b40c030780c0c010312600000a498400010b06c0c0b4940045c04004d0300c0d42100107180a6118060414100c000041c0030b80140d110030441000380e40c4a244a643e415204c554a4a0b2221a1021003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 741706762 1250 741705512 741705521
    0x140108130b0c09280e0c07170c0d0e010206070c0311010204080102120f010302060708030408072f0d1223040b0a2c040b030109060e060103020f010c03020607141219 72
    0x8110750150200014080040c10880c500f05451120800219076a06c5030000d101910850360001c1041419078080003402010300d0281410490301400d030f601c08409100c0c122000410ba82c2a0790060384220086a4994002c0c07402d80300d00c0e801307450030f03104080c40e0240c4507003a84d02561102005a5002419401940c40240d80c01e40101c00307002050100e51541d00095243d00881c10041d0909400001150420441804480c0141d510078500f5103040550040d04603280314051904035500410b41004500d0311b0600480324002e98803070342c80311b444011980d00b00c030b8600740000c4400a4104030b0244008800101d0081c100820011402d141c1d54410000018101c02a031882081d840d003042c9070840080b103100043d10350f451030a483c000b035030401180c0001e0240c05141d60103001146002400681c039503002c00c80300d050380d00070b66040b00d18044039401144c81100394400580180c0000003c0745055200700344e503100721203000480340c1c100f0203001038244070b84c48141c03540c120300f8072a4011800e692515008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 741708012 1250 741706762 741706789
    0x421050d02160b3006191a090406050a0308030702100e101104090f020912030906030f04050703080c0313090b060f0d1401031218140108130b0c09 64
    0x40c10000c45420500c1c0d0714100940210304070141c0c049583c044801022202a2910712030300e410f640c010721001d140e1095500107561741c0340035102c3d024490b840324100342d04102c21608840c13070300b0000c01e400d450445416008010400d83c0141c442c40c00013055514401e10401a600401c00703542c1c0d030f00780107002a1400103c0c1103014840d0b424022411a03c08022135980c920300c9010030007240803181c1c10360006841c402d030b400c001489841c0004200321140031f680503208811081c2c0d00101c1d0a2070b01c01d0815502c2c0504111203034014001c000040407030601c11040d5401c14400c1e0304480000b3384030381c1e40d080950000b100003640c030742c03021405034004042290f1038401418402010081c10031141c020a403244038110300b64403c0840001c4030040780c8030613400a41e04014961900345596101e2070101861841624001d0015403088007107d00000b600118600b143c040080c1d1107000320200c0c1c015615900d00614007040740b014440c04d480491809070065100c2c00b070400030705a407584c18600704404c000174681c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 741709262 1250 741708012 741708017
    0x1030b1914071d030f0f06010e0103020607170909070509040c090b03011509081e060c09030a0b070c050703050c130915020c0a05010606050901080105040207030c0312020421050d 78
    0x7500700102402554203030400c00d40d18140407412000101004061000c2d041a6014401c0300e0034861000700101c2c482c41c0c4c290f0650159440c9980c1c0303280070070321684207000103035100c04100680c00c00220410310b01310080020310f9005080614000000b00c0303940003120f0003004142d000507503085614043c401c80c0c124072181d040c81c5103403a00b0081810724a00050043e00294000c403041a90402c0c0620411001000d80034101d0307041183c4031203003c40d01840500400e02510803580851202905002580c080d141c01a0003850344101540702c4005900c4091b048005100320350900c2000700d002400340340081d601443c024648001e80c5820b021001308440d11020109150044240004500d910341e104240c0500602617101c055a4003072505020304414020400c3d803030301c4000105641c0001c040c01183c14240c07110060f681c2c0e102c0030300c0306034400d60030007d0004400300310303000000e40164201c0c0e03803042032041e00508107610b60b29180d02c06900859130401c284008000385c42044410031060300c4603085403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 741710512 1250 741709262 741709271
    0xc09140708090c01110a02030a0c14060a0f050f1b01060f08010923070e180613030c020d0606050d0b060312070b010e070311181509010e01141201030b19 67
    0x203005a41c960040f10304150420918040f04030540070100080c00d074240d00203040d501070029501d01881160f070300303100e0518100d00c0b04200d14401e1415109440354200d42ea00d802c610030071980301c1251341e9030103052808200d4034280030030750f246404044120701e404640b500001c0c0007828804207007404031207607100b043e42e84c2c10403001034006640c04130041075454130001018030040d010f0180c1c0d42005c01640040b03445612070030401c0300d400d0000700c00d9020140320070180d5440f0348a52031440101d05c0903001c0034003c90065070102c001810720402503603410f030164400050f00b5403540c0c0060900c2041010650f08225000140f141da8038080c8144901c01c09141801803915000c0e42c0c40801080051084600c140030141c0042c1941d40282c01182e2404158466959142904550b1000001080915601401c0b0f418407040c0030440510440b0403100301611500031404880004641c106040c40400e0201070701444201d0085101c01c1000c4d01039845000500c0c92403401e03400c48a0a10321803018581c046041 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 741711762 1250 741710512 741710521
    0x15091a01020f03091e150c0d14030709031509060e0a0516030b0c0c0a061d060a060f050d080408070e041a0f0106030e0312090304061805090705160c09140708 69
    0x10750704a01d4114002404c085e85041e405e074001040e4030f030a418a040174960000700b02c00d02c0d69000c6041e540c101134549a001d40c0ba20480221107003808100c542c1e801040342d51038180081101f950b8545c043c1000c12502180398403050346c03480140c03100e00a05003400e511001700b4008000c010700c2030722000480301e500c28000a05d59124140500c4c409445018520800200c0d4038030a9014000e400f405504050b041c0f020950b00600403585c01460058190b0381d0080c00301207100c07036400b4007415040342c80540c200351825080c00104010146d19881c1103801110411000464400c01d01240004105c0700f00140080d14182c24481d1414800d00c3c1841098030345001001b060084011410781525040c0c940094001849450507107540301d404410074140702d458040000c00304000000740144c1d030740355450007402041854080c1d41414031707008050780310f200701c00003508140c0300300080c051a038030b800541402c010058076100f1035000b5680100c40341c20303103c00c840030750490003500c1c03507401000901e003641c1d840c41c1c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 741713012 1250 741711762 741711769
    0x440702060f07050304031e02010932030f01050f012430090c051c051203091f02040602070f050d0f021f0e1201050c040915091a01020f0309 61
    0x2001028000d04001140702c200340042042550080c40d44520640c8003070110a025411a06000030100e0014495601c08a28190542c40000313842c216100e84400004c1800c0107080c80c0c2240c400c01c9900b5100e102121160342100b40180360203071401c50fa00f5015541820700704c500913030200c04041061203941811480907907100f20008045041d01c66030404d0415500c0c030700035038081040c06125203181000c143c4000d00a49204400456000700e071080300030381006070601103001d0040006401508403043c0400208183c100850f480480007050f1404154820305580d01c0003070301c2c0c11000c4800e5001c00e003485000d804009840141c054404210381140c074000000300f24564241c070050031050403032000d000715111052400c0100c980704c0c0c0d000c038800096041c024126423240e039980344600c15a5030035001812040c41154054500c0016480c5460304000d21607004c8e0100540040c00560046000582444640708103601d03200ba07044080c00104651000900d010140c1803070340c1441d001040309502d10398 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 741714262 1250 741713012 741713017
    0x605130603050a0207170a020c012a020d05010e06010e0f010317090f040e1f0203040c23040504080904050702060106050915040f032102010207080307080444070206 72
    0xc050345070100c1c2695450350900080d004515009200400e8040b00e04194181d0360040e02d83c0040c1582141c042c00501070044500f61181620002c0070103481c104080c1161042d152601524009082101219070541d142802c4ad601444041070540296006000d9400d007080903542000404080e00240c1d4196140c40f02000751180b07101400440001d030b40003e58441d00c85000f001d1030000c3c02000703030070080003003241c4840008008221036901184011074006091090780c1c0117981085040301c0c6507041c0070260680d1103030300c1e2100010000b00400d101899445000e03951186224804403034a400303079081400309488000e0080001d640042e00140031b0307254004117480c5541d400b21884401070400b13400d0100c41d8801d54005188040107800084144115031006403910141c060728030b0307404443c5c83c50403402c034056044020155681000401c00c00d605c244402900140212681f014001500c07448031201e03518440340c01102012048a03400c0e45058000b0310401d0740501d22131618081141d40001c000d0b1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 741715512 1250 741714262 741714269
    0x7080a150b130c0e131e0c050d18030f1d061b1b03150408120a020c0d0e0f04090f020618030f07080105100513050406110a0e0a060513 59
    0x15580c4061801403030755806010031502c034204408010300c074910500149648400304200d8020260f040b2001041841c5108802c00611035039002c581201518180340081c1c4200c1400d0800c103c024002112600010710648003030000c03070203102045043c0c2c0d07d809000d800034110b07024144032a1012045d030525408406032500d0000f112403641c1c410302854442034140c0703011a81c07440d522620710010302503003d09400b844005011011200350007420900c0c40f500c2041200c000306444002e10508842114490829030030480c14003000d4106810755041a2900e858250300c2030009150800e103082d6402d040c1110646200145c03002e0202c1c0115803107030101590040f000078010381000460b507814110220640c100784000905544900a620721119602e51540c0036881c92075103000c020072203034812103099904030350002c1d020358014409801401e008040040060343d803162510315110402020038000c050169958403011100a140b905100d40415540c10400034404100b290245040a07000d400044 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 741716762 1250 741715512 741715553
    0x31b0f010c0302010e01020c07180e030d0b031203091f02040b1804061d07030e0105060d02010e03011b03020706050906250e0a03030903050f0d09090209180a0c0207080a 74
    0x1071101490b049004045901114081e54400b0480c940c040700041a1030049541c141d40c40d401d9850001ca6840403914081481c66003917004108c41c100f0391604d50000b00fa1010000c00352252040f20411500c80343d03000311609030240c0c00c00d050603112255412002c4100a203244411420b29051284110661284001d071102c042c10424480304155901c0e00103002401c070004164103101a00b030b1305c200549106a40c00f102003410040d00039904031052007850310920001300b5144010811741c0041d0303141200449001c3d055500c80d00c44900c003004e101e00c0d0b11001c000642d40103986103198100441220805451020244c11641c05c2c02603030340303201440c1d1541c9100c2503582928010564416614096445130f95500641100e20020030f064205a4260440303008800b6989006000740c851520b6500c03210032035000c1130950340140240b0b0300176030242400000c007410300703598080c10103140e602c024030490707241441c1a151400300c3c5c2c2a69042c03040d440244001402000c0144441da1100147c00d83d10000108 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 741718012 1250 741716762 741716777
    0x15030d0302070c05060c0601082a15070b180f0a3804032f07030308090705030303010311030d08100b030402010306090903020f12040b0d0b061e0405031b0f01 69
    0x1402a003448203c0203080c000c00007030740e0b21541c4500c551200401d214108aa0041501f604017045600d0311101c01a003843c20182d010803001000c00c030b042d90400f203811149000c24401480001c0c170b1040d100b4000c012104402d1000340d6071402d06c500d0112440060300c4250041c0d0303140740001d40c0d41c4a51a215013480b0f00c0b50100c403071448900301c0c0d452141203181a44030401a0601050507045410082011072003841c071070740807006103000a0f20140b41d030700b6001658840b500410110341b040c2402c98021000c00141d030300361035403000000d245030400e800030780e296000c0400504181c61304000c460031100003410401c2081c0303010383d040113909000f4402d0032029600040010701710381c841d0f40540040c040b1504100205c900c6820300a650f410301905240d80c501ca81d449841c070006100c8251001c50300219410340c9080503190f000030141840d80c40c1c564104205000c25403840c81c900840421000420076001d889505e000105440d04280c12081d00603801404030148044d1030b16034412414500c01e007455003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 741719262 1250 741718012 741718027
    0x3040b0903010b09040c0e01140907030b0f03011e05070807051603020106330509030c010302091207031a06040507050a0309051f060e16080103030f0e090c0a0815030d0302 75
    0x2405003c0725951264001644002c100400c4402c00da0201170350344101c5002c40580c1c88d0208c44000b1011042d6555203ca205400210324034482d0300117940511010380700051100030800030a081d504203206421054491104441c5001001d00c1801d501403a41d1502035240d0a0450340541030340714600b50b4003500402c200b0014107060003500090018901001881d00012001c8000420b000041c11103240c2411009022404140702d4815906a184000d018017120004500150001e40c82802c01d01e8103c40000707040e03104130300c2c1480300d5002180100381e441c1d03101292500160310b10704000c00e100d214601c1c3c0700c180600260321134140c80005005003000184910a410311070325040c04820f103070984d0741410f0884101186140c2002040b1400c8101800d81c980717584591404080c41c0c13441000020341d9101c010004288603551610f5403410340e060041080d80d442d404180c0416041756a1104411f0000351546510380c01041c2c4c0380d0000c0380e03040c0c40b4401c42e001c02c002034890703100e84851b000300742d000b0440c003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 741720512 1250 741719262 741719269
    0x618021f0302070c0e01090e0105060105040504090f32011404020103020d02131503060501020a020603040f0c17150c07050601090c141209010c08090312070e03010203070c020901090e03040b09 84
    0xf00e8500d0b41044013490700c166a40e407006040d0308240944090141040d0300700546180502895010b0f42d016120340d81428100020b1000415020724141d9049820001940115040701d00740c4a8421007540528050640d03201c919001c818040e4008101e40e140c014051807094101c090307981c110f40d092038056030320740c05017607110080c0c01260010f040001a00000044d24062421140303aa03512a440134408d85a0390b200590f140d00c1c8a0030040d410110400018000802540e00d00c0600c81c4690780c098140f03500c2e00d6901c00802e51980342c103903a951280c00388a02008241c20015440590224020320b000019031f261a142e240c18481c0d446995101e4400303054150180d80000d11810265a13542d86801c440c45e503c5141c240184d8407140740354680792079914054840e03101a8032450103000254541107881c1e507030241c0400001c18070b400700281480c030240107680a0001f5070140006907107001580e5424010401d00c410181c1c0120b21232442c107402e40000c48404810f03071303013100c0c0301605150f15036a095020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 741721762 1250 741720512 741720517
    0x20303130c0e07020a21020c060702060421050c0d030c12020708030a081812040b071e05150c180f2806030e030a0801050609011205090102070618021f0302 68
    0x180b800c4a540c104110075182d0001e8200c0d00380d4010108480702d00740000d0340352540700160300c4084c016000701c421801241403120040c0415031019240d64545a5600198510b100d1003521545010b010040f0350003e00a00304a090704015045619106098860b5400342030708818103401040c10603002c0403140310a001f40b1800004105003000d4a81d03404111a004011020455407510440e05d4030f080041e0000002551414100c918a1400e10b00350405014154a400403a411102c0b5047c894000d199a41003078841125140b08000910f008103010b1a4402080300c000c0414812150a00c4010b0f4600290744c118021010141e070100e420542400103e0a07520001013840c42c54000421302034649120062800e04881d02e0365010007200546076090b6403280700c1c030408040010b141d080140a24600400140301c5101c0505010010841d1000148140c45046566200c0340e540810294140841c501404000c98a60440c5801203003484d40060070823000002c100faa400040d43c50b0b0041c1c035000361b04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 741723012 1250 741721762 741721769
    0x1508100e01090b04050a0501050616080c031801020d020a030e0d080c0610030c0608040c1512240b0306030a0b071809061a18090604060b040b040603061203020303130c 73
    0x85403001e40e160030507400a080010507490140340340c480040d039030031200c0c8901416110018007507403030610103c909441845814200b07407180c20081140780460542000101000740c45d448103031011840d10b000290070f0022501c0e080c1c1c19500000140b0002a5203c15090f110320012034102e08204490306113903201e80140852101c0c5071080340144840d181040b01c61208403481074405041c0c4544031042103c20010986008013641044803003807184008039403840c0c050000d41d103030181c9020008054401030351402038200c0e07104100004000c070710f2026807079044050210700c0c1e8014910f0a0000100f59280743d6540042d0035082c01d85c0108401e03e04c260708400e100c03002003001104060b202e203200d100411091041160100f01c1d0380700c1e407003240c2443d0700341c0c0c2101c50041c129514030341d0b900041c424516030043c0b41c02e5200f65038800c045880e80110340030f4070242c000288510b03212420088041c0031950329800030323905820107028400c0000d50020072a90b103e5815505a00a51030602d807918060f0103641 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 741724262 1250 741723012 741723029
    0x8011e0503031804060503070e04020420030a0e010b0406260c1e0916020a0f0507050303070506160509031c120c17220b060a081c0905010207150810 65
    0xd0040e6a820180183c802c403450840301000a15039a40c2010b6440350103120304c40d070300c01c0c3c2400018058600f83d441000340280e2100d02c1814440c603100700000f2036008032a06008135030307280184402e01500340b181480c4440300782d4041280c07506100345440d4103001c000c40205d4820040c99030414840d003e020f80c0d91690809052104903268205d01c08001e020001501c9002d103101d0800180000e5906850000c0c822039a000381840540613100c2440b07858009000f501d840c400e01c02c0c0065583c40c2080105011401240030b070006050110140c0361198100300100d08006050190400b141d9020884280c2c5270340d0100100722588040c00c1c141c1e4280d099041080c146840c0401c4101d816400460303401900d078040c0154100c5a481c030074040c000100e004140c0290b05030200705000064982d26036280c1161004200203000340d580c1c1d203030501d4419101358043c5a003881b600c10005058202d840c100190000b4009000d0080c10561041580c05130b0111241c1000026400720342540d800400c10800350401a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 741725512 1250 741724262 741724267
    0xb0411040c020a0506060d031e17090705030c06030403021513020409061a01181703160f150e120d09060c02010501140604050d02010c030207120b07090602060708011e050303 76
    0x101c0380691070f0503200400b540c490040c503001940515100d840040c6241d4142c40d0040c5d070341c4440c400f000d0801d40900303c00c2e00780228200c05842c02e012902c0c00340c0c864802c1c54020711160742000b0a150a1a044800040c0100400c0c001c0c07000094000ca05001c2014018801c00e40550340c003150060000c8031144084d4001d4900f0701144140011608454102c184c0307484201041c20f10b400044400c041004110010304509210920500003911050440a0200d0045070f08010410404072540c5480755021550342180e801580d003017020750511418890780340e6004200800350440119101c14000da00d600c5a01000180c003000c5c0c007196440344070700b00d8110710100404c41c0c880801038000e000070700a2030442c1800705c034000d14600d00b410469040c1c0300064842c07400500240c0c01034400c8404050120194011044081a503140d1003200140395401b40e800a41030342024030f4064440a0030b90041001c41d048001000395144c1c20000c42411901131280a2000110341d441d0102c510071140c102a40c0350100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 741726618 1106 741725512 741725531
    0xe060904050a080d0b04110903010b09160309080c100605120c010c120c050615010f1d0f1f0c051501050904030302070503092701090c09030b041104 65
    0x40c81c0d0105d58802c1410029080d2045844003145448000c10303450b10502d401d00452000804c00e5072841d405042295180303c40c0a462040301c0e0a140c0c4030075080d8100008401201c7c030f800010810355000d2020401c0d2900540748a224032441160b41313080e001001748020911500340e840584030328844114982d00d90b04265400c138001400c5c0003169823560007084081c040c00e032148070303402c03c28000340700d0800c00904640780e9a12145c1c00c1140700d1100320250441004041c081d144104c0320400d041d0f85c804001940941d18182030f0f2040c542d0440900000c2c0c7e000714071000380603c150140e40320044000120300c6184024481e01c1d40c0020b02401042c080b9002c0d600400c5200c0c080c409581c50325000354007003402c50b13020100d0103049101c41c4101500c298003401e41d0b01e02500ca0800306100e06402a90010081e140740c1c00041c01d170f01e020780007160401806000704c2045100262060020041 = true := by decide +kernel

theorem cover : BRFrame.Cov 741546762 741726618 := by
  have h0 := BRFrame.cov_init 741546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 741546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 741546762 ≤ n) (h2 : n < 741726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
