-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:44:10.100241+00:00
-- url     : https://prove2.me/submissions/61affd1a-5fb4-4dc0-a0de-de6ddf33304b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 916546762 ≤ n < 916726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 916548012 1250 916546762 916546781
    0x5151507020d080304120c12050901022401060e0108041a0723030f1807030b060f030102030108010219052b180b06040b0d0302060f06040608060108030315062a01 71
    0x2a0100c1c2d03980e441c0a004562086804441c899440e280410b60140f1030b45642008903440010b41440a0300b00500303480a400201080c0c0c1103200d0b0503869a005024070011a1740440480380340062541400710141150301010b042e24100014a4104004514012030350b446984075140181c05070b4960620480714900840b140fa00a1414140c05115143c5110011031042c1c8080d54040340540700c1c0303d070885410a40d500e542e00143c0c403d282c14004070344120155078001000429a201103a01c000c0402d099070802d80c401e04507079602051007010040503103000540740925141040c0341030f03842d101c40c520740c5426a800391840c0944500c0e02c621103001d84e00800250007450900541d8031f0389480c20b20b8102c031088808034040e078284401049141481c0a1209002d42e260300940199502d40a421707800e00e0008000950054644000144032201805414040d0600c0b2024564901d00204072154000098080074001c0b04200200741008410600700d0588003805c085c1800005209480079015081d0f405 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 916549262 1250 916548012 916548019
    0xc030c03060109020f042d0b0a0c110310150509070c0302030a050d2d0c2c040b0a0e07110307081605010f0f0903090f08030403021215011202130515150702 68
    0x12031240c400900e20111047d44142c0c9031001d201e0340e121003221180740140a003000c04203030010a814001140b0040921380c4540150840b400c01c0c03018040d03681a5680200360642d01d074183c10041c0054109070760400c0d03210110341810841c02009075002507907885030103032460030020080b900f2030b2480020b401c40d00c4c8800010f07000d03540144582692910510000c0b450100303c500d0719020350740d46402030802520380980407000d18a01c10b000242c1070080c0e11046007482d80302d556100c104c0c0590391103c43c0c9002400a29a019800b4034280c0000390400568003078498441e4000d01110001070280000c40f035000c40042040c664403050340c50315a0141442011340443d0500704141140c00500799401082c441f4040d5640000d0b03140e551010b041000a9800b07510150b0300104030034030250501510150402d4000011038800c0700004040301d83c444002c0c2c11112800106072401e07015031420b282c201304521001c40040100b0300300310341d0011070381e8410001eaa000721b11040c2c008440b6510308045e207020a0b00903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 916550512 1250 916549262 916549289
    0x80613110d020408100c05091212030f0108060c0306060d1e060305030a272c0112060b100801031e061103040203070f080c0d320c030c03060109020f04 66
    0x100c40c201c040d402501829030360388981c01c0104028142ca00450340c4040785520341e145450101018082c5800d046203000c0480c2c401d99403030f0012102000015403003030001920324141941403051702401c04001134040b03043e5800a0050100c0d95488108442840142c0000080c0f84580c0600c21350070294000c1e6804981d51402e1000002c1c0100400280414011030781d910744848840c0c0303202c0240700185141514244c48030001404010180f40422484544e02480d03010b501d4003402448004402c02d820440040400d11010400c0001d030f405495400c250440c0d0984010000d0a0001c095030720520024000390300020303500c0052400c991140c0d0040782c01070014420340c0c8018905880070340c01600d0032402031182ea440081d0f4902d1030300c1c2d8141552611405062009022010000410705480080d5824203a0f040040005907034142c00310f402c402107400d10b04222546040c80c500380681c40310524001e40001030320643c0740d6000b251181c15540480d40050f01c1e48100b001c02e0300070740101d0308a0741201000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 916551762 1250 916550512 916550527
    0x30203010c020703051c1d0a030f06020901020d0c052d0307030206010533031e09010926092209032d05040329010b091302040608061311 60
    0x40f851000390781c0250308071841030110304440c40704484034040c620002036444000021010516401203041280100710888640d1a44c80e40b00c046141e0003c203c0c0c070540c0c001120020355030140300c480780919032410320f24514081c1d925001d454401c111002060003981d076150942c0400c03000d06400d140e40e00310301241c1e01c81d6801d1401941c2c030f2400b8000c10f442101980720850b4042c5c0c0100380b044d240e14084003058400d40850740283c03a5908043c107050140e80c2088481103c034000c1c000c208bc41815540c1c00807070040f01038100805040c201d15104030009200c080307234003218001d00084401200c0240e401802610781440c100340c00c5028002c0e0304010700d0030254030405042e40001885a00d00c01c00d244e40764401050010750480003a4502c406000c14014042003011402000c8400c00064090f00311a044040419010300342c42024ac020001c0f080e0017050b4024541481c1c40780303e1005181200842c07501d42840c9014007440c100a2580344a05000c0c01c001c0a900c040780c0008901090750030031076803941c06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 916553012 1250 916551762 916551767
    0x20a0906090c4a030a03170702011a0d0303020d0501090504050f0c18040602120c0d0b06090d0b06030a12021f09020f092701021305032113030203010c 66
    0x424482040c000f07241003049840f40c2c208240e4200c0e194000b1038500803440e000c884050b4501c85501c4040441e6840b22a145910751020b102c201ea000c1d20981c0c0b281103041d0004c640617002d0700c02400701011680b400c401c00b05280784810080c007440d10b003200d0b24a141c008501e41103001e4410040440e50880c1003400001e00c00722a030300014000d0b072080056900520ba0b00418565400c8161101a80310800c6030104516038151070045400170f004000240c42c2c103c12070410442c10780150b903806103c6400240044202441d07124440d00003c040300c40c0780c9003014010001e49003071400100070f8207030032401002c606c0310368041080b500b6196004500008500640401940f248600894071a2510048142c40c51030075440c8030705020b455008040641540c080c02c14800d02d03050080c2a02c004066058061700d07401144107101b1081e00c03a100015a407144206540200300360940e02c2540030384d000310810b0314100b1070b000348107007031410690a040d181d502090921a1212580e80003035019460403a00c42c0c103456 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 916554262 1250 916553012 916553021
    0x13031b0305011a030c06120a0c030f14090d050705070b0c0312010e0f010506030105011215091e0f0e0601030602130b0a05270f040510031b080708010216060504020a090609 75
    0x6404c50517159003031004014400b1505c20451010624a250000201031a0349584400014a218a00001c070035014a0212088500c0340c140384840b14102070400c05144410040c00e015020071740703032032802c01c0c07040e0740d8a0b0760781e000764003505c280c3c00c0e40030514031104a01003080d110b40d0101100d0000e26540c0d01d0840094110b810b9540d2a044410b0740000f00e62170038440c0071070781252410307500c845a10680c0710008004225000b40050303401008540002c031030005010f250604030a514180549c3c001c010106000c07151b00c00c0c45203400714200004080b0035580404c0d03003030460b0741000c40541d489010701e021b079042420640008603241000306541303282c40e61003406801d49421040c1203c11010500a00020f00f81004440e150702030f041000b90300031410507820950308007908144001d9075a4072a0b42d000905114840c4480c03c143c2c0c108801c003d0100c040194000a02114000714035184052000c2c4014a481c480c0140515440e4400700381152144054000106a40001044501c1e1035440140151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 916555512 1250 916554262 916554311
    0x7061a0f0f300d05161e0c170c040c21060306141611030a0e040207080403050d08070f0509090c13080102090a210f02030a06151a13031b030501 63
    0xa22621001400d40f82c0120304940101007104044100c07017005a84402e81e00d41201c12421850b08201034000010300c442101c0400b401100e80302c85041c0d040340881c18a00304113588801e203c2c0341880f20b0748c00c180b500f2214503908002000c03a204944007040c680d42c00501000c0d0300081c082071401e10309284000c0c1c0124414000c0428140228003002c0007002211688a00714101c0e429400c2004003882880c0249140c9064800140015083c00b0040e1588074894109a10507501d641007a440000c40580c80aa0355600501608004070000866400101203010702000640078400d5400810307a589800e00a4603450740d041102c801328640c48400840c040e4001c15240c501941c20100d0204404a050381400769034110ba1034501c40119050b150a014000b50180070303038060080b01d070020040750b00c0d8080c84440748085940700504d00d25002c45260a8002184a8080500c0c244030030b0010103a0300c80340f00200c903000540c104c04100c00d10b1a6004c03002d80c0380e00c000c0071507103003041c2c08266420840c040c1921 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 916556762 1250 916555512 916555609
    0xb010c0f24140f0a060803030a060e0105030f06040b15030a050a031409010c020f0402071a100e0c0a0c11060a0201062d090f1409010207061a0f0f 64
    0x3100306a071500c00580340480200b2030030621a03070002c1c0f2445402142c440d482145400c011036513954845d105400c0d60b1007620000440e5071628414800c842c02548801d0040c001034004148a40c0301040141c2c40e00000380c07005050341c0c04000130500100114000090742040102a14035424080c94000d0786e640c240c13001100480e8130088900900005501551400c18060b107400494004d00c1c1d003045190100c00c2c2d21103610903030910500000c0f0380003480d00044000541001c0303201d8140010a030005442d90703801901682c40410401410030b543c181a1810307035809061160301c202161915407441d5980c1110240c1003007010901642441d03054000c0022958003042600207010303d9036451100d060340201085020091010401007000030303611080d100c2240035000900e800754406104854001034504014581d0041000c50512001d03203d54110390305c0c00c1010f202000344280204041c1003881800f28411003036203644a0141e15010400c059135200604040c41a0310114030f1004600b0210300c200c0c0b038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 916558012 1250 916556762 916556813
    0x1e0a0e01030c090602071707090212040515071b02150a03020a030b0405011406070303020405060712030f05041104021c090501020327100c020c2e0302040510030b010c0f 74
    0x2d40d9801002c0302e00c140c0350194040c1500ca030802291418030841c0f040001c21030311801d90b002804602c188098507010581c121591220704160414525054448680c030410b0201c030710600600b1a044804560b0300d40d03255030b6502004c041c900000c1c07030407420b030300207a00350500c001a08020658990300510440700785440411107044402c0c280300880c0c000b400b0302d0b4008a200b1120300038900c1c0c04000361404c688a880c025181c15100c50104425400c0b0400885444404503060507546826000b09000412145001c026030701c1c21381c82d0712108800380c1c201c0c14015a40000c03a4001103400c001c0039040d4061180040c0300c680c0302c0340350150003588200c0705a034003c2c0840d000e05106440060001649000043c010807605081d110a4001003071078130640c406521800c0f91500c200d0f00c2e543c4401c488006044c000c0841d418400e000070310000340540d200c0040510400050005664201c10030000d0322203454001260115003005a854264030b160182400d9a5001084200075101d1075a000a00c00e0848000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 916559262 1250 916558012 916558031
    0x306010b1c1505040b1f08070305071106060f1c29010e040204050a1d01050421051804090b0906090c150316090b07030206060306010b070305030c1e0a0e0103 69
    0x2411aa1180849840c12401920802c06407510717412040341031000031b21140592003107140080d000d000184845010400c05010000c039150103208240d8060464142a4003c10b9090303492525050010034003449000948418282915202910040801e1240315401c2280040c20000c072401da240c0c0300f412034120ba0045541d00c0481901d00c10b41281d13402c84e19515982c40d10b87c20003018000050010b504031b07994482404002c4c40421118115010300800003d02e07007842e04180b42082003801c07641540110503e10000140d82c80307402c85101e100f00c1e0901101a9406c40002000303040130706000f91000d000c034401e1200e00e800c003041c41e03402104982c04442d42950307248140625822405d0780000541ca0031300c0090042400e002180301c0784941850291031907519501c90900603001610103038010703400303141000071a007001c001c3c050151203450445c41c203002280e43c004109120051000061041c0404c1c000c5210000915106d208024542503d48912103442d0042111400c4a9401d0004e41080040c8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 916560512 1250 916559262 916559317
    0xc010606030e0d030c1d0d0b0403050c07061d040515120d0807030b010c1b050622141518030102041508061e0618040c020d110f0606010e0f0306010b 65
    0x28000b050562100e01c0c41d00032010b106c01884480725000398000c1c401c02040800100d0100010384228030a48410ba00c0c1c1990b640d1891400d9103540108003480200d801000c0010070311a80e1040b15131040b038001c5855910604008407500e50b0303d031880d800c25000700c071448811201049004640646513180c3e08940d42e40e400403000d0720b009940580c00b096994140c0e402250b0010210000110849844100b9555500c0805c0080e0311a4102112244040500e4070312100303c1c3d28108002d2001d0815a0011002c45000500100030000c581610040000711200c01c0004114a1a01d0341c2c3c004000310746565a8009401c0c2c07a901c21b05103500000e01c000001409071501c02d41c010000580040f840008106010034008503030702c02e00345101c0b2081c01000080c00f594481c003440b1812001f03a406042003800b40c26001e41001c0c504490b403071003034020301810f010030f04000408942c02082403800800e07207204040403c4001d40e01c0351510390180a40e400106400c440b8100070490403140140c652411030201058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 916561762 1250 916560512 916560521
    0x612010f180c0915020a0f0b090708010902062a0a060f0509030c0a06110f0c030c070608070503271615030b0303180a0f09090204050606070b04170c010606030e0d03 72
    0x11002103600e00300f052010f81000710f503151302100da50044407032110b80381e02c58050803014900122801c1001c8010001c6004042c4510401410008020300c0301b40d5031513002a00301d018500c42c49418101050b030a055500034104c0c04802d40000000b954215050390510501401f01034009030b10043c104000b06009400010403104400312803c0903041420481da1001c001d040c5014038032180c075005000010349051510010800c04071500000c41d5100841c00c1c01908240480d03000d0000d121003041001410798220b401c40350b100d001902c40c49880103d10740c03541004500d4503110a2184130700104a0f03200458072450800742c0d410501c4800540c034460b0802c809907403485e00050b815420601c00c110f014190100d003041101c50042c000245d9175200d002480040340d5541c0103542c5180ca4211010541c1400c2c444c10333422010a85066242c04540d40f00d50701001c070060310060811030b00c041c501c4110641c850a40320340c10300170000be00c0f44c1640c410004003d0f1400d4903107003100d80075141218000b203000307106 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 916563012 1250 916561762 916561781
    0x7080d02091c2f120f0706032304020a030f080403060906150b03090a030e030a02190306050703051e1306020309070e010504150b25030815100206010b090612010f18 72
    0x50080d0f5541c500240086082c00080403030062003400c01080e2404000d0003c0340162843c0d60700007813522000001e44071083c005501d4000c0b03802032282844050780b1545900f0040d65040980c50b1030180c283d10b840302c000d100c1c07030340040d1400b4903101691080040036040380003083c019003080903085803500c49210f074078802900c110700203500201b0b1000019016410503a242000282130b280c080712140c003c540f805d010300300704a80f1002600c105008000c0036106031508001ea40c60100418500504a50100c840c44c80d401c6401c610000000740e000c0e641c819421035290340c044429526402c1601d803090f5210070a000301101014040001300b11070615200b400200080180ca04000da0b1402000000c240d01035501d40c106c404482c0c1c15440035440c071202c00300e0901d00c00d50311500c06d490200342c140c03103c100081220f031140082e500108c0d102540000e80307134103541c0d8031000c0e01e55401541002803054442c1c0035015075102410000005c0401051011078201c0d03800d1485a03400008452061081f2041c011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 916564262 1250 916563012 916563083
    0x7180f0f050105011e020c060c01092f0409051f060602010f0504021c0203031e040f06030b0d0303051f0f05030c0607051914030d0f06060306050607080d02091c 70
    0x51110803440300400582120340090059a1f003050091340840c819030f202072020703015030303468055410030050b040380061030400d04a54140070041039046580c40c140003450042c0e11540e2202e80a00a211051040ca5208404a09621350001402000401070101072041300c0140d4a0038490a60006141c020b9510540e4010200d12101d100038003c0704e90180504000d80c0c142c4800c0c1700e0760158000b8084003030044142518a1781d1182d180c01d0741c241c01130140d070b04040e003018280403030400c00c0d8407102120070781e5a0741410045403d68030b5202140030200442030401c820041d08200140502c505c810f441e080c1c8009030103a40d9441c5108040c03249510602070b00030000d6001c00192490b90b100301c04002480d51082c40841c8030308100803d218a541c0295040034141039030ba07030443d0340400442c8074840c010800ca0401f40490f270b00e0800040d45501403410068054180040c242443c42c4259040314540d401c000c1003084d082d40952120200005007000c11a40c0c00b82d60600300801c820701500000082500b50b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 916565512 1250 916564262 916564277
    0x22090903090503060123041104120804030b130302060f19060605030f100b030f0a090227101a0d0225060608010b0a0b400f1208070507180f0f05010501 66
    0x800e000c000c28905040c1d1405a0043c00084ad01d403a2642c9000e100358010655541c0303840c2981401c0c4e1001d80701801140c0c4c3d004d4410000320020b0b8002c03e055500070001500303031a8640c2c0e01078036900b0340c040340c200d850310051500c0c3c1d0100d4842d4000e0702950180e409020300b40c00c6a5503290f00c11241e0000d6004001c9420030070700c001503000102c40b49032076202c01560800b2407804034990119480022600000c59503818003000c182e52002a0f41c2417543c017450503030401c55105d103040b1499140300800c40e0001010f0750002261415480c041d0112002c007800c3e1110504070b00310460280b903001c15144412940507092240c0083c65400501035020040802028074039107a03d000705002084c1c3c44648460040c5c03411209620100c1c01c0703000041041070620b8611901d1401d04404007101c1601600300d0484202e2030711080c0940440c40c031810415641c0003503240d54514160400301e03c3c20700b540d807025000500d20058008140d5042c0c020383e0035030008450078814030052400708815200c00740100e0f800100b00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 916566762 1250 916565512 916565579
    0xa0b1b0304030201171b0412021f080a2a02060702060a02070201080106030906090c030b0712020408122d09010e040e0d030b0a181b020f03220909030905030601 70
    0x3445c01482d0000c0b0660f00c42c85610340c04541d501001e800a600c0f03401001120340a0f4001d6082c800781c015030f600b00199007201c000b4501c40e80540451000740c51070303000c55502e800030310480403140c011070300020110561110041600340d0013981d410040f12984014019180840d111341c0c43d42c000d46071455816180c4d4100750b0b0074424200c00901c000c043c01c4d40c0041d1114a2a0042001c540c080030107507021b502c03401c0051a0240303001e40b1160b14890206d0038684100410010110049404000d003810300f00c4d865951020030f01a01c184d0310354540700c00801070042448044d01c082a00050101e11001c0e00d030360310703140f050404000c100c601d8410115202d8101642d0310f001d10b842640030101c240001084020402d0700c0d400c0c5440840f00f0544007945140c7e40c1c070480558568501e40c189450341070342c40201054415484030a843c0e0207140140214101d0707443ca10140c0000e0010b0440113021071074810481b02c0410306006002d400180300d80c2e4028000d1701d00116030b100c00c8409440c0749850344444400458203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 916568012 1250 916566762 916566797
    0xa031a0a110c0d030b0a0803090f0301150807030c0e0f0a09020102100e060a0b06210402030703021e09070f091403030403080a0804120e090c0306040b0a0b1b0304030201 74
    0x401000c600d08036a0300c11900c0c000810110103001400071903002410b43d1032410b01c001c2c045501004031584a40e861503000c001158000080700c00c4040c0c240c961400405481000c41d000d4004010460000904441c000c102c1c070f0720001341031040328002c80d400c1e081c2a9442d0b00302420070030191107109907406288001854014150441b114040c8107104a800040c1e0340b0f03a5900c00c81e440d40c295484503400c80000c1c85140340c054001d4200900742140e1142c41d0800e603090b81c890205001428510440700c7c40c0001e802c1d9542807088030300554015191445a10900400400e0001016450380c454107040d404501c1c810b220b50740b01020504280c845981141c209a03100f4210b4450360005a414030003000040b00140c962000745c184243d141d225030b1494145490009105802c94101c1c00400604100100099603850709180c0c2042c205544256681c4030300e03004c200640780c030145640d00b04e10041c030300240e09540030f80148407100244c60051113a1050f05005502e0341700c1d40c80302a0000318000c0c1c505445d40e2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 916569262 1250 916568012 916568063
    0x1120b010e1e1806160503060d0c0b03041a072307050307170c0f01020a0c02060d14072f0a02061c0e0d09050102060601170901200301060e0a03 63
    0x10808128142c400c0c2c0107004018030355108490702c80c000000d040c06200502c10070890b41c1c0c0c000d980d442d0300c01c0101c0d8400f040103010f80001801c0c140303c0d2803030050100a103c0500303100e001500200c422542d07a80740c9410074100070720351440d03156846c800e200002141d881c418802e403030190500490311360650400201280c95504003003001e030356602003000f02d280000c2c2c0045c00d80c020b226558003101e80301c000307440c0040c0c00c0034114016040182d0040018101c1585d00800350042d0383e504440c50764a40401c00c804a00078103048051b08040d10102e030920503441d8118040460850310003448445d1341e075540400d01910015140075464640c8010402e100520713011029044c1c05480d8540c02c3c1c180000754005200361441c40921013543d800c1380030b03d0a2480d9002402102400d020300003004142000c0000902ca10313030441c03000110f410141c0100751082d5081d0445134182000714010002010500c2907003c09510a101d10030204003c500c0d045254104031130f1480849030010756681c3c1c440d0403441d2540105 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 916570512 1250 916569262 916569271
    0x90203090c031b03070e01030330021204020a1707120227100e06011b080405060703050d0b04050115050c0c091806100b040303050d020f1902010501120b010e 69
    0x24010038240000c90349080204403c480c440c1d592659180420106140c1449503540000c008505007100610219400041134216051280c000f030304901403200459542006c95045072111600000707510504100314558913004034002c075100242595070b0100d4111031580740c04881850307000068200031000005500c0301105001420108840e600c01181508a50030a030018501d0176000061001c0303808020010805404a98460202e50400b8000030f04940c008806000214103012030080c104410003054070020400034200ca52511128038014207284c0203400003030109440c2c803407e0b040703d2425001d000c0c100c858410003036421203a019001c843e60b0380031580659051040c4038001c0d506840c1c1004542c441c1380003240c03030301e000c6158075052404c00001a19400000703911b007100740a409850400c4404403a40360070003558030940c5100c1a07000e80106200154090804070300f8070740c1342030810b07420100a800390b4001c10041e03884074013822580700305000242904001d200180700c50000002800d400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 916571762 1250 916570512 916570531
    0x3190c03050d02030d18020f060a03200711100801061d131a0f0609042a0903050d08041a0402040e060405012405180709180b011710090203 61
    0x82512501c0d194541511904090016480003840d0702c80750060b48900d202c0000c4818402e190180f0355000100c010701d8941e107c81c4200000901210310901940c420f1185200440d2150707004030601610b11030b150000c0c00c050312400d2a05a01035820702e8840c6486c03040220503201c103049a42440c00c115441c1d00115681010000c0800303140310142d540c0ca8005d005141c000b00c011480351103c0b518009040f00c1405102d005882d0554545043e66a80d42924407400b02520001101c0d4419910410a1925056480d40303c40c04501b80c0124547d01c02c10041c00d8a010700200d5104041850301103c010400300c074040d003e8a4252180040400421105c7e40c00c00d000610124041c14001900780c18035000383d50441d6143e42d50340c6800582c20f00042d0500c001074403128100901d070724040115214040403018108040200c0d4000342c00706024940c0600030385855034004500c0154034612600030000c035102d1501003201150100e032030a10071401144034910100075113401da850119918060340002c0c140c0e00320f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 916573012 1250 916571762 916571783
    0x41703090a0c09020a0306080f15060102151512070e2d0703051005040209180406110304060c02010f02090d030c020f040906050a050903030408270a14010201060f050319 74
    0x2040e09802d40b400902040c20006a4940380500c0c00b40c04c49003554084250f90304003a06031060201c0118103c079120641c2c0d02e1907050341d920303080101d0801940c094001c40c400700140600c00d01211210384002044011b8815042501201050964452040c440c030048244100c00041d03400d600044c04840304000540b0711403086045144807400e00f0400c42d0901c0019564604001341940c0f240c140c00c1c0109010f4034218a804482c1020500500241e000c1c00641c41c04000800d0030095103a2008002c11344c03c00c007141c0ca9007001c0c0b80030344c081c4c0b2401807094015801c0c0300400081880700e100307d81005400802114180c43d60f9a0b06560030140c9003c203a0b807008840c52005480e844600802541c14480c580004d080d00c3c00328a00300c120360015107689000c0c0d10a00c104000109400f081307480c0c2c0d03400c0c0c0540c051111481a48090040142040d960308250003010000c2c0e0240d087e04c0d80030071310400f600248240381e118980b0240ca41c2491044551641c07007800c40c11080d074a860000302d0014001c0760002c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 916574262 1250 916573012 916573033
    0xc08061012061d1e0907030807020a080a150b04050709060c051005010f0611030304022d030115051f0807050901031d0610091104050418210f02030304170309 69
    0x110100c548034100d40302d403c0510800c02c00aa510f004400044204500e0310500d0038040d81040d44c858890000a020a500045100c1950384036070610700180390403021542c0403c3d0741d2a044410b2071214070040c03112810410050403515242c01180d100d81088da4035a003c203868944112106a2064000d95680c081d0144200c500c0c3c0080c024103010f0030801d41140e4929250074001400b6a14101d60307000160424010b01c00180c0d00d210580101000501140d100d406200206070415203501682382d80c15880c1c0040c2d0b000040b44d0640e110200d5108445c1601000c050b500c156140464100400d0001043c500000e038415010380090080740c1010314000581d0761030002024513201c01030030303410700b10b520240821507120403150303d00b80541a010000d00184030b840d03142c0e09240c010390007010b02c03490325040464a894117a07011804110741001081d0124000d04400255030034442c41c2034ae000988907066280ca180c0000101c0c0d0144d9842000e10301507603d901d603200011742000c4d10400c4540280e00e980c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 916575512 1250 916574262 916574279
    0x14070b2b09030e0a0b0f041e120b1006030c0c1b0e04060f0c0203040f141341060d0320030c0d0924030e030703120c0806101206 56
    0x120148243c0301c0d0140300380c1d403400300318030421954440741d440c1c3c00400643d41041460b505841c01c8400ca400c01d90300442c0200000442102517805c16821002608134000520201026040c0500c41c00311019503400d450b00400c03400d442d481010b601c041000750209200081440c040044040004160388121507200c500752030b0a40380540b000c0e030300d10380c90303172003026042c0c605120f240c000b80458002946014600b0b0a00411402503228241d007103454440e01c03a1854940750640c0262820003442002182c024260707426000c0101244500c100c20420595400f5460540e589502064a84d0344c10150f0b940c0c050400c594540f03112070031010441600c0e03c0c25404021440c0d21a0910390b030501468079001c52040203440d003001581d40701d04001d01c0705010400c98900135500d800c1c25581003d524201568080c080c0c0203400c030390b403c070740e01e074440041c1000034164030150342010601880c0060000c443c840308116032492043c0c032400c2c1d21080702d09208806034091508403400140481c00800c42a554000d1b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 916576762 1250 916575512 916575521
    0x30b06070803150a0909030e0f0307050d03030906061a0a0206060118210b272e0e1015121707050c06030a0501060807090b1603090305030f0714070b2b 66
    0x100d001c19000b4a012108c1c0c6450068420000320590040060306d01c4c100005881d900440006014565101140717000e10680741c10001c0031780060704000202d07110b18161800b40b03500a051110050140001184c540d61194010314070381c400341801441620b09140e1041100c0b5119821900107840c000724602c00281c01c0540588035000d017003c0003e001c144000e507100150a80c003550491a08100b803480d031802080f0810501c00c06001300f20b907410741d105100260040c14200c0c1d1240f40d501c9000710b10301e210041504900c0b40c01e1818169040e0007552411403000300004c00c9402003c0041407580035074030380340a20180402c24060b03000c440d4146001408a00c070380e40296243e00041d9240c0006020301e613000328040da0031500d5444c1c0400740503d042102149070103100401a4241c6003801c810301814401c1d0f441c203000d150400140ea542c0c0c1410301c4050001d9004200803280c401c21030201801100001c60800704507010800800e28292001c0e540f010003180e0185102c82e420054005112110124800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 916578012 1250 916576762 916576781
    0x10020708070603020c060108032703010905070f080f03031b0a05040e4231050a061d0403030c032d0522020f01031d0a03030b06070803150a09 62
    0x100142e0b141621a900d81c14211b0503040b4640d00da00402451820140c0104280ca1803507c0c200c174a041d2580540009015080c508000b07002d070b104d601008200c7c51a07003240c0134222040c00342103e07000c52214080503203c1c04221840150441d4602103418411040c900801018100c0d140003460b02d915110074008480c420b40f5446402e41210400c4a280480811954904404114200e400040c00d01c200c160f07e40180ca40715024211050007540600d44a00450f400c4200b80c050b1501d40035290081100101011902180098100030300025046821140340701c502e000701500840540c1c0f540c6080d000fa003081385100d820199a015441c0310300307c40d8182e1201c400181c11544880340c070003620000071f80740050106203903c640079480701d00c995401c00c1c00c44801c03035040c0e451002c0c1c24842030058005020030310050040080e01800c0c40c1110001003004000603100351401c0201c454100c3c2808102d019401c0020008401003010a90840055110740c040040042160110340e4a13034056600b905d00700d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 916579262 1250 916578012 916578017
    0x90e0606130608480f130207110f060307050d02031f120b0c040b07060504020301020c1c090e010f1e0302151e07031e0201020409090b0402040507020c0f100207080706 73
    0x4010b0420404291041000303107110000035440e4040740442c104000200800580300f410781012a44154850740c5100c42c2100441404540308c58580c01c00d0305408000100132880b0701401107409400780b17031160540740660780300e0340c6060a08620700503250080d400980401a06141860503000c8402501c035030700d01030005c034204151390882c185403852820b82e02502801055400340020b0206800340c83c2a14025500400d0101e032076256800801c0c028030950321441c043d405080b034410061245da54050502c01c59a07525044c40f10703661600e00700d505030700f80901d018a5200c40d10400c40e0000da4074907112a01143e4042c55440e42d52680051062403054040c3c0103018408500040804580860f41154103440d2003c1c0c0c0c41c0440c0d135070b0020610003071152204c0300500c80d0107440030710758400d40c141c8000e8010500100880d102500741401c80c8841207030101d101d13a0829001500003840462006c0003990054044140c80c5000b00410900010001c51101148201e00c000100c1e04410000c1d40020410354 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 916580512 1250 916579262 916579303
    0x8040b0403030e041e11040509040c1502011103010303030e100608010501060311130614070f0c0512010b0d0212210306040c0908060f04020d0f0308090106090e0606130608 75
    0x1450050f1142d40e40303ca4003845545800740d9107140300403181c05a080b0420040c0300256a4514000004040c040c54001c5d80d0446141000c000801c11010004015543c010025816000703d0101c101d0a80e800390754244443d180506c01000003d0098015844101003c1c050f114180400c04100701107923100d6219140a80d19000104601e40d007501c186010034291200c1c8914080310b041c59074144024910407202080245d01a04207111403003025240e5041e0711003500f8074070b119107040420000d80c050040500c10100c02d210b4000c410014800c0ea049144058180004d500c110b8081141007250850290440d01881c0300c2e089a14043c220611800d0b45031402c0503440381000810702080313618800c03002c01440001d5400740101d00c4005941d90b801780a100943c903942c0d581c3e20114030001480c1d04002c1c41444650030103000c050704811202c0c41806000000c02c030f900da079640f841c81650b000d924400216000340e00840c8443c02c0c0558076984d1005030202c0800d1a0359604103261602c0034085505a541058 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 916581762 1250 916580512 916580519
    0x110315060a060e0a0e0c07080f1e120423070e0114030d0221070c030305090108240405220f060c17180a02040f091a1b070302010908040b04 61
    0x200c0c100c409480300d0700c3d150341e00c0311806000c1840d06005026244030386048000184400d130350101100d150b079a0081600b44c403034040300c50060b041d40100f01407400340350100640800040f642c6041d200305d03a4070f0001c01c000c1502d881d216106c0700c0040300d0001c0103584c4001d54124101d5000c2160300c0c02800044000500b540c5409110500007110351403040c842d4008074240d14503180c1c006003030340030f100b00c0c4032100b030000040b110001c1a5100e500c10007030500411860003c03d25030400d001d001c1801081e02c3c2c440700c583d0b81c001404000601c0e0002a904844600c501c620700b0f0801c0d42c800c545c0701d51108440341007400340c00095811682c4070302089a217614101104c1c4200a102d0081f1210322200f41080324002c403101e248070250440080280c00002c40c10519907450315010020140600c0c0c000e0070401548928051000c080e10f00c03d40700340c2d140c446600c1c1040313a80c145400302070b125501e00c019050344048107180c0034050f0f40c4003000a608542d281c60340b20300890102d0000348003c200d0b1080b100d039118035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 916583012 1250 916581762 916581769
    0xf01200c150a050306011d041d01150807090209012106061106070206060112140907140901030b0402150f040e07032702122104080606220911031506 65
    0x501e94208100081d05002d202d41c860b070008150f03a041202401e01d21948440d5460404043c902c59015a50007400d00640685070620141202c41500c5580c00911040c0c3c9034011001070440c0354800c00100b980300701010802c6d100700e640a88102d000514144400004075591055020300d0388169410003650744404000d4140c0004013061154101005814039180c01803010352a604020302d0541407041850b40c2044041042d88070203c03181c1c030502e201c1d009080c586043c65544c0014056003004442c0d0760665089480e0000a05048079401001b40300d441c3d0f295401d20200000c5420340031100e4a00348143c80b000108600640003902c210702c035810440c41c001100400b40c401c0c010046481c2d200503003000c0704001481c0c1c076603c412501070710003209540100040754545000003400614414100c00a02000c6a6100081040b6040a03088946c0c98540100308032400e031a0300603584480f02d0101103410306e0329603030b081418898000e03605840000100310100f42000110242a01085100e00402c4454078 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 916584262 1250 916583012 916583029
    0x9060501170c070201140f0d140601030608032a0f010c03200304020405040c170601031b080318032a1327172d090d020f01200c 56
    0x5034030155011181c20103004440702e9114021000c1d0400a2106140034441d0130903044035a041e0030906026070b1100d03c3c1c2c1038800182a4010300907103100e18034020400d00e61007802560182e507618000b661500c0600d1001c15aa50b00c0610088120051910018035010003840aa0000c1c0744440000c92414040343c0004c04541916054517250400810310b22580d01840c0d003035a9006034151000a03d80c4c8603410b0858141826912099505c0c0101020100c0030101103030300f5040340d1080001003404000e414a4044221041c052400b40d0f5000b4001080d165001740c00071002d110028045e54004405202c0640c498120b8481d030110b1034003484040111401c02120101041c1d900c14004c0048502c9120039640105e51048600448041c0703540300e0382441000c041401e8107a8032032075869910382c032075280b114480b01c030b00404494200020100121020b41c402c00c40d01040002007004c011091141c0c03c00031f419190000031410801c0300d100c55040d04034040b00c0120040c1c00c00c802000c1c400400c1c1e0802c403610 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 916585512 1250 916584262 916584287
    0x20d0e0a080d1706041a22020f0705120c06040b100b0406030207021f02060703150e010806060a06030b0f040509030c0106060e1302040f09020705151303170403080a1109040609060501 80
    0x4c1c4e01d0f00c013404206d2103030300c51081e290703241c00c80ba10425156142c0711400f144185408826400e44009030820b40031180b2001020440d2180b0140d50400c403005050101134040ca10040f01c02d03811050004001a244001041c1d100d050308804203038281d00d9401c1c03400190000d401c5100420340c0004d1107819403608400f0200022000416100742c420a050001d40300c10000d00b5a40c2070503210348140c2d480300050959a000f81000d103107800091340e035420300c45696400075a000c4e0b0041419603c0030403004d109009200c200c800c0601040440000e0707006020003880c004004800901081c008211038030000e024800c01030a180d66180041603c3c0e2041003101e4408011140304540304001c1005048801032240c011111048001602c1d2201d6081a40c03c1c000e00252003482082c583c1c042145401d80d181c81a0301c0d80f40a0740daa20300000c0c0441c00c0c103031040d80545025020030304190004002d00203903082001c62501c085991400c03c030403034011806407003060308580510742e2030300700c144441d523488034061844 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 916586762 1250 916585512 916585519
    0x1603050106141e100903060e07090e06240d020d0b0a1a0a03060221010e0907050a06080f10080307031205070c031e021f14070f020d0e0a080d1706 64
    0x40520750000000e2100008205000341030090b1440001c0d8052403844004640000023401000050b81c5034070340781d100720300400c1455407504920f0350950780001102c40c45540050b100c50078541c42c20510f2040b40b450b00c5030782d60f8400c8a8014060068948960402040d071040310780b002c0e6400c0c4100301c0825540e40010110034880303805a560056a5a200104112500301230016a50000e1030350b003521034041c2005410480c0c2c0c804000141c011003c101c454854001c20040e07625198581d820040f06039402d100b40d000103080c00d00461400c50301c10701241c2d00b1194045801507600d0b0f0718003090b800c641152106074040740380005c204520802e503018407070340a00185030003101000c040d0b038090592807034040d401c1c001080d9113211500c424000c00494010030f0300caa00910034100c1c042c5c10b00d03014200c0c9001c407c2690094801140740300340140f00b01c40203200f0a8019108410340401c013106e6030001e021015030f0100341602d0004a60b0018001c5208003012079889080c0302851204070004208040d022600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 916588012 1250 916586762 916586779
    0xc0d0c021e1b0105031b041514161509020a2711070b09031c06150c032703080a0e1203040303050403060507030e010f05071d130203060102160305010614 67
    0x980c2c5001c503800101c00802424056269180c3d4030380341e149100c1e410406904600c0002e4080782c1d0041c0414100181c510381e80e2031a54803681c00100884c5070140301d0aa9003540480c07401003002945014043c2e040d807402d181c00080c8150f941d000201c0c4914240e10605050784011301c07089034840d5036440c444071900c400005112004020411151b0b520076040050100840100411400032081c000c4403280607003002d22070017240c0c0541342c1d400202710038070446904010002242c071003180503680c8608200d805403900f1180402c96900c4c013000060600019000e050040310100c00902d00788007400080645a4590308012801c10911150501eaa001040140d005000800010f9400302c115025294416030101c0c140d240c60005030b01918015044030220350070300000240c420f8480e8086449041c4564800114040c0045100c162700c20398030341e9540050940c0d4400d880c05a80703030000c0d5000380043c41190780c10303040c22210041000c22034008955a94641d0410060700d1800e00081c81c0c00390080b00e0410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 916589262 1250 916588012 916588033
    0x50a15050301020f03070e012007061e0f0315050301050a05010509060a230406031202010e011a0a09020f070f0539040b15130503070801020a02070e0c0d0c021e 70
    0x600001b400700d4100075a800481c505a407250070740c0382c03c3c025007258000c481c0186480090300c0b9442805414001140b41201900a021042d8451300000c080c0c0c5074040c1da00d4581c40c08a003d0305040c2d00d0503109090482c40054240c80900c00c4620540030144001110750422080000282003d0003551044540c8842807000d500178a01c00707649200c0902c040d2400c0c1130071a02080c084c3c4400c0c1d2025081c181d10341040071001d6010b410190306016010300820524107490100360030a803042042c40e800226051041c0705842c005d134000e05545406d603a01505007403603036032070707040c20000700350304459a402c1305400446010120044a014030084441c4403841742e441c0c0301860341c1c200e0218045100396100c010300f155903102d000040c402d020004000075234902802a0000040c405840381c103001c0c0c80f46980008400c1418420789100140d281e000c0c1c0750507898040c1c44680b01101400040342d64804028481182455114034214400f098001e003184052400d0404003000c030940c0a03802540001c04041d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 916590512 1250 916589262 916589287
    0x50d02010c050f03150d060b0a0906120605090f0111040602120f1218101401050f0d080d180308160908060a091a151c0b0601140d050a1505030102 64
    0x151403c0380c08441050301c81d80d480d00754000b41480300d64a95080101c0c00c0080d414007815401c02d058840d0144e03811b030700381c0b561116185c0403292a48511034034215409005000201c00c1d800c40b6800a00b84422a54840c480b9a40c0740d08440d0103a00040703241500040030041315405000c0c80400e5003901d01180d040144440c1d01089a101d8005105405421140021868100040030038010030f80001210807a940c0c180e4010000c110b0b80101814000c061400000d161410f2481d85c40400d03000790140e107440b441c42d0345503101ca800000405515a071107003800901485019003491a09000369110301e481e052000480c1c00c0342505680020401c40e8080b0305005803880001c0b42a00818983c0c00061000709505202e00c2081c03440802e441d4000c1280c0611410490056611114910490340ba10321000400c041840099070f601d4000d0001c4642400244158081c1c221382c0e0442042c40c10481c94807907200310b08000c482e0b0450310405413030754925401c0d02c804010a000d0016220581c02140b801c025140d40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 916591762 1250 916590512 916590517
    0x10f03020103110c0d081f0311062802010603030905031605120307020d050c03060105010206041208070c140f0105100b03150f09040b150a2303030408030c0703050d02010c05 76
    0x64181034581c082c1c4500c24941c3e00848412950340d005407420041c0309140145104025900f0f6103508810350700a5000040240e4620101c1c3d40c880401c492504840c001d10070280c1000d995107204070425500311182c504030340207242c02d1801c02e5000042c0d941c207514010f000e22455400540c003039889650004480b4041140b100140d0b007003290494505e1010148003403561040c1c00c0000d400082249030340d8108800060040105081101030310313203982e20bd000481e030301c03d02110f010700800c2c0b940e40d2a401040c0600080c64200f08207150942c1030429a40f1005c0c1740381c90750130608115901400301e81075103c00a100d110380126040040d854007918121201055000142281c8018180500c90780741a9480b800101c51820018040743d5492915003801c2c1860402164002c80a482c5094070040525240505a040d00c40059098042801680c11a51003054440885825100401c00410f8441042003c1c14030566240001d00003c1c0c00c510340395051000303410100d82560704107802070009a80100030b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 916593012 1250 916591762 916591769
    0xf0b010f08150406090b13020a090b0f0d1103160f20031e0a080708060d08071b0f03032021090603010e0402010816050d0c0905030d0f0215010f 63
    0x40c100d449845028002c0c0e052084080c9040d8032619042c00081c1030001c44e0410903140340c0c2101e10720301c1144140c10110a034440e00741d42e500080c585060501c101c02c48200900045005010490b0500307522048031822a42e015564404652001c03040100c800e00825000703400107c00d00c3c291911501585001e445080000c040390b402c0700702c2d0036401c28111410820303950441d14803000c160885085803010192980200d40da10005078604000500d502e0003968130f9405444041c007040c0aa9003145c41c0c0800580220b071046940c0b0b084461100d40481004895402515800d11100c408518500c2c028000d543e100300a07020220b000314517110701860105101070361106403c3d15190b21143d40d03010750054032940c14142e51000000c0f00202c1c0c02c945207510b481c4524801c1c0c1b103040e52070b1500d03c1000185114075458600048081010401058940d0002000c0c1c101606020000315101e07400642842040d07010070300080e03040081446500d60400c80d00c0703022000c0c00110000c0394142004600e592080d0b00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 916594262 1250 916593012 916593017
    0x126040f060c0309080937031401050603070e091e06010801180b07180806040605220c2c01090c03110301030b0402060703050d1404060c0f0801091113080a060f0b010f 73
    0xa445240149500c1b80c0c802098201e0008547e0301320f1000b000d25a004c40c04141d4541655018500b1140070500c1510302458008005008040c540000c001800b9801400440940220b0018601400418401c09000c101c654080d00056051000752030856542c0b00d401484021b02410b028046850700c0b01c403540120080c80c00201c280c40092041c0000d44055000f0a0188168410003007800240e07407025028001050704084814140000d2007541000028054490640c0507410048000307035007c00340760b01e45100800e800000b0401103428074003500364001c13030780d45449445286013103a251242e075028603142401c09066504584413401c010714003c00007802038100242c210103140c010415030f101e00403890030a00c40084920760400036028182c60840700c0501341540090391901854000340d144216a956941c56842c0004035400f80c0300700b41401c03400c41c5040040fa10700654142510014000f0b00005041000301440c0c0042260203c1318081a554900780c1c504046a0b44600c20010003156403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 916595512 1250 916594262 916594279
    0x8090603060d020d030e1008071d03013e0418020f0f0a0c0209090d1b0c09060312170403120b0a1e03140606030304050126040f060c03090809 62
    0x480c2c42a6a200d4020f0750148a0809070005c040d072080300698440f1054880440707001c01c1003025a5030790001e548070f1001c241c4c01c810603070f4002251212032091203c02400407503e460100c0e1401d00c1000810020b030358007603102c40c2c04d002d0040d507040b41301c81c0c8040c24145503141500d081c01e592070b402d0300081c0000145800041c0810003158042c04c0c2c5640c0801760122070382d50820140041d0511004400032406110308400107500b6060200703000d65070078034545964840070100e02106090108103e0100c07074150180801150010162041501441c0b00d14580f2044000034800500444140c01d800c05ca0261381808000010758480846003600d90303800030100f0300c1010135000880c0c0d0145d6801c000141e0a100410060700c2181001c08030450f80038601071000a00c141c0c80c407945a02c011105140c040e881000204000e51003024101070800941d2051a07014211100101c19001c0a660560749651040c64100601c0b50710320a02c40481080c4c01c04000368481c9540c0c083c00307401024030952090f20700c0b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 916596762 1250 916595512 916595521
    0x30d0e100302121806160e0d0206130e1b0a0c1707022d040e0604030c022403040c0509190e0a020d0501090c06090b040e0411060a0309030f02010908090603 68
    0x70b40c0558070808600e0f18000c030039142c080146522540400c0344860305106003c086a0001c414120307482c0d850f8001d90350740140c1801a07080c4552100342c400708980240c01046401423040140e171191002d450846c50941041c00d050321a20315201441509001d01c1d40104108a400c0e42c114002d840c00c554482d040c4282410b95a000d40c540d4060008060f4001041401402c40422101803c65180c101004130440c03c150034414002101c02505c0045000d60000740400e001c0390103141c1403000c07a880203040c0c500c500040031000030803002c0c40441a03080d0102006106c10040720008020107018103680c01103ea20b003054600303101c60711086042200c603070f5560441800040920940c80640e0b005801ca002140ca04d1800310700a1a40302000d0b621003200040100d6510f1140500703000302d440100c0024141414142038844c0490050411114100d18056900f41e980b10784001d03000494658500284105c541e0601400c6500301c08450001c40e4544154a0b00160101064410000040c2c0f070390360300c2c0d94030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 916598012 1250 916596762 916596767
    0x1110702090606030709090f0b12070504050705090306040204020c01270209070c03050a0c03050c010e030d060e0c190210051914070507081b01050408030901060f0e130c0315020414030d0e10 83
    0x18160f042c241c200490ad2a00f40c07a9101c0007035124111902a40c041100782e0301c0107011101c0f8000c403012654076811040c040ba015240c260007800d1000f822000006500c6060a009813071a5601c200c2d0030710080b0b099a4210961811a403800e603c80b089044c202c0c0c4106240d2341c010010321500c4203400038489403a95940515100701c0591301c903041008000c102c1e40074600c22481e070340d0300b00c405440c0f081418000017040e0911a0034086000390740d048001810009000840c3c2c00311103039562807100b14420740084014247c2e107409024010308408500c111001440b41505090742d0500d014030540700e0007a000d12030001e0b070000803034001b20b40010006803a20039405e204d1008031441c1103003900560038142400144605940250300804040000f08829a40c824820034007001c0b5120f8151224206000644071a18903240e44001e240f0821070104104e89955410305c940011414404020340e0105080c0034031a84a541c0044606084000300f4001c10110801010329041d202914015680402a0301c0b2450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 916599262 1250 916598012 916598021
    0x5190c080315030106170c060d0b060a090e0a1a010c2901060216030201021f090b01030b0a0f0605090a0e1009120f05180f060c01110702090606030709090f 68
    0x5038016a0386960b03081001c0140b5559040d007a8051003546004800100b03410710041504015415502500c507500e80c013030410410750400c0041c2c990b2591a4290b180c800c1d07807804002c045000f100e888510b074844c00c2413504c0990390386c0104895001c902c0d1403088095200107515140704c20b2024600110688400e02d42150340b40e81038006040c0d2058050708c00300040b900c1041c81c1e41a9441c0354200c81070a0f0708000c0c180e00380c410387d00c406405600144400b40815101c00144c41c10781c2403001000c01c0ca1007155840e902c0840003640140d504458007001c1c41410007483c040e0500400c070303455041c0461810100019404540030704a483d2807603441ba21a41c002ca41030101c440019103031502007200c083e0b281440603500382100480c0c00000c80003400c2c0c09195015605450b41101d0540303285a143c55a1814000032034001c031116a4820800e1104042d0030500b4060950340120007041507480302e00030310502c00042800ba120318802c220a02c00c102805500c004103101b1070b5000c01c0c01150721102c4512420040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 916600512 1250 916599262 916599287
    0x4060f0b0a290d090512131a07020d0c0302150906190309020306010e0a14190908091c0507060525021f0c0311060105061b03040b04150801150519 64
    0x2100040f9035000c03a021941d1118650f41d00840c1581d40015200021402030703c91280c0b10050811400e105210303010500100e40c0d03829040748816813a001c44c0c0d8001460114481c4000c94a840c8451018400c41c05c100c1003003007017003802c0080389040200b40c2d000650301d4025904407498a50300c0400e64081d441c0b00350410304d0b0300d070b4000d8180d504070758440108611040003203038a01102400c007006020a031042001862107024131200984846d4001c0660b0009040002411740d401c01c001c0c80b2581613030f91261100000d0451003070100f1403234001483d0060514040b503111000f400070034013100d000040344082d1541d04441070201104040058400210542d112504c00c50781501507418880c08640c11084181c040c5000e03071504e117440504502c0e51603803001c0c01d005030341c0c000c0001d1142489110f0040000040c882c00038040e070382459240c042c0811140c1190f03210407101d40356088440200c40c0c101181e240540301c020041d41414141c44405000c510030420040320080c0d85101089180380300d0709042102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 916601762 1250 916600512 916600589
    0x5160206070c0f0b0c0c03060105011b02031c0908010b040b01020303040201120e01050a020a021504050304181b182907030e030a05061b090915032404060f0b0a 70
    0x83c1c0d1280c00c400c0050b000f0300a8000c8030711030030301c101c116032030005200c0d4100c540580d00c41a0030050f0900d014803070f20b0600c90498152099000710402030a080c2d01d010140b180a594215940703140140751703070950f408440c40c02e005a01e450035885045e603000c030489510580a09010325202c004c1d44984006102e01041000c1c5946400c3c1880b007422065001812200120b600b00d4440f001c4020a061004d10203640c01032403035008000800c02a05400300c1120400d036100310000301c201c107040600e05410b21800d19070380020080e42e0190b0301d6020052400e00a06403804081d4843d82100e40c14100e182d0a5901c80c190081011039541b040511501003d010030070080c040d00c2c4808044e00d050355079200181d6050b0350102003099611508200c081c281c0313120120081208140342c4850260105140d5403007039040d05802050f450fa259140480312102c1321885101041c0310614090130540c0482c0c008034020081d083c01c000e400240713603882110000c191032a0035052521843c0b1030903040c001c0d449088000e042d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 916603012 1250 916601762 916601789
    0x1407030b192405040902070c2d090b0d0c0323030309100b27010f170c040b030712031106070c0f06050925050931081e0c070605160206070c 61
    0x4000d0141440011103411700140070070743c1040d07090921003aa004954a41c5100702c844100701f28049504030303150104c003340c0301042d180100d44929450b80c009130400c3d2410004100a01e40060a070344424100c0085003019500b5400c0075540b26468941c00314001d4501900c03848440e038540c0e00e0b940d40840400d841c0c80c481e6401d0140c0f200c1e02c840140b09115610180c5064180020307591282c9072a40007962580015180e0f01c00a0b108102c000c0018241d010381600c20410080764101f0080d541e08400f034043d884140030042d94241c11071400d600200748204200c45d541c81600001c2d00b4010a0b00320950012003c00d107a40c03215010340c60649034980000108100c42454240031041c4540003040e95810b0783d03051156544d001e00d0001d5100344454801c008280028007941e81e5198905406c2410300c00e0b007002e880d0070701d140c005003c2d248001e0a0f190820700002032020541c001000544004d100c50b042060078162884800c1520601c24500a4010700c8001500000c005074840c04038061324080302e00d01e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 916604262 1250 916603012 916603027
    0x20a090c020a0302010b062b0b03010e100f0606080106050309151005010305061c080a05040801020d051f060f030f1b180b12060111011407030b192405040902 69
    0x1c2d80c8540b100303420360155103420070b00515428200b0888210b007891848901c2ca00c0c01100070082400c80492002d1031891f51040e07055080d60b401c0c05041c155070029001814500031010000003110000e41c0c102040c10b2504c03004012558005000c91304443c0d40e81003864407076545000150800004c202c0304101303190403c0c10400c0307000148102e407043e00c0c000c2e80d003003200755030b50002d02c100c1024015201c100034172109290300000340d000f002401c0c00403852400908080d5565211401c1e40c008a12503d01302c2d80303510030001c02900d000c042ca020004410000e103c640d18100c03000e403c0d40094a842010141c585122000300f0000b030f0000300328109416000328291040302c3d401011038502c012034250400e083e500004051400702c3c15203800c0751102c8034010007030f100d040054407285900c8070200040d5403150480344014846a26081c802c031025200030031420381c50010040000ca07030b520403003008128040d0a02c02c0500f51102c902580400b0180d110101c151400300741c889002d00d07449980307130900014491 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 916605512 1250 916604262 916604267
    0x3071a0106030f0501080a0206090105160f1103010b010804060b19080307050f0703080a052b090b060102010e1902010e101e14070b0408090a08060613090b0112020a090c 74
    0x2903048800c41e6600304018044555144140c450070300c506c104c40c0e40046422009407a044e8014064000141002841c0030300b0312450f1015002a03407c140c82140c0403607102c1f41404141101454910001c800800020001c1030020b841c4240c00341c00504199030f80da00c440c45a80740c00308000e100c1c000c0440c0301d00d01c1c04d03600c0790181e5803a8803070001103070a8091506020700f004400aa5842030300d500c50411420718980d1340d4216200e80004403038604444103402900d46050001142d401e00303500c14840450707421036905010041440c0038010a0441e854140030480d070300b80c04140003401a2540a4188103240d041c001224000312924506604c002440000364441d500900303001e449045c0008a0385000e50b0040c42a298024520982c0c449441300700f12150001c0d0490f618180c0c0030384110440390400010501050740303014950822030041d4402000d11000c0d2501c40a00c1000f80c0103c03005021038560307a92030244001d81131040c0199600c0148542c01150358a811640103003201d00c400b00000410440c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 916606762 1250 916605512 916605563
    0x708030405070806040b0f1b0301090c03060509010621060312020f011a091f08010c0c02130e030417010b041a0f120d0c05150a0b011407020108010608090307 69
    0xc031414442c02c04001a0a100801c01d50302c51908000d0641c0c00d5500c0c4001d10011180051103882c00d001c0003040920780a040101460191202000009400407020009403c0320364a0b000039103c0e592440c0100702150b0710880400b1000c1e44800e4400643d11715088542c060f080f076800042005100e004492682540012400340402c80800280030701e2004001e4010f02d442901180e41e002903030a80028611401c007042c1d030054035403140c2c00c14140303a41d40449034216050000c1c0c181c00a1a1200c0003029850a403554090021911508125028200c101680d0701d02c00c91140e102d1034000c0320f50b0b030903001c0c3c4c0130f50210b0000300d0041c000740420005208801d01c030540045035207108050703105000ba80c07428518001c2c445001114024400f0103070002c4141c2d082c03000d4101c112aa481003640030741040c6108442c460081d01441400b15442905d0b50001d4014562200c0d0380c02d81d0002440180c000d40ea10649040c11030300c1a0501859580f00c00c50014218814858081c01c102034202c48450746001c040c40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 916608012 1250 916606762 916606771
    0x10030b090703020304030c0b070c12030f0e0f0712033e06042a0314070e06062508091207140d0c260609060a11070206032406070803 58
    0x446480e20364036440260200d000036240680040c9206c20b814000405400b0f01d6030f001030888c140b04d040303d501952001c1c2101c2400040c1000a070b01c54000c02e200302a24018492800001005814002e0410400681c1c405480c810b55103820740c100c0003003003818010480c582c01040c1d03401d20710340305c0c035034000c0302030f03903007000320b50303c2a5444140000c0e80019240420820302941e0b0044041041d040c4545e200c1c08110b0701101702c894010080351000001403c1d082013401c20303400c0034002e49042403401080075000400140698040c520820448451600310001c10701d401804880c05442c540550404410902424441f541c00465002410302403010004502d011078075aa032000000794050790600c60f01c43c0800303000900001000e9404c1c00242003080044494001d0140d884031601803080322941303007100c140c0340c0d00d019030450400d002034525180a08a064142e4108040c40d000703035540820341501c030003000040d50f030940e42e1804403070100141100c0380004004003415210400c1d42008486a4001d88 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 916609262 1250 916608012 916608019
    0x3010303030b03070b0708030f07030b0301020d24260327040c05090a060309021807080709050301090c09050613020c010b0906040903020d050d0609050432030a0e0102030910030b 78
    0x120001600712804d1708540086038003c1072242591108402e100003c400903000d9400c1c90303160700c0815110f40b02440680104980c8040216101c11501b071a1014165003507503604604510386001d00c43d03502c80d0051203054440000b04120202500b510b800d04500806840c01c0ea01d05082c01644481d00140e80210581101181e0412014441c2001561b0784d1042010b8550001040746003000407034081c0d80500141c0703001805c0c03c200800c0a03262007502140446040e40802d0000741400300650b4031640c0b40c0003610081d802086040519181e66200c100c1600c100d4071019110f400040460b240d07001560082c01c2d50140c159114101c01c2051806080e0719401c0902460201c00080c00703070724190041d640c1c1c0c15090703005466400c10746401102d2035840291000402c2e40c035840e000910304011700c00c5920880c01601c104142ca00418140d0f0000e44400a06294844801d050f00182000100c1212240c9003e0308061041000302d01c0140d055009001d0440d501c540101c05462241d034254000041198044 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 916610512 1250 916609262 916609273
    0xe0103050d030c120e0717150f0411120319050c0d1803170408030a080a111e1e040b030a110406050d0506150a030f0b0307083003010303030b03 63
    0x290411411030b0303003c0e10198001141c0400b10941c062141d4492840c2c8003417401600c00e4641c54511442e066501c0112407504c80c1d101c1c0b070100c002c9060001c0c0168001a40202c818050b05090319002017030300c10701110794070a0601d0b81d0098141c01d801c1040341c850000841680089252503540680241c000c13040c00417182c041c0940f00c043c6a0703c24060281031406410a91400c1425610f4120801003880100c0728080001c11012070040c00070805809034808c60750700c0104a14112118030192003000d14803041c1c441003070010300f00068000c80c1020310703400c52000e829281c58070b4031340b94042150b01521408080d4400030340820b1031074111000390f01c5582a11002d010710000c0302e00d1001d00c0d00c1240b090740000b0700c041c0040015403100c1d800c1203800200c0204900002000c120112400c0c0e030001e4403a80c04a540c640060002a40901545036401d508a010b0300c3c00714942907046807603510705082100c0c1a4054061259290b104a582448056400b4016034803503849240140041c04080300c018864401d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 916611762 1250 916610512 916610533
    0xf1b060906071101020c060d1b0c1a0402031c021606090b03190b04060902030a1505101107090501030b04030305240f04061a0d0e0303150d05010902030303010e010305 73
    0x480840c0d2451601901003440c021050b200c04024841501059045019441d8103809580e1160081e12410130030410000c0d841042001005407076041c1d80d0560180300303004c4803031070206605260048001c014140c100703560b40d03030703500c00203061010b2000d00e04c443d003004d8100340071801d50014001c441240301810311061151510400d0340c1d10410b80c0315031220180100000b0b400c2c00c61714a450a0b900035684c0380441c0646403400000c090319116001401c0040e2301008000342c00b1000e010b0700c0e0700f00c2980c819000607641441c010a240c610040001003d01c0f0095007009103104003045050000e0140281c01c0211756100d02d46881480c0d0155000d40000c0e080c0008180c190003604401800c00892442603001d6903410402e000e001c0010450313240c1c0c0240c2d5600002165000311400c5491130800c44101a502c442e070a80d241c0440c1d070b000b03a12000540c428030400031000130761849040e0007a0116141c1d198107041c1e10b010b601410590000a41500021000140d0402181c041c00d040c1c0384075800392401c2c0c03480d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 916613012 1250 916611762 916611769
    0xa0c0305150a03200904061a0f010f14130e0f0906070e010e011e02010605030f030c030405040528020901120b0a060f02031b0312130b0610050403050f1b 67
    0x490075505034050820001040024070385060486915201c1c0b8200c40c000341c1c90000250080021501900c015807220710000d40040743c04030001035140100c808582c80c034185800200464021800300041c002d0914291b4200007004054451188007091240795582c1c490a000f40741000584c1e2000746c800350b51000ca4030407800841c40a2203200d0682c1c0d05000040003200448800c0011310300d5906000064500c107244040307084c1f92021181e1240c00100300305151005261800d0020403104071a60400d2051342d1400001004032021501c04403030106450311070740181008101e2720901000005410145284986956000b80030452800d8841d00c1400c014010007400707603101408802c1c1d0082e014030003840740c9400340030184101c80407841280d003040d00402024601d5015503103405404d034804140e526282c07894028003684038a494007800038200540d070b100540060302600c20341c41032000140d44414944507009640045410900b01c68240e106981c8854458680803400c0c104c40b554110522107904 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 916614262 1250 916613012 916613041
    0xc1d07051b010f1506080c0f0a030f15030b06030a11300d180806070c0501020c070f0f060302130b09030c0d1b050301020a050a0e190620010b0a12030e06030a0c0305 72
    0x4860364804d4a062385a07a1a04220745c0040084c406065950074151004031151060141c80000310700c03610340c1c46040d410005510b0f02e0060906220390700100d4070704002180455031607680002603e074034048034400310201c4009070155000c000512030039000c0c12003c4000040c01200300400741c5600d0780d046028606640d909042c0d020340b41d91540b0400104030890303c5100d9448c04280100700050409840c8400c0d01d041030b025920006c90148501c00500814441c00302d4140100a035060851070014100c29034284114588030b95180300101164a0105441c00c1c404016001401403010850401c0f51600c0144c1a01c0c030f00007000c45030080311000c90242814401c036a008051501c4070f50409491041c21200051a10981030b0441440084504844015907604000e8501078031820544176040600e410f000100050038801a810f010740c09850740c40c1c15041d03c1c107403585901c80c05a491201d04090b681c250a11001b960010400000c006119a03154400040d80c0f2042d03034140b0140c1c071440101800f20303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 916615512 1250 916614262 916614271
    0x150609060e01051923040305150721020c0105101806260109080d0c0206070e010e0d080c06070201061a030402090c03040c210c1d07051b010f150608 65
    0x3d0390421421036081c90080013540b070100e41c0d24140204031108100c5420194601483d2590114041070500c00c100d01440f1405c0502c06044895a251815200081185000018911000407c40030064006a10307804440c7d10074030850080c4224146444054110400d610482005400010031540c070007956010310001c82c0c8a460000d5155a02c801c0210400800d2600c1005290759032000230000070350101c00b0300032040c09803d00058411010034081c2c01c00a0080c0720008012103c0060111aa0422000c001c4003000744c40d0910150b9152a140180c1c0c0300382c00d546c0407288944000c03c424245d05400031010b8400d40c0029080b482c104081c4802c0c107000c15500258003102140000341c400c1103100c041c50b88a4028018010056521a0010740b182c1d20010450b1280b41c415030840240614000c009000304104912500301000c42d0815207030b1864040c0113101000b000080d0724010901c100c4519048107840e40081020185408249008111500d201041c0038000c0c0d00004100b40642801d1340325 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 916616762 1250 916615512 916615517
    0x120f0103020a060221030c1204050a02090f07090605030a0902031e0f1902040b0303071211060c031501082a27030304031b0e040b04030212181210150609060e01 70
    0x14042503c480c0564100824102c807141f01030008004860304600018011406a0084c0401c805180140800c5150042800481512032400e03c01e250740e0117849a411035900d4544070382c0303030303190308004a000e810200c202a5045c4101c00c026040e082c0034201117a8a030405904941c29400c5040c44140c881034a4100c00030024416500e10f0301605050300700c0403401000400344c0b460404a527813031120703042e4100541d03000142c101c402c0044250042090300e03040000c651507141580381030400d2061803c00180c01d1410002c0710000700d02141c01136040044080b450203003100c0180000c14018a072038008200382c1d219085c15210555241074038224410036500c000c0c010350714242c1541c0340d5052034580324640001550801c180014a9034000090b02c1c003591151039910075604290400a1400310440109500b60b041007241d6071032960108000004441e041da0522240600c159079541000340c4040b800c0d4030517050041040c4806024480c00c0c0607a60651584003009071142e804070384251000210030301 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 916618012 1250 916616762 916616803
    0x603070614030912040803041d0f0c0705120f0a021606092c3909040905120315100503163e010f050402060a08040206120f0103020a0602 60
    0x80d40314101d00216400440001101c5400e8030011302c03401c41d0317445503100710000d403c0400d00713000c2040e03014006480c0305000d25500e007803801c01c03006843c0750312809400c40d40320002c0080e0480c00c200d070030301c40302c03141c2e01e0a65415a140e448070002c84500d44e000404e59401806461130509542d4540000c0300103443c010f542c1c4070401418100080308542e80e14002991803885030030407034000c8225040861003020b0080048180748101a40c4407844007008841109030822001d844480304501001c7d0355642c3c10442d004540743c540c0341003035030810b01485070302a9441c1c0300008100910f43c0242c42c80042d900241d0300ca004032850301000311030501080d180c014544102c0000e10602c10b20441c1c1d00c07840300b19500521190040e000c41c001da1001c004c0890031582c0c0010480181107908284505100e004c071810b0180490714095002580f64403d400e9040140201e2001060540d260790003038580d040a4084001e410303090180703492126135001d101c01c0780302c1e1604590101d041c0384089004046009020700094 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 916619262 1250 916618012 916618037
    0x612070f060516050d1e02010c0c0219090926040e0402040f0605030a051006080d02030f03040f020901080c0406090e2d0a080c070902250f0605010b1206030706 70
    0xc0b02c070340c8100d0410340500440592800400d1050042205c50011134550051808154842407000070340003130b00c0800d5915007440f0001c03080d00300c8003540c50f00340e0407a580510070210344491421081e0a800183d1340d00d141240e01010800281003881031007501d890303282c1550404200000980c03080d07004807103080b401c0744040350041c10715400c040381150343c0d0100484c8481d110400700b89030010310001035900341d2108042c0d1560803861310036200a0b04518028080c0103291500c06540e0303114103640c640020200200003000d0000c420f00e504400c540c014001452965a503c0240d0b8581c40c9103101c5200b280303008400280c10300c007172040c3d074a880000000752115165042d03102e62402803000c2c491582c80112501440f4101c018001c0d594900e10914504d82c4a0f545886204d1a090442c1c22007401c661040001c400d507200058410400c0d501c03000140502182d083c07805001003a900c0000500507414076001040401a01c03000d052600c00d00c10308030000f65151010580c0c4ca101c14803420000c1512010200d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 916620512 1250 916619262 916619267
    0x4060b031b031308030c0702010915050406210203010602340302090601020f030a0504030b1e2a040306020702132007050c030d020a02130c020c0d020f0901030b0612070f06 75
    0x443d885056540c141405020719201e1100381d0b03104640e240740c20840050700d84110768009100304c001d4407405501070000407200001900034400c40c0105c0c020301c807500c40540d4801c800e03031041c80d441100341d02040d5101c0d6580c540c082d5803461215004e42c80d2104421007240320400301c003149411032009072407020f038040c0385400b440441c0002801190440c00ba964060b250080c0400003030441e0001ea40d40c10f6941d07841d504003581130081c00707002c0303402580998001c070620f0b14200c50000d4004c110048080591917041061404000e4000140c2c02010700c0494000103000c180d5028084042c007d4940c10324880804039001d0403aaa00d0000e0003074420070005040204a000014021b180e208604991a8140c407030f000a18182155680800580c1314180080460030800c0401311041c15964003400000044800a902d618401650f00c0c09501280042c0081d991200400c802c0c02c00c01401c80841c55840c2c0c18522491241110b600d801010491484013000303100180a0702150180d00340011050300b488400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 916621762 1250 916620512 916620517
    0xa031e020c0924030a0b090706020a05100b0d0b0c0301091802031b04021c020703021908090405152701060e060f0918090304080606060c1c0203040807120204060b031b 73
    0x1811151940f0901207665503c00f00f1580450030300808441c412403070304006103481c2000c250400402c64010301184000128002074101136007481e84004114001d04501040c803000640310054141c075081c3e42840582d280780c00c000c505030b0b03203210b006202e0f211601c01596041110020001d415501415542484180c15000003011010050000d40340170300d44145881c00d00b603a808800c2c40b0315400a001401c1540410480420108100243c03c0030b4000b9119082a13000354160706010f183c450340010400b403807901c46108840002000010805407078050101b4084070450054a644400400400e6003802002d561a0008008040c50300d40010350120121640080b0f001c00d8000700009074620042109104040c030912482d8011031b1190b190040a900d84000944124010881040303003d043da80c0100e03000c20352115807031142c00c221040c0d82c82203107140715a90041101e03000e41100412240c0340580102c490301c3c0220307414000d0a44a40c01741c0c4141c441a5075540c0400c280603180300885460001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 916623012 1250 916621762 916621801
    0x71a0606120c1b07051002210f0409020f03151210020f0c030a12061406030a0b0f120106061202040e2707030b070813052107050a031e020c09 62
    0x3803050a21a20107240f1004010f0728039200d4443c0c110700700c1030081d030038140c10030549420305200505481084042e2130a9129180b0b512a40079400010402034400e020005c030340c000c01e00510708541d11090440031036070720f03001074614212a02e4a801294910f141c083e0110034000020b4016080c00406030303a02c0002580102c1c02c200c0c14510500407594414428000340190009644421102c1d01c450b00703544080305c00c0360f00601d800341005282031059444031420781c0d50000140701e00160071000f00d40050416070343c4403038295205040308483c462621040d004002161007940f9100040c0d0b44032031a80c001d80c0184e00440c04130005490004400702215450041e03100c40d94406400580800035416081412640042e190501d001e002c4c81120b585c00020315034400c400184600c03000c04150364860f110a0404400c1c02e020085101809198204030129036215901004690024102d46130150a01c4403034100c100440454001c0412011700206d580c00c20031200a112120740c1d41c03031350904044082e1014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 916624262 1250 916623012 916623031
    0x70c0c080a060e06090a080403020405040206090a031b06051602090705130303080601260606030a0f050115020f07210807120903020f0303070c0311030a0c0605071a060612 75
    0x44005944501444109207003401400003060203444454a5031908402925a034519031041002e00c002c22281000c0d00d0640e80d04070b90102e00740e01c580c000500a8043d0030402c03075001040610010400840005020302088480501c94040355108025078150180c620312804c1c050425040400614080c120341e640540642001403d29400840c1c4a01c114425001103000c914102d082c404c0d1503800840c10705200750035180101c408030808c0c00040c02ca8001425890007071a000c00440c440340803603080300d00103000e00c200811842d80d44114605081c241d00394484050700890004401c515008200c5da020f03166844200c010141212045600c541d610380c0041d030341c1c05404d1052400203001d000d40c850302c2c410706564060010b81180108100e00c01403941c2c40b0b220750700420030600010007070300c030075000c51350171002c811403000580000c2802d0030340144008120000055010403900d030003502605085019071070003100c0d250544642008a0000c0e02d003a54001e0040c040703c040c4802601c505030b031045604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 916625512 1250 916624262 916624283
    0x10323040c120302060a0b09040213110c010905030d0614032107080c010c111617010e01050907060908010204050a1211040507020309032b0c0602070b040f12080c03070c 74
    0x908a100b02c1c1c0390710000880050708031905000803001a40650000c0402c1102c404820b82050b9000864040b91690b80100c2e00e40c5403031000800ca02e070001554000314500d802405024034a2410640700e510464280d503140c0d03d0300c40c01003628112810707800784061014000b810080b43c503ca40d0f4034500c00c208080c0318031460401c04070740050b020101810014100c940080b030b500094031406040f680c00501480c0e00e07075000006042411090390100310454000603031031000c10300d0441125015100090b291607103503007005d09100c03044030001a088116901e542e40c100c0c403241c0b0f400d002d60a0303104a10440e40c4c840ea00040620001c0c200c05c01032041d80388503c8030702d241c00c076608010800780d400840308800580c0000c21545174600f01442580c494909002034414210506415072441e80507886040003001852540e10701081150341c1120f154940001200b00c10745014a08401740b1101580c04503903002d03541213801181801380483c0c0b40a0b821041c05a42123035030761041180d0b00c113840c4000b540c2103c0b51 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 916626762 1250 916625512 916625519
    0x53012040e0424020a02010c0804030203041202030a0f0b061e03060403120e0607260f1501020307080301080705042304110d06091b060c0c050139030e010323040c 71
    0x202c0703e0a0b00004001c2c40c0250b01c035884150b02a0848001c2107541080c00361400802000a40c04011201910080001c41540950a0010914160006d000100400d104c1044041804608280c013803040e035080720044402c143e02060340d00c99625801c2441d4160780710401240001e8000d000c0f84416100100300040d078032801c280442d151040503500603001c62040c680101d80c40010032150401940b0f0000011007508240000d8541000001c040d412258821400449268820b0044130f510074ac010100a4032545c40d0110301c0d450b0481449000c0c0718034501035500c50321b00742c8210a82006000d0301c2d00350303400e41e4a41e01d4850602014001c091360100306100312000081843c8201000580944203001588034910204200300c0980d80001050044c1c105a407070004000010500035140e0a1030304861a0b40083c0303880f0400104108240f112051802a169000001502d11b0a040e4080d40d500613014003c2c000540850790031086951015040d80c0700000c4407000001c0c0d1300c0e0868845d1150700c07402aa03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 916628012 1250 916626762 916626803
    0x604081f0e032206050c0a081e040801140703051e0c0d15050f090c190210230f3702040b030108010e01110d15053012040e04 55
    0x108516446010201003c1400807440d4107038401c3c041d01072800c20303d1800c0349007030801307580b56004c1c0d000800100d0000303100d800b105025007041c681c03c42c40480690f1160348510001c1d000c1c0c4130801d04c0640740e8030000e0000c0c0801e80f0a0061034041d014011403250140740c4500314540390600100080920903082200c812440410301c01c20107458000401042624105420803440d0301134144421700c519510030500001ca8244422282021340c905040310850075500400c1e8106102d05d0700810301c1514140311600c1480501c1d960101c13070000c500c0001c1150b075940d05400c070048001d4501580743c040e802c040c40c88000071951811079030340181c4480c80c0d10032280f40b184000d981c0f083d0031910000e02d0200c010017840600f40513803d1401c020300000d2203000c04039240304000d4014002945503250303d5280c00380c0141c4041001700d01815000d000e4409115a01003448014170030707260440c0e4520130b40d1710030311210341c0081204503a560f0f0081040349801e01c6c0c5803184c1c0c080f076005402500e03584d208100b202094003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 916629262 1250 916628012 916628017
    0x2100e030d0e01030e0f0712060b030a030507020118030b061302070804170f0a080a120902030f03032e050d05030c0f0714090709030b0a141806060604081f0e03 70
    0x60303007541e80c00c42c80b1940a00050950707503440d15507040e0f544052030140100d0804116003003a14071000c14860300a95a003400d0707015080104001e60035025102a4109142c2c0c044000e10906000380c8410102d800a40d200ba00d088007984400f905102c043c00c04210107240005642800b150b45020142c109480754541c14050b074016844a400500e1035965442a03000510090b40c45002e001e029000c02c9246854402040c03080000d08001c02411800d00340021038141d10804034941c02400710391210f01c0d103030044c960f00e5106491441080d5050f00141134006164030542030300e000224100f03001c031840d00050200070800842d0480e003e01042c09103420220040000c50920740110009041280c41c1000c2e2200d4410804040d034040d0108070100300c200e90308038582c08110384e40903246030b0b80341d6142d28816009044c400c1e0500602900d1b01300b030001c459010000c40039134992000994606481e03840810009203d644208501c0d43c2085849603480039040442402c61400604081954081c03011481e00f1507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 916630512 1250 916629262 916629283
    0x5060d0f060f03030f0519031d1005071b02010e330901030f0b0105071103100c050c1903080c031e0718090e07090b0d02090c0417030f0702100e03 64
    0x540814034100705055001c0400c801700c0c3c0321070500524160b211300e160f100c0980300881c500c0505881d00c0c64140310407425040c900c40c4541e45030079103a5400318520b401d030180c175040e58000001640c41116541c0c040c031a940c03907200b20781e05846001d4000d11540034000ca06030303401401001200c401ea0343c854410207030401242a0035030000704c542c0d00c4030714030009002c807905049038146180c03030324038901f07040d90300300b0102c41906400c264260140d0004500203460015952758030001030b400c0c000200081c1380c01c6000741003204e6054060b220400c28402c0d0342c4402151009010f0001b5424001054108465030f00443d00100044582c0361410038500c0c1c0d0b4000f00f541039600b0070001d5003a50b444160121010146009840d0880c02803000d00d43d40b00d041e030b544e4042c40c00395110180d0fa070103071412030b43d65510301c005113554040c02a40003807a090007042104e4002e48140d40c442103441c90690421130000c401c8035042541c41400c2d504001d020380030b00041c500300c040c01d20144403101c8080d001c60354040201a000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 916631762 1250 916630512 916630529
    0x3060f120807022e09030b04020d06060f120309050418031101090c060806040c02010c080c0a050904320606040e09030c01090b1602030c120a0203070c0906030c120c05060d0f06 77
    0x1458042c0c200103040e244e000811000c00500f0078041c00024000e1039204e070411380450b0b088188404074100140280259400044d03400c0c0e081d900020800b0625103d82c1c950380c007944500d084503644406010648684040007030f2100c03201c0399800e000a008411640e0001c1d0340c1800011028090b40d40c0a520b04141d0700b184c400f003100d020401109150500034200010710501c003d001c903500a100c0078000900103030038002d0940000c80c6481d0303118821015a03102100c01071082c0603582010750080340214421038400d00b01180e1043c00c48a4102c0e000e00a401403c0223042c05252900c2d00b415907069a20141995011b400200550184403c0c2400303000000c5004802c10a1503040440c1105070080700d1041100664000b80700600c4d541c8808075802c40c810a8001c0e10590303d048600e07049007148100754004045601c1c031900480e0590b95a4000000e980c4150706030039074251127800090164170201c1008009440c1c004041c44641800c40c064901c4509541c0d0214048050000b03031000d0316102d401c0a0301 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 916633012 1250 916631762 916631809
    0x409021b0a11041d0c060309012a020607050c070b070c0801090308060f15030604050a0e160e060105030405030a0c0204390309050714061b0102120703060f12080702 72
    0x49610301031051842e200022920144002581c4e4001d40c1c864018184d030340e101e8080400041d250aa080d0000c2e07500d2440081c2d020042c4451070340c6000041c10000703243c8014890000001c03001d0380503000701e445010484004004e8280f030300030f06007015401007004a801c842418400075025500340560302019120b920f0351038036072421509002c100c43d420b1590610800d441d104890341070031a001182d81015094038042141d0380e03240101e0014020300405044203100d0805083d018507000c06202c070959011007200d44041d04e50800441d00382c0415500680582c00403c0100b4000740140342c060703003035440500003090042050710307021211a00030102a05042c401e20750030301040442440c01ca6a014582401c1040b11015110b043c0d0b9680a0f0007280383c100b81c0c0c120700440560f20318050316403007084600c2c1c200c49400c14640c010302170340208200f0000c0d9a00c1c080880d80c12800790180c28142c0d850f00e101d02c0001d0b0710b42111481c1051250a054408850400030030015880d4901801d854241064940c038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 916634262 1250 916633012 916633043
    0x120206060114031b031b0720150409052505040905090a030e371e06050d110c01020c0706021006030c03030c02011803060618110409021b0a 61
    0x601d18007a6a8269000c032000700f0400a155600c1010f4040d0315070a00c01541d240e6840300030031a00100c0c842c1c400102080f0201e600020040e60300a02e802c84011245000844000c1509010216014070086540c03d403047c801841101807580c803242c2c0c03101150b460720310710ba8500e00207020304030761559900380003510014091106007034034000c440d000303910080208240e49803514004d040410b0b141010344120312601e1100010385c51032005000003401c1d0f81c41e40c40080310322a5031102040d868452180e03012a0b442c4000303d142c0c0b4070416901100c0023511810700d00b00c0b0140f420030081c100550b400071000d0050010f041410024805030a40104500060100509244001c3d00d80401c120000f86680e0500d6410300000b42c0c802e04000c1102d52500f0b00180c106128401603810680c0140003445e030000c003070707070003c2440702a0304408201c0e5182600c01500c00741c201405015201120307486505244100010030080000784d00425551000203445584200c080540f41d00b082d41d080d10650f091000280c105 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 916635512 1250 916634262 916634267
    0x3091c0323180c0607030e060f0f03010314060411060a14040308070605180709271203110c19050f060103030306080601170a0201032703022d1504030c1202060601 71
    0x5000710007004005050340d507920f03c002659441030b035200804010140742007a0580c5c864606039002820a20501038903546440300460454200b4401a2002c0c801c9251b110480340300400c060303001d1138000c04050b61981d03400040c40041d602c00c0030454100035070307580b610354140d03070300380c0504055880f4110417a43d88085003072603401c0d100047c00081d071740180c500400d810503130b0015043e41203d0001e14003040c403d031282101c0d040700031200d8500303144000c00340c2c1210810070308280300b5a402c0c00700d480400c402c130841a03025100b0700030798060303412640c0026045402e048000b101030800c07034440d0048410f20800001100c0c2002000c2c4d10450109480345800d003c41c180602c045400740c01340c10b0304106070070000c410300ca03075514074104041d0606035100c445200392110500d81a02255840c0c5170100c90003500e03d0025070300c071a81400d0500c441044d568030302e541201d408080501e03d0010004141100b001c1d034030074050602c05841103052180741400c220000b445081008a400003a8001e41503134038006001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 916636762 1250 916635512 916635541
    0x9090b060306060a1508040602040e011805011a0f18040207050604050f030f07061806110406180305030901080c0c01051302120f100f0e03030c0a1403091c0323 70
    0x840f4801c0009981c1440044240ca100c0511845d43c2c0c07900c01c0c800d441c2d07418800000c1c4621f401001d00030704144008125286082c0c5840324440640d4020001e982c0d0761003141e1f000d24465102c502081c0020003124000f4140400a000310080403408008040b00781c00020b012a40600030840703445e0099400c0005010007800540007403c0880302442c909050304980c003c0a01c21003400030001651045d0301c80c8200038100d0b003801182e82c400383c01c02104020f0003810354203800074031448001400c0281c11010300101e83c0d2070312084a0748240110300b415000d03401074032542c1000703105800303176002440348409540302402094001d11501d11007005055030350040c81410b4454440a500c180d00c81400030006a00002d002d60b00b8108004c1c0005808007900401000340c80314015040d0070748000310600401800890083c07504005d540c666042441c1c88140090040c003084402c4101c503004000d203040b0107221094041e501d070481e80f60000700c820b11203188081608141d0b8100d442e9100b00000c2160704c0007078641 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 916638012 1250 916636762 916636771
    0x1032a0302010e0904030e0a03080c01240b220b04060909020c071707030f0506090c0d0c05130b0d150c0c240608151e01060f1809090b060306 62
    0x1040900609540010704a840c00040060140180c1c60005050520541500302c0d00f103001051008030a6036424000301c00d401c42e4035403440300d503c1c1191607408071140110248040007480800f4100902e0720314104816001312140d183c00e812032401c00c0e00340344035880700702d8060901014903d80711030510200070180507068000c206070510400c07101da80800d0010790101100c40042c2a2240102070068480c20000d2903400100038a005040000800c440812807500c01e034021070481c2c20030702c2001c0c2041000780d44450058141c240c403036000e04c241c0c20150f10340741740c00c01c0c0e42001048640086020400111020809484c002d8400c1d114201100490080e110441c3d00d40c0b0341030403600c00c4d6845441049402c40300c08a80350081c0d89204c082c68070980c100c0780061048105444801464503039040070328904441d6981203016810141c080c034a180305115041c0c032600d0381c840e07010030215142a20b031f403900c26a40070120543c202000031005814000e04088a01c50050060781c1d040010070725240460142 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 916639262 1250 916638012 916638083
    0xa051201150f030c0503130c08010f02180102030301030c0905070c14210414010e0f030a031e0f05160302070314010b180c03283201050f060706140103 66
    0xc00315082c0c1c0041034a03040447e2001d0000718050f54508800172030007650119006500b03042d0000c0884100c0d0707014001415202c201d00001c00d0078100126140d03c03003400000c0c42081001814400a2265031146902c5511810a400640c08545680b4000c0c0d85102115000358441c0d040c3c42c0320004100d65450100314600780d000d00b040d05141c40072040c04091000342d8108a02117002c14040c0e607a210740c00c00c8000000c4c0c1038550488450500070040421240040d90912824804100d01445a41c94a0120010b81d82c0c4504042c3c680c901041c6151f4082011b0f42184038640300803000c546c405844404040c4032400004417140018184901498403050741409580411f042003003e103140b03c2140da000c0b0712011503690204140f00e42d40303013000700139507110085407800366011240342c550b9060340c0d000540f40c00e00d8009130320f103941e80100444090207030542042540e8040c5c1c0c0380c0e00340300c000740490324800d0601090001e54010381c4039484009900a49121015003107905000003005c0400d0420300c07800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 916640512 1250 916639262 916639271
    0x712020c13090602070c030803100e04020604030201080c1903021309090503030402010e011b030f080c09030c1003090834110d141b030f0106060e04020a051201150f03 73
    0x100141403580110700d1568100d4a4084141c200103555040310186a808078103052544d81f00c0c28203071380b036404c200d03001c212880880402041400316444481d11940c0d0060000740380504550044801404c080c18950a43d0b00c2400304080c042e0030340f4480b90701145182c1d0b005890741d800843e91000b4050030740c0664001490002c1308400314101004503944580c0a00300a441d0a01e143c0040366905080c060091400447c2ca00c00700804d0740c00304882d00d03400d00c907944070030660b15002c00d401c0c0c0070b116041141d40d1641c0010750103000350400e040c107590105070a0400080d01c402640300c6e01820343c05141b052500f110b00d020f5281d0751092510560940c280340c00380f114800402036842c0303c508500754420300d104140ca01012400c0108403003000c0c80803828a401c2da1418100922148040e40c0e050841074403d00580d002044101d60511070041242c1c529518504140c142900b804000d60005501c04204102000f0608009440100d20f034000c01e0702c042c050801c01c40e00c1b080107060650341d9420500b05400d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 916641762 1250 916640512 916640533
    0x308060109210b100f0e01030512161103030d09060b090a0603081c0b0d03031e021305090c0904090804080d0305010b03011820070501110f0f131a071202 67
    0x162960622040c0c1c800c020201030389603004030013006003555100010908540c0783c00b062803030201c04594100c038460f07002c0307a417110411040001d41e1b000301d00140501c6c0c21070307001c4a40442d1502200c03501c0c000c4043c00380e92615220324008010b0b1210f40c00c00369005a114000c00b10070b0300700002d8180d400116980b08200c09811a0303500446449100141c102c40040d101c4485020103842d0700032900c0c504010401460001c440c030b07015020709546150a081726140c10003c034409a517a000b00c886030085900c818845c241000108103108074041c11410901d1410700048071503445501c182000300e070050030043c0d03d444c50604450724000381c080c50401010300708001000101ca003e8241c906542290b00002c61402890581000030980104042c51004d0607103502c46000d00c1100c01400410b02500083c00000c00d010a069a2446091001405541c0420403030070118502400307400f00300800d0007a052441d41d18180002e9803035021944810118000894004000c40414291040d1390180007411504c1d95 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 916643012 1250 916641762 916641809
    0x1b060403050f130530240907180501090506191a0d0f0204080f070303080f090a1a19060b0909060d060903020c04060e0f0f07142706071e06020d090308060109 69
    0x301040e185000c1b003003d07004645110014401c120180c01c0c900616a05001c020341c00c10044d01c028401c1d182414503203030210380c86082144600c048140200d90a4200760b20301400c1c2d0601c00c8041c031020305a400c052243d2038241116001d120340861640c5400340e02e075420420000c0c10300903204100d2542c0e922030107041000940000c040340d41320300201c01801ca070f83c0e04c030030038141000c40502c0014918449050005499808041c1245c001c00741e0b880030324031101d04015030808840f0341d4000c5028180c020701c002c281c50b1a000134085c0e8050b401401c107103500d444980d91001030300c0c00107a0480150b04082c04002c080d0a042c42120002c0c14016154106401e0000200c0c2d440340029080c2da00020030480000d400c40d0260042d16850075074009440c1e03031b454601c20307007280410414902d21050707950f10000c10554070b0728000791603c258018034030028a56400307001c200786021909003110820f400b4410b01812245a10032910000e000781c4030440b00c0e181c04400100000c0041e0061454254008611080f064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 916644262 1250 916643012 916643053
    0x816110c06040f1a1804180501020c011b020106060801090e0309090f0a0b060306100309081306050301091d0d0c060b1305090706030e0c190b0c031b060403050f130530 73
    0x78415100020007009402107c0d51707201b0720a002a01540c00090f00080410055002c1d40d18040001c810306000955540c0407801c4e031701c413480780d000010440001482000b00d1503101f03c0e00078660408803882c050a50000c50342580e002c0340c174020b150b10001c080000780303001405003a00d0303450110340e0245180b5149001820700009a061b0b0b00c1015502c0054604020004040754090308030140031180c05552008001c240c0c1d071090040c0360f0130354184041d400c1b030b14000305000010242e0003800340c080c220804c2000c44000742c0074501610010f85840514581c0e80b030761580a1040d2000c000c0c0403174946001c400c1540b170000c2641c0702c001018605910728940d10000b00b00c022031840202d4448455124410b007055202880750040d038440b6000045078030400c80d001008048000102c8803000811100e4942c4607103c0074111005404100b04002c030903e564170707040042007041d14810003c000580c840b004107003040c3340c080038880035100522088485202c2111040301100c00500140f000d01004030801d00c049 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 916645512 1250 916644262 916644307
    0x60d080412022b02031002070f023109140a201201020415080f0403050706020705010e07142d0f03031c05060f010816110c06040f1a 58
    0x110742556a9504541c0d038524910712451500101c070410318902242c2d5800d0140005049109210310103400c2c12035902402500d85094000a0980d0684025028800b181520f001d007880c88140d401040019030502951484000d0310f1340000003041c520318604500c004195840300703d4a03600501d400c500140f20f1442298065180740c28400b038000290b000305074910007124902001e0750021401060785407041c011042007603495035a000c01520b0302000748801910644d006070000d141040040c011400c2034008241030743c407500000031061030b94140340381801c07100d030001540c82c0c01c0e0198060702450280c0e140401e540340c0b003804103000c02c500c0c0f0a0746424400121154083c20381710510b1103841d9400c0c020ba50300b0811015020300314003030700c072050001001c040f5900352040345513444490081d44140c02031882503920070b55134140d040716001c1c00e85600103a88004549449100041d4a01d0380700c43e00a80020404004400d01050501801c1e8941400024076000305240911104015541c08203c0982c0f8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 916646762 1250 916645512 916645529
    0x127110105220b070b0c030f070305220c032102060117070302060a050d05010b0301080d2f031e2b090c08210a02073c0e060d0804 57
    0x12050a294001c80741072030103451214203092150700048400350240205000c505c10450710079039036030b610b010000a0100340d410b00d64901401000480d514000d038861a0800303403d444103003450703000c1c002017514400c00240460348021048810001c001c0884c07451040001c01101c401c854604242c07009640d040d0510520f40d40c0305600403120800a002e00c203c0c0051a00a041c0d240d41d44110305014145a04c07014000702150b10b0600001407040c91102640d0581d80c13000042c11640382c2c101d030221420010039071458030820001c40b6030101800c01070003803c1061b01e824050754950fa108060300450710300101052180c50010040f116071b54842010a41c505040282c10722800340026003030000800c880d080c003c18080302d1030404120401c001a1201546240c90300584178170401282c080603500030441540e01590044005000c642904802d038040d1004841e4800c0c2e581c0200718562100340729501391001004500c400c180160800c8199250b030003041690740107148d036102e5440080c68861441341170b02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 916648012 1250 916646762 916646767
    0x30c0a110427030e03010c0e014a030a0c0303120f02041202040507030c082d1e0f04032a0f0602090406050409020f0906120a050127110105 61
    0x40315500c1d54400200c90004a60300200c100011007a01c4034550074400036004541141415295454140280c0401249965486c105400c0b43e01c019100c0c030520144580002941e6205120301b2840030321959241c5080418252018851101040903c0a5404840c2c025008007003500d0108502228682c00c82c0c0c0d061603e80c180d030b4920121000209401000d0b40605400006c000540050300e0005048843c000c480420640c0c84200c000c0e0115054401840007103540100001c800340344510710380c02c4041c0800742642c0502064241b922200d04100c4007600e4110b6140e20400c42e0742c44030070003168003142c191248102400c01c0d8401402d0401c1c01180d01c80215524940c030300c040c0074400e0198040b0343d440720003011429820720301a0302030b40110303403558003c0f840e01c000041c10740782ca400303001201d68002e0032400b180c645d0300d0288201418014659504030212025003200103030100f00c040b01c454042c100000c0c50310100c6d081402100c580900306004100b8280c00000441c1d0144071205031820242003031036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 916649262 1250 916648012 916648043
    0xf0201090f030b0402040e0c01020a021005040e010b210408070605070905030a150b03160b07020102032709060d0305093f07060f090b070c090515040e030c0a 69
    0x903455140d540141e8995803100400008020900320f4281c0158400c81d02880444030600e411541c0360740c800b80280c016446510800058200f0884821640d5070303c0c5032403032500c0d80b10b80401020940c203034059542040d0000b00c5200344d10064208010614004580080c5da081c69152104036005506000d01201d55520115030668017501015004000180c2a10b102d1415804c010000b0b0300d204426800050038012070315112b182c00f00780c400040f401030410950380c83c02d02d9080c0d03000b40c001100881c1903200400c001c45032011204800110000500000c03560303920b00000344503164102801c51030040703041080d6031001941000a0703442544054a403100c0c061405100c10f0311450384000210f11171040e06568048403001040e050062001c4802141c1c0501d81e100000c550000d019020800000c1000c0c0d800c0c08018428001441c80c640507980c1d844103d070710390102c5404c8801c10740350a6008a24030911a40030b05050148001c10007401004c0c6050103240c011803a00c8291003900200800e60b000100d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 916650512 1250 916649262 916649267
    0xc0709180b0a09060b0312040902031816060905101409010903170403031106060303030c1c020f0d140f070c08070501020a410702060c010f06050112060506070f0201 72
    0xc030201500710300d1840081c28200352507030042880d00403d8030140c0c213004212400e8140000e54003560079040100394031b05480c1003a820000c2d0005001c2080603000b031400340304070280400c0300c1103da10901240140d41840c221020b40a04407039404640070740401c0c2c62003942c1d15007000b452079850760f00014181d81e800104004840e40c840c03a03000107000600c0c00031a09591140348010b40240c80c03203501c601c025161802c034040e0781c8150071902c8036415070080000803490080c5002800c10004202103510103c0043c1d40400241d8100143c81c07003031008003080070745a01d1040e02030100851500c1289a00b141403441908016200c0201a10140300051000c0406c04c403500301151141034000d0000c6407200c0100c2e00c010f0040c12500341190505a103c0c40d8103485425100c0d00b82981c1b042140e000c0001c1c0300d111510349890308204416a403100707044c810411202428003c01c00304541145000608030708001c00502041d00d00b015919030350303217004c0040c03103952500c0e0200c4403001d401c201282443d15482c03004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 916651762 1250 916650512 916650551
    0xe01060207150f0216030819051c231e01090b21070b040312020c030f0c0f010c0f06060f0b0403020a18090836010807180914100503030c0709 62
    0x84000d170121081c0004140301c45103011303049440e0507c40080ca20800118219560302070118040d0502c1a1400404080c0905a011a40c2c0c40450b4080144605001e05d246c564800300701c640c02d0305080b14903802d040c0c0035400e5441c81d02502d0b81c0c810421441d05208003294100243d1600401c070300342a80641c01311680c0401c1940700614403445440c0d5650b1f00c0e40381107900c031001903038600054440c0c015140040d103008542ca03450403a805c8000c000e40f40745001008035000847d03244505001c1ca0b1507080c4c0c04650001d03591a1094055203010448070320345540c207003403090541c3c008081408144420310050303031448128011140d02190005240310300d03c800034001c1148c004020424000000e9034103400c0b0441660007000140c00e000a030001c04843c0503610319601c07101449000408080001303110fa40035004074480c5c01c9440300303d90300712519a81d40f03504450224400c054120083c03010455040c2070003d07508098030050303000d1403c00524042403603441e03030319000700151152038400701747c1c400300089103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 916653012 1250 916651762 916651783
    0x70804060b0a0308070506010602151b04051305060a27050c0c011b030b090126010b0307080a1b0311090c07050607050a031401051c111008010e01060207150f02 70
    0x2502050f5501d1500d1942c50b401140b048407603018207000029054000305492134034040755991002c45a03904030f11402c2a100c0341c40c40c0c0c0050b100c140008500b5840d95000e25481402d940b80004060400004000c44e42c00300c0e9110740c002e81c2c80750120000807000212031940300c01d15040c020030903850703c00d061405030044040705003256203040e5040380d94030000426482010307001c1e01c00b00a061070301300034030036140348c240541e008010800060868039414882c0c40c0340710f480d18000000b00115220300103418128a40d01920b1a41e201e08080350a1100f0000c200c0340481d40e40f01b100003103900c0c40d030780c03418180b5440d011a48107071052400108242d11074000c03240c1075541f010503540700f4582804044c000341c1144e20020002843c1c405110f42d8030f141558858107803007000300344000703194441c010003514003030089044500b1221003400f20500c1d100c4d91605520b54540f82c42da0b21a9604105440c40d603400140e01c40c2c01194003040c0204032040c9601030700c10094000d45052495000510005d0385400000207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 916654262 1250 916653012 916653019
    0x110a0e031b0f01110f15041203230c0706051602070902031e0c0f041d0a0b130f0915020a030c18140612070906030b0a2102040e0a05060f1e070804060b 66
    0x100c2e001621b0215200a100f50310800004106203540c0408404541803c8074108040511000d2004204480d56810381d104c1e01701c103551841c0070b1040c3e55240503542d0603203180740c0c0040301880700030069406010a01c090140e0320421800e40c42c048549600a99021180e01c000428140c0400e61964102044561402081d010316a0f60350b40c803014680b60400341c0554400700c2e040304000c600a8134990040c240741c103800a282c0181d2544008000004007000030025041640e61005500040e030f04075903075900c0f18000d190060301d803031329000080c06954042d1114001c000001e0b100d64100d4003104030500036103c0302c03201c003411401b210020840d01e00c505403411000030010010803440d141d014400d20244ea0b02681c0512880c9070030300c144851050180107a080b96845c0c0d0302142d0030b4007814142d20740309600092000c10041d80521820b0b0810f41800004e03662600480c0812011003110f03100c40b03811854013850321001c1c909615074000c1ca00d402502940400008002050501240f60000c0d1104c81006 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 916655512 1250 916654262 916654273
    0xb16030207080a020f01060509430c0b060a0e0c0906090405090a020a090614240c0d08060f060702090402033f09061606110a0e031b0f01110f 62
    0x7618083e503140c0170210900c40c0d5601301500465541403400072103008240b00c000d0344d0045d500460340140340441c03c202001c0d0811482510012a4810000c08200b90a140d206c0044000d01c0e420808400c40d4000c5c485800b9030141c11040100c1001846401e6012441c101803d0711001101d000070103612404003400d0b03020b400c281c01d01042e40404242030003854400c85241000654494140041e00c465104102c40c6d040012102c0c005820202000d010f1160713000d1a20498040c40d19400402d40c112224109040e40708a42005c0c0440c0c101960a070080011203862103494070b070700e000510350301c0f070303000000e0140c1b0103400460115241007156488500780300020383d09075208035804a02050b00b1020032403900c0e00703d581030159565188200c55a540740948032038980540d4411544103034080403c201c0742075950b00c0790484101041c0740903048500c1a940e0305103030342c81d5601c00c142c075081d1003901491801400d0240d60159903103c1000c0000701c042802c01c240d00310501200c01d03040c400c0718802c5000c54000e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 916656762 1250 916655512 916655527
    0xf070605090d14040909050307140c09150a03080a0c0b161407020a0b09030304030501050a0204061d0d11060f030108101401150c11120d0306050d0b1603020708 70
    0x2900140c1c4220081c20840e86005002d80c0c00300d603d5580f94401c0085980d0400052241d0015600140c0e0828003c0c3c007203d10788070103545c80c0c001e1106101752030343d6a5000100114030600c0c108440e241c02601504844118042c1600021808481444001c0102c0310003e03401084a0084201600542c3c0120341c00c0958030300002c0c0c3e1904988281516030001d80ba8202201034284160107aa400d00e80241456032002c1c1024403103041c035400612026450300c014480000090360134050180b0600c50303008056180c500d0310101400f2890038030108043c2c545080c0284145403107840004c0d031860b0300014010441401c40700468160710950140560103c1d0000011a0035240080e0500758440402020000346100020207010f042080c080d0100b41c079a07242485810f1480bd0480c2072402d0301444200f11a03c9080d00020355084000410400c0c03604010781c215600e9406205840c014030041c2d5000000c0d9800c0d59800e0ba400030010880141c0035100885016010b00ca076054400580e1b0041300305540e03600 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 916658012 1250 916656762 916656773
    0x100815010e1b0702130b060c011a01031e0504080c12070c08030c0616050d0513060f0204122a0b04030c0b0f0a0509010e0306012c040804060f02030f07 66
    0x74000c90501d050200301198070b400c880c0050842041031144071500305003241c0e080204d21004000c3c403004403611184490200d583d140700500320401c603640002100c5584107041c031108044c00c0c0344141810301c3d0207022840010b40144085540458030000100340d52103141655040c003c0c00c098a001e44649540b010000b00e00714010084d081c0600040e00c9901d94844c03149a03213100c2d000e1601d42c90313044500842c40030740b904501e100e041005030528034100204050010100c0d402183c1020145620108480500960344a140345800781d41000f50702e01404c00a503241c1d1400c60100c001d100c62400e0740361444148003226481c9890913481c5a1001c425920122140c140c3c00500040c0e40c42c4944110000b12810810222150142c000e20118140781c1c1007141541e254000b05001818030100c070007407420990302401a103010780285504084c44091303d0203503285c2c03d5043c1e89810b1181307040030144001328103c0e00c291000c0361206d113040c0841003030702c8070104d084d402209a61040ca08010461030308000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 916659262 1250 916658012 916658053
    0x181c0f02071a09010f0309050a06060e090f07260105010602010b01110a0b0109180609051c0c0c030209070203130f140301050709031202010b03030705030705060705120f1008 76
    0x401580c01c031820251944080c07240402d06a000c4110070034200504222940500c00586841a5909000410000036120f660030046184412240030b5586c0101784181e50004c0d51680e003219001c8018030100200c4a1220340c0c074800c90140340e0081d001c0c2c980b07180002d0300c50300600c070400001c10003c1c0070303d5a407500e001e0301a009120030a07001c56850303000b465040200044044145400c216002c40607440d0000350743c01040f0081c0034130480d013080000c0802040090290b00b064910813001007550000e00401c840b04c00c50038000700c0080140c00284500494038074012a0250390701215040c0a503201c28074180c0ca0342c820071a8a8800030785400380002e0f0700100811140072611586420103113083c80380105822680308aa184010400c40401400424801c500301c1c0d006104030b00002540354540070000b895078000340c2040311035a00000b0399a08000d0180b000c20b400640394180303507040002c108116403071111300500c1e88461407503c90009203150000c101c400020141d00c07080c1e44594900141ca0750450 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 916660512 1250 916659262 916659287
    0x30b040207140d1715010f110d0906090f05130e0f0615010305010b0a0813080c100902180c160614190506030c0d060f0b06030f0109180308181c 63
    0x10001840c1d22528009840761500c24064005c4841c1c429801100559070640306030303602010011200110409030604005000c80824103441d4180380301e1030034800030001c11594000c4100e085e0000703010030058a459000da013180c0b4410310082041204a04c1407460055070060103481480b0703030000e00001154540c460b596000d02a0303000c0c049a070304d805036428140300300340741480040c0c0c0741d400280f003c0c042d0100c001100d42c407481ca0f81e450040c070307c400580341c0402c0e510640101544e03591400118034000c1c0119040b00d00340c0e40400070714075040c11540464003a4142600f083c01039040b0740e00802c03000d80d000c044156401c285a003800c1c103100d10700483e241d0081111010280c03400e00031403540d250002e4400c90610004001c1d02604031980d903004003500303007007402c90610f50329444040c4039a07880401a41c4a01001165001d007985012000b0055401311451490040034000081c00400d9100090036440440c42d6a642c0708410b5640c9847d290450220700d1088150340518dc50700e000c1c1e448500e08202 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 916661762 1250 916660512 916660517
    0x4060b03032808010f0303050c010e0607050a0201060905040209040f0c0312030c020c030106030506060d150c0201020a23160f020d03050c150906040b0601020316050c04060603090b07030b040207140d 87
    0x140b000c00c405842c45982809030401e0404070810401c0082c0c0b1500c02007214182040000c00c01060500d8070600d020410355203880824008a96900392650920a580c000c0c005900b060026060580100d005c580c0e02420141480c41032842d14828011303448103200041d5401205da4400091510f4001d0003485c00d1106607005028507060184035190501600c0141e03070f00f101c05407003a62124400c00c241c1c003c00d61401c66002c4203080751403104250500c500003c00101f0340000d40d49090502d001096003076800d82e4403030b1303605a400850124583c582c0c15940d00c02d021061050740c1d05c003541049441090a5080254800701a0301e0043c20554094080d02201c0c07003c9080f201050172101e542560240219042c80548d40540b00040203e40c08070340480d00460103005070b900d4640c035031241c0c0c95881c0ca00202540e05070310102540c902c6080502c00d0704020901880d08005d602020340d074803405040080c02c50010581c83c0c00184079aa034440c1c0c1290402e5030301c2900800041c0460700010b0f03d41508540302c101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 916663012 1250 916661762 916661827
    0x915081510020d030f0b120c1f0903060f0207300207060210091b090204081011070308040507120515060d0305030103060c14030103083a0504060b0303 66
    0x46050005491003050704a80241100140e420811801050380c507408007480c903200c280003240d170348031106040c4441c000e0802401000710080144440b441d04016021402c402d50709007821001e0303100f00c0810030384e07034841000724440481d0b0030480080d0041c075802a0589a80c0720504c101440c0312100c14650b1034074404645541441180e041c0e88950503449403002682149207441c0c1900d203568400510b1034480c100d00c8441003541d01d00ca01e0410102d4100c070038040d03030004041c40201c800b04850791844078007000074000d95400c65507000301c50040780313001001c0c0702003040441c0400005200000140c09607202c01c100301c007200c0c1851903441d455200481c2c403c419000103d0761606002207640341c031030341603254145180d18550f80c1c04018002070106204111343c1c003c060307022603401300085000714003079603045860f8040c02c1300300880001590340b0401ea031080448103102228217001e94030202c0e020745500080031368581c100140a00341400c2c00d158140000142e034400e550b1400e4642c241c0205a541d40c40 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 916664262 1250 916663012 916663051
    0x314132403020307141b0319020105060d030903030f030e010c0c02010801080307020913301106090624100f0818030702040b0d0f030914010c081603091508 68
    0x81c01c900c01911148005440c1400340120300410b4001044500686440305020781e4040800310f0440d00568480440302140055180c505503090103400c0d001942112040f1150090750303009000059948402400e0103104d2101d000441d00907800005042c0d040300c002d22410703404810003000c0240c1080c0403400301e01100004949494000150b815440c1e01400c01140c54850619940c02540c040b0000c8070542c1d0743c10020214480c17040e600c2c090203195581c0c60600a446c201025000c81038080b02091254440002c21031071003000640c031500b003100d00501484401c0340c807044158100c48600055040f83e1050000705495912016040085090344d0b9171400c1508c1361000c54581d4100b10081d5610390b4014040400585030a0340b0200342040001d100104249031591410004c50724a50240e010448050301002524005201e180910300c09207400052000c6035510030000e0302900001501c0d6550302c100e140101402080300d540540a002d02d0044020340c1a00f0060044800f2103994400c4d100803880d65 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 916665512 1250 916664262 916664267
    0x220510030b0901090b0a08030a0509042d020c010b060301030510060e10050f040f050a0b0901090e06041106070c14040b0f01120c03060504091a060108011203141324 72
    0x2001048000d02d591400c1e440c01c41c4c04000703003031200c0d00c140c3d0000c81c0341c200090324203042000300b94900c05500c44039200c2e6041801c100403030300714071080c40b040300c0300da50140d2401203a24000c003200c0032074940c01030315085c000030598010b05000c04d09a41010300040084248100003c1010941180c0841071084988518620300c1c500d50956a1607010120014140194500b08074140307020304c0080c00014942480c03070300603030550b90207840c040300450f030380c0c80c44403c541440f8100c00c2c09440d020005105001c0641c2c0080e9a92600030b001400400441801450603616002150a241d402944d8204425200d601ca409001d4a1079281c42c4034500d000054005400c01c00d00e20560024161a0882401103000201c005041e071404543c08241d035172440850207680300d01c03030701e03008600400b03108901450142028065550180c1001c1c10b02030b6280042103c00c000c0d80501120f02d40c10b15260000c20414002c600c080c2c06000c001c0c0000c1d10001c01d0108100a01000414080d03801140007000c2c501200c20a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 916666762 1250 916665512 916665521
    0x10c0903031709030d060b180f0f1225090b031f02031008010f150b041223010507080405061014040b03030f0a0305010f080c0f090603010222051003 65
    0x740407034071042a801c001580b07802103561040010094a2401c002c4141410444030181c01007030001c1d8001c0780d500c4080094800750581c1d440c040e80c0c6070820300c540100290201c04c5d40e0001a100d43e0101d03550300c1100d10b061149440062102040c1c1e0010318402041074211394150180840311807901649a099140002e28540c1034260070300450003a5003451607400182d840202410516032000d500000c20440c24407d202c59a010303030f40001079480781c1d0250421059440d600281c3e54140501c0309100c0f666080412141c202d5102406022610742514820030000440b000ca100300c0d4078180c100043c0e90340080316107204510840030740b00d5507501d02e02500844101c038010f02902c6881105441258107241d03200c0105a0030081c00c50b420105101d6034404594454042c90740045e40b10f000401c141c1500b42c2d02071000d04040300261902e24209000b00f1389180e8070092280c072a10449000c5162910300798101c1c5c66810b25000c2d0030740c6d003920620b4810940d00c0d03c0d01c11240145410072401030302c2c0c0c1c400e01c03c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 916668012 1250 916666762 916666769
    0xf0209100e0a0906150905010f09050c09010c2301020304060b04092001021e070819080307050706020d020c0d020c2704061b0305011a07050a0b2511010c09 68
    0x22030055540b030b54503200e40140400c400440740c1c10b940d08003264420300305005801c002c01c03029002003055070501c100200340c2c02e01a400a01d51904140030b011b043c00000d415265050760a00e455060360119081508801d18140c142240c00c80245084000c00d002c19001584194061001844040b480d10306110072104583c0e00a0101d0120303407141024a20711a1020f4080e403414412505a4828103207400e205060201449450350302c00c070307003c00c98403100f030210001c105c9141c03143c2c000d802610307150a1441e1200800394020020005140400c00c2481d07070541d000600850301c11074940038820342e01a92036140b03482c0324000d07100700c10043c2060301c2c1c440da00f0810384041782200712000c0b10208001844110142003203407901c1d1240807034001d0300c02240440c05441034607500410954940000102c184100007101d00010004206002c0460000100c0443d41c0707512015080460b903a682e44600c0d400c010840c0d814540c41401d40d40611587d0020300044c070b0808920003009050740001c0d003607503201803521 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 916669262 1250 916668012 916668029
    0x1f12061a0915030708030a17090604020102070b1e0a0e030105100f060e03031209160f0308031303030b04051512011a06031005192d180f05040f020910 66
    0x140064801a40706141c2051154050f044507a03203500c405e845811038000b51800300028110a07441c61258a40d0113206402c4211007014085a0078a900000c0d1608000d00828594074800207510401d80056a00809036040c0304c00c0f801d496a0201200604414012841c40c0c070039801c0c03c011403110f040145c1c0c14400c40f0b21014108003a186004400d440c400c40c0d815045e54180802d2090032640b294207407280d07110b88041d40c05801c2c5035a220380100350740603944c1c101400c0c00b1500c001c1403000650540443e600440244441c009440342c9203411000360900407a85034005044c8800d005444007401c0041c42d0184d002c4500402e80402c40d80c00300d0803180c002c005101000b8003002400c04609080c0c1c010343e000a100c40b0b50340300320b513100e00116814420700f103040390800e00c100d542005141c00601e1a000a15090340902440790380d22410711201c0d030110301a010500702034440f40f90074034100360301c900d00e58084001c040c00300b80340608100038803204004059005d0030982002695078284050b8000641d040700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 916670512 1250 916669262 916669279
    0xe03070612060b0706050709060e010c11031c020c040b010c110f0112090b07080915040206030c1315030c020a0506070309020a090911030d0311030f1f12061a 69
    0x8030301151400e88801a1110542d542c08010646080da40e0040840c01d0040001245500f815100144660041c1e40700c1e40402100420a00315030b0b034010709403010150800c65045409014a0009081000b50301510150409400c424503045402142c41c81000c1c0e01280c003088000729203401915500d0594030010701e4540102da49403160301d400c40030003101d15818500880c091658020042c2107440c0c0340710640d45040742c0010006002e038003005460744440c8038006068030103000803000d074480101070f000910400e40400050702456100b4280c88500d484181c2c8480001c0d0b46888070008090b1202c07100c0c0c002401e10070600c011380c1c00018a54560b9034000010142e981d02c90200314000c0c034001004a90050b070845001864003d5401000c03c51401110b400940c28101420945424480002c3c5402d260510782c3c584c41e8101b0140c01e82c0e51001140c0c001c3c09859032030240181c0034442aa9110080f040d11103c0030401c00b50458440b616244104803c0140c038603003c120380fa0180c0fa600001c0d6010402 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 916671762 1250 916670512 916670519
    0x30f01061d0315180a051b0d0803240301060e10060c0519020a050a2606150d050705101214011505130302221a0d330e0c010e0307 57
    0x208100302d0b0303022481500d0704c0a0802505180b034104a070210054130b0076440034110300c1c0c0500f000c078400c4d0040e050480c4c0b0051031083c61390f1190454040104012105000c408070313000210000004a188404000c1c02004140d81741c3c0000101035005980040907540050310118800c0e0180c80c50a0000303400000402142040b017002d0100400e008a0481e0085001c50000680d6151503002c00c000d001e0045840249440044201401c920b40300b0318034040d40c0c00003080c081038820304000c1442c0807900380c03480b5080f420f43d414003501d4415654030071500607841000c004142c542c08000d030104514020401d1181c0302c800d00002203070810a01504000501d4240305550407030040c03000f044034090005d0001c5496507650002401c6000325034006c01d00000342c03920445039000070320445558821080c0c91164120000c03001c1244060703d10001803031180703510014043c10314982c07110ba2456000001c49840c084c01a071207400034040c20600103981e4498090804040c0d800b51080380c246100c040c00801a1a18 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 916673012 1250 916671762 916671793
    0x3170a081b0403060606030b01110706090b130b13170a0309050f120d05130501080c070b092a0108091c08190204080a050c0904031e050d02030f01061d03 67
    0x1901c004004007900d04000010010350f060103040e000309441e481c00140081e000001402800c10000341418503002880d091000a4110103404251407440021a4641409503625040e0104030781050380e90480100d0740d40791110440a10b00245c0c0c1400e94400340c6010b5180c11256030345001d240050100320081014419400d0074012100d486000900002505854001031401d101c114901d81c40000d00008441b0005032004084600510003807a02e841340d40b810b50b0007074a40303000c0e20300000d21070b80244000c980c0d10030b41000340e100e4a00c0da140000c01c1103d040e0086900f4076100c4007506002c5004400000c0300500301050034950740010b0083e10b113a6080e040022110a80b0080035a0b0000d0380c8250f9040300300080340301030000740c90100014504d0b202035041083c0782040e4200100d105100440800c40040d42c02560082c1e03410042540707003095103006400f0f840c0e074043d01c03010700d803464800310401c0707881d00d0b600e214103040f0390003611402c08103a600c079245a41210003211007030b015445140b0394040c184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 916674262 1250 916673012 916673041
    0x320120706230105031e1b011103131a0301030807060504080408010e2103280f0f0515150f13031202060103030305010b16081c05010f03170a08 63
    0x6110300d0000524001c814810740d04010344041c11009688203100511032820100035040165042003a100346c03100c844800c0640d10111001070311485d00006030f101e20564040c0384407040c9400e150003600e454040c0302d1101d2440c40c0703c621901c1d85010300950315412030940c4e141202c0c180c94000900900c0c1040740e0316028080c0a0150003200c5103402008001006502071081649504040380030b0100038204043c28681e03940780c0710315583e17042410000c0c00422801e00680c143c40184501503503040c4041d441c1c52500a158020445901e14140407458100c01c1f19540101e200d11280f003010008400c0310400d10460400c00c07501408201740030001e410303400080c00068148203602c0740c0c81000850b03c035079886881c01d020b2092040940d0101c0014020583c040c0119409081100c980e01c0c00c0040d81e5509d5500302d05680c9000c0c1081c5e000050510760300b401d2400110403038120303400030312865030f45000c400340c0c0c0601880182d4480300750030001250a1280e0307089811950302a5562400c64480050307001c03480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 916675512 1250 916674262 916674277
    0x901090507140408030a031a10110a0b0c03040201020d020a0803071404030501020c060610020607050f0c0c101211040509010e190e0304060801140a090507020705040f09032012 77
    0x101200410030501e4000a00151844d103010715280e241c03a11024040d68501e480c121038860107015081010744480400c0440d0250501d4840fa1800c184001203041c25200200076088601070700400240080040c000c600451003a401c440a036040b1100880c0c4035144040010411501000810059440785a500044412112a4601d000e0756551400e0880e071100d1210b01c0550000b60402c2418070b8441d42c01e02180400707001030f03e420314140038000c0c043d1144c0100000359460100380c002510004000c2562241009003544401c80180b8501402c0800e0010790342481a00300300541c0503031100c040a8408031100503080d18083d9003001030844420b41c0080041042d01d882900100d0010b00b14004c20080d0901a80070f196101d041010040003640b05070852040101c242c10303e60702d980c682580c000125252010001a41d80700e00d0004c900741885588001c0d40581040300010391500b19a12900c2013600c82c2c0c9600301019111101255140c07280003940d840c0d0b40002214000180ea100000c0a81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 916676762 1250 916675512 916675517
    0x60105030603151003060b030a0b010506031e0702100c050414041d1b09060f060703030b030c1504150f0c060504030201090b0103080a080108030c07171204060f020607030b0901090507 80
    0x36403d80d42e51203825501242c014a401038a41c9081042c000076100c1d00d090210194007a1080b1003590300c038070741c9a4206200d114001d050000010f0149542c40d107450540b0007002c0d04840d00c5051a11000b540ca903035500c02d1202d514509030224a50314080c90841d42258140421a00c00c50702c21030407c4000d100ca071481e41c580741002c030320f90443c155041c088005030f081000b03076810b1711070f060109000b4003050062000b07015051100311010031390703121001d54400e9903251601090001900340404d05010f15201c0c500e03040f80c4105181c0103034074081b10150040e00ca0340901c00c1c515221000701210700040c0b07909180f0102d13060080301004a1419000740c0d5000d4060300006c510b41d8603541c0da81ca543d8800740e1082d207c074a40404d1681740c095004c0d08590041036007000a6050101c0c0d107849540b144450b00c140301000f0407956401c0c8100000741301c085038280145041c5a10b4036500d20003c0c01030402c28007880014005d510001c0d00450007031043c0c9080c00406401d54007280e00f41070350100109400380c0300206 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 916678012 1250 916676762 916676773
    0x503040c03051e250b03060d02030d030b040506030c1513051005040806060102120f070c18090c0e13140c2128060b06071a0601090617060105030603 65
    0x4a0010806058070040c950842583c500782080c400d03003481c2c0381d40c0c90b4a030040c142d403402c0703e0032440020880059800c1d05012a903261503485c00524040549031000b90140940d007440564143c0507401103e6041003550180070980c0d424007003540f00c0e4400560341d50310113440910354064a0400d4007030003040301f102c0480c14003a91a030000501010b03086054600150001400b840382d90002e2020345d03040b000c28001094006c0103c40c0084082c0221204c1d01c58195012171640c00740001000803100a0080440282002100c0c0e41c2c41000741c1403104007a500f502403004002010b02e42aa00680300b04e0300c6088201c071440030f0381e49201000c0d40035851142c00d07200b01c0e41c60b140f41c0d5460056600c480081c3c0d1648030059102000d5040c1000b00b0603e40000560a26172160380c4840d225041d240c0c200c0c0e104030000f030018480000a140c2c1d006401018005009071402c00c40996001c10171140159400d0301c4031240199154411509051a03d002c11103004003840411120350044002d5604044028190740 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 916679262 1250 916678012 916678019
    0x1b030f09170c150108341503090b010e090706020f101812020a030807050c0307060507170412080123240c07180606051804060308030a09030305070504050a060503040c 73
    0x480e0b1070f80a80100d43c0b950000050741503000307045010000c061060f00b90428110300821a4421086240d202c1c080c05d8404031441464204c0c840c0d40800e40d02c5a00035400000d135616a000c84103c400100c03102001841000004940c40d800011201c89880302030f0000c10945238100d81c41c4c8080c115040070010391f075165814103000200c503000010003030b8601d0790081951401d2824000d1401c200508414184881088040d81418001c0121404250080c50210f0039466902048511034000c1c2410703c0200011801d000c10024070114040905819540701200f603604c03507e54001c2c0c4001c000407510104c945005452140c03d0410348840c1210765851903141c11070500c1c40d88181c41c0d1110404950a0300001020f200ca00b40e012045c0c0c4240041c1d071400c10240303007041c101a10074414000d01a020040b800c108a249540310340000b0091580040342c9a12801c01c050480c0281480c4102203000ca81024001984103101d80203581c11140010300701c04415280c40401da40b598409403003a03e0903046c004010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 916680512 1250 916679262 916679293
    0x8010608010e010b090c0c012d2a0c0c0510170f0c03280e0304050103060b04052b05030f0a1205040c120302010b0901031103101506120207061b030f09170c 68
    0x2900d12000c1014a00c2c40c26040d08422010ae0710300740341c0300c1161005070000440f203191025600c01c03078050b036050103185c01100c5d0800d409a99120340c00580e2010031008003514242e4044400d14907400c035900c0907800794440424000e0005c0c01181c400d015030341e080c40000c80c000303407580404c00403100300c01040d690107409039003090a80b02441c100a209a000140410007964180302d03920050240401c50340c1042e08210006104000306460400e120085404541104440d02902020075a1110490350385003420041200c540d0440b08524003c40c018401000d213515280c0a0584500e500c50b444a5a41e406c040d85025441c0105205904565840c0740060300798449580c03040c0a58000c44218807883c60704400c052416141b41c06205440d4248540759007924005921102555090305068207041c96000300360000b03001d4820045e128a041c22005d506101c039400300c40144101030b9070180204151040d01d0170039507490102c0181844c008150a2144d40c1c1000003401444401d03000341c801c1c011049001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 916681762 1250 916680512 916680551
    0x5090d08031906030203150402030f1006030606060e010f0324080a050f0d020706030c11030d0e0f010e030409090c1d01051801060c0f170408010608010e010b090c0c01 73
    0x8903010340c0000288031640d614980718081074400040144500c0f800e40d03002c2034980148103105840008031710003203800c55034140100da0411500c001106d1403d000c0d141e42034090b140a100546e06180703001d401150b03892050710542c1e042e91040c4c50300001d0b5030044904400600e002003800c50944452070307601d07198803190b0400e00c1c000d0480c00000c000824190908a0904407452001811680f2a120306800e20342c01080d10f0302200d0031400e00040d490311080c002d40700303118203040c0c016071400005402c0404802e140c4c080204920680100d074505c081d02c00c001402c881d88031050070f006a205110030400c031440354004120b99445002c1840074266911814000e100840070b090121520303400051003e0b08124019441c540e0524241642d254580b4a0140c030400c410100a00728002c881210024083c0040c0202d01c0074854081c2255500d503035000c018024207060007500340e254200000007895140500070b1079000c0800909013407103601c884400030080c2d030051001015654a400001e90a190300407107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 916683012 1250 916681762 916681789
    0x170c0f13080115030c0b0903010f0f0c030b010203131e0f062c210a0b011401260f15031b18010614070f0605270714040c0509 55
    0x44003400600302200d550940b040300040c10700c44207104100b000816003090900017100d05002e030260340c982003034003c640500703580f001090f022410490001806085a48100c051540e03079a030070000c0080e403800480c0c4a210318001000a0540107100b405000f0b081d05405a00841d4028404200eaa032455210008081a8400b8010541108240030b05414a01900c1d001b400c8055009080d2100c0f20002040d10a100c25100303181d03a400d0584200d10b50042240340d801d250001e080344d6156a68a040701103160084401d41d0015440303041126400c034502c000000e4044400c0901e00260f43c400b004180c1105c0010840ca040103200000c04149403024802e84403070000721090390040c00f00d00b10512042c2d82c410310103040b0b803100400041003003d03481048281700044415103644e5850181c24962094174071a08050640361501051140c401c40340e080c484503806e40c550346114030b4004402031503204c0c5594840e10105584208400c0603a1525a2100c6080190340c00c01c00c0c103003040c00740480d194247d41340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 916684262 1250 916683012 916683037
    0x12090f08120f0105060414030a0606090204080c0409050709240f06030c0c11130209120105270c01050d140f092a040f060302090702030904050a0507170c0f 68
    0x3400719200011000015400395000001c401c10b545080d010440c81e03c02c52007200e1021030b501000c07003407655090045205990300024140041501c50101d880250f000b40b190f050588100d14803440b0b45d040900030758080b203401c0301c050480d01c0d191480d02d2025000c000070400145602140c0802000550342448020309461010030412504010740641110b0020a0355000d0022000d0141c00180c0070030030102c1d440b1415111580c103001c4000e500400780c09003000f06076101031811080fa4032140c05506c202c2c07041e0034800e50340c0c100500c078000441c14550100c03200e0041c0d400c0091907200c25402000180a020444c03540050046000b402e40c881d082000e5810072401c59424090008100081101016410301d80c110440945203c09200105800c40c2d010a4022034890f0300b044034450160703128100464016002c5c030024580b040d0001c0d101e92003041fa142c400d41c0f0f840041200f8030982d1080c0c134450175241d03c50103080045055448181c41c0000c003000100740041100c6803041c051407029015010141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 916685512 1250 916684262 916684267
    0x1b12030e060a0e19030309050901080a03031a0411030405071e0b180a170c01020f0709051f121401110301050603090a0c0f06090801020a1e1206030b06041401140112090f08 75
    0x506d00280400c1c0c0795070001d441400340c240103018010b8003080c614100d0b03606040000320749020035140e9081d0490740c0c0e01c242d8854a48148403006004100085224512500a5072113003901c0300b00f203550302448000d04940c1d5459840302031008004407030040040458185170041807106490000c1c0340080190000c1d05801d81184000c5d41000c001c0164440d10b0000340040c001d50819181400d0746c5401502c94090b0f00ca4076080895200c62110407030785001d491440340c202c00103448980c8026090484035089866410200c52490500011701c40c030250074054400c5145164a00020040d05030406042c6032094040e102d039034000509410b0345100102500d8070300084552804d80b016001318003590100c2034990041008040136607100910481441c000201310494040d4480200c41070003d89010807100f82c54085d010081c8100c5c0740c0168030501085405009405000304400002c1c1c9087c8600482c2054030040ca400c03540c00b440c4400700c0300100981c0094003403030030384a142e8082e20041040e240260300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 916686762 1250 916685512 916685519
    0xb0a120614070f1d0306040506160905030703020603041a01060f0e040204080601030f0f05011e0b06090906012114060102011b0206062b1b12030e060a0e19 68
    0x81e015540e180c4401d10007809080c41d10300000707050340d0048400032041004224040826107140e0300410b19060010b0b0454010340343c5480c0c11640c5280039200710b00010140418095190320501c880c2d4240c51014000d444403510310ba00b80704003500060401c845445101c4541c000440b001d6410a00805580c5c0d1502481d401000014158840c110b01c2d181c0114010003080c041c3c6200000c03d20b0440b5030001030081001911304024603111501200240705500382070b240481c24548090301c82c0c0c0095184810041c2c4819201000481e100309420f8603005425100002c0701c940c0501110440b1a810750310050180c8450700c00700c403c07980080c110181c141400c01c203102265909204000302011209900c40081050400207907480070000d107114030655105022800c003827551848040c0e030a822f60031030f0072002c980d0728240b40440c403c283c440788003880502d400100040003011500d644c039050385540244445500034461143d00041401d0103204039035070340b81c4082c0c450407860a40341226240801d801e504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 916688012 1250 916686762 916686773
    0x4050a080a17092b06180b040b1b0a170606030f131b030506040c050303031b160c080a02031b012705060304031119030f260c070c050406030804180b0a12 67
    0x206c3e60560392401805011000000c402124280e0001d400c404a50200e903555803404807501c0600c440706040b0040070408400c030640200c91501101341000080d0326a5541000b0303c08c5a0108650009140c916000411702440c0a064800c1101e80a585100000052800301001c524200d62040360b05600100401c0b0601804c44240c00207480c00f1005940b850610f5034991042c050f409400c1800d039800002e4003913010143c4400c0141b1640e000c01040d80140d0303102c903003907116400810264024022078890301000d004215000c5400311058460500c1c2e107c0c2e040540110b524400c031400c810b1900420b002c20a41c0c2c8030300c0654801c500c240e0b00d030780903203036409082400c3c00d6810006241d503030031071801280001e4200d00d0061103007981d0b01d482020602e1640c80c1448000212240c1c801d03403c20f55051203040e03070400c0d00030038195015441030f08400b41e540040c401154280e11000e4020b86e020703c81070100108103403141c02c0030b0100d10008600b55003034100040309003006130b000e403014043c1c00c03106404204 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 916689262 1250 916688012 916688021
    0x15190f06080907050108010302010531031a091906060b030a02070c08010b060306040e010f24060e03100e03132903072f030f04050a080a17092b06 64
    0x20842c014043d10f41c50800045e06100042c00000d05001e4003245407100c0c14040d004d007071210310b142d5111316030718240c08454040d80d07038890105850700c0039610b505101c103000d01260b4a00800440e4018205451105050301d00811002c200b1201c00b611040000380c072409001c0038500404030400016034a07205407030300b10780c0d0030348035803000c6800d0b410072854240e583e8954003035a5200c1c030b044e200460307402c03110001180101201d8864103030580c503140c078842000a00c1400794006d0869102c05220040c0c42d100d082e650410350400065140e031103c010100c224006400038181036200030101d80c1445444850550900d08075004119000310071030300c0c2007854141040da0208410008261342c03440c248018002d1000181c00b2280250410843c0107035800c5002c6681404015680f47c1903c1d20380f02c182d0382840c4a0b5200303201d03051042c0407a440c085100320010540f003003001c0d030200410743c041074025208000b5801030511a58040240540300d402d60718100d8401200110405210701d030f010407464040200c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 916690512 1250 916689262 916689271
    0x9010c0206091c031e050a0504022b0807030903020904080306130b030604030f1e2102090328080a030c02100c0e04020708040323010e0105040b15190f0608 68
    0x2c3c0d00070340c41e49001c8500b0074129100140b1901c1d0128280c1007842a0803071800104c1c00c40141d0b03a1403c070800601b030b401c981c40b8034061442254041000000000c08503543d91000d408145150926640780000440803030003029150711a0800e0298580d5940010742c03400c4040b03500fa2854000041040b81d545420bc14142e01c03808804000c05c0a4146030000c6035644000a200a0510800c0403180303101c580120424502c4a90301c1003465040c0e40100c0008002048900318480c07400e0300b079512500c480304280240ca070b41d42030207002008840c20010111503800e81c0054107960240d0085038403008140b208005015124040d10701003200852200c1c02458400004e03c1c600c995807038a940021200e90014186c0180d100807030700540c407203a060400f03144038459603000802b100f000e0001501e00201000c0a001c22900302c4001300a00014905c040d42aa00d04441c0102015402000241403081c04c0301c10400b108005444603412010000d6138103130251a81d003000300d132071340744400400182e603000700d215030310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 916691762 1250 916690512 916690531
    0x501030c1503150b0304061103070207061b0f0201080c1309090203060906071e0201020d06080a031b0b01150507020310060512070503030d051b0a0801052b1e05010509010c0206 77
    0x143c003983c604400b988902440d8110640040030609000300340c1c002c1f0007811520b810f015078a00b0304142c0695a80c1d014030071080414642c00384600c080426250140120f030300301c40c00d46828070923a030046550120041c02c400101c04140b202e0b94000305800024005460303a900c0c0058a6480d600400d8606400144110083c0e40304000f000f01e165845041c0c000445201a000c07072034986408410380c0a80140440005c01518080000441c1740000415400b1140242c5515101003038201d0003210210b40142d0141a41c2d01c0b6000421200020200340588440c440c6405030400f03105500107414010048414041180c03940001c2c0454588085254614000980140303002d038a4600801e40340c1c095a4031041c42d09a0342c1002135025040c3c0e0810640b2800c0e4040e140ba030714807060b60080c01410b420701480b0301906099a080030000c8006c096003004401118140e104000c01c0d0b912a1180d00d000e0824007141d2600080f5000000e801340682401004c0600c0082a0364401c410000c1c0342038001881c1020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 916693012 1250 916691762 916691771
    0x604020901020a0b06010c240c14040302010c020f031e011a180a0e2e1e0e160b1803060606030106140f03091011090604050d0f060501030c1503 63
    0x2101c1ea00000c1c484001076109003290200e03500c040050390084680b140107040c4900f52300c400c010a003000c0c1500d002d0480d94200800003102c841c4400c950250440ea146e02006204000910156024403d54421140300900e89007001200f40c000c0b070b01b82407083c403006080000c3d07200b07104040350082c0101a02d1100d0801000081004140020111858502d07107640310311201020a00c00ca280c3c0c1c016006880210b4101ca50059044c164145802c001da0213101100d018840060b0072007a4a00804110350f034606140c42407000948045030090540080311f40240c840c005802c0e603003841825031780b0024951280703001d0701c0c3d2405040552807060085c020b240309030030100c100112940e490050380c0c1510580e18105503004048015144a8440c0036200c401102c004020030030151030010b10202e55990f02c0c8800d105d00c1e80b01d21a0502c0c14003034540210362100040c070040c0920b00b4048503030003003280504609024141aa1102c2007200c50a820a44080c0140304081c44044000801400840c203540b0b801c21 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 916694262 1250 916693012 916693027
    0x708010216030305100305060c03040b160509010503100e0c04080601090b0108130519060c02010c0905011d0f040c05030621071406120f09070f0f090917030f010e060402 74
    0x1807405009000281031664a001003041403a410211070091a880303000c84146061081d0b42c4002500204c404944d0a41c01c07a0024030030f50000030a0b00a01c0d5210b031a00d42c10900f101005448a40000303150401c80b6403451400a070504162500324003c034007401d165640c50303041803c0681000c00c140c1001c1c003202c2c1008100324060342d00450303640c2c0c40017449490074156042c92a00a00300307081e0b8154500b071000c04520410910150303901081c2d000f40b0a40007048011f07200101505c00030030501c00d05000c120034850103c60805111200000c2240041c4406ca1800c0840d00140c100d0f600408100700280010041290b18242000e404101c070342d800d00070400650010344542d950304038501540715404043c40100a81d52500383c01e580c0d40c60040c50041210741390100c81030243c05400c03207000301644514403001401c09000030140d0180c801c1005040a40c5040400d04000380242120440d840320a007071503460b1560354007024601550b0050301500360f030f5140000a0031900310280502c0d00c5948100b0410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 916695512 1250 916694262 916694287
    0x190b01080d05130b09150301091406010f0c03031a060f03070305070801240302090409062702240c0a0b150a0b03070e0609031501170303070206040f08190c0507080102 73
    0x64041300e29060049942d2104400410410b49045950b0044000c000c03001040e49180c5030002051384076074111110051391504011140304a02d40c03148404101c0109648010030b20940290001029648900004030405004650158084442250701c60004020b100940b076050040030b0b0441807170b01d89403040e541004c41040c3e00030403480a0841c522800d0344194091070180c1c065400b18103004108001159081c00c0002c050001d29030340280400103030446101b80380c1c05410f001840ba40240c06003403003800f109410b00104230b030181800142c030010720010086070010454048520b11507000f144290600345645440e80700e602140900c6103c0b0307a402441090146002c2d1303a40240d8a203410503902141c1c1c80407451500c5001040c90b0503003d0705002d80701c0c409924040f20b040301d000724070090b5144480720f0003a0301c0c0e0205660141c01a000301d008980421320704015131800c1802101c51031300d0b10540e000c440010080c0004c1280205060182d8201170120601c481030007810b100d4009d518002100082 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 916696762 1250 916695512 916695547
    0x2405060a060311160303060b160b070f14070510290d020d03030c0c0501020f04230f0d050f030712080a050103080405150f030411190e0106030509190b01080d05 70
    0x7040c61805452855818503200f40c00c203c0082260b542020341d90b90440789d14112030607a2031010750b002c0c140c0c2c0000c100c1c42ca2154844441e0360209a07980911800a0700388075200d588840030030346e00f80c41082030a000c0d4a400d41701c0ca680e0100d207009100e0829581c042c08a0001c0c0d54003040912480068cd0f03900050f8031484003511540d035151034001102044c03504207444c10480040082c10640c0f0100e40f80319101a584028400c0d901c42c00580d40c200500d03030140000c60605021415003244003240c0400003801c14a0b41e80c0c1c00c461003031059400b0040206a454915040060300b69083d40c000748070070350039907041058281c00c00c07001c04080c010703903042d43c403141c00e2882140704040c0521001903118904440c0c041c22f40d804600e40403845650b0341801d0400002c00c0c0a00e80d01c0310312801b60b4040e032142e45420404140c08031400c8500010540c0c0c0391a0050b0300a200c024010354442c0078000b55100a030030414130072004c45208420030701d12541000643ca183c040c80005a00a004013040300b0041403101481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 916698012 1250 916696762 916696777
    0x110c1005040308150d0b011712092803061b11150612100609060509062407030c080a031e02070309171204080c01022103132405060a060311 61
    0xa284900c03030714580119191040316180a00b03804061400030440d4083c00c10032380b00042c595004c0b5040c011807aa2014a50312440b09015440341001610203568014426200000c403c0390002c011180e40c1ca03110203080c0d40c128500f00c9102c01c01c4803461441540c1041b0528020209440144170a0204010441a2a0024280e640305508a00c21201c100404203c00c80c809000094103101565481201c100074005038000d29204103202c2e400103103207042c622030030a0400c0c19410012040c0440c28642d8070598080c000a03010440c0800740c2c0004140c202005121143c0a55000100c0900100815012601240750440c20300c4c0100003003004682e00c004004103031802e000700e07881c00312b400c420807603d0800e0350000c00c4c01c440800701d4002401c0350080790440c142102a02a40c080c1e60355242e26681d8075031a00302d00f5404c1c880c24404124610140e40040454031301c1070038490200583d0305080000a142117140440081e12401000000d05200c1c0c040300040060741020303c5600102400122140a0a074 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 916699262 1250 916698012 916698031
    0x7090e010f21050c060d09120c170a23120105060c0a02040e1501030b01080c010f090b0306010c06150906050a0b22050409080301240912050c04110c1005040308 70
    0x182e1800380001406044200781c0c004080350385ea81210078408000d0700003007a0a458055000c0c841c1e0309180c0c0141030500c0d02541c0a40200c0c013094100036000100c2c1c11942d40b14040200201c200340b021300600b40ccc181c4005442840c101e448010280d42d0402d1890142c002500070f900c280a40c142c82e03000051348509080c2d04a5010a201010410051070501d8003a0032250540790f0380000020302c220546401d050715105002d40b07540ba40b00b40d00640d032841185110500040c1402001c10120510002858001405150610489600342c8983c02034503200308401304140040c460400c000402449042c1c010718040e82c000d00040d150280d10b0107940240c48000c41d29400361302500c0c0040d2100c4040b0405007900500c104402403c600f0000d2064109020301a40003444018103400a641d01c6914407000d655079680401d017904102d42d00a90218100d000c41e82882030721003200c003682d5103008544207490000d080c25222035500340001d2030220712042070f400041c0340c4030900004c00c1e03000307881961110f1980e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 916700512 1250 916699262 916699319
    0x1031a06030c03280605010909030f0507030e040504050c0a08060601020d0c05101104121109070c022101020d1e0b06030c030f1e0405010507030b0f1c06021207090e010f 74
    0x41300300c0103103103240001801c2c68a414004111101a42d010715491400b981c0da203404944040c900b1f0300c1501c5082000380200f043d0500449041c6096046994410b00c0b600c10390b0411035907000860000c54464003c0c00060308014100802e0b961304002c0c0613034560003483c0c02c03580504680c03601d54072000e110240c3d580c80c0b80c50700203030000003410404031401400a8820650400b2440c14031800410040607a81e11510a00001c1400076109504000c40315800420855984600318a11000307070a03036039003001c40c954003440b60751810300040c4a581303000c0b5651101d500c96424111050b008071190a45110301c02d000c10f10501c035400c00d00605603548000110031100c001e4642101a620048502782600524240e401c200020402d040d00000c3c00780080b40c40500000754040304100a0311000e04019800560046051a00e60001801800300d580290030061a0030349401d520100410111542d40205580f00c4040080e0304145041c14010104045803558060820010f00c100700441c140000019180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 916701762 1250 916700512 916700563
    0x30816120c020703051b180603060723040e0907090903091502030d0905030703170112030c02060c07080313060519120f050718081c0c03020a020901031a06030c03 71
    0x2c01c00f1402864004049070758001b805684450400c03211407240d4001d0340c10020a464640e0340d060024090b090060150125944a80c4212100d60342c94955907540311984030144a44105000100701501441105c0c0c60716140c141d100c2d9103000340d030754090320a0740e02d071040a83c0401d50002c8243c087c0c0d0b01c040310085e00740c194804205e10358010020a00310709898a0583d004000002008107005403098540c2d1018100b41c0344c250040541c00d2050880d01035003680004006032242c411045950b2000b0801400d0030544c0100c20710b8004250400b42032944002000d0800d0b02d02120360303000404407483d0040c0745c003048001023a83d650a1900c84d0081c0020707100340d0f24006290b60442001c201341440c04101a02e0071303641c001c061540d41650b501110181450200e0204030114004001e161811111320b009c1c0c800990403215034100c1e00055045014640c5840b00680d544580507000310700450644540c40c80407011907480341c8015100c103200b42d0040d4846182624045080703076000d0b032900c40c0b916100c4c41 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 916703012 1250 916701762 916701767
    0x60815040b190f1a01091a0a03060f03060504170c120c150a0c030b01080603032d030f10050f0f0402031e0405030406030b100c060b04021b0a030816120c 67
    0x100e122403403501e0308080d200c0d090341d040340d881010080044d8100042003085a001503940d04074500540707149100c120500112800c04200400c410b03050b9240c00124030395640c0f669141c007407490b0802c0351000d48400c144018821404c8001c105e45001c10400c0d85014024080e45a4412138000c18455880010804000c0e1900c140089442c4e81e82c40e021150b181e2821160800051036880c2020340400d2602520903580d51003489900c1c40340002238011403600031605140c0806a5042050520034201001c8200103c05618040d5016003880da203906524100321001403000220350b00000c1c00b4407036040d8000003070380c0d4090b0240300b2810191001a920f40baa00c0c4507103003004002682104c014905002d210401c08000020812582680d07010402c0c0d050640030086114044002c0c00001500d803444880401c45a83c814440104010700061411400200300c401c2c907030314502c0d20798141d00071000c401d0505801000c055444403001c054022000b00a1002506c8240080340240703019a4900843e8901030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 916704262 1250 916703012 916703041
    0x102090a1d01121a040b070f110c0603060d02030a060614090c1e19020309150306091b04030b04081801091203050d27050c01030612141f02040306060815040b 69
    0x44091111300a81c40c2508000c84071080980f01c1100048116040000c10b0340301d2200040c030404604003900314080854200101c5420140c1440d501c800030500e0100182d03001c120b8071b1780003417045402050322840d0035080300000340d00e0381116005180702c904029290460404a508145400d04ca10214031401000824a4010171400481c0061b1004100c0240c940020141458181c2103680586240b480400b0983c64041940d203290050104e00208600c40046460400f441c4410100c0c181403d549488540402600b03480540b8200e1000817821000c48012203103680240081c204011184e150074020301042d68080005001c111b0301203803e00300c0007404c0d00400c000c05100310341412502d00c0c007041c0c1c40e441c0454103022501442901e01000c1254000d0103450101c854142c0c3c050b400141c00c0d01c605d03500315404000d4030494016203840d543c0b0404500b0fa0f107040582c84800040c1c807141140791400449810350810030042d4468503100e0a40c032034007426a80d006900000c1c20034961105001403c449 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 916705512 1250 916704262 916704293
    0x90c0305030d06081c020a03080705192006010f0b180604080f1b0109090f180507050a0602060c0405040b0114160b0c0901120b0a0906080102090a1d0112 67
    0x5010004001c000b5441a8106400f518a28010b4a14805403404508802c004003000300000d600480600d001190262211642c4000f450904070300d068a800303884030340f00c41054a1140403981014030055850840c0302c07101d1f540300031840107040950400e882c42e10303000118811038014040c00a140d8821800e02502c0c2444090081d05d6251281d4403049065150311249101c000c2030700c55006100d00d91040c01620300103265040e1914000b860414180d200900704c4580d84503141a150034801040b40420090111010700400160481c130381482b04000010303e850713022200315844103060025481c1c0d01c208075011540d00b100c00280741c0c4107201c01a81d941d0328403480c0b1032405001285c01887c0340ac81c4950562154402c2c00c0d5204030303aa4030f04090741e481c0204d904140c0090365500c440184809658801c2d41e04e504001c20380222a40d55100c0c0101350303001508002d904e42d40205401c5010b0900e4421000a4204a160407914031008202c410b59040144078003000249080000310034000021803107280c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 916706762 1250 916705512 916705523
    0x3041a0a060b120a0e060f01061d1906020607020c130c020c19090c0f020a020d050106080a0807050105070504060512270c030c010206070c060902030c0a030302070911070f0204090c03 80
    0x5503e1050082403198008a401c107881c0b0b41010524516000b000c6441440f4404201034810580d0821100301e601038034ac4084500d03064010075012034a60366100720300180020350300c0092607440c01d145009041140c0030304503030207650028083c07040654a5003c0230010081d0f00c0400242c1000003070b02289082c3c8103104243d085128071011030146103000800d8403e03a00100d40c10303c0061054402110100f48007440000142c0040c0d00354001803034020400414207014800110300f01d82c560581e2400c040248004440c4501e0014014040020a00556600a0041c140b95082a10b02000500a0721900b0003040503100c9000004100c902052061803500400541d001d500452841b2801d43d2002078068052103407280080b10a4107610024007680709000e03035a83d0001500380c5603101000f42051000890303140c000e4000d038400f5034451000329001540030364010b20b0baa0340352401e182c085079203402542510b11000c110803004184c0b21020301036115416a400680202035040000c2d03640105e0300000c00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 916708012 1250 916706762 916706767
    0x10060605041a0f0a1d0406180515010503060607080f070c0918020f040903050405030d022508060411040906060b04060905090115051e030a1d0303041a0a060b 69
    0x104903520802070002c1d0307070035012003641c0349208107945840350168042c100800320082010641c0d0074802c412402c1d140e0881c540790191016800002015100c0541050b040d40541c00381d04000b07526240203898028041135010312820701007900080041c40000c16141c059000054240c04101c1004200da40010400c0c0180d42c45191500d4842d004c1c42c06481981d14903810100030800c0e0800d040040644281d000b481c104003580d4440520001d041051010380c10700100b800006a2501e0030b02c0311144842080c0c6c0038002c00115039480c0f008510201c2405410b442c854030702402560030005035030350410740000c00728a01c03000d80e400090103841084c1004102c0d03410040005400c5440c6130240c807c0c0c1c0e4184d11000d92041c1c5600510811200906c50b030114020001030051909004200401036016450340752039a40c4c21040350182c040e441a0350901071725503a10b034840c5440031004403051030090307070344040c620303500b0517845104001c40c01510311060b41880e003021454480d0307280e00000040483c0c0c0e95564 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 916709262 1250 916708012 916708019
    0x120601030314130b03040c14210708100914190b040c030f0303050702120906040902070206040e15010311070809010f1206032003010b0603040303090c1706150105040f060c051006 78
    0x1030203800943d011582e0910b80f800204240230403804d030804d6281c0207031000011409107401c030002000040764002e0360380251580841c90b01e4051100085c0d0304a491008100600a49404e113445804a80d00d004903411201c0d40200c54280300c0200450075400c4860004282c40f0703800c068104490f950b00081c802e02c200142c400030160540c1050b44560625006e440040c048111140580e00c80c0c10344003035029204000c107111000300c650140c4101740c0042c0016042c07540700c0c810006410740030340c1d00c4d000072540c004c25096150b03450300800d004001c0b14400c050034206176a40312085802014011030501a41d507042c0310b0060700c6000141c885d4903002c1e0003484050b49e0303802d004400c1100b14414404811110b50403007580e040c14007600c90046400341c016031550ba61a2800c13001020054401c03140c0001c240000140d0f164000300680718940c0380405402e882c141070880c00a0820f044400d18140a01407004126802da0340075140100c410a00303003100035041c0c0340351903410000c00510a08000d4039140002c0f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 916710512 1250 916709262 916709279
    0xb0a180b0408100e0606220e01022a0102090904060c0314070e04050f060603010608070315170c040902130c030209060417070603200903010f06180b12060103031413 72
    0x741c85641c1e084208000f4130404c0c014080e280d0400301d03611074206d50b12804d410490303080c45400c0001d981c40030a001815031050541035007641d00c416a542d0380c1c48901044030b207e480800c1035030b40c11041403000031440c021401000c10106000100003900c116929128450414000d420500c488104c03040c0007201d80c50205030103460124403170401400740340b80c10000f60600c03000d1062180101001002242180e20300402100c100e00010543c03010180c071100c001d48203503d000d1100340507020384000c1c00a04810540e4451a2442500d40f440c0b02d02d082c03158134030250320b60322591111040b04102c0407440d00c40380300c400e5010348140f051643d00b04a0000c1c1c0015145a941c2c0a00d0b0160a44010b43c1d0300b0a40e03d150440945012004005040da0710740301c1c40001e01c0c000b03801007510b884042d00121390030000513060b03800c07200c2503404510070091440460444484500c80d0056400085440f1420301100c50011a0340b203005000c0142800f030400f40800003000010300751100040001e452412aa0301e406c481c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 916711762 1250 916710512 916710523
    0x72f01032f04090b01050909040803100312080a14040c0e0a1112070305010608071205070e120d0f02070303020705210a11090c041212030e01020c06011703040b0a180b0408 75
    0x1014421490940390744c04540c0300b003088581048000f081400903440316120400c0e59440600041c800c02400030000000850300855503084490300e4036214124030b40b842e100c8050b00e101c1720407044d521280b0703010400041c050000d034400380c2e210705580150b80d40c0c0301c4040d100100544010724080450202d8102044006c81342101d00c1040565411711091366588000d844801c07082c1c0d4501e011403090b510480b206251940071039448020380c984469048c8810700800e05440c0444082481908503221000d034041d04055090400d0640380f008200d20b51560710000e450f0051801201c0c4501006007112902c07412441c0341d501203d81640540d100c0420a14110b0b80d00844400c2003800381a4810020324005420f0064504030303504590a07604240d0310b40c0d51a04180301d03600801c000c1c103030740e858012001d107801d1010300048444040201541d50500203082e403030000e43e110707081c0b03542c3c410042030000308840c50581d0380390b4206060102c2d01109500049403082061381102d000300102103400600320720300152 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 916713012 1250 916711762 916711769
    0x40f06090b030606150306010e0d0b0703271515080d02070605130b0702031501090b12011b08091c0507020f030a08031503030d090503072f01032f04 65
    0x4000145200742030545402c0110740040d40000d02650801882110000840e44901c0514042c2031040303040000410745020004203485441e410020000c00d240c02d031140d0740d29030b20320003100c0c01407480c5d04007003c490000c251001040a00681d0b04900b00d14055008010308005400d87c16242a03219020f00c1d070340e074009012480041c4201640010080e005004896008502040200b440e50808021081036071007420226054800c90160507a20004207403058040c0074448800310b082a022010441c40d082106c0ca00c07a1a40d14040095511070420310100b4490090360034040030a5407a5461a13080281000742c0349081100f8a20000c8201d620800500c2a0f5200322203041040e00c6810a1503910000c2c131a0050501a08101007480701804819158104000400b26840d0a0318802c0d100c007a15603074142107800d940301140c80c80c200020200052090400c0300b6200740e9a0401c5610140f68a03032074803185052550741e04081d117000f00c81844200311640070b0402910404184291841154440e10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 916714262 1250 916713012 916713029
    0x9040207020f06191808030f2b0608010c030506100e0a08010203100f091e111e0d1d060f101e08100b030a1103210c1c0507150b040f06 59
    0x501111184481c0103224265601ba20040d402c00d0b10000400c040d580c003510581300c4241680c502c0b00758418503080700c481422802580860032621300450a42982c1c1800c0c072240c1410300305010030009845543c1c0408001040d440c020103080c8540000c5207090f8040d810004003035000108121981e012031182c2c1c400c55480d01c450010044c2d86110300700465512003420911620b000d41c22420313a01c0d00c0d4018200b0072040820061401240d8001c20015483ca000f0301074908601080f10094581141b144040002c0180030160307401d50189189a2500c0e40101414051100c1070049180045600d20600160811094000304030130b503089070b886148039902c598100c902c03400d202d101210000f80522401d0b4400507000300303003e808030f87e04c828610421072200e035003611a02c1c1601018501910080228000134401c09030f8070003813441070381c0c200802c0d280c000c051402d9852440c03401c60707441000c56054070381003c0c10804c101c030358111042c003034035240e10380076802400c08035a00010720300c550100d0125603841 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 916715512 1250 916714262 916714277
    0x13081009050717031206010306081f0501060908030304080a020307061d1e070b0915030c03040b0609070c02041a0301050115031b0915050408010612050f0703020609040207020f0619 79
    0x1400303045518840e60403450f0064109000c0d82a100d02c40c0c01c0b1a9400c02414180403034040d4449034450702c2c00301a860b07601d403000440d00030010801e00b40e00c185405813450345003c007209400e2450150f624400604000e080d504006460362003603100303005441c480c1c0d9105200384580604a495400354032500404400b0b54090020300d204204c44c1040000030021414000d405680e1400c401b035540c43e00003c0c511a00036594000b076051a902c040002e511504240300f060391281020f082c444501c0600420150081001300b0038447d8154022490b207218a43c111004203c0380d01003200c0d042c669616132806505907013440000b01d10071110212803a107984595408120700c0c400662014851001e41c00d039a80801d02c0c184041c07022001d45400070b4902202410220710306540e6000d00307030851301141c2c040125040c3c3c0311225800c1250034000d80c071002145134024903006085030000b55082c8654a00107100c0c5600041541c119100c120308028081401004951642500403280d401501180203501c00203648 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 916716762 1250 916715512 916715519
    0x30f1505041a01021009020105040902040f060906170f040311060411040b06120402060307090f090c0f03020309060708150a080a0b060111070326030405100c0207050114130810090507 80
    0xc0903001d500c402c205034000c0a8a00d1013150190040204002c10303810068100301c045001c1c00140018001418210071140b09103180000082076515a2340000c4c080013036426401326804000c050198109400000020b92501c81d4542500d45950b500003420181c003c100821081c440110202c000f8408151014848040c1034010801203101c0c0c00e125408400544d40481d001d42003903406141e00811508055881603115040072401c460b003503000c1c0b0441c589454a1a0f20b10394410201403a000c940d0030290304509101041540ba01001400ea40400c4003020008082c1d800d01c0803c1c0a00800140100341c4035629040541e4441090107425a42c1801040114034039511406050b0340e510030b03450203040c41c282191358548001d04800340320742c2040000d1003c1c042003a940e00c021409030384541c0c001c122415068820109482d140c00d11a406c1d500640420402d90341c0225448690000c029400703591540f4030071005151404581001c4800d22400e581240091001d034443d6012501507002c42c2e840c1580c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 916718012 1250 916716762 916716791
    0x3090e010902040e0a0c03110c07031703091c050f0c1005090708060708060f15030708090f030d1d0d18080718090c080607020a030e09091c030f150504 66
    0x41c13031090341140440c00000402c0310150382d21030034801c54030307140c04204e118020750a02001c1d0001c0024401e00c0c1c0003150100108640303070080e000d60060f0b51040d24214501070300060780300d40d0108c006040101c030340c141d40176a562040e030490303200c100220f11250301d41c28000d005170754500341591640c94562802c0003059540307000203a10700480c3c4160004007081d50b20200211841180176020035000054400701da42c2342da807040180c00d4850800c0518984a140c005030040c550903014011100c0741c0c000040d04d480910001c02117503941510f2950100320041400c10108034507081d007504030b4240c01048001d41307495600c9401e0000720000707400241c06041c0c032482d00c2c5840b060180f252000300381c6030840044019596411829146019100b41c4421581d03418000b03003086800ca60604c0107801c00c039070f49402c240d00075158050b401010b0340d50b90700c2450900d00260380c6070034421a00c1e20040d11022407481692281e0000e02d0169004501882042d1380041c0c601c003410514042c0d1807050b811300928129008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 916719262 1250 916718012 916718017
    0x12010f0609090f15060b0301060c0b070305091b01020a0503040902030103150c0e010311070605011413050402060906220306021228230c040302040c02030a020319031803090e010902 79
    0x5030419802d03d1010300d1580e41c3c031300d98245160a0703803c5540325240000c0070200580590700908060b1580207030794090b81703807440c01000300030120011b041c5400140041050005801002c1e4400364564aa45684090050345032007601840180715100c0040d0200c6e8604050b00954101c912500201c40c0c2c07040d100040340c06035201001c1010000c0e11004142c040e5600c02c0e000702460030780c00d62903035180810580b204800e0f110240c22911081e403000301c40c40542e051072454078002c058510420003490901ea40040c0092103040610380c0709540201c0c003c04a50b80141503450021000c100d03440050390b5a246c00c1010b5080412030300c0c0356664003400900704040005440d50f600c2c10810420048800149203040200f03c60354541042000700303001c91500e83c598034016030051201d0010796803154654810001075510300d1901c00115041406152021034000080d80d080d150440c030845400094940c7c110000c0c0010b070f000d1018900a600c07a00103041c2c2040c0e0380c00a0f0741c518401084182e0302e407001c1c03c0076071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 916720512 1250 916719262 916719281
    0x5010b030c12030d0b01030204031e0201140a0e0609060c0601080c0915010807030f0b04092f0607030e01020a120f0306090c0e0105161a090d08060612060f12010f0609 73
    0x183c0041244e524640980d6100b882280014100142070a0302c0b03441e01c01503030b100ca220300442c0300000400402550307044240303420005d0110030315a1605280102c0100600d0354800568028078000c078428086645000585941204440032640d00f580e4900c00035551b401da03500d00900400d220000b280241c84d030034440000001040e11046400d8490075011401000c507900800c0c00c043ea20607030150140d69500512030001e010f400c8a02042448108698090200d40c40c040c031060f004020603040d82e01c0380702c2552034154041c00c10903100c01103640180d0801e01a07082c01420b42c6002030340c17141c00e01d40050160003402460383d000c00c2065107a44001d4104d0300d010400c0070100d01c41102016482d8828002005000e44503d00c10f000740c2c1066a81118001700300041c9c00c82800c220782041414202004416203004451414140070304000003c1403061040403a031090b00c418110008060342c4074843e000760320010191a80c204013110490b482e0080c488954000140360400c0c1002076589498001e91841 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 916721762 1250 916720512 916720549
    0x80a08030115050306010e12010f060b0c10180b1305070e0f1812070c09110c060c070834050d0e03152a070302010902040f20090105130305010b030c 65
    0x7c1d807141040100c513503034034428240c1640d203514645d4400c000038011140100f92800b40141c5907480100032504003060118000300845c5046041d0800a100d0000c006000d0740003202c48070705859050441a1414503d60054220721800e0300008000c0c24982c032040c400c40300b80b4540320550700c034200f0a5100690200703031001140d100c1e08040f0000e16401b4000c210341446051002c42d084e0740c0d0706000c81038540907401e00c01d00a4021807030200d203200c20b00c00a94071861126043d490720a0560b501c0001d401540700d210401d0760601d0540700c154000881d07640250760f002a45501c1050f0a1900950300c044901122000410551112402e07050001e00d500c0400790443e62140d25544140d10006500b03042c500700240c5c842503241000c1c081c0e08030001004820701990020072030394070b5030043c44152125581a103a406240890b80740d806422a1100c0c041c446884101956542540c2c004071f071720b8094208292025543c80b0000020000c055100490049c800d500b660b100d00350410400810442005101d1030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 916723012 1250 916721762 916721777
    0x10305060d032102040911030405012703032003040b1801090b0a0b030120180105070201120c180e060310020a02061f1d071d06070206070606080a0803011505030601 72
    0x302c0015100682588030343c81e6800509007035860396868141e602c44194801d070581d001007407101380207003801200b601e006203000340c0e07600030152041c42c1c1e0201c00d00c500c080c0030143c0ea600040b80004400b03010725600140010800d44a08240c14011401c1d481500c80041c06401c2040c800360941d01806010022078100c410342940f5619110080c01a241c10b84549905540e180903402c544014a41c002c43c2003800005440d45514007210b002c0310018101c1d03550360510030709000000050380d215103503400050402002280c0d070944001c0c00c0d01c1700300306001411005003031280e0100f245008000038500c20b00048080307402c05280889820101d204480050b401078100c2c00008a2820718039500c0c0b10000072250038075020aaa821200f02000d441e003118041202d6020223003e0032651201111070000e07600240080041c0100f4001003403440f81c000028000c402c04120f000c144001c5030701803001410910b0941f0b20300c0800386002c03100d0754024042c440301440134581c4801c81901c21802c0d24403598040e1140c02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 916724262 1250 916723012 916723037
    0x224060a12060e0304030b040311010b090109020c0f120903070b040f121a0705040311030706120c03021c050601020601091b110f010e01060510020a0503030f0705190806010305060d03 80
    0x40329448050402e039291500d4039410798689204000a01c020750040040306400d040030710340148465421039500115a040002140e40349d03852207052030443d0400840140c0e140043d100d0030382804002c0e154420036000e0022002030403a00a0001e042b24407003101a43c80c151345a00a0780480d003e2401180040c0c50809000d02c40021507880061b01d4a000c1d050510220569500203645c1c9902100c0b078100040001c94100100311074142d00f1101c82a0840140c01c11a040020051480a51003214045281c542c91050340b0103002e0741c1102e00449446a60800140201ea210b1010304403d603821070041c46804000a00d40c8094402d1510b1408800b4000d641140d0502084030301d6a002e101d1351025000d0503440c070008480c2403280c1312003d1580c10010a520303203840100108242104008019504188122030000d0008422a9485602c034000501a074813402c60448060082c169007803800d094030f030045600b47d500004802d1180d10b00740d0b8180601e075114004d10800300000d0200502150001c0e034950f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 916725512 1250 916724262 916724279
    0x5120f120c07300807050111041503020a0f0f14031609120f03030b22090c050f06071205040305070803040e010909020f041e180203010c180e090114070224060a 70
    0x45055034003c542842c2043c5d010744503182190724400b800c0c502c441001504100f5480403100d62001d44004d42003c42c10b144408502411600d0074040d800200801e1402c003042040c010700310750120038034000e00740381c4030310f0b049080c01e030030b81d40c40d0741241e0110300c008000203000103024150141d00c9901140103d042d1009503001e9014004a8818541c400c107030900042504a00020245c0340458084011400940c941400907071444644c001074010038000c1742c030380400d40784e071011a0682a80300041240000c800441141c01c0d00403030300014181c1c0640b55002420510010203401078890a880203441d6980e500a000200c65203200002d4111120042c545824a003580c810350000ca28280131a103441d45c507105210817124006859031140080c2036106041d030600b4443d189840d919403c08403201074685030701c00d0002204d48a0f4541650340345002481b006000e4200b80c044603202000002c10342400f0102940322540b0b40000401915100c11280c81018240c1403d40141d102804a114250078010131 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 916726618 1106 916725512 916725599
    0x10b090603010614060f09101806020d090e42090c042102090a0b0f09071b02030115060e0118080705120f120c07 50
    0x14000d10000c4005007a4034503045a0486d22001c40d002904803a100d00e1060580000420001c0e250040d04401d03c1000c0206046101455540300c4000700e03a04c5082e003503120001a0280003c220684008800300d402c08004400102d06104550218411200d80e800310103014020306421708840f480c58001084070101100e13980c2c1075090501100505010b40d0240030035800c60b240c2400c085480d40080c08a8060b40545844040d141c9090601c00400c441c003490703402044280090381c041c1c80d014000342d02c034031041c0e1643c0c00c400711542100d003c030380d2138030b03104903010b40d80c4901070f5404c0c42000f0846002441c25580d41d04c04810352000042c51464400100d01d04240e080ca001e010001010840c3c10075600b040d10045001b1b00074001c0d003441c0500a400e440ca5034010400c44240003030548001700040d4003000100c4017407035503606101c81445000d0820301505a03001c1b04803062040704070007 = true := by decide +kernel

theorem cover : BRFrame.Cov 916546762 916726618 := by
  have h0 := BRFrame.cov_init 916546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 916546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 916546762 ≤ n) (h2 : n < 916726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
