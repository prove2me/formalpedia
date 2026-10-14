-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1762
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:34:59.95328+00:00
-- url     : https://prove2.me/submissions/baec6c91-ac3a-463c-b0b8-6c1659005aec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 316726618 ≤ n < 316906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 316727868 1250 316726618 316726649
    0x3110d0507110c062a03130902040918050a02091503070b09040b01020f06040b0c09060403030509010206090c0609060318030c07230607060b150a030209090c03040c0b070302120a09 79
    0x180165481012911481012040c0d00c1400c4484104c0090040c2174242045c2c90400312501a03800c010030081d0310100389a50045014001d45002c0e1003050341c81000526440c03510741442d61040d0700e4400703000019126a04a81c00214280300303501c42c22044c02c000409840d019a150908078429030840d0303c1c99070080303240100c840c1d2a0350000440c8050000c142c0c004085607916541d40501c00d0320010029102c9130000d001316200c9480314005040510712a0f2500d82d111807880000a00d400740003090083c8940c01744880d098992200c038211440c1c00015104d281e502d60300c000c04020104402d041c0200706100c0000c0b0820100b40c0410f00b082507448850422942e200d20652580000350300a4690340d010f502000a000020300590003030007052006000d48584401801321160640c2200c5840800b00341c0000c0c11ba1510f140401c4a560300c411700d281442d0560605032148074980003140250302d1500e000003620010701d80200005181c2d40d01040c4543d0751041c0203100140301e101d1a12458120209094 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 316729118 1250 316727868 316727893
    0xe0301020408191401110a1d0f190e0c070203060114031906090f05010c090b03090d030203070c0f0804030606050f1e010908010f05160906080703110d050711 69
    0x31201220041c80c0285058011180f003642d90a021003411070791540d01d5a140d0004403028000c2c0611002045d031243d4503001d04e10b00c05808100500300010802c0389914003042e0a698455078105e80150a85622546450b110380300307182c1e403505070420b40070141e0020820810b441c0a40050810724406e80c2a15030036640d504038004581d12001c4240d44c5601b01420b20070ba00c402000c0c590200074028100451070030513540710103040c070342101c1d8250340da03946409000d02016000010038004010701c240442c511303c0c01500464842c10920400420190000045007465220320300d882d2101c0d4004040081d4490b50b841c00042590107813004540041c01c00600144c5450403030481140c0100151102e185480c00300300071802c01160301452811b00c0112800492480d10034030400300507401c0142e0008180c10624109086440d02300c22480400802c3c8405000090780108426000101c5003400f2402c1808085180d001d03000d11101126402d1030b0008005810303510418040301c0714000d03407e8402011456 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 316730368 1250 316729118 316729121
    0x21b0a02151602090a0b18093a030b030f03070c050a060c060f0612060b04060e010303172203080a060509130b040203030c0102040816050108010303090b13090c030c0e0301 75
    0x440703105641d00302000625000d42000c065060303011054a400045902000000810030748131f000e0040584c085030401c010f190f8100b0807505501203551840d0048914081ca490400c03080071410913075240c0c96078034003070004a019420201c0350400050170f9400c0e041507109403543d41d0300044c00a0b0b9420107000c0000a460501c012590152200395036422542d1400340c0355034000d09040389030001d80b00d50f10030740000c03e43e5040541c1507440d440341d50b010825418603000c0205860041d081807007031035200801040004e4021035041150840b003903001a003a610f90084600300030b882c09405002168100b20300c0105a4080c9225104840c12601008201c0c0c80d1818402541c504130b40310700300c0740702511401020541410069a0140c0f0050482c0e16201880c0201d90a9810a0f1301c40000799005242ca0b41e8425105945400a04420300e05800c00d585141c60003010080c1620490841d1000041c0701144006240c111101a10022105000c61240940010024040d004250b000240d2400a40a1030b2030103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 316731618 1250 316730368 316730377
    0x206010e15010c02032118040212060907020c15030415110d020903101104051c050c01030e0a0609080d0f150605030601050c070602010b0f09060114030a021b0a0215 72
    0x84105140c01140c20000654088503005020790703040c07081c00341c0007a400c4c2c0002184400000c66106c5181c8920b0420040c4007035900c1041c0c0b59200324014005030101c400ca20034440c4e84254200c94100203921042d0040c3c0c01d007102508829004030960311042030240311800114042e1384a50f401042052841007103904a643d140e48655264400b0420307429400d041d030700a440c2c0c0102c002c050340e40301c00c03c81140c03000f1104503600650301c580300071408102c070345890401003030b0a2422800e41404050350b40d4070b060b220384d00c0d1038845041c185d456281e40110f8004009040001d50700c07a008100f284038504103009107420a41180b42d0b13860401c614400000d400e40258201c8000000f61043d10701e081c0a4152131a4000620182c1000400e1102c4071380142d0800030100140480d800000701c1c8541c00041c00403070385042c03a005014698400c1071040e0f6990000c0d61580c04031800d900c1945903190784c03012502a216a9651582d01104040d11413960a00402e04810040c0300f250fa0703018020607080000401e025 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 316732868 1250 316731618 316731631
    0x160e04050f0406020c0106090203090f010c0813150204080109030305010f0b090603010e0702010b1906021204080d0e0f1008250503071103040302100309031107050609010e0f150a0206010e 82
    0x74201080000b0441d4000d4141e01d100d503400840e200d92a40301c040100c0c0c20454560f100c6900542c0045001e840038854001103801c2440c1c031119a1800d40070a0319144204180100001b50b00644400e8140031f5506403030251100d00002e110080603030400030b002c0c000c2806000c041d070759000d80c0040c1011007001220b120080250819017584e103840c02d0303c07040f404014800d4045d9503ca06141c452642d806642c0c3d0801141d850310581150b0030190024603001e2441890464450200811b00c0803000000d1915014a80c42c94040c0c940c054507004148801d0002c24002d800c42d0202041088441d000f411591248248085c4440a10b00d0a02078a40e0300c44a0031100c00462000c0002c0f6131040d101740310308081192100e044078980b0341e482d404540e0010f211040310001030740c1d40800c0130400d42e00401110000280000420000c0e04002c0001c98622400c81d40c60b041c00302d8126020015210b00282c41440c0c07100401307000610066841d400200d0f40328803110030050140c107001282800b80090580d00484 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 316734118 1250 316732868 316732891
    0x30a0515030712030309050127060b01030209060f030402010201060b03151f05030103030c0c0305070b12070c021309020a0512010b1804030905122d0c0306190b0d050105160e0405 78
    0x90300f83c0c6050f030082652980941c2c0319502c80d840c4404a042810346c0504142006200c445000010f04000007210f6204905a04150040200949642e540001e40310311800d58003074217603661a1480181d006010b950300070040903001104000560030501071031000302e403080d1138855198400049a50381c040070840010f0114031300344010b102191191484d00803141c418103501001c1603da48880b4034080e200c0e0b102803640384000541031101050507599540004103801d009610021582c0090540e11950760305e03201080d5140030020035135640480280003000702901c02c0801d0f8460180d0117020304409982907000d03418046143c40042e50305910588103903015030f03504074968105800c1054211040c003910216205582c4040c5c16584441640d85d00c1d120f40d481104040100590400c1c10415402001d038460f800c2002004418400514014074040b0320003000203250741d030b01d000504424008140a806980b80108002890100e102c0ca14064540c039140c0d00c07203103c048410001034034800ca40c01c00d10707507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 316735368 1250 316734118 316734149
    0x70e010306090209150f0f070c050f030f06010303080c1e0a0306120b040204050402151b0f012c0f0f03040302151c0b03103308060129030a05150307 65
    0x49050f000b4282003406d03010306074039200b0358040f031080541222030180c070142c0c4404010815403a0400e245541400150081e10b1040010080243c4035001480080c060000c600001030141c20208201c64408090000c00d47c3c00d038511840403c0290808140c4e0400303c0e00d05800402c20010300504030500780d51051055a0304d5982d41c2c28030000e014050022030300200044518000d41903004054420080c080142c0f000034044007445500c1d00010742900795251340740095604159202e2003040d03038542c0c8603c601441910340c03007010a10303000860540c1455801841142e58403004080003d01c11603008464104030900d0071403a9854a1042c1d03101d01c07200742c00c42c9051400d441d0264001801101c802810384102c0c003244003032401640e29980485040090f03000d2664045410040300c0c402446095030010443c50904081c1652208180100c40140390300203800d402d421a410080c13289094140d440940ba4203048510b44040c20054405024100c0e503520403c1060500241d9a4100c42a011020942 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 316736618 1250 316735368 316735399
    0xf010b16060b01030b1c0303051501050406030b0d061d01060602010227010903060c020a020103052a0309100c030c11151f0b07050a021813060e0f06070e010306090209 73
    0x209903282e24141415203c0c04050303455078401c8245042800300c000c00350a01c4070907181c010220f400003000201300414000c00901b05982c0201a10706943c85401e00041c1644440001030306a84100d0b401800141400c00a181d4074079840c0800869204a074000d101c13040e00c501007a404e030301070381c0e030a030500401604a40003141a440140480c6100604000501c90344a0301c5000540e006e000301040560f110300008c1085583c540b0039943e10032000102d41da8017000c1d034080003021801c07401c19185000408008220409810b000b090450600d6603020054040c900e1000b030040d01040700c0c1040442d001c041010030005e07002c0303040080e0411103c1890616501c4403805850200d010302030524220320100c0100e030181d003000c0184141401400208a0845148108501094074510114040b4800d00900a104a0800c00454070b1030b400796002c1072003801c08446900d84800d22100c1d400a10600b0248031600d9080026501ca1030420ba90621503585c403222074a00741c1c031880203020780000d46858910752 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 316737868 1250 316736618 316736621
    0x90807060504231212090102100605030c010302030915011e0504020a090e0a0e070f050a12050a0b060418030c020306160503010911090604141f02100e0c030706080f010b1606 76
    0x600c0388004010004c82c0414200c2030b8075085040c14000b6800c0c40c000781c03803080b968041086d26654000c0000038000303982040084bd88903a198030301241031540210110f20540000d20a240003038108200441740ca41c0c1d250054185042c0c0c00743c610100d2000300001041741e092600031100101e005441d88030005141000c0070184540c014182800b069071030621881000c01401030304010301d0090060080a41030004019040d00c0300d0348200e90175051280440c00240c1e002c00c83c9020b2503007140c8100f1460b514040460302602401d02880100d80c210443ea00405d030308881400c0b10f0500a034222044d681d104e000b0407080711041c101c40300201b80241700400c142d01058019400500801d00100d04001000020a000e604542c001c0031880401c0b0308460258109840e040350246d039a004051080c0c2c0c0100c6c0c010707443d40c0c1610480174581d52262408105180300700505865040080c0c12645125a118001000000c040e601e00c013803040c5c60000020a03040310010b84600c9090009981900c41290713031500b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 316739118 1250 316737868 316737929
    0x6060809030a0f05040510080a0506041b051e0406230406170901090b0705040305010e19260a0c0201020c090103050c0126040c0602010c0207030809150d0903090807060504 75
    0x43c1040402c000c0410700303440b5800b94116240c2d203511001414144042d0311402c0c0d40d4000c01041c055850201e12000c00800450406051501c3d8101950780eaa002a80500085021000340c01c0d41000050700145895100d840c0105009810307a2054207840300c040c580c840c601c154402d50001a03110142e100107a2102c4000c640c01a43ca00000615204039076603191030903d00f00c5a02003c1800481c02301709100c000c0c01a01004520300c03009d05500320003c00f0b5410341500c0100c014000344000c010a07070511a00403200711b00c1c0403080760410380703404081c04000c100c034410103070880c014040e40c1c0c8806c1481c180106540d0690381e20401071b0a01c100000011907a1450420382e00803605008141741885001c8079001500445c00303644900340c090b01f0a038021342034419080c814000c66010b070500b000032074448000d84000440445600c2c2c0c0703004501f031241500e0f000d0f03004010203c0e441c1c00e100008141d001444d0000b269100c20684007090b50700c070000e50b402d01440c440c61024901002c0861400d6561705030300c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 316740368 1250 316739118 316739147
    0xa0b0c10051806010602010c0f0806040f0e0c130603020619020312091c1d011b0813030c080f0c010e0d0b040606030c0b040602120c0a0803040c05010306060809030a 72
    0x29154030821150349420703210140da01c902c0400d200c0100c409084014482c0038094103480c0020310441400da080205100d00e041403d8040088034004910785a0b00e50304002902d00c4000d1040c00b0614035001119122007180180c580f0803100b02d00440304c031406e00d0080d28201d9400a10783c600b4541d030314941200c42100a8220811400200b12220038004e0300500e550060004400401d00a107440144000185800510720309110382d00c40c00341d07064403002c100071121040c2840c160b1301040854014420788181101c0c010328601e40842c0326600c246e50001340400b2603003e956092107144d510321016803104040300c80c030324a40d00b02d503403c1400b03075006001d0702583e95000b9201c40040c010383c3d101c1e82b2008000313807001c84200ea100d1100300103022070040a81c0140103011881c0e80740a1801e100a562602d4104204648040210301240039032002d000784024160230012481c1e40e841c151030145000c1042d400b40501003468107601181036486a17501902c9607038400011860400c41200c180c0d0030180380c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 316741618 1250 316740368 316740373
    0x100c15052413020f0708030106080402010806011716140a0e0319020306010e040807020d0f0c0e1017030d09030f0813020603041b2103030e160e101a030105031b0a0b0c 73
    0x17050000303100c000190b00806003541c8290a5050a200040281074041c1065040100c070040c5104805002e000c0c1d0342d0040c00c0311100f400360200045050311a1409003214228044d0301181c000c004a0300005882c003220707800c41c242c901c0300a081c0101c1902800401c03006c4d4065000e040180810880c00e21881d410900800045003490303003560000f201c020050300c0440c2c804040d401c078102001a0196280c000d4804c4a414071403502c0c1075003000550304c050f44104520311207984841c0d41c0034032041c82221600d41c2d013500c00707000350b45440c2400760402021740f0410000405820004581c032022491006015034004d090516580762603c0311905d0200e00502c0068130099000c0000380c0c124040c1d83c0c40c038020301140c0d15558400060802404503100310000ca402c54218080389400a4500c00c851400d880703800110b0301e40f50b141c0b0001d14860004980105500410540c03000b8408030b50000514100c440440456161104400080700f82c1c80560302c0594200000722400d2000010010150010307107002c404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 316742868 1250 316741618 316741627
    0x6030123130c0909060f0e030315131517030307050403060b030c040c0908160302030a06090f05030a05071e0309060e010c020a0b0a03111206100c15052413020f 70
    0x40d0300114800070f500031225103030f032a5201d00401209000e460068800301710100404050341407401d4407841700071700f00c095542029480c0705045d1b80e000c001030341c810041803042044068401440e800c00180d40103001441c074010051815807600001224403a200320381d01e06041525642c2c51740f010b04540c0601c590305d4003038401c11500741e484512038100301080c1c0782d80e00d0040928000b01c103030401c8510f10401d1345034500c00e201480980c43c001181101c150f44558000340c1d4031702e107042a83d4000302d000c40003807080c000001c0904044d60f00c0b001034100c0a0080c122000f0070f8048000202a6144200009001c43c408440030003a1a01510b6402c20040040c1072090a080c001c1e800500b01c0e9105400400941c0c101054101c0d6455041c81150b46e41182c40f01c50318500f1a08902c1c0704410240180307818130404140d00700d0300c0c10b00c0c4614440c8803100e0340850020b800300d203000c4518018141c01ca81d0040e14500e550982540d1071104c0e59181103d0101510070141c00c81e8542010700a580100e2480400000800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 316744118 1250 316742868 316742873
    0x140303060f032802120d0e0111010b09010e0c0c07080610090506130e031e0d0b0103020406050d110f0a02100e060c0435070305012415110706020708060603012313 71
    0x807106e20050300c0d40c5d481080c0c00c031035640050304980052004d0001c90703144c20b060400079140e600c1114151121034000e04103c1d96043e41501d000d01c540228081640220540010000f400080c0c05001e020302106e5525030503240d1103150122001144c0035075104c40380c0e90000c4141c0005502008850a03100e05480c43d00d07103800704001502a000c0d044800c22200000c1c010085002841003086a0100346000d520f0030b031400c46e0041c15401807100100c1d206944605402810071641c003200e04449074a5143c0c1d4035070b01c50030000b0b0b4503440c03030880c5281c55a05026071320140b008007054140c440c5550400a0307052a00703000354030440c0440311114660300c40f9400194003d5008001c1040054410718004140c8035003149051340c25281040019881241451039000c4003041e00801c61083d04c0c01c2e01701c42c8a20b080748a03000c4030010302201030300355140280440841c03042e42c00302e020030650703100400b268041d80310034092500325940e2080c80540095100c0c45204040f5082d0390307894018000844c18402d01c08540c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 316745368 1250 316744118 316744123
    0x10507081f0f150243050a06120b01111c020a080304080715050405071202030c0a180c0503040b0106140705101e090f020609010309140303060f03280212 67
    0x640000040e689520f080356507141c0e040101c01c403c120301556070029011140310400e04031045540d80f085554084041d4510403614100000013014002c0400d0380b41e41c0d0f543c02c05030244201c0b503144e40e1724a043c07040080752540645038004a00a010005007043c9140f030020380d00d42041c903280d8100714041d4000c1c04002c82d8400c0c0103540070b24025280c10755140c4041c03130681c00100d50041c181e0b40c042d00708001c03c404558081400000c8a000d0b0900c844400c1031480080d042c512a44d405551011544001042c0208620707841c42c0343c1c1c4c8002008000140c2510f0055030580421a001031000c0e124000602200d4403ca1030400d500e4000014141000640d030303501070808414500500481c0c0e9181c2d055425000e200e04030071400794218004110806a0340c83d0302c00b1280030711002a00604001558444991090348640001504440b1141c0c648145001c416120b600541e900c1d442103c00c500080011314020400d000c07506101c00c8a0810100c07564030400088880c0502a83d00c030301009038520042406 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 316746618 1250 316745368 316745399
    0x3090c0311030c130f0e0f1203100b0316031116080702011103120405060f06060d0c05040803120915160c1a070305040b0c04060504090f110f120603010507081f 70
    0x4c030400700d0031495080140048500e0f0310b0341d039109940030b0510007441c1ea2000c600d00c4030340c181e442d43c031555036542c00d43c00e60400781181d8003001106000208008441034160034240c3d040209640a00c5081514202441140214071540c0b0282d1070701400d0300d00180407000205007075481030605400919046100c01d040d600301c0700e10b1170ba0a83c8a4000c2000f0004144a80c640c092064001c00c022410324502180f6a40034401d1150403e55644904403120f42c000c0702602d000300200700850b41c0c0c405c6407480ca03401000307064501048a21404a040080135403c0700001c2c0705d024502c4205c942290110400c4580c15024101a1000110480c9001c030700700888003a80c0c881c00c0c00c3e0728007180900b807915001c0702a1b04010310407405550288018040141d02100300c80c200c81d03070304902281e060301900b2040b000302000c0f10302c2c0328402000688040c2000c500d102a007110482c5d4a00380480c0c0d5600d0061500740e800840b50440001d03842e200041c080300e10740047d040b51a52559110a91644854119244001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 316747868 1250 316746618 316746649
    0x306011d0f030109140c180606070204060b0a030903020c04020918070c0206160b0609090d0f092c01080f0705150d0c020f0d030b1e03100c0c0c0603090c0311030c 71
    0x50400c5e80c2d1008440c10072031420f100f0029a00001000c183d0040c42d28800405404a03200d1000040d00c00155615608000c001d07202d503000ea660784008096000e401032190540440250154283d148180d141034800d40b20700c03d0010703040c81c4603600d000c0790009084100501c45820312605403802030141e21040b000c1d14294490b04000c030100503484c2400d07050408000e2580b4030400904040140c18117021138a81c2c1c00d038415082111100c0700300309068131503200b03e400480c175061200441c540f5030030150101c00441d5a94891403026640c0b1205030071b0f00c1d503013a0400c1c0c010903401140100004d0400000c04514400c1c08000142003070b080e46001030a880c1c4c3c0c0c3d1a40790040e80109882603012900b4800840444001e0804011800410001c24515044000070030364814441080b90050b4806110340c505840e01020200419141960080e02c0300003940310581d03001940c00e074041580c50107803040070070994103c8a654806403a5a85950100d54001c0a058043c061340c422124540c40c0c0720101104101c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 316749118 1250 316747868 316747883
    0xa03060f210804080a2004051308030907180501050906030307030c080904020d0c020c0103050c0909040605130f0302070608010e010806062b050105040605060a060f08070207050a03080c120306011d0f030109 90
    0x3502c00003011035910030031b10540c8103d1504041c080c10600e8020740e04102903014003226183e0ba00c2400c550b007405c5055000d110407580400b1510300b15405907009505880f0125400d18031038491000389036407070103011001404107180c040040e000c6200303100946900c07400140090301c0d200c421725410050707a0260f007101000d6404240f580d007507580c150007540e81c0100b919880a042a00d11400281e5407080500082c2c030980d9108007203414441c09014070803289400c481d00c107405441070b1400960341ea03032901c2950002200c0500100d940340d030407a581070495461500902d2991109000c005140c0f0041b0b000070014418800489001810040040c4005000710000142c40c070307003403c0400940d4801400940b00e03d15010f005d01125802c81002c1085191038541240241d0390101e0591400030f1a400c86075004001d04800000c00c4109802440d1460105d070944502d4041c00e038082816001c20307503569002ca900d10306411305840412039030340407144006044500c0c1440e400d001c03d0844e007540500781c0307081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 316750368 1250 316749118 316749143
    0xa0207083f0412021902010c0f06110705120f0712090e180106170303070c03030e010504060504030f09030c060c06020f0f0403031e02060402040518120a03060f210804080a 75
    0x141684014030790f8107080c006851003003076401c0c40c804e07418010b02e0020305104440c0d030000c09009038410510112136200001304140d242140d10000e4030b801c401021950340c8103008068170f9000080d01940c411440490007281410341d80ea1711181150451041c9501300003030403900040e1610307070b12072150080300340502500f82c4640c02180c02d030a560158000340c464441c1200754440c1d42d000082140c2d40701c25585405421210f1602d003c4020b01140802000744d0741c201001d1006000441e0f22244c0a00e101c0c2d12100c09140074050156a8000e80b40b0028252080c4081c1c1041218041c1e0007250040d403040c4001840c0a01c00540900c140c1c1001c0301c010a03801c0c010905004040e00300040000200e03850501400c10046040c0082d9a1200208028003454031400415003031402c400130042108420b0086e515401c008410820942d0400a900070000b410a030300014138a4a03003d02e00181d8034036000000841040040300001075100c81c030203c2c0e40381e030b0400c400140c0600074001d002c04188202d2020380d84 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 316751618 1250 316750368 316750373
    0x15041104060f02030405030304060f020f0d031a09060d060f0e0307050604110102161a040b0a021f0b150a09050a0f0f06032c01020408070b04030b0a0207083f04 70
    0x655a0520881083d580104002e000565001050f6002c03503c485c9040300c415101c0860032424950018100c903c2ca12078210b0b0001030b560544c2113518600c1008041c0c890100140d070030444c02600a640003a080422012142d011603281e401c2250403001415002c16210001132041c2d02e141d0000d401581c241c1c00c1441800200310340008170300380c40717202480200f13819503021419045d84501e510500d683c0f40b98804046e43c0c2e041428003540d00918245100546441c0c0300040691245241281c028803003583c59600812844944144d24241001030030100b021046c080041116600586480381403046031480040c00e56521100f80010340410b80c100701c40186050348449001c00c50b5000401494100401c039203014a054012a8152000059011503410f98415081c0207204076088852140115103000c94612200d40041040304d115000c101065551009400102c0c026240b00416601c82041542c200c0b0100c43c0760202410034020140801002403984c000480c01000c010b01d44226008080009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 316752868 1250 316751618 316751627
    0x140f0c060906060918210a1112092b03120f060e2206020f040812040b0909090f060a0c080901060e010501030e0705090103030e24030105091504110406 66
    0x400c51a01002000141001d10005400342030040c0761010380e014a00017075010300c8007040744940f4840e460340e0290210000e05c901440c244c0c840011200418200a0200268003000884601203849155082d04003103001c010071025189020010590341c242006001d400c2c1d400107400d5503820f110382c0f1545030b138007256110002a280c81d9030b640070045140190800c80d0003180b034940c50f40b0000480b6200a1755940106d480310300c4950140161400c1d2021420359400d1041d03100410070b0311301000803034001e0000c520b8a04903c1c400c0d0f0247c003800c444284501022420810741c140d401180e141d082ea022039030100c550754944001114841c4010351100048100c00341c2000006400c44400002030118500b040c00424a0a40c1031003024100b5070784200d00c0200450070b0240c040a803c0044c0001d0b55941c0d01d0070000c0c4455076001d410f601c96144a090158441c1e00c01c2510405010503100340b41c15a132a00003045040c204c014205440421b610668600542d107078800c541102210a0703078181c440d03050030350003803 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 316754118 1250 316752868 316752871
    0xa210e06070504030218040303140a051f14040213081009020405060f010f050c0a0f1103060906250903050102120a0506060403030e0402070611030a02030403030c0c030c060c140f0c06 80
    0x2810b0090400040c00540c07100b4071341c1880b01010840103402c82d140c1d441c00328011300a4a0440038101490014008448195003026002e9180c41b0114590b10204c1900d01c00420400c0c4a5590540034244411010f42020780280c8041c1a0b0345520642c0180e407017896a084c410b035144500700c200e03650310003070b41185000c0c0300d2580c00010940328a115010700d400064401c8040202800c2031190114041d00703010010465141101e03403054040f1552889841c2501c94a410308503480d209000e0b0f44000307000344c6000104548a026452500b000195102103d000c0040c00000348004000101d2000700c08114240020042c206034107010400a1602e2441c030411a50090300c41c0c0c5c46660200002c001180c1e1001401107514070460300140e595040346401402004480d1130f91056440120400c071700900c0c9580614892806502e05010300d214110044031882007042c1c0080116902d4290f28012910561240758200c01c5400c024115956000060500390010070301e4803031511002551008100d000e21245 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 316755368 1250 316754118 316754131
    0x301080610060e01050d090813030c090c08271002030906090708060603032b060b0c01180b010e0a0b090108070819020114031509041211120a03020a210e06 68
    0x92505090900005c00d41c1c0705e1202c00100003521600d02d0f000340501c4904850b06110211282240241c1d03900e8410810303030152080c6c03446a8940300500003858000c100e031030b104815101d20255640c650002030114540d01c1d02d1000c40511031324054404282d02c1d44019401502ca1900601803454550526450b0982c20b4000f003a6135001201848440d072000400d440c0000c60b4840641c21001d40e14861400f1480382c9640c101040c0d0400c10700140c0d8441e020000c0c0f140b05100f4000740280b041101c515211402d040000400c0620144010460306480041d05604581200310214050741d103440041c403818402c0c0c001c64110b8000b800308001001d002c010030800488554241850344640d900040c044081c01c141e2542200d50010005556018540503000642c40051100e43c0c0c0d414a400e020301000c50079500031000c5035800546031145240051200b140480407200d6a1405400f018200c01a4001035011410300543d2038645484038815240c00800c000c0150001645130242c0307400350318045020741071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 316756618 1250 316755368 316755377
    0x150e06030a150902120a0803070810050915010323070207091a01030b011112030417030f040201180b0d0e0715020a0206030c04091b0e030f0c0f010e06030108061006 72
    0x5000001c031100741140c03a241d02c0e10390010f040039803800414000e0951100c580c400d8058544000b0030003040201550080700540e89100c00c0d640c075104003400b5101640540307588a0119000190301c1c0040007640c0440032410724000c01c00140c405a408458038003924500415002c07d0100840700703a0411211000b4699604180440c4040034a0100c8040071040c0341c40c100350300d4100d0009107900642c0110300045103032048507a040d40100c2e1080e130760382050360300b110003e200485d48411041a041920700032501500120800d4883da8011f450b400d07191a1421502c0c25900400035108140034050070500051034404100d0440c1c0c4c00300310381880819004403151602008402058a034001030b0310a005130705031469996902c944404030071038007490b400341c0229818103001c400c40481c0f07102c4030389404209440b094079141064040540b105a01c07503003616a5405a40c10024038508545059180081030600d0001c82c00034901040b0303070ba40240c00640165010320b0602070154264121200100050700c0c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 316757868 1250 316756618 316756633
    0x70b0a1a190b09120d0c0c0603060617040c26010f0e03040312090504021908010905070c0f0822030b010b030601080c1308010204090e0106050d020d14010e01150e0603 73
    0x1821006035940e07020b500c2840d480420318045070b0311560341800c03a0709800d004031507401d108424024400328000304201e031406d03e030000014000303000c0d025250648c1d6040e100c1104102149072460001c2100403c2a1501c04400c0400035441a128502c0c030106c00c203a8081c4c1d00361207a1803c9013825503241e541600304080c600051a0711005021054405581d44218000b8601c64820300c05c5600c44400e8105036440351000891741050184920012807a44a80d150b500c03c41e82d0310707172030001140e400311140804501c451407141d00090050802d0504548580c190300c0c140030f0042407400035540c281c03401c40304100e6a05828028410702c900040e0050000c2d5104038518501030000828070703107020340184d900880100307485520207200102c40b000340c0407800c002c41d1070390368810150b03010703281103a1680030740e501c0c014001c41d69040480d4014412078010b0280c450a052a54441c107860821f134113558142c0d5039030304144100300000e008241740356070440c1c8160700007030070301004001c115030140005110b540140c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 316759118 1250 316757868 316757899
    0x403390801142203080a02070c14100801050306150d060507090f09020301060e061b0a0506100f05030a08030618040b040311010b1f0c0c0e07081006080604020a05070b0a1a 75
    0x80c500c0c07403c140e01d40780007200c0d9162030700c0c2c2c1c1010b80101140100000180c10300403a070a60501540a0441d404440d07410344019a901c00707440c9103c0a005058254002d200014a209031002e905170120001a042d05172151464480d0003c4a1040da032800024801c80c00070018950818040005000d10b584214030350351600b440030300760120400c81c06010b0200800c03201036a50340d41ca011980c030541002650116420707450300680350070048440603d819550600454040a5a6000740540d0406401002040080d80b10a5065007000700110703401240c149908101d101d80802a034001c5106108e03d81182c00d013441c0250281040d131000c2c60300c40e8075064095401e81c0d00c100482d03541c001d07541ea440c103615420500490311000e4420b030250400300601400075541e80e044001c42e110346e002d03941d0222641c0351000000030580c8103110701000030b00c510000c90307e51701d0039a0040c41c6c0030466083c11403601c5816540c0b146032800c100ca02c0c848103603540c02c120304114070506503110080404c07a41c4150610501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 316760368 1250 316759118 316759171
    0x3040b071b050904060b030d0c0b0a0f1b030221060904120e04021204020a080601060228021f02210403030c1106120411030102040339080114 62
    0x10400034064004000200d00141c0e11100c1034005010040c10900b4140790034180140500300028005000c3d1144000b0444414460460601004c1d8044c1030203d40ea04e40024250103841c210040c01c80c0181c1d92086440014180b00118103180c0d00c0f5200507132a44400030400d60101907a810303219000c1d00300001c11059584243d46158042d03409444a0720586c4900d800300c580340258010545c04c01d10010f245c4251640d0f206519220320320890f24514516100c640184d21000d0a11480d0090307800a2205025141c04954603085c1c40c048007a14924500580c002501d244042040a41e10500d0605d060001d0380d8144900500352003c41c600400c0c00704103500c0400359220303074403002e001c001c03a289001040050564540214180040c074242d22100100c0c1e0405800b1070a884c202c644000a5078040618107040c001c1c1c408880e08020300640c0d0014085045c141c10401c1c00c62500b842c1441510000812841056200505807000000491100031f52040524200182400088203019240804c800e51035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 316761618 1250 316760368 316760377
    0x10605031f030c0f05040614031c030e10050a0506041505010f0309200306092d0a020406080c03120c0a0f1b06170703050709050f06071a1803040b 64
    0x1215200014040e00021a0880c41c1c090b04010300310700080500266140c00d01c9048016104101e1741002042d039102441e060038209558001d400d90440364031440b00c0d203000308065500403054100800c0780181d5200e99410100c0034502d0807812581d84050100801d464403c040e4800340c150f41c00c01814401041c00307120003409103c0d60341040200f068004105201b50442051030b5400b884040d020245607502441203111940f0700750092064000180344450005080c0c10104c00a0a12511305201c000b00c68075804002031060341c6500c6004111030058440b84103c1000708842c0000e4890782c410743e004c0604100c0415400c0c9600ea0007800f4001145502248501c1402e80c801c0c1d0741000d150b850301d0a41c040600c0c1b0600c90181c8140318000081c0d564020b410580c051100e48520081542c07800004d500f1100c0a03140c0740c0005d20f411400740214100b100e910040708030010210b5080017a00d175100d05c0c15549401510310092048000c1c400b075040001454000e84400602642c02e003401e04034880100e004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 316762868 1250 316761618 316761631
    0x602060a0609090b0a051b0711190b07230a0303060f0b040602150a1107050c01081e2a0705161502151b16020f04020307020d050c01230109050f01060503 67
    0x2c0e60000300b2901d00c090f1f0000440e0070300314414581c6500c160300380344002c00c040720360704d41c01b81c0400901109045a03020b404c4040d104041e05550401099494080e841c81d400c00f060a20301c004520413000704041005410216446603a001c100541480120161190750b60b00500d0450310500c018040640c000c5103107031802ca141b40102400e580c0e840085006800700341882d491404c0001400000c0c000b010401d031a00c03c84c2030f2201107035525030345201d100c00c02c04546100c03201c2155001080c8040305d8491800b4500c2641d6101808801859440300000e5019010031600c41e405100d05132102100d21205000800c2007100050750050316001c081d444001c0b401050b0104d0350024006036150f0b5050700c445d408550001d003101d031100c01d81200450707001c0783e05009070321a00e552811419035140030b00849200d50341c240e014001c0c0c510f151100fa84c2982207600b03294860b540361080c0300310443c030317a42c1c0c10305101034801c1680c5020b5140248030801c0768406085448280010300050026070b40080440760800c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 316764118 1250 316762868 316762871
    0x30605040507171203090c09130b01050901060f0e040b190303080c132601050c0c0c0d030e0f010509060f041d0405070302092a18060301080703060504020a0b03010602060a0609090b0a 80
    0x86e2040356003030611048030f914990140091080c800e1550030460b08403411071103188a81010390b01c41c0204640d83c0d03003d21900307001601c2e040d1f41802d80392086810030f000440140011500402482c0010404400c0000340c0700c40034188481003042c10391040050b900801c01c0c500d8039181006020740310104a0301c0d4081c100484550301d501180c0103401d42c005801c016081d4008103d1400c103070321004220307480760013980064130a5801b0300c2203e150420400c24901d5050f164028000042c0091281c0c000c0c21034225414001c00344003080310340d00c0d900e004000da100102507190741d850811850350040c1c4100050783d070030007079014100000643e000880c103003920b0b012985a4940d03030700c01058a560400d1030000c200000b4804210307800d42040240a454000c46801218000c030b89070209000681c00f091288140c103034000b200410105910b54840c9400ca03002601a40c0c010351a002c03841840c0e03000303030b020318010780c8100100000d0802603c80c090207480046810312032007a1540303c0506070304002d80880f0955 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 316765368 1250 316764118 316764121
    0xf0f05120c130b0a05030a0e19030819020d0207020411030903030109020711061b060603010905061f1a09130203130204151505120f0108030a110115030605040507171203 74
    0x9001602c146001000c0480032a6914844410001c00030b80090340d00c25489414540ca201c1030700740109032181031610405104621201c41e841c100d03500e40b405050001840301d009828200b6001072300041011806010300560b43e026684107020448080b035402242042e0180203100d198240441102c0c11035041c1c140150300c411031810805081115000815409000010010243d0711021080f0203034442c00d5080c1c89040e9100300602d401c0e681e01140061441d00312100080d500c210001da0350403d94440d61300c91040c0c503103070f400c0c00450161020040d030100d500070a44142c0340c41c00c81c100c4812007007012010341c207504144140c580440c040c0750009205035122514010103624516890740208400304010254096402020384194000112610b074401c43ca400a10b1962003074034818101c1d1200d600861030302094240c1200c0e00400240745003842c0d52500e1005084110b11513002c0e02a60140e800041c081c2031900e0501e15043d6a80e0000203c40070030f0740e000c245e200780419251210007056641d01c0d40c4e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 316766618 1250 316765368 316765387
    0x1c0b0c040f0305010510090c0f08180a200102010603080405061b0303190b06041217040803030709051f09060516060c03020a020709050c0d09080d06060f0f05120c 71
    0x160040760809001c12405100c000706000054200301c0c098041003060341d0280d03459600000940300321010600204455156126070a4401d5004560002604402809906003480058103001c00d6000c25502c040c550100c5c1e075000d5803505440807192100340000c002032442d65903040c005000d03511803d481a400414000c0400d030280300c0d01d418000d00c1000303580d560324220348120f620314845480311900314a0b08038000d000d801c1c0201101d040c3c030011481c81c00240c040e6514003800e403594200e0003c03c1301c018000041c0d1000108081c40c0114255203554001340e040105010184e81104410f4041c45070400803048038176081031301a419140b05181c266600c800941543c140f545403400f00400b407078a0304109d016210352641c0a401e0902d02903080c1ca2140d035841e01060155502034489940e25801007040000111141d8010b1810b984100c0c4076a0400c20212400012500390703500c4a0302003030f11000c0407803510754000041401040350782845402d0019420307011024a200601220848030000f440b04035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 316767868 1250 316766618 316766641
    0x605030a09050f0607020c04231e01090c140a0e0907020f07080a0b06030f07231c05060912090409020301020c0d05040e1311010815131a1c0b 62
    0xd80580000440343d801d402c48814580d03500c411514400140180b401000071480d150042d04040c0708410150b00704921030721054940800082c090b00005d94040e0103181d203180304180c8150080c008100c002074880314515019080c00e24030540301c10000e10400000d824240c02c01a4202007034010ba0360310525036120307107060345060024604015648a2020300007006d0400003810040c0610446000030180c4441c420705960300180350f200103907500310404c2803042d01d003c0c407030302c101d800c0c05a81020400301c00b6101080380c0341c12b400c405020305c3c0085143c002c11302c4007c100c0e86070402a01002480450036840302c810984c003400d80036a20a0b41c840018005641c0c09406440a40ba41070051716045915080c6c043c20301c3e48244507800442d2500c00008120b501e00c03036420f0395100e41082d95100c2032002030004441c8604014010f0007400c98907036109006849050000c0005d6603039240015000c001204010f01500401d20300500c113034924030307405944121000b4070b8942c1c0d643c40f158244054549900300c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 316769118 1250 316767868 316767881
    0x9050403020a0b04240614030309060406050a0e04020304080901030e0304080a0f080f1309060b0f0304110a08030a030c021605061207120f020a08070215130c0512011b02030901090605030a 82
    0x1170b1005022517802a03203040319404a000c450300d181107648544204414542c6900440c00308583c4a00c0600080040034000c1008000400e402d00d4010480190200054101d07007003500c09507150300e004240700500c3c1d41c240c4100d42c0186804401541860f217400e440c00d50361844528000c0241d070805004c0010840000c081c0c9541c00b60f00308480343c5503c1181100300604245224030030009050040005410114400711740321000034100c0795255940c1d43c0c642c01d01c0d01281082c0d09411aa0001c0001070100091029020000c0c0503500811101c02d00f1038005e2921302288441104400c9203842013046556280480e8070101094098655503641c03940207940c10b0411280003d000b0341802c08032002414154014094000d481d147e4089a4072550300480c0e0300c01d141118141440d44000214108070205081403052038410001041000c3c0c4510100f40203c00c00d885483d001c1e07440d0498540c000c41040c0c11486004c1d164030045044c1082c10300000c2c04031302c00d07200c0d00050002c0003002c209021411341004c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 316770368 1250 316769118 316769153
    0x20a050109050d1814121606090f050f03060f1305060403050306010f081005120f1509010c080f07030b180403020d030e0309180702010612050f0709050403020a0b04 72
    0x80000c01664140380743c07104215100c5800262541c6001c0d407032890b00d40c240394240c55032a01c42800490901090244554015507000440e106102c44420b090030031050380c1e005041c80344d945042c480d1800803c8071200e40c1a0300f04034420fa01201420b2665100020f855501c1000780030800b80c5030b00c030364803118417904041c513005d0014084c00c020881170503000380045000345c0081c0c2ea2040c1800e01c90000700c1c0c0740c02c2d00351041e00107164680c008000ca0301d02070700807250810002c819180d10802084400b880c18507050040300541131100104400d00382d0a10500c0d0900710703c7d04103070000c1e18122921807a0382c2c3c80104a2418166180c14103003564445031007010381da40311550480d049003000d0502075690794940510000090030910180e545040100c02e483c1009000790450b100f908180c20b404800b0140100444119035840e1030001c3c101d0201002580c001d8060800303007551704202e00752303d820480b0300c0d00181d0816080009010010b6070004030700d0b00250b0400300403109a140d52821508060701c01220 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 316771618 1250 316770368 316770371
    0x705060319110703021515090708060105191d0303070305030a020d0603020901060e0405073e01020a110c010f0e040f0f05090102040801050108060f010e130602040303080906070c050706050a020a0501 87
    0x20f00b010950002200c03042e2484a1036a03520310b513500813070400d002c100c000e03c060308040e2403000300304072034010810650007030f40504041c0c1c1029100d020005d206500186803100150054002e80034040c070300404450b0100c8103a01031441d00720070b620040d12510000c1e0200c02c0141d40002d2012480e452940400051903009249078201e582d01c80c0c0003010009804070980c401c501e4800850101409503071040f545d0641311100c03003020303a2021700b10384075004a00250307e42400500b42844d0314002c28801000c9101080c0c44810702c00362a41c05103850011008441d50510105035541414180c00c020070901e01c000448020816072402d0f0154400b41420410004c42c0a0800c001d110300d91006401400c1a83e84140003002a681da88011a42e20342082d83c3e40d11341c28040c4801842400000c0c1c010961100c01e00c91081e1503c02c0310369920080303a00a920a034001607000781401540401404100e4014841d40313464503001010341c4401e07494802e1441454240705c03000901519141c0244040e80309503800000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 316772868 1250 316771618 316771627
    0x40b01121406130201201b060d14190507050d0c050903070e0603010c0311030403050307200304030606080a030909020c070914070314041a100312020706020708070506031911 76
    0x2183c248065010800300e022400909104400d9034001e4540024045500c00504090030451042d0b5840c12126444070b40149007040013403a4950580260301800642620003a0a4a0060b42c21210500e00640202184e420901030141c03c43d8450180c6c1d2108450309400a42c00c2c25011050340c651244510b0550980208280010004400398001303100300800c0d0000e00c40c1c0d1903410000c80c12280c00c1080c8120190040c4003150201c0e2080c00175603406421030404c074104408a29010710320340e0140581d922241c2c40050300b8000c002041c0904d800070800400102101d00160340c010740000300301e00035686a41d50100d944508240108801002082032000030012500303400411861108101c6411001c00c0c1022131840d0000c0303448224030f11854100444000060142d0486602040081d000c800c1d103804804001c4081403800c42c035a400c125840d0000c0c983c00d842c0440207403d0550b039603c900703041d4100c40700c10407054548004a9901400318002003682404c6280d2810082014080c0074401e51f60108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 316774118 1250 316772868 316772881
    0x40317033105010608070e0c1803120702030c0a060503040b091f1a0a030213050703025206050a0905070612140610050a2d08010e040b01121406 63
    0x1d207030850080c0600001d015640c1c82c1c41002d903407110240b2560001345605800904140070707400142c006500c4034800143d1070302c4000c00080c648040100d0a81c920000080c4050451904020348488141c0c00d80b84403103814641600070b0031500000740043d014440140000391290402d100134070300c0140c0c8070040c545449030414408010025001044011390411450002c28580404082e048a50040c2401080903003200008058000a80366070207140d001d02c80c07685083c0c03100301e0030440c80541403401840c1040441d2004044124901846811702000721584101c2c00c10f42c600b844090323000300340484c20742c441c812684002c0805100c09803513800784400c0441c007103034815000b03054a1001101445854045042254510401d40c0c4680d40300c0c02d00102c000000f40520081c1803070350158240f00418244a070002200e1070b040849010441c0380d0b1030401600203400241160142c481d02080044c145810303640c01c4c500e0700c81030245500a1400716801c01c1000f680140001c00c458001c0705031006814402c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 316775368 1250 316774118 316774201
    0x30f0e041802040f050105030c0d03030902030604060915050603030a030c140d090b0108010b0d0201081513020301090f1a0f030304090c0513150c02091308030103050c120304031703 79
    0x40d000c80c0f05508154840e0280b54843c003d0f24161400240507110f8078501d802086600201010100c042c16240c102e0040940c2d0180145840340e4007510700842c071004646000c01001c002a1180c1808524100c10b00504e43c03800025212a003981c0d042c00503031414180402d0701c032600610802801c1c01c000140d230f114050b01c2c64100c020601c0c41360b480b5810f0383e42c07182525401c1e15a142c4180e50000d404e0340b400030140d0b10030079031143c100407411440d040480503940411504404140d00ba0701e4580c00000421051150340701c0e034600c4014070f003002c0204a10882d2079541d0150111842845400d0040c000001680c4c140101c4008007283c03101000301d50341c10701000c2d00c02d42201030710040d801c84a005c0069420080d008002c404065666196a003000980c00c0220030300d0064882500c5080409440d030000da8410001d5000c0c50060004000341e42e0103000f0010161010904104160814081040040e074512006c0b84071a01061070252650313200402088100407000081b038040100c1c041801e04084207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 316776618 1250 316775368 316775411
    0x11a0903010f022a03090105071e210c020603011e180510050109060f1805030106030506160927090206211b040b07060f0606050d051302010903030f0e04 67
    0x10303410030310074001c00070fa080303055512142d21650203034004014021b001c1d0311401c010007560344265890407609103a191403e11144140d042122003012200c441c01d0403000300f00303984100e8415444c0c034003002c0003a40d01141c8a40010311031580700c04014002d090ba012071a020b90000f803c40d44508000c52680301e112500a02401c0e510090141841c04011416501c0380300301000b80e4070745e0f0f2180c3e400d529a2100446c0c11200503041c0c544a8022044040b031141e8080c014200107501130341c02400d1508103607103113103480000d0340d03103490078003c0721b6008200701c0c003a690380e045485080790200040c240b03241c0707211400340c5040c1d80020f40c004d80025070b103407240e000c075403003002e00c0e500003003001140d41d840290f45404403400b010079030744080c4144010084911048001c1c480f081c032078200480d41c14512444141640c03003a820940c0030600100d84840f4111b01d620030680d02c00e1301100d0f1050100200e07000130f000342c0030a00000d81086000007007090f08a00460755104a038802a008000f8543c2190410b01c0100381d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 316777868 1250 316776618 316776637
    0x8090907091802160803090f100213090203011401050c03040e040b04140109050c04110d06030303020909101202090c19030507021504230a060e0318040e06011a0903010f02 75
    0x407807040310007250b00510a8a010705990f10102803a901a504c481246400c02000f034841442044d40c00300e28810240540382202a20307550160312001801c0728600d40304219000700201c9841800100b103410716042c01011030071000c0c28050303a5103600c060324504510994020303218180c4c14400380300c2004a0701042d00c0c821805003001c0301002c1100d101d25070070303945403001c05021640000100401440c040d400380c10a0b0710050350003450000049400026a20542d009038082036010924986500309000d84503801401b80700180c980500780802180709500300f0390007074064070740a000505428500d5085139142d064005095250344034907a80100500343c12120200107004118171140b008000103201030181e41e000f01d051040340c550301400003003203c0b000791154170740c4a1002501d0200301c4900c6a200c1500a5101560740e03002c012011b6600c1c000c580c6011801a4600924034007800808140e803415580c0b007200c064010901d03200f010f0420b02034495420303815460014401d0310501a540105940388 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 316779118 1250 316777868 316777889
    0x51c0507060b04021204060c09170102040905130b04062d0c09051207030f050c10020715050a0e0f130243080705070e2a09010c08070809090709 63
    0xc0b04503003488280e0240a400c1011170750300b40081400607400350484144880341d468100c101660f20070740c14a000d40c1d0040c02c289503960000d428015181c3d40d0090f258041900716031401400190f54031030302a0400140040c00f001da0300c1f8008000e0b0a4001d0b01c00542081051510801b044c4a0700039030024260381c1e008174082010320800059508003402aa2100382140018001952454840c2222100f04100c200e0301402801500d0702180e594880048000c07000358010146a410580c0c4240d18521101da0002031203000d2081e01029503219400c044550030680c1d4440051110002250021040807003d001013030010408503419295544031130076550344c004046c4030001c03251440d1190744090f1141007141000d9210145c001c90080360042c481c1d5445442110890b43d5242d0740380c104a903064486007031244a00b4905484034103040c80c4001c0700210811039074038050345800003924100070b81600820a40b40440c0320030a008482050350201c0c600030705080142d103401140184140094090050b200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 316780368 1250 316779118 316779131
    0x13090611040e1006090b1c02130305060f0106020102071e03110f010e06010b120609040327031109010f050114040806090a02130204060804030e031e03031e04020d02010c051c050706 79
    0x2072042c0a0b4000315001c006c0400e02d041013201104291580c1d510300c4411080d02008070380341510490001c7c600540c020070103040f10742401481d100610310181e200004581c010b00040780464060720711040c07078400d4050448540e500c00d00c0c0985002c11041e40012040c02680558004940190814500520107009550050ba21203a038403546010382040340100c081031100280e240e0070070b0080182c1180c040d0504030110b40c0d058400d000c2442407020441010703001c000c02041004030000036010b00040c221290040c80d810701c40b03680b249040b00d114090400112031803074440395181e88115800350001c901031b60394514041d0364466070380b0300c440400c03401640300080030079440704c0c54800d0b0b03819544030740c0e1480d10b40d031155201203031420a1901c1092349801600381039400e803921106041002a008d0014548030702d0a0044100c00f102401500a80ca009850411005980d0f08041c140f1090382400c007061580c0a50400ca441c0940c0c81c1c0e40f0150010780c00124240d490b4010010b80400c070301c5904280800c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 316781618 1250 316780368 316780379
    0x501050301080a080a0c0804030c030312020715020f0906070c210314130e070801090b0d020310151d01031b120224040e010503060f0613090611040e10 66
    0x588024402c61115402200c101c20018051000500384010149044c0c6612802e58584040550042d4070480e21483d00c1e0b07a00f00200b40d0403820b00313250305980e03940860422049444900220103100b04903100c07541d0001e008042c0349420002d490b20004081d0015840c0c06071803a109c424200c05018a041500000111290501e0f4441c000300b0116810340e212000d10300303c3da8031040180c0040c1e4020484c006040f5010981003000c900315445000107640e0b00440e94580b203085411030343c44291082c02041c00102410160700c1c00035031650700a0100400145400c10b400c44000802c005811009181c2039411842c0990305581c81224141d03406212000e618101c20200840d240b40c10f403007807986040c00c1003203910152809002020000c10042104480000c000d0200340d06a8015002403030080440030042c04039080030040e80d03910000309000700f07c1038104070740069031122407400030550468543c003000c000c1048170341014507050b000003c9981c4868440e0140d42c010001110f900c0a90b480103440080d0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 316782868 1250 316781618 316781627
    0xe06120105071e091502100f060b090d0218101d130308070c050f102016050c061204060e0a02090106050f0405090a02040312030b0109090e1903080703060501 69
    0x5400d0780e45402104091000402c2810000c40f40580c080c00040c1c50001100c4540c40e118010105081d4040e004e04074103189580b0403545040200c40ca800d2800034248204440c8004588d040c240884800c80401003901c0020030602e08a0f1b041418004404288640c41075000754450607142c41c0707103498030a01103015441c2070320942107604001444d07070b95007440c0100740a4114650000d925240242c1c3c00c000c1c1d911001d25001a00010114550004a281c2c060910700c0c81004909092540411718024103408200b520340581115492119a50043c8100b00041004030702c040900291105442c0c20740344030301758480c2c64200d4080e51668104030300d04210480100b0382400c020303402007205070680d007440421030f00e58010180c48560b0820820000c1842d6440410161082070307140000742c1c1d158290b25000031f0f124000d10090007450f042c290040c0150781c10000c08019520702c10340008180d4000e820003841c00501c0418511160031980161081c56400511584a0f8845840901500d651100111f8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 316784118 1250 316782868 316782871
    0x16060603210e2b14160605070803010611160303030212090d0801030803090109020d1202160605030411040207060c09320d0c051507060b06030c090d030201020f040e06120105 76
    0x692010120955100304140708407414010000000c0b070040c4000141d681010750800380c0c81040b100c1c5e00c84800009042242d0364560042c0070740b40303810b43c20a00d0f256100c3c100390006000315401d00c2020305010709a8903040021820303940c1e0b50703c68024504e590381000350080d880803e11520050007000080c1002d00300243c0344426144035038070b2904a80c6540c840c40d8981d00040c014142554807985003c015a981c0342495007040d006000d0b844809195a40183c5418120400c0c50300e5545030070802c0000c07a4002041e030781d100c0c0d000a0160040c00d04200000d00911443d1401070202e4a81048068015404030781e5105542c000030700c21100c41e040d22200202098441c503031080043d010000000d0608003498840e502512581942a0160301c840c00240441006000340e183d1810100c0c2c86020301685005640355000183d0b601455030601e02d0015105101d004c0c2003a001e0b0040141250405200754112440703119800b58031629241c484811391001041691120320039500d41441c5a45418113200f000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 316785368 1250 316784118 316784147
    0x70603021809040809060705010e250303052209020c12041503090c0f060206040c0504060f090905070510050d110a32182110021606060321 61
    0x20351400c600c5800c1181000c802803003103d013039a0a20540e40592641c80107001020311035000441c40040d8554480d01e0b08240d03940c4031030032860002165996000070103080d015240c00d0300e04146e4a030281460342c6802d030310071011120021504030000138414416409040d0180c84042a01c8030509054850fa00700d00540c041c00c0d2806550f4001c00c500340c2d000760b001038280380c41420018501d40e03079682d18800107001c55005d031000d40c10440c01c000c20801034403080e00c09003000700da04020842c10107109034080c200c00d00503071214035901e400032410310404100170401050024062107a040c0d003400300400d00e8100001142440341030403500441410810150f50200c1c080d9075518030f0808568801c4241034031588070b12201c070f0b4001c407031007101813044038000c1254010095000c2c50740c00080083c0413040940c400140c1c00c02c94204d0184440721320201e5050400400c4480150b1102c4000c41d0302c0340790034550b0b01c004000724130f04040001005403403030b183c2070032400d0f00480c140000031f445c0094074105500c0440 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 316786618 1250 316785368 316785397
    0x60a0c290c070606030209040b0f0117030414060d0527060105300a0f1205180f15070f03020d050a0f05070f02060c010b032103041e050312060307060302 67
    0x500c90a1041c02a000c0b85010300008542c8907a02c0d0046480f0400540d8141d036491041010000300d100d811f00814010079a002103601104c00c4c0c6101591a402140622842c00c0250060076005603038140990300d420040600070405030a0400080c0e0508003406000522403c0d01040c0180110020800a0407510080d18500c0c114074030000700701c130b840708160700711062803451541180703611020004080039034480c2e0028044034040e0309080c0502c1c40003403020401c00030200318258030740001d80c0402d0408001a12200c4080c0301303490008070020746004480c901880c0102c0d4603018000c005203402c1189000750255142d880322007008490b2481058060000b00f031040000c2c7d00c00910400c014004a070003030f8450450040c195002a807554091085212280e460780381c60384080c40d0501140b8400340410945c3d10324011107603011200c60000401c00341c41c85500d00c00041405a0701c0e0a42c13043c5a6010081d6a5030382c00b0203100c490104403e440c8940a417098400108802d07001b4030840301d03244002c40c174 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 316787868 1250 316786618 316786621
    0x703090201080c12150301020c03040803030103020f0d11040902040612080d150f0608041a16080703020307090b0c0a050a0b0906010806010513240612230f15060a0c29 73
    0x1810840020390080b4607030559409c001001c0040c01c2800648060010100170795541d500d107004005907a401c8180740d6206000140c2600000b500c154602d003440c130b0007901c010604198600000d0020710003680000d0320121454800010414000300034440350303485403003c100300c110070f0705000301e0344540f40554014184001c4060118501540f0800d91092040c0b21800c0340081003244071880030000c3e0740d1442d0660156180c2051030790803c1e91a9404034032407808604610344420018020703845131150120344d410006440024000910000c1040b50b0040d0031101001031501d8880041c00d42200c0c280c0341401604000f09210001080c1c1ca4100d40000b03010301011011100110700030120000019a46540ea100c1c004105d41642d41e094020071960325501c0c8a01c4c60341507224103440343d0303240d10505100401c02e54512a0041c20303804d07030040d0038608050b1144d580d140301d4107100441103514030750203880410941c0c122607210084440480c403441900307030303154143e150700d10000c40400b82c2ca04810303e9900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 316789118 1250 316787868 316787881
    0x20108060d150c05030420030d030c1103030f0108190f200901060908191a0c07140304030614071719051e07020f1504060605090703090201080c12 64
    0x100c540140a00a2404041c072980d503400440c212203415840d100440c5002c0100400c0c04000040c4500351f00b8041061491000304200003a111602c41d810b10781890f640d08c09400c4030521803845610300c0d60582e81181d642e07050021481c03ca64109200703034a51840350450307104560083c6e0020050b4180e0000708101c41644690700c800c9a40d00c82002070780000351003295910719540e8035103424000d0401e51281c0ca001410511445d00f814040b0741703c4681042020100c6000860a082444107500e62070020000c40e2a1110b4401c80d0303206403900608600305201c41d488564402000400c112445001c00300121402c18026484030041200c1d8080030a07000b004802c2036801008610f5880500580c440e03030003203040b0300100c0841e0002d44100c03201719860703076943c240710b08564041a040b240c18001449600e01403045103a42c0c4080e01507215942511202290030008076411000180c03400030440c42d890702d480705e0014000c003034640c010f90000c3e0752003000c02d030004a104200c480c4084d1306055070300d4558804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 316790368 1250 316789118 316789129
    0xb0a1406030a020909040b04020405160c020d0c05060d0f0605010e090612070510020f0f060603071e090207030201151403030703110f030703111002030c19020a320a02010806 76
    0x740b204203519002c01102d44982d0b500841070380724a1081000116500706401400300300c8600400c09112a1840b004c1c0012154120f41a20000c1c6d904440440071000545080d40c5a1803869104641004000c81c044c010a640d5400a003540461428208a07007550350004658007455114159004003402000c111541400803807c0440d5000b1400c07600c0c0142d846000c600c0362600d00c18581c0058000c03100d09212803200748000003100035190000c1c94503042c50000642ca680081c480d030000740e0700d0b48081c12100c8805000200c001c20801c207045499101905020b40a40300d28907102080582014011030414540c03c036144c0c040300090000c2d41030106aa400f0740b42d001550042d80c80c5403041d1020540d02090820041140d03620a5071050303500c0b107010000743e15000c050054030942a0041c402c0010f00103500c07003a80c101020408007600c0350143c0c0c06042e1b0526600c4100070340603000c0000e0b0043c1c180a0401c1d02880042082c2c05100445034103600d26884402d050b100034002503e500102e8043e1519 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 316791618 1250 316790368 316790371
    0x190501061b0f020901060e0307050301020c061603090f080712020601240203040f170727090f1202010b0102070f0b030f07090b0309060f16090b0f040e0f0105040b0a140603 75
    0x5000d0825a0b0750a5000a2103c503070980c8854006011a001000b5904050000307100424042d070003541030400e402101900d5a0380180116001e80303041103611324261103604415031094210810502c40c82c3c80c0d080811143e489480117561441c083d0b040320076010f200041d80b504039070000001029003c1000ca441c59030410900401007103100074400425003070350500508005000303a15540d0302e10080350b80a28103095017607001d210802d01603900104440340d241076450a03205103000002d244465490120ba26107202000500105445401050902d40541c0f000c0f00040b026021980003a50340c0742500345400c51806200c0001900b0300102e10181c2588081c1134100880303042402d51161203140340041c9030021102600654000d5044c842080c03a801c400c1e94103d400c10203c003240d00c111100140030603240d88141c0405510024401000d17450000030781d0045d044610361100ca0381008982185616000e000381e41c402c07807038a86070031110301e01025500c2c221111f40007030b56000319480c0d0420289400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 316792868 1250 316791618 316791623
    0xc18100b0d0903020712080f0702010908101d0d0c20130203060117041e020102010b031501031104060303080a020705010f0c020d031103070e0d0f0204050103030206190501061b 77
    0x204080411404012000361402114000c000038468410f410b0081c07078803129520450190102c0c200640129081038100d03440d08501c12801d82d614482403004a8800c4082e42c09a882030051000c0030f91103c0030754203d06c01e2101d8132a10b4045052100c400a511400200b44400100d0116a120400240322600511121700c04141c0390010010501c00315203410601a441c8613516800001c01200c1c0d80c11601d20032000e2103038141c80400d440c096035104e0317540521194000f4044040b5804208682c801d4108080340c1c5405000ea4020040da14403c0c80600020b010403103441c8144242e54025092500c03901c0704032901036860f80d80c2501c0d11101c0364000d600c4035100784c0d46075407107056030301d4a81a140140001184103500030040d1581c4010010f08a030340342c01045403844020810b20000c00e45c0603007064101c5004644c1548105480d14128084030540e250080d0031608120000040c16004605217204841095400c0031140451490500302c403000d020350781c0800c400c08010026070b1507407100403003500d1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 316794118 1250 316792868 316792891
    0x6060f040b120a050d02010c0c020a0605070c05120a03030e1c0f09050315060112090c050103020a0c0b0108030712091d09012c010c030204031101050f0d09061406030c18 74
    0x2818800c028180345510703c055869511001c0840310307072076092181b0ba0740030f40d0364503010132020080e5002403840d000a126003401c014000c42d860091020500b8000c0040800611640c0b040124801140c0c486204640c1600805e240a108910307a10010401c141c2c4908242d98466071741c00021400e03258004031007107160400202c0e52000c45c1c0d6440410100d04000030070303080301200f803a099000500d07146040901c18101c41c184004040000c03510b0302d00c0c000351030382401c2c00360300c07401c0380401100d8507101104c0180031408181e000140a6a0110040c03d0290103941420154180b0041c29507040040f8440e0701003070070b28000e08600110407068000e80102c503450010407108c0001e4004000d500c007441c1381480003504128000b981540034440d2074062003003410107504041c51038440d811081900398425050000000352126041c0c1540700f15008140c0c9a0b03000c10842d29142007201c014001d0309000710180c9088404101107140025103501071840090004e00321202004203042c00e10805414484d040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 316795368 1250 316794118 316794139
    0x301170a12030b0f03030c10050c070f0807020103060605040b0d0209065406030405160f052704150204050a0815010608010b040b1c06030605150306060f040b 69
    0x60241c048400008460340c0c0c08141030b80580b04018100390404186413180d07204005c5420411030115028441d10462030000626950f81841140d031441031300740050428400f0a0018200326540e00a098a64001c1c1d07402c011054465505590341d205a003c3d6601d042c0043c8540e08204640d6001003e00800c0585a14108040f01704a0791140295906400e029510003151384080c4600149900711751200b14151070311144056948048201040c20302409010000001414401c04000351614043c20321008107002d50f4031a0000480022806a00c1c42041030041c0c3d03000d00c1403400d905002c00b425030610070341d0307030749aa41e114140a40913041508180d5001d010006040d07549030140c1000f00111406001480e03003002da414800d0703074140c02035414030070450018400880f10505031001d0369000d5074070650b510b2400781c000e0000c5c1940302c000002c450408001104101e010b402c040d01075200030010516038440d03c810941c44c3c041c104c0c1e881d600a2035040445c01c20f0300e0a81c2104004441c05416103005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 316796618 1250 316795368 316795373
    0x6090203030405060c1c0807090e04021203130612090b010e0402010e090a0b0909011505090a020c06190b010c03120b1201090b0603060108070303050a1d0a1403070801110301170a 78
    0x3650480c0d10501702540080799440014540120940c0e442d140505c2c01d00214509002d0261814007580aa209000541d100180c01c5403564000000307210300c0a401c0340d4840159024078407601480d4004c1000041d000c40351000140179600030035003065800074600b00c1e142c1c2012000340d000a0020b01c240e0410100001589643d111040c14602030031040381c020070600091001e10010b4031010340740105d00e0f0300d000c0102180000341c01603a81a01c1e000c6880514236112240098064040e0508a41040c000c3c00140085041c3c0781211a84c000001c80041c020400d883d001900c142d03185007030281c041046402ca05c0f8000302541e00185100394003c01060000c988407514508441c903203202194071810314024481949400c211040c010080d1034000d09440307042d660003d105000f0b0310030746014018240720070030102c0340c813031100b06444001501d900e446550360751400c480e02055808060190068400104443c181030182241130440b649242e841d6910308031082c4412007101c000407116000e9943d48000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 316797868 1250 316796618 316796629
    0x60c030f080601030b150c0c0901120204090f0501050906040312020a021509030f040f031e0809040f0b03010905070e010f080a080711030d0302030108011103010501080f1b07150605091306090203030405 88
    0x2903d654880d81e507c4a841c03081c980c0c0341030102c825403403141c0098001000b000702d01840080041d030307064a001c520001c1d0307803801840c801d800c410b0043c090f500340300c20001ca0500c000781051180c2e00968448507450342c076219490407440f50403c50303070050f001240c1130f50600355068540742c0c110740c1e0481168500420365542c9181c2ea0002c0d000440c03c10f48804041050106011100720980405083e003c40404c1e2560f9507444d0f44160f030308003401551079040420740403211f90300030746214401400a21141d1494a042621070b0943d0084101da4422140081202001c41184406480c0b00e0001048401c0b055181e58034640c0103038004070342280d80d07000301c0c107607036102032101c059102c0c042c2d14096102c1d41040c54884c01d50341044aa800f881c4420300c0100030300e0f0b0303000c06000e0304071758004c1c0c4641c55a00d41d03d851a007608a0084100701007040009c0100401c10351155014a000007a50200500c2d5120801c0241d00b00c0b05491108244001c3c55015020036056480100c245200408681c9403d0741c88000c41e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 316799118 1250 316797868 316797889
    0x30c03021906050114030f060106030b0a0f0e181c080a020f04180c05070b0106050306130221060a060509090711070603090b061801120201030608030f13060c030f080601030b 76
    0x80b02c0c140c0311030041210b501140030907104d1901c04c50242c54404001c2c03082d1030345d4100503c00d03241050f440713010f8030043ea03c0e0204244050600a450300241b1900e500360b001f1034040641d078080300a01c008485c224045004540911000380542c01d0b441ca4a0100b101115881c102404800f10316a08010b04600138a245006000070404001d000c0080d506060704903007200c1000c01030900b0701c4002c202500001d0300032a43c80b8151040341c01c0c800d441c0e8131600049583c04142101d54110700344002505941d2a4064050082c2d4100c11000403040380e49074000d200f604141807060202041050000348803519124100c0340c4d01142c545440c0c9501c000c075503c95464110399610041c04203075200b5501c0c042c04402401154080c4094034500c0005000e2504212483e00511441c11060441900c003021a0b1103500310304001c140100c11262600604504212554010306801051a00700c080c0010002d000f03c21080740c00e13416454802c026944040300303403040100104401e041680e00c0a80e50303440c1e90b81000c000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 316800368 1250 316799118 316799123
    0xa14120406150e090c040504050c030610090b040b100f020307052b020316080a0203070b040813050d05032703061e0907050f0f0625020916050304030c030219 69
    0x20602c8042520403071518455a0003041c5040c80c1d8004102c506900000c141400c0d010503a80041c3e569298140142807040c00f19903130768540030312814003200750344911501c01640c0c0100c0040000000c448100b1044900d80c0e0701158202030900c4450355443c0c000c0d103c01074600e400f40160f0349058070b5aa40c0c44e0800600540c1c205620510042f2404008408484507514402600017503284c864041101c0b89a07952514000304099400500e001c0418428000e0f01c8507568084940010b070b0902c1e02c0c1064844e004001c235060202c004600009a500c0c04076a09032580750030002661509080d880e00d42e210119043e482000101e95980c0c42000351410000075104280d80b0040099068403401c1025a004018000c000a0351010005014070340e038055800c40c0038074040391000d01000608000ca1514095031100c0f074641200307807810070381007111281e00c12942d910881da41c40070365441c1c41149642894802007880040e105100150000e8003841100c003040780240111044910341ca002c01c0c03e181c0740d08008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 316801618 1250 316800368 316800371
    0x1120b040e0610060201050a0204030f0b18031206190303050715151511013305030303100303030506150d05060d020613031407050102060c0a030e161404110a14120406 73
    0xc02c94503034280307c0c00b900981404019480c0524544a058465004400241001c20f440002c509413040f250460b03c50030000e9401c0d66140e00c0640301208054200700c132402d0089400d010051407040c10103104005880e490f80310b080c181211501c80515080594580c90003003a43e502034079450440c0d41c680f43d4003d000c00c0d014480f041d400210700400c003041424038099103a05080a003000742c2d04110300541020308041030806444942402c214900c00ba6911051f01b6010010074450b080c0e148410500907a07001c0d0b1400d0005441e16006d011075046e0900708900b90407002d00c03c00c400d1200301c1d00519000500205007544900d8140c0004003030b9070220111140000521004004001404044007140baa8036030140c841149850000703520703200c0090107075804c0c800c001038100000d070003036100542c0014828101c8540b020b401d518141d42d999680a600d000c4071030014800e603d403030306005a610000202c0d01032410808011019100000403c154000b5060240000f01c44848400c08091040f4000c240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 316802868 1250 316801618 316801651
    0x32205040b09040201051801052205031507021b01020f0106060305090f0609031b0a1407031e0f060c03061a070c05100c0f030c05060712061401120b040e06 68
    0xc02085890100310640540c07240010080580e0704035081d903c555015010302c29030300707803c84012900392103035280400018101c007008407603080c0c1045008084e507800354201c81660402010b2003000d81012070343e400059100e112180200100304000d08040303401070044810041c8585507981c2524000e80107e00080c0d941c108000c106d2508011714044003020ba0041d10f41428200404c0e07449100380315520000300c0007801c442c0550f10302004002d2a080d04180e11114070840004d0042e203074681072200b594105a0319282d95154201c29680780e80c0c1646c090000080480550341c4c1c04082d1100d40402c0080c1580c2e42c0b00000c43d85807200100e1151480c0c41005580d9180a00c0c00910112003078100c14058038014407450f54031604403440c1c20b121a0081c00c814504031140c07030100d90b0541c40a400810301e025540500107000c0d0010100803040b14101c206115094031021000d80b022050041640007030310398003409944a900b43e010701c5800d50b0107440400c1c01c0c4a40c801c1c2d1440c000c02a141a00240403215 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 316804118 1250 316802868 316802879
    0x7080f0c2a10110414090603030909070201050f0703110a08040302010b1e0901271109100309030206010602060705071401180b040b0a0203011203030f0e0601060207030b0f090d050c0322 81
    0x45075035402d035100c8802034142411712210240100040c1303625402240c40c500401e04554080003501c80301c050007411303901139140c14100280070700425502ca000c0c40031103030081400b6070b0007070080d21041c8068071040d0303003404c000f2441110349580281c0b00358195503850030000c11648481035102c14554003e1500c0c10061880c0d005e00410040507070000d000c01850400d0100365030f110a003501007001c00840e0200e101ca48481d10104148103c040369035204071144091100079030180c1014007418000c0e000d035811680c1c3c0d03030800d0b40c8607a03088882c4400a05e0800101001841c24003900d0b41c6c140150740000f9203081078440904042c54801402d441c1911000104410026480e0f180c41e4052130400c4150300359454681e9074800c11182c007100809040d1a00721070004200785038464070512230300504039101569071700c00c00380d1100005e002c01d440841d10000010080b20300003516502610350b1000030b02c0dc210801804a40b1608203400604050008001454403026150900d0f45411495400d01100501c3e01 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 316805368 1250 316804118 316804121
    0x605070507090203091c02010f02121e01060f2a0b0414030f16030c0b0f07020f0c060d230403050306040b01110c09060a0504020c0c0907080f0c2a10 65
    0x65002d8201c0b14010020418001e1010642c16181a2985965400d4042d40d201c160f015001d043c01d0800b030719202103103e03405080d40e4110070340164041c1c2800880288044554410301400f4000d810104450a41c0814054860b80c1040c60300f00602c448241d1f40b0401108150034428110000e84441c10078809010500508004078605500940019440d1121103000d411842c000c0902250001c0003d50007101454000c5041c884900d130b1242000c07540d0300d08140f43c2c08400d0015540d490052040c411001412080000c040240941c010314050030601340d078015a014140c040300403100d070030041301c0081c411042008403600480c46916034949030b00d000c800f0f00080700c4001c0315050401000303c100c80d050380d001051480c5031a90540314082603607103000210f0910041c95000302c2d0402d200280f10b00c0703084000710b00c1c400c0000045907224055110841d084a010b030b402d842e0513402e40c185002040d01d960442c8002e101c66010b5800d0f03510842802c2902e00c1c00640c01c0c0201d04240d0300b0640411058a1f0076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 316806618 1250 316805368 316805383
    0x50610080d08010b03041505090f0709090201091a0408030a0201060302010f0f0f030b0a080a05010603051b0901060c02130903081f080d031503120207060e0901060e04020d06030c06050705 82
    0x3908024802030511041c01025808184911071aa1800201203401c3c40f00c03102c210041d20f1410340c0184214104441295900c002000f89000107004000300442c200303503c0e00400c00100d405031359101c81719007425103001c21483c0001e42d81345003000c01c01001442010600140c59850f410b40c00014006195000150582c0f00a640c200c3c104903580b440317941c900c0d40084000c800242c051a00040f0a45050702040d805101604024914421940c10204000c0150480c03000e1340d100d00165001e030003281c601244001c00c1201115482140840144103c911940c80003c00d103000510103a034065072500d8903c1182d000300825800a80e0b04810046c85003248021020001d40c2441240819880d114242d80c4442444e0b80620802d6219114550710313090300401180510303008040c2050160600c6130181da941c08500c0789402290705106003450501d043c01003181241c859482d00007101025404100003507201600f0b0304030300d5990fa880480400c0040c428000500020b031a80717a520045404c0031482c0864 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 316807868 1250 316806618 316806629
    0xb180c070c080721030908101a0613030f080409090c03050607020c0604090c0210020414011d13050c070f1101020c030a0f0222140106030e0c010c0b0a1107050610 71
    0x124440c10803e81400f140300f100c001c13541010441c080310b80c44c80c5c02c40b502a06176008007807500c2000017400c0c00302c03019800807012652282030b030044811540c1c240b02e0603016071019046011b0703031420308001281c41218903400f80c03441031b403440e4501900e0b02c82900c2107540e0300c0016a000350716117000380100311040042c0c035000b80c031a000602d18011001c0000e40c2030f01c694061140000d0f160310f0300f049030f00d00802c17824000e01d100714025512107440d0180444a4074449620b0b0380000e20968244030070082510100c2071610028200354450024402c83c0e1014013000b0b01588001d110400c01c03100829101081c0b042e0441c850013003591484161000240b80a0041c9003091003904a403000400081603204840c002c140c2c152585412040340b0755130040010380c6800c54000c000c0c1000da594050400b11152203050341c00c1911f0400c49500044083d03569056200b1100d404292100750071400308410180c944c2c0c0c001c0c01628041007800b44421821002d4115085c01c80783c9900240c00d1100750103060520201529 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 316809118 1250 316807868 316807873
    0xc1a180f0d1d0a090b0f0303031806100807030602090d080a030b03100e0330010608040b0c071a0406060f03060f0e0102030c1903090b090303190219030b180c070c08 72
    0x1001c40000780c64001d16114041401c0c1c5d4940e95000d01d03888564000004036002004e5039140d02c0c0880001c400708401d49281c0341580a02c800041c51120f41d4940c4c98141d5451f00001c1c1107144c195511140258404d5110550040c1860000000503005900905410805030740115420301840189460306442101d14a0ae05040c5060000204000816101d42c580114129030442e041da00710341003601070072444c1c3d0071902c82c1d09001040042c1c00c020514091481000a0360465890308c5001c0c905004080d4028115088054403828580007404801d4204c0d003c1d000010340c859036280c2c614045191a0700c1214190b0300c1e070006000d10318441c40340306650b04035003000794550b14060100500701d10800d24140c039550440182148014403135800440310300c1e402890b901803030501040140c0c3c3e80d001241c1044182003150403c540340b900d24026103c02c14244450803580103152032065001e80f030028066078020580c030b042c031503040c041c2100304c0d80103c00c80c0c80210b6842c942d83c1488078504229401240059 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 316810368 1250 316809118 316809167
    0x12110109120201121103180d1d220f06080106050315060d0c0b04060908160e060f18070c03120207020609060c03120f0a0c0c1a180f0d 59
    0x3a5180216480041d42441c00c0d01004c001d945103d4001c256070315405683d50004010403038401241c4003007580090440c4215580540b441c0400c90b04143d95041c0c4903010020f4103018902c0e82448094000b000c8040040c4104400300740c00500103da11000080448a480d228108011403082c41078a01800042d00585070008808031070707440e0242c0181c1914042daa406400800307002501665802401c580c40342c0035641c0380c0d1000300503d400b025020b09041c0780241080601c03444600c1446400b2585c00c0d40015565075264000c21107038418008000b40c100340e0440382e0400d50354184065610404407600c070701c21000c9071818000c00f10416645948001d0380304001c0c450160340c4070310645e50314010445034640c1d038140611a003811805031521300c1d000301c03001405000340c08160440c114410420700c04c0c104800c3d059200101c601031000390014152013824001245008046581c0a911481410000203030a60a42c0c82c6868940280c5c4941c01c1d0f500300300c21280b103203079021941001c60740c902400410721 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 316811618 1250 316810368 316810379
    0x503100f05060a05091c1104050c07020d200909061f0305030409090f02030d03050103200f0f010302040e01080a02130507020d0f0306050d060f05090d0c1509080412110109 75
    0x80d100e0b8410f10300a00101060441c055aa501c0e40c00072454072000700c20003251468a040290028086581c0d8400c90a1000140c2c0380a1000e007a150210307001031120100781c3c50303503c48082c56462810204c2248a017035407250807a844541c5164001d042800c0102800e01c2e2403038402000b0b50705142940c01b183d08100b0100082140041514142c4542d100000703040f11840c54960340030202c0420080d0980100c54030b0301d6400d40c00d0f60080e41243e01601e80540c0b03040504182140341030035601e85c0c641c0205401c00f10100c90500c0e13407455091090604005142985810741b20340d45a90990104429601209220045041c508001110f4103c40001803016003001c0d2030207500c60700801040c500308403080d420220074600c60b420910040101404402c00c07640c82d4245880580b107401d040c503450700d0910340402e03058103000580034a0000c842d41c0c0c80341c001c44140d641c107101c180e200f42c0c000540d64580e0310400110b207106005000074280503401c004041c89900d0585800080300403d2814803150200400c81c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 316812868 1250 316811618 316811629
    0x12130305030a0b030304170102090109081216021201140108010c0e0a050603040204110315010201060b0304050a150b0414070809010b0913060204080105131e0201050d0e010209030d0503100f05 84
    0x200141c0ba004003040e2040f075040840d203140180e030302c01e901480700b12154480388001903008050346d100a0345c520100c192111216a5920301803e40341c144410108212440a01010313010162548010301d000d00d4081c25012050a4a032801000300d4240381c4070b001000480001d1141d50840c10040c14844080e240c2c46000032180700c101c0c400c0c00d01501d4000001001c56071207902c4401d1003141c84405c95140d041176182e4841c02d0004003841400741d842c200d4007044110405064038400d591110081070520490f541d1400760203121a001d174101c9494502c0000c440d41d0324014054800021203a0020a18011000402040d40944080b81e00c0c2d15003095008280c559a8440b0340c0403140c18030384490740c8240c0c0340250003445154807040b800d52900040c04442d2a041c40304c480018000c2c154191220103403000c030350003d981500700a000c1002040505c81c62511500119064905840010b041410040201c0e051607103980032440001d100201f0800100440090322010f8140406121511420200402d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 316814118 1250 316812868 316812871
    0x303060402091c03180503070b0906071e0302010b01170618130f0c060305010b0f07060c030204030f11040c14120603190501020c1e100906201213030503 67
    0x203024940001e91403450761503e00901115a806001c1060601001d0900500c580e420f103150010300e00142a0000782803500181083c140e5443c000c1c2c441c601540d000401006901050044802e0310f601496250f01c250394004000382c07039000350004184441140001031020700000052020031000c4014800e03951592001e4000d0441e0170002c169058450151080c6140c0030480001e048510200c090300801000c0080301c000c4400300d890504c090798a4920030038280c010001c00c203d80c0d20050013101e0114001c4c0d00018503216081c1401413400d9280e40303901408004115055620715003d608501032030405100d808103075400d500c0c0000601030400e180c1d0b8002d11402140340f010350310000101703505503818841159400c0d10500d0f151400165458141c0c043e41281600c10f40d00d00410010041a02c2244500e409200d0480c000c0d03c411000300b00310744024030001d5019102d0650310040a0400082001c01035070603042c0c803074100c0d03c40e00600441c1200301402031a180304052281440c000080d00401680e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 316815368 1250 316814118 316814131
    0x40612030e040518010608100e0706080412093602030907170c03031612030501120b1510020a02030c0a120b0a0b0402070c26031c150311010807030e0303 67
    0x1041135251800244000b81e034403440c070103595192442c0050100350010342000b482c002d0031400d001e41003441d401c164590340288144004181080006400a00c0080e441d20600300749003040800c10340c075500e0000c1213a43e0300041820595800442d4a85141580b485466140c030b20f840542c03440c5040004252110309030311640d1141078070b8501c40101c900c41848003a00591000d001c0780c0c3c4584800395000c40d9402e610f0f07402ea60007180541d0060980e842802400d041e02c4400c282c0f000708800b10380e84c00d0040480100011044903902050b21010382c0d40051030b51030103085a0040101d54464010103080072602030069105410004003042010f49190344030312065080040c031500d80e540c0900302e001520240c0c6da0385500c42d1002506108000780c442a000980e2035a043c20b14080d80d1000034100c082044000d48001c6030b0003070001c144200c07924069484020460000803034480071010f11441c0003500ea401c210f40525590040040315684441e28036841001c0386000e0056040498a02e6141e00c0040d180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 316816618 1250 316815368 316815371
    0x3021c091e03030914040f1104030314130509060111070b03270604060209030f01020d0212010b0703140c0115080105160203030c16020f09040f0c05010507020303090f0a08100605040612030e04 84
    0x5c0100301c1c0d0b141d0784141079002040800740a030030f4680204048a0788640000c0b0040390740d407019410340d40544404c0c4c0f00320583c4100e4001505040c00c04204480400420307050403c1110810b4040c0c0241c14071544008101d00c004082c3c42e4204840e550803155042d590302681950b0200c040c1c80215400a2503075042070b04000c1c01039030b030303454500031908000b10702d44e0154080d8000100b802d1088507580c001d0030f818144030014283d90340c9400307981080b881001006000140740d6840d000c0f280101f03c004103540e40c0b4404c00000c4005800c11004008a410361060190381d6440c81000904009012050b00425a5102461652800ea44000c1a5020744241c1400d2100000311b80300454542c2e15141c0610708009041c6605440c080c5000e2000c0343c0c03c44012144146070210001d595406181560050369000f4051030a04a0000a0020f042041d5801580c0a1150f0600040700f1105001c000d070f482040b0000401c0741070034041400140c1e8220380c019100300c0d00100a11021941c40001c1804031001100c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 316817868 1250 316816618 316816649
    0x51f14060f04061e08060607060e07120807060b0a0506120403021608030d0c0f1205091014010e060f1e03071a070b1003050a03050703021c091e030309 66
    0x4540140280c0c518844100300001d008121a134001c81c141010955801d2111080031032040b044aa446040e01c00c250018411b000c0d1500290301a0801e0800b41011412500c541d071369680404008101c030740c0706441100000407040d05002c550f0140c0c1020306419901e08101500d410b011560300d110701400810260750840214040501c01d000042021400c81c004101164a0743c049644030390007000c0b07130299680743c0780d9440c40850082c04442c890b43d86a44891506071804201c0401034880100f0814550040104058a0000520a45142d070600001101d410342c1070444034107800d00082c111034402c1c22004520119991515040c550030f213040106150b4039035050001c80d01e04411908102a90540140300075400123a0101411f941030161342036000c1c6446015000c040c40042d4003000d00302d508024140000700b1f0081d402448490710030701c121030f080a410103549146200840440e000144211001c02495200f1440c00106030b9000480d600120f16640e0050280e141a1141a406025104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 316819118 1250 316817868 316817909
    0x50d050a050103210c23010c0206060f040c0c1704170a02092d0108011a0a031110051e13050f03100b0307090e0d030e150c030c070204021c051f 63
    0x40d17801d8112940020b03094402808a00700407200c1100110754242586040e05013407843c3d20024407580608000f40407000100c03031510034807000d0140d8040c404103000481800d07000190405803140c8440380e00076007503030715142003484010030480e44400d0002c079030b4820200c2c0e901694803d1139060b008000c0b00c421001c606490707048071070b610280c1d011000c10728503a1000041c1495040d000002e00d120700d03020345560b4003480c4041000001003404041c1c502c0310400c49101c0c45080c10984800340d02901c2c18094142092040b0281c031107aa030817041b003c42d07400416010311142140380310f040600011a0828900b5480b040820f6888e040104c2c02c03035005403500d400c40d005480922034040505203104080c080c8089410708107a0701c2c800d103e60b01d4006072500d80c40b1203807001e01180c00009000c080c2e04000c05500c0d415120300450300b01a0001548000404c11070b00142e440388018400c42030a420440184028180c0d100c00720755005045010440e034500c00c2d60035401112601c2070035030b880840c0380c0b2400318000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 316820368 1250 316819118 316819127
    0x10804050c011b0203010c0201050402030d090b0d091106030a020d1b0509040c050408100e0d14040b0c03040b0a0309050601050415210507330905010f02120406050d050a05010321 78
    0x440f00a9059480c0007404925258107400881c420350080c0d08550510f6000c0a081f6100c4510f4410113401d2102406200070340700c0d0940108088500400c10302140743c00900014840b075000b81d410b070300c1160f4000f414540740340c440c0c051201500c0d080044410040c8034614080e01e20310036400342520840da07a85031990300601072016a00900341540c21500720032400340c2068000c003000c5030004d8040c4280340020102511489140040c105443c0005051a10740079410140c0d8002e14080c150314001808041400f95441c00a80032202c51941c000c00c0c1101e203410000d041c110181c1081e400307507050603100400c51201401000c101d510403251100b40071011100300300321001c0e010b4020100d0003807407400100c02100c504090500f40b0852400c0d00840c25950300d0b03240420810260202040c0748030010800c0d58010901400300101900641d0004211102000c1c0c0d81e03485900b0550108001089600860031141300740c581c841480b540400107941507031516407448030b03030356400d54500c1422002808000d225 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 316821618 1250 316820368 316820417
    0xf2107060b130510050301151518030819080a090201051b03090a030804051507050a060c1b120f0c0506010902091513030312051006050a050f04081b010804050c01 71
    0x2102e1040002c0c2c103044030b0310102104039100f070500c65030030800140750500b0741c50041c504171703074112506a2841c4a041d5041d542032200b120017a00c45446402d0000215205d0303402006104002850300340c180b042c000c0f0160012038042c044e2001a841c0400650060f41c00808a0b1400503400400700501310001000918500c00c01520b03507000a03900b04000200450703000035105030f400449981600d0b104011154200307004e14107000e0601d51001d04500d01040b400d6205402c40b100501c0d2101301240c8001c000107910003264011035141d04402c0600d1205a4840c041c01c51700c40a51400c0f180c0c40e07020b510340564074681802448200c1c5c1d8001105042076842c00c400b14000d516008007140c480c6a081443c615080040c401034000c0380710002e581d54044603d12a00748608424010124a242030520803101074002c1040c000c00c0c05402c100300170011a0341c0b40600010301801008011140215044003802002014800c1c18050404d040c000021008680ca200640d03080c46c00c1c6400b0301e10f40e860074031503080703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 316822868 1250 316821618 316821649
    0x6020a0909051b2214030105070c0b0604021303080a0e031e06180c0a03030c0b0c0c100b0f0307120218100902090102010f06060201020a0e03060105030c04110d0e0f2107060b 76
    0x1803944001780c54501c0e41d25810302d0000c00c41c02040f09960751001500c40c0180ca25004001d51523601c0015405d01c3d05602401c035141c64021040009912590303500a568070406c400780c08100da0895540c21031408020000583d201401c446c20b8059035076540c25a914409040d1078250500950070f1010100108007440f420380300140b0040a943c0c1c0c80c04c010300030240d400015112800e0400014605100200444040d9903a100081115140c0c0400c260020840d0791600d9501585034540304c1919982000400050b04a20b013001440703030413500c100a035a0b1010b03540c490015155500300305244070160b8643d8200c0b008058050303039030103500004034010220314168501692400102240c09941580581602c4103030f0b48401c044007866404150f525a1309124995055000c440e15060340c0c00c00b50410212006805119030a00013103007403a6043e00d101c484200d0380c0d54054605120602401c0113007510b80d03025409000c3c244941e0901203412446000380107085a81c41d00018807050300c800905581041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 316824118 1250 316822868 316822927
    0x203060108012009032407030612030f05071b0b0d0e010b010801030212120d0b0102060603010b06030c0904481d0d0605010b03060f06040b03040204090f0f06020a0909051b 75
    0x11440107404000c0c6c50070389050002a00d03080004c80d8106c80c4502c00b000198041e03d410b44035090b9110708981650040500300d0715003034142c0d488403a01c161051502e0142181800f85501c4055403000e9000302c6802221100ca10707810301e0000355559800c0044c090540703406440540303d80480c0d0a2252070090040f0040c0e044071000200030800c0d000907409441212801da098607541e0700c1c1c4400701403ea07259050820351207801000030078455142d041c0208028039025002150315600380d0070b0f05030454001405605224980c041c40030016081040402550764aa4241d114840403120020320b52100c21102c00075546807451525070665030080f01d19100345c1c0c01a030522007580c40704801c070801d41050b0359060040380c585041070442d00c0c201055074161401980707a24116960350302003201900583c076007540d0480480026a0100e10072a8600e0500c5010b5080542d48691a010081800c0303401d5001c07510f058944011b20404619041003040300c1c0140782000d5454800001c604408140170b000035041c00b5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 316825368 1250 316824118 316824163
    0x30504030314030405120d060f1502070f0f0905071106070c020a080a1a040809060307181208160507081905060106020c010c060207150603030309020306010801200903 73
    0x15440002881940d1203651800015504075860340031600050b20000e040d074001c440c400280031003a90160420701030908010804568840c054840040aa008452016404101040a241c04000b403000400c50340040b682200c0ca0001c0369100e08035140145510386442d2808076203da8410310f051920001900c0545050b4100301002601580c5441422405003440d000300180b82c0501084004041c2d42000ba550003c0141c000c0d000b01d01e1000610440322071405001e06c203120b480d0382c0301071441100d41c0d88030f820803c0074402c1004060b006540c040c0c003101e4940701c170000014009005840380b404420004c841d401c04580741c11403c00055070080307040c9100e0310b000318a02815a401c915003080c0a86d003603a42c1da98843e101242c81c1c0c0c41c1d40001390f0201d2150300803000043c64030360003001c603940140b0307564180d14100b0f41c0d0f401c1907450316401900000d0326040310381d00350b24040c01494010b121101c000c000b207402d810f40e8160340404551035001c400c01d000c5440f240580f01400a5529504d841c0881940d2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 316826618 1250 316825368 316825373
    0x30a02060d0e0106061d12070801090525120b15100e12030a020c060a03110f0304060e0d020c0d14060c0318010b06030606281e18030f030516 62
    0x80510310305407200c56082c1140003842e540241803031401000400450201c48a0201c240000f10801fa25020620310450300d000409030401c0c0b00d101c0007184210082c0441100e6040e01c00c40e954840205526900807081c01000300864803201200c040794403030030307030707a010741d01c40200d24442d55005007881c3e007040f0100031010940303500c621480c107130f44070442d1011041025000159600d004040140016034803802d502080741c07501c0400350407411818900460b08103602846110641c00201410394881004424041002018080c1000402000004110b41c4094500095440118040780c034014550181c0050600c1000d030600041c80d080b850403204a803c1101501400c1d620485580c0d0742d900360366001c01180c540600640004000c0109401c0c02c5441d0007003001102e50110343c407061441310291b40c0c984800051108402020b01d02e8884121088540c002100d41084c10111901000000f010080d1001703a01d10958003525040781c0603c030b25200034901958071303100f0124401402c060305601c802c02c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 316827868 1250 316826618 316826621
    0x13170a12030b030118110103050402031609091406041515030512090414040b04061a100816090501051c0207080324040506060304110a170a1a01030201020a0b06030a02060d 75
    0x40c082d8020005800030059082061305e00d04070041c10100c6055014480d58400d03017140390020f00040070b540c0a0301c081c80d01c503690b003d200c0d840a05200d031120380e8582031185a4440d401d4100302e050242403a0714196844170100c40707090408072280c030b603502c14880840010000c507c0285502904130380a4010212503a00203030003501d21184507034104801c0898000b00400c100d40a240e000c10500403940700c0e40c0c2c030400608482d904034204101742d08030070703100755450320b091348912155900d80d106141840c00380090906140c14100c800c0c010202010081640d000b001c850309207c09000c0303410b98500712540040644070350b41d0301510241d000300a008052940880143d20100d00000c03510b282c1102100703010030b55100320782041c1d100c0004d00014010940143c2884075a6000900c24804940c86035001c41c0070a9180748c6a44440c0e110310300a1003008001c2d103440f40f03800d09100004249602d142c1c0003e55400b2980b000400300442c48002c507500c2c0d18108095030a0a030700822103515015031030130920 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 316829118 1250 316827868 316827881
    0x40801020c100c090e31060c02010c08090a0b0c07060e030d0f0b010c0836010e030a050604080a0504080d030e01140c18060c061003051213170a1203 65
    0x5201450180072159203070084c04001e08075241c000c205170042c0d0f80c82400d110303024401d103c1c6c0301d203545190301146132010121b00410181845a0000545000002802400c582140181d001031161000078081c0382200010130581807540312040d5911655504400d43c40307401101740080016060000314135103540d01001810707501565140800061a240f02d100090390000c410300c0c0d004c90248103020022502e40b4005106580c0448100c0f91114216000d510500620700030f0058488140b04000259603031000030140800c0048008181c01c29464072903540b0303410043d00c000d040c030350300081c0000ca25002e102518000e080800c10b0360300328150b66074003030041c7c01623280601440d40b900c41c0288070b00c1c0c01c1d80160340c0101031070005607003003260728108900714104136420305c4e6008600344081b0715146010409c60f0720508603425816841c51451400c0d62424440c07099200301d0745814040503288440c0c01d1801800c81b0818000c0c1d210906a541015080084085003e0b00c60b140c0c046201104540607003100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 316830368 1250 316829118 316829143
    0x60103050d031a010807021606021020120601260417030702060402240f04030204060608070503190605180f0c160b0615040e040201080618060d08040801020c 69
    0x21090861014811401c40f200300445505848400031100d083c1c0d480f4031511680020940101ca07440e03001045444802c1406a12080c0103a01660300c51158012500500240721242c05801410030000aa10803d82c010704d04c00c8650301c2d80000001d00c1580c4940700c9042c48102900c03031303445501030745185200000000c840544054064070f95207982012102c040b40e11480e080d034003600711030b180c80d420820b40c50411202c2ca51408110301b0507103561070050004102a030b4150343e090359600c0c510310510040c0d070140d5200000b0b010b460010040183e41001c00c0380e600c80e00c90280f100001d00c038465600c1c004c0126400541e00b14004c1c0742c00c00642c41c150844c1d5400750510000d014a81e5030340f40c201d1000741c40b496400881058801c0c503c080065124581c954004030001c100021440341c410135208640c115500c0300c4180542501030009658010140c1a0400800d41d1109502121488203980d5500d002d48072500030b03000c0c0046074003417040c82400e64025001c1c02d80290b56034486072142e25603c1c10140c012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 316831618 1250 316830368 316830373
    0x10091802030601170105011706040e0709020c15010510030f1e02070303050f0c1b070e0405030415030504020901051e040203090c0103151a03090a12030c0e04050f1603150806010305 79
    0x100320190301a82c0a1368100c8030140d50314010800740c1510514400d90103042c02e1f4215407101142c080046080c06210060a940d20700140c032600407a610f1442c000c40c03002002c030707102c040d0001406507446a00c0c1880c0307041c400e4100454a02c0382841e41000411000d00030136503a411391030790040400c00540003800614000da50078480d546a10504405000081e00c40008114040168028186017803501d030400d40d5a0f40142c0f80c01039035626608203e07800c00c85c0c08a8464200081c00c4c085407418800724003500103189010002d40c6850b6000c500c0715070060003028854114200da071317080c11004c0e001c11641d004c006041135480382044c03000316940303015010300540480c5c2041c03d40b82c90040c1340c80c142d1044500034511003900c0d0301260800605648041c02e50500f500031004c2d19000b081044c80c0341445a00283d1300060441c02022006040b4070308600b9040c415803c083c00d01c46e00f03055a80f24150170803034541841d24599002c8800758001c2040200b03414285d02714001c0040c040704040f400340d049900030f009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 316832868 1250 316831618 316831637
    0x904061418010605191709070305070e09060112061b0905101103030a2403050d032d05060301150e0702191a0402010504050d060c020f03040302010c0210091802030601 73
    0x110381c412100900402000640070310643c01426203151030440405902e06090001e08032024000f0b19180342220300306455442540c0c01c20400200b04112401044888409043d03800c005101c940ca0700018131440302c60b2100043c10105201c1030b50f000c1f900d21114012040c000661443d40642122401e2044600c00c00184500c10100c0703014070114086002010040c40c6556901c04840b03000300850300c1e040f0f160040c2091140030900c010341105001c0c40c0104014442c0d0038a0482c01020380b000b81d02910300742004000040d03d4580c1080e20101d080c04424408141035480c00017080c010410383c40080407400d085040024001c0b6440d5156002e090300382e090702c000c070b41000b1a484207411a002d000340201c030182100c2d44090150798071650440c2c17052410fa840e20799a1400946c0c0c1404041003910809d0356013090001340b5804001c0300e0155001003003c1c6082a14503000031300070040030600640a84800c05c0300880c2c0c10b114a00740e101600400d82440550111012200e0007500f0890b402c80c0892076030407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 316834118 1250 316832868 316832899
    0xc0102070f0b030a180303150f030203030d0903020f0729250201140a080f011502070e0c0c03070503180609060306300d02070f0e0c0c0309040614 64
    0x30341241640c151030aa00c02603481d00d00201615030000740744803050b90f51030303c00c001c000191400c1e0840e030502a680100341d6004411038000409502e40c4516091400b4034030400050701c000c403d48080c0138030b0810004822000d130405070700f4141203031102500c0d406680008603070f0456121010455200482c0100c5c68101080c680782c59074465002012140000c5540fa20941d0074104038403880e052040c500800030740301d40407105045802ca2030754a0003040e1248100803016200c6401c05004151285600d2400580e5441c0a511f801d1140220845d10320803000003812990720400321000341e91f030700040360368504107030500b2500c2e41c105181c0c04180700c1a00a801010b4503080e070507112560720042c40b8a10b580c0b14007013000ba40010005d10542c80c503260101114100152601510883c000e0740082c142d01c40842030028141b00082d00001400105090309000b0721010440032a03005072181945680e5282079142285035000d0305091036800381c11b01602141450340c41c108000f4881095070800c0b113903c08117 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 316835368 1250 316834118 316834123
    0x203070b0a09090203070912060b0d0609062a1112040b040f08010b0f010f18080601051201090503092e020d1407030c0b060a090227010c111011010203180c0102 70
    0x146c408100040038410103000f80e5515100e012107052061100041146c225170210741102c41c26007054440f00c1d0342d1420902400018001c03607500c03507114030300c440d0000e5811000c2c020b0860214003007410040d0002c020980684104041e507004030840c0c18a603288e80d51803031800150392041c000c0700110011408005101101401012842d000080c00c00c040e1904c0000119101902e0744070400420103100c603048050745090060f1005440c0c4c460180940750b0400080c07140d03000c408010304049070b240440d0310300490340c08030544503d00000c554070751250a08203082c7c0c014603241e042940303070000a07a00400200741c0015000c40d007040c2c1901c0707152441c0b07041091000280a000d4011340410610780e80940026000c28001c1d602041c002e1252501544840c5000d0407a0000500c905001042000b40e2845803000b082090031b508091070b21410000a95a8070030700361001e446d03030074041d10302201d0100e4180c0c010720201040001c1c441c0215100c7c9000c1040c0030034281440e0b0416200d008000f400c05081d44003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 316836618 1250 316835368 316835371
    0x31c060512030702131103041b060c02090103061a06030903040f150f030b040f0e0610050f211911090f1b0906090a06170109021809060a030203070b0a09090203 70
    0x740040d50401c1e00640a0081030120100d03041405a41c84500440300311115000c0e601541c052a80714810070b030801c01151420500e60000f81c2032117440f005000051342c400b0040c5c0d05503640300c44003103002404524070741182c4000c80b02d0581d1101c40401042965280003015104450101c00200d040990301e1404880081d07503a16085d0020b01da01e4103a039900b9020307411011090030301900001d0100c41c500004001c458400c06801682e82100051016040e0314a5815000d000b046425000720310312071000404030742407000040760749021519103c109850903c0b043d0000202c2c0d400b095a4012075203030618155503402c030000d10500d4001c1c00700d02e81c20850503400d4407402d40e40c941c440c0340c40300b643c2549102c1c0c0c105005042d4400f00401c504491038072845000c400030140340c0c40d001c61419406400025114050304040c3c1054410b000082640e902e0308c900880b003060684121886488001c00720322560025000a07400d4828a100020511a030500600b80f0001a6944502e0142c446032144180c1c1300 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 316837868 1250 316836618 316836649
    0x1507060c17060603060a080d030e0c0a2d030b0a02041d070f030e1204030507060807020d050301030f02121c030b0d0215031f09020304110301140705030c0c031c0605 72
    0x10318100042c003609005000f50707000341d00201140304141d5030f540103c0c60303e19160903500020792a801400c114041c20000c0e1014000c080720041c0390107041020141207854a90900703900c4040401c10001c11071400440c130030286400c0b811021151501c4a0341d41e01a6005100d1150b0680703a0316074400f02c80040040d141e0180607266070f440001711a0344000c4010303004c01d041c27484c03441c020030f00d61240c03918546005200a600ca40003515040f0b24088003c0c0c2840402410f9106540190206088407a070042c1100d041d00d51001d442c031848103d600100320039486103035169400c0e114a05800201c0703181c020540d0020b4245680038484141c6000c1445460700c05620001d411403100300d2000f104105140246a0041407500300e0501d10307440030140d07039100500d40c3c0f042442690004c14001805141c18900200a800390024410500715a0405068940092003181000400b102141c01404a4000c40312201c04117000c890f256045900c0144014020707071100384086160081c00201802c000110f80384658 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 316839118 1250 316837868 316837907
    0x109020a290d0605040e0a08070330062102030618120a030504030207050402040312080a0b040c0305060a150f030b0d0c030b06121603020409080403021507060c 70
    0x30300e804000d0080d900401915071422440d9401814003040e0305001d0084805480e03000b00d0340342d181000f44021180c132500340401c1504004182408a411001201d9035264949407211500c8020b4000c21042c21046c0d003d610310031040802d0000021058112409842d12501c00281710345542c00010107111344a04001c2d00740e004600040c0b051a841c90302c0800900125042c0c4444101480e10210540d010300c40000119540c0d00500081c9a410481c0c01d0207090181d4086180c181140c4910401d1300e00c41c102e11042241e0040091100c0a164000c01d5980802070310034845805010005405020708842d40c40c000c10340c1b808009201c01410402c15910581600c5603151607000075022000342c040c6681d01a000314800e04480001040b004941005501811035403101c0d00b426001c02c501d54506805000382d40d070000741550007020704640329008696040701d0014608a052800b000075000d168000380d4055a2107a040990010715401014468800c0740100180103586034140e4038041b8000408500e00b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 316840368 1250 316839118 316839139
    0x20030a0212160212060f070c022b0203010e100e03090a05060f04030c12050105090106032a0b03152e030207050f0a08090102010608010e060730091103010902 69
    0x4507400700042001c03a0300031020035051003903a00821030100d900511100d0a80c05207040103d04818000042d421070f60500d411101c0785142c0d0001201b0001a43c00c0340c0c4140020140d035042d40030311031a440b1074254043c0090008000c1d0300300b4640c039002041f9a40ba84141072019080d035900c4080100d89203e54020008100310341440d003801500d80003d0400310104404200100108000441e400c00901d51004a601202c046241090a540001c3e0811a80c0c3e810b0180600000390201c003d1064a04142101c1c5040640505865103400b000e0b4403014001900000b0301001607260101107040210903520070880045031146100c00340510107130424115400004032020314071a07002444054000d0303085890786591070100f6420f200303030303254121888040091041c3c46560203002d513a0040c031211008015602200d031455460b80c90083c05c40e41084036141700402d0250207002681040d048a94030400d5402c8000c540030000e103403030901500da481c042010354529180c14002e500b291a4083c0c500c00c0c80 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 316841618 1250 316840368 316840393
    0x40809150f030a050613020c01051024030509160e040506011505030a0b010302040503250b090d0b07030e0a15050a0501050618010e0312220501080c0a180620030a02 72
    0x503c1c0142000d50300007680036807510203c1b0280003030005080502e000040c0c90401041e00c01c0644141e070b00048135000701e000308d1140741a0440041d840751607103040104666903800040c609044202412641c00c00c60218085060a0000c0c101417080384140c0031a441a600d80343c696140c01002e810410000700304200180c54100380b50000c070103446041c100541425101d070002402c15034251070f10003102d2000165006892007204c0c81d0b20003440001c200d24039291150012604885d00640b010b0040c03080100812003541c442d0703004230201e9001078195100e0301d0003440e10301801d0f40c040014820182c02e00010801c503815511443c2c0c100ca2000784010f00d8400c9104601c00107043c25a05141801100b408401440e20b0074050b80b02c0500300c1402e03040c4e4902d80494059000841000d0201503000180414400390f42c01c000040d030841c401491154441d220100121000e10311240b1030b019010042d1340015505804c85e03a14019030136010b08820030b000c0c0c04c210b0107540340110503c400059110314480b00c00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 316842868 1250 316841618 316841621
    0x21908060a1401171f05041a01051e07150c0504140d02010306090e030d110c07050603130804030f051908041a04080d0c0308010b1809070203070b040809150f030a 71
    0x3040044c140320b2549485442c15400b9842c08417851500ea0307112903100d071041008242e0710400350030211402c1061001481035030002e030802a0459042c031000090000e00034004441c100300880e0450030325561104c151400c402d1110803094880e05003801e114005209501840176981580d00000380311500950000c00c00c02010716100050341032547d998404901c100b034a0049920100c2080d00440c3ea940c0b560800c2021100c00c42021a2800018401c01600080c08221b1800711441101c130551a9116141c6651642800072001030056200117800801c00241850a182d000e015006440d400701104c140106a02c001c140e0003040c5503400c0009100050303056041584585400c5402030619450303039022440e000c1c0450510340401c400e401c0f01000c0540c0035031464050041e2002c0c0d08d08280a038058401c0800c15459103500c9511f0070740001c0e010a20800680d00c40c260050008a054249803c0c20560b95002c61005802104000c0b0412421400c1c001201c6a0980c10840c007031455942444840 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 316844118 1250 316842868 316842899
    0x903081012110d0507031b062102030705120f07171510090512031b030a0c0f0602070219090b040605180711030c0304060e04060803120c1c021908060a 66
    0x154016403c4641c80c010500c00c02c2450040d510503041d07250124a95400ea03a10620705520000070440318410b201130701c485805543d030056000100244e140d4443c45420358040c001c0b61103003c648a00641000100040629103e01666590316100c04034602582c1c20040340c8401c0b5580c2e00041407114215625042c13003da56071300c1480c1813400034103041c0c94900240311500400801942a8000306204c0383c0046103002081407020790700021407400c44490301c064410000d460b0082c084180c0481140305004c0b26804407200298018800700316400248030302c08454416010340798010385404400390650426108141c00c0c1d5000504010302d462504121583d030342801880c4100b04a40070884d490201c03400c1016211100c40b81001c2c44d01e036410024010294145103800512550030048208020207010040300c03d503865603010308185070f2310341501a204c0e22507084601003400b0041000d40c0d8a1006602400030f81845141800c0585130180741154141000d171855940f04451000401030b0030440c003000c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 316845368 1250 316844118 316844153
    0x406030302061b0c12030103120503060a0b0904020d0e011b0e030705130603080708070b09060f040602130e010612060e06091303020f0102030c03090f150c0d11040602010903081012 79
    0x6a103895030400d525821700100400a144159004c001442040030080703460000007003500c0c10604524180000545545182c42070301d090807400a24900161100d404039a03043c0d0400505015a100d9402460b00800d0f41d1014541540380342e00b00c5207100b41c89608402114140100184100c0c0e00b850200660701442c0c1c403031080610382d541400000a125103010f05461801005125258000ea003840d21000f0300c01080c0c0f81a0360084800c0003000d11311207044507002a003110006803105024030001040940e1a000315495120790400021010740c4583d0346001074142850602400b03554512030242d1180c10b072039603641705441c100010700e90100803d404c2c402030300030301c100c440400140d00d000d42240d00948030f01c10340314400410000d00072000c001010001c021707400101003401c0c00d60150342c0c843e00080c026a41350000000e00405440b40c68100d14071299055010f1690340e507840d07402900030b000c0403004802040d0441d0000d01014556000c5000325240300b00c40105002c0d00e0751703500c2c030f28005081c02d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 316846618 1250 316845368 316845421
    0x181406090103140a1401090c0516030323090d0302030903040501030b010c0602030a230610050d14010b040614130e1e09010506010e040c1d010c1209060806040603030206 74
    0x6190440051009440c015500310800242ca5000040c10030003214058001f24842400c1c25150400710b54880c00311040a00c5900a0380380034401440c017100030744004071100303456050078280e1802c60344400d01018094070050048800c01e45409209500368001203961081c1504140030070807143d4081c0d0004040b00005142c1f060b442501a51648200c0e042030f41d010050a90718000f8114120f0365990410b0489603040000107e4503014001505032110f00c1d08403020481c001c5450b8400380c90f5904181007000310001c1000742503071240607914450b0844c1c45640f0000359118082c5d80400c0000d411174820709444942c110025081801046805e84003400d2001c0e41c60080100180601ea440101409040d43d01c0000c211401c1500c001409c0001102003a403003145458002c0c0807494003c24010207090400310100000352076100161803c09200002800018524103411159030f4061410001c0e2580b98680c1941611303844184402c80b00780303010041c05640502d02244d0034030228001c0b040070403c0340780c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 316847868 1250 316846618 316846631
    0x10f170c030402030a0b0a020c12070b04060b0a05060f03060a06080709062601030809030d091809020f033f03010b130b0a11060a02030402031c2d181406090103 70
    0x40f4a0041b0000700d0b000d140d03050740414204045001440f01896060b080e2106504002c0f043e1905450460081c0000b4091a5680c0a1124984070848458014070b00104201c2e225003205042008940c0215004c030b20030300d0120404503540e402101080d001c1c0c84550341d03102181d070802c00142e8500080030000d0030004500069031044151402c1114060741c030988240c3e031200007210506190983e03140c003800a108a4030011301050005042d081e012030001d20b00882d40e0003203400441c0d01d1454007150150540503114030245c4c207001c640b052085000d00301030242944841d681100d8210441c40e40f040011640800040101000800c06410300c240101c0c44081c503943d540038400c0d0294403801c1d03260081400d840780850456420b1009561101c01e00034103502d1450035030300080e1594400303494581110b00140080c205148503410122007441405410301021a0100c2c82e00140c0620075043c0b0000703a004034144039060303410350000c41210a5500e035140d2600c5e002c000c124980d000a4121b45c10580d8510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 316849118 1250 316847868 316847873
    0xa03081918150c36050405010b090306070c050d0e0f1201050a060b090a05150d021303020901050409020102070e0606160c21030e150403050105090705010f170c030402030a 75
    0x14040584074891a18240e400519030300d104103440b4a0004801400008108880c950802040b03403041a01c0045442200d0f4014044c20303800d4401981109811902d4440003248406075500101480d540c2181210a11303a50004100c0310044c007503c00030000c0e000202c8040c0700c14040d14044540a500500035800b050301071001c1181c0d244170a0410005179180d1003405801001d07481200b0281c03000404062605000101051890210f1310809001e03c0e0014138601400030003d05a40e14071010100a5640740920616145010401d000c00c1e03100c1d140d000c00015540c6401d11036203441d00d9068001c2e041203403a129512200c410010942c60b0081010003030395094240c1030082c800c82d90722440d03001c410141410301c005c81c5e4080030f60002c2c4107149482130710030120b90070400da212007510803680c00c4403000f52030b40c80300800e01071a4002040c9600380404e0080703041b4080394401c181c2d482a07071889003151403010112040c60305c0d5400d24121031201c8000c204003900400003107034842c1c00981110152601039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 316850368 1250 316849118 316849151
    0x405030a0b040b060301060b040302190b04060c06140f0411010504150201060e07020c0a0311010302040b0d0c030f0203010f0b09032d070e160c140708070609080a030819 74
    0x1054119064401d040400c400c02c0384071046a078000c142603000f00030280c201803003400030f84100d01001c3e10401c1001c4d9483c0340d066550b00c144014020010b5000c2e2159612000034003501e21015046072b00500700380c032350350900004500c803078401c0d1080b040e44400c033340b2141ca0304840090907094590403c60104400b19000010100021100f00c00d64000660b00c0c1c80c00510342008107020b041941107402011580e0f846960f078000040940b600071815a03c0929900010390092107103900c01c2001c410049089459181180c0c040c00b80510306840600525036240814001c91000f40505440c800640303400b03106511070340d006030180c00f2025080303c604500c94514040c50440d00c81c084100719041410150494006010f924014244000000e0f01c6051210300e14072014000340d031a03c10811407a05520500007040601d00e06602c0c1c0c01c082c1c41641d03480c0c0c040d036038490742e41e4000e1070701140791110001100200060030ba01d00e1038056030f07000d101d9142d07102c0414488004040c3c0f11600354680c1200404046139 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 316851618 1250 316850368 316850383
    0x60301150212031f09020906031f18020d0b032e0f0528020903191b0605090102010c0e0d081b0f01060311030d08070e03011508010c02070503030415080408040503 71
    0x2104d42c2e2090300440c42121300080710b650040c00409005019820054031341d00143da40100b03a14180d40c07041d2460380704402000031f0b694030a0100b00c040190000c0ca2044079801041c0040710200103000d54200320050507900c100481d055046c01c4189202074a001c41e0310401103484100d544c03000b04000c01d00318000c0b402d590f01540c090b0500707060b00c030850181c00f007070415069452000303481c254144401d800001e0b031030303001148031840e403c400000c0880030030030b290391540b0403183c29490080320749880d074000400e141c06c102c150902640c1b0f4584440351482c0200e828080348440101410740e00d40040d40c80d4221a00000007100c1003251100c83d40c00091320a02880c40c41504030400015194030b1400d010b4031010f080c48801d4001d42002620303003003080c1d0048031194440c00c542808160040040301090050001403004501640020b501160041040d0850010210783d5801c03141403c0e15001095140d1240d07108608070b03601e201c901c5901040c01200071580c8140944219818031756074501190904e0310 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 316852868 1250 316851618 316851631
    0x2120124080105060a0f0b0313020402070506062716092102040b09040503030f150a0303090f0603060f0e0712090501090c080f0d0c110d030206101406030115021203 72
    0x40c50144801c9000b44030f400d521050454016101e6407a0150740031420100380164a0f400000100284003029940008030710a54054401c66441025040c001d8a403c02513030024402c0301c58503006801602040b160b05036000600840030308a4448500f10415061101d255005000a0345c0b03002030a0070b0300c41c2010b01411100ca14561107e03400c1d1041100301c2c2d40443e07a903807140b0418000c7c4400b0510020903254084039a4241c2001c176144c0300042880007400b2200940d02c8848032402204042c2d11444c3c0c50110751003070f03c6499030180c4900b01507054804038042c400706214000810002c030901501c100b03800900034103016008207034003605002500c1c0403900940f072681d103400e000380400880d280072030000c1074101c3c06010318040c10394800d0340fa06080400041008507690a513401d1007020480400d5017200109010f02030103241c41c003c0c0d00d41e801100c803800031410340c1c2030000b40e03401403c0d00d011849000800c014950381c01c01d81d041d0045103d52491034114810100c041000d5070410004500448 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 316854118 1250 316852868 316852931
    0x151602030312041406070e010804030c210801050904050c09041a01060302090112060e150103061205060103030f0810050d03020f0124081f0209031615030e0c030703021201 75
    0x3600d41007500004401c0c00703d04c5660340c040c0d0104024154080d01c9003501400928045107070792645d0408854030b5418200c0940901c2c0322210240110000c500e4000e4500701e1034990880d07070784c1d9580401106a0080b200981103070803070580d01c3d42c5843c00c003084591040c860103810818071205035181d900c02000340c0000021a84c0052031412668100c48481e0070350b50b070141c0031b1000c1d50801c01030301c0c0c0810000e0028126202c040451003000ea01a800880141c003182c80b028614800d281003055440c8170038401640810358020075100014400d1095622481c2d83d03403106080755141c401403040c1c7c0640d070780007a0110702a9442c18001d0721400c0c055003114102c0105c40a4410034a03034900c41030010303e5840800942d210900c004c0488120010348600b24900110060303d4924070008a810040f500551072039040443c2d601150500c9542890f80040c003441c1d034200324442403000c0140c1e403402e8142071154107600c060300800062030b11f81d0030400c0c02078000f0004207500416603039440b40c0d081d40081204c46d14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 316855368 1250 316854118 316854121
    0x5061b0f070e0c0c0a14030c030f040f0b040312350601020606190918080309070311180a050405100e0619050f04082b021215151602030312 61
    0x2000b601d030519400c00041d4a180b4a04100c003040e10340d9401d0900170080458040b00000003034603000303005451125030b2100a480e5610a151140c800715031150080f01c2450610a4000c0781580c1140e003a601540d0740445880d0b0f55402e4407106807600c0b010000c140074000401c0d80792005450040303855059484145201201c641484400a4100500109254060744980180448040700101084122000e00c08000b8440c060010000702e640c14003c03002c0c02100b400010f010030041c0001c2c45400b220b00501d007003820301d9015005c21580360140c00c09080a60b441c0c9011484006440d408250054805c00844d010314a454091000740c81810b01d00c00d0807900000d0411040b10400c896800000d80b1800c4100b2142c0f820b48000039459101030405440039501041100440a03080c01240002085a94210616184d40c05000207540000c01c803a924403d030302e001c82c2180c04071850350700d040c031030040c04a01c602c402c2c003141d45a581c200a002c018802640182c2c04050f840c2480142600b82d82c0c4260b00455 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 316856618 1250 316855368 316855379
    0xe09030d060b09043e0904050106121a06030105091003020301060f0302040f020703080115120510080c03010b010203090607050c0a06020a021906090513020d0e070f05041505061b0f07 80
    0x200c0f1494844002040404503c017081002009030441c1905e02d00c803030504401d41086002076080c0070700349255403c1440c010000ca54203800824103410503030b501070184a01130713002d003d11402d542d00c14130700354001005000500c103514001e82051f41c4600f0424404403580ea807500000e0950301954004c18590354030350024070039410a0701407a240035918000c194501016681d000380200b03014401c4180e900c1030040708041882c807031028ac0703141c802c035902c040c0320b14240800b0003224012613100d0f000151146288013120381c2030600801c404000c2c160043d43c101101030044c0701302075001903000c031094010500865040d40d00d030600c90b0050081b6900410400340d59105000c40c800440c902407400f1990780318100601c0b80e101d405030094903c03e603800c0c10703081d0700403046101070302804c0d09002c202400c1540940c1c9a94000682c0b00c111404040494405030380c441c1400110703800480b000b5000c003510801400709051000061603030a808006000d10036401c00c1a039428500501500c1d002c035009890100300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 316857868 1250 316856618 316856621
    0xd231005120604080f07050601090615031401060e15030f07030b06120604020706022502012615030a0c0609081516030e0f03070308090106060212040e09030d060b0904 73
    0x1506007501d40310350031104401042c0d900c0c900100001c000b042e000542190140030300081c0c0f421070740d100080f14002e5071524082009040940100b82000c44c00c0060b4126241c82405041400351811600c4650b59007481d50440c1e11559401d07061381c20038110352605003815107800080d880b80d02c6003000303010141400340d40101600d0300796002500c29902070010107045e0b01443c69440e0060422a4010394400c05031a188021380a406c10382d040107042c01c5a4030a90060f2202c12081daa4400d13038608200384c40d00e0010303900001014600700426416070000580207442ca6902d28a9543c0c002c003141c000102c075aa60181090007604a040000c01444082003403c50411048240c001e0107070041905240112080c20809041c094402c101030301c502c0c001c0010007050144050302210392064a90391a9036041c0501010801d42d056810b82d840c00000240c99440802c49043c60000911482d01c0c141c40d0a0003c0d0a0590103490b01e50203000c1001070088101941c030504000301a050001c0e034840c00400f08000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 316859118 1250 316857868 316857901
    0x60b0a0f030213020d0b060d0e01050705040f1206060f080321041208060a05060a0f081303050909180d1d010c0c05210105090f0f070b0d020d23 63
    0x480032000c1000e00059aa44001060046010f140142c0740c0c0035440c0000040c1c000c0003001500590000b0311845040c015030088911105030350024000c5884444c0d040340c0910803807103048118081c02c40203015007202c4980045003240203804c02719200343c0358804035510380d910fa80032940c42c0d400007540c00704850010104818180c1400f00800140c034040d03c0b0040d00032103c0b59603008002c0058000381c2075a445000c0007003c3c00000d0907a42e25154064005403041d08a0080c50000c01c010600259105040c00040781071607501d0b130741d41400d0041c0c2805100441d44080c10841c0661500610410094010820440240b94980c1c404078406620031060400c1098080c0c054100807450340c4403808500c40ca0528401c079030342a90b5a0301d10010039041c202c124280162568115424442801055400011040e402c4120f510070347d108140a019601da40d10900e101d650b09507001070005012a00440d8040c0c041014440c41c04608010300c04406020050480c07000104045d0300780074007895500403404070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 316860368 1250 316859118 316859129
    0xa0606080c130510030e0d0905011d0f0609270105041a21030c100902180708070e120f0a1202070308070605100506040906080105150d0308061903060b0a 67
    0x540c40e100724014003010744805070280138041d84c0c110f9290402d0510176840307040c0020780107050301da000000c50742c0248440624841c490002d8110b06030f0300400d05110304050340040e0002c0083c0720604290040c005c550b000358010350f5001d0a900028490682c07902c0c41d03800c10108401c090000d039810141000103c41203507544400c0300400c0036040200d03031503907403c0c100c00000c00c11400c128004011603c62442c803a0780c070320441d240102c40f030407100a202c0750403403840ca500c00c0714144441c5030303207030f04252450004071180d500003a0040042112507000302c10a0740e00450203015841030101c2c1100700c51612072000e5a50306554841d01c0b1950501641c941d03c01400ca00c03a101800c00585036072a00070031070180000107044159a100414000084070300740900074400500b1150722a40d8400c3c110740105800c0c4103240955090071f0005840c000c0c07206002d91101c600900d0040c040c0388540b4110381d5103000515568000074800c140c01c1c40050303032130b02c1e071402503100f800042000131844e414400883da20f503000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 316861618 1250 316860368 316860391
    0x2010f060e060d020406080f031309050403021b0402070804080a030329040509012018031501090c020109170903011d15070c0f0c060206060910060f0e0402030a060608 73
    0x148400744510403103540000c0120b41c0300b11449100d00028004201c187d00011040c420b00701c04002d643c0c008000b410b440c10010405064250303890302403000707071401190001d0041e004091010049604403240c140c5601010700b006042807402e941d540c00320b40c420b4002c5900383d404800c4440c00c140d40b6000e19407408066940340020006485420b60480d048030218030301c00d80d00c03400026002c0100b544258128482c03a10340807800b02e404a0480342d141e001e5402d444c0c04036071000c001c1245007800201e600c20010428801e050b03680c6001c82000080c40a100c0101c110354a40340503501240c40041c0709010010942c5000755180702c62001c15085804c01c030007201c020414481d110b1154500460b9258a6600000d440c100990320090210340c091803041c1e0080c102102c8041c2c1206121003207441e08180c420365022180b00d40c90341e03010008440e008848600c585040d4240c184502813140c01e04e000340e01c0090608010410b140000074081ea0402c0321600c0491f592581e0810000d6031081c1c106400410740504c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 316862868 1250 316861618 316861631
    0xa09060e07050a0b090102030c06070c0b0108011107020607021909020309070f0b07020d02240d050c03090c060901090e090d080c12160905060c07090c02120d0f0b03030f040602010f 79
    0x1140d50b501080c41584104d800c0400e0002c1143d00070710031202101c12010684002d442d00c0d040c01741c01d94040c84410345003c510035002042c0940c0511500502d5803000c208a820240786a08101e4181d01400007241c01441920225000e9009503000394050812000d0141e1246007040045140101070382c440150190700010402c414806034045072a00d503019504140c00d81017900100340f07600154201585c194100030107c282640415002d00a00410004188100d4807107200242084c08142c5640d08603401c0850b206a071880c0240090164100604200010740c0e5502e4003080401c1c03085580c0f10240e0400501d030f0307522541c8a1611a805100c01740701d141491101031012409280040818041c4a185501d04103038a001c2c1c00d0000050a0062070303140c1d640d504940c042d4840d01103126009800341055102a04a8000b10b240518041c0008500341840c8071144c007200504000e10242940303517035a1246001580b410310003400b922400ca03110b981d48516000d0001d086900c002452064030b0728290 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 316864118 1250 316862868 316862879
    0x1e031b0305040e060f060f0c06101809060e070b120717040b06010507020409030e192d050307121104060b0a08090c0406080124030503031308120a09060e07 68
    0x20a0b01d0035601400782d500090342d81c040100e4100b60044150325400140440c0010701c02c80004010022020b40009440316500c41c1c84903070040000500803080d02200a11042c00741140e6581701c91a401c3c0202008519142100c00f20f40c205011500001101c0c000001d0120003c12501c03c1140c000c0243e14002d01280900f80d4224880700c3c1c003400c01001c1c5c1c101c00c03001c644643e10640966128680091040101460340e03c1c0140903042c042d05103900a01d02d4540075922050a240a84120383ca9140aa03c00e8100e000c03503807485021914500c1b008a4604401180c0744d02c08210003c080c00120300390b80810100380c00e040320744161041409114905251007440071140160644503400142d04212055480b005200303418040b01d401280e4000d0301d00103001561400542124200c00840d02e0740c0c4552086220b010800c007030306400060000d610800c003240320143c0075011001050300460b201400c19245c50001246a43d0544900400c2da844105030400c3c030113940700720989a03a040d00101000c43c43c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 316865368 1250 316864118 316864127
    0x509030705151005060a1e05030114040608250810021213030207030f03030b04050a06090b01050c0304120c0305060c030a0f02120a0c030f090614070203030f221e031b03 74
    0x80c06428040d220125401d10b8184c0180000322002e070040320062260b14200100238a181c109204059010004154561071820244140025035074144040c00d40411514684045a0b044400320080e00c0514880020000424040c0c249810703807042c800340c0e5540b000700020b203020902800da00d03090180d244800d40040e8001803a28120b0307034051409480f85c0170317a04080d802886030001407034101d03040c0810004008040e51000c810b903142c20390104680d01c0c412004641074000c050101c18503078001c05c41130040c1c1c02041c048010f404e2040ca11120340c26103a0356142c0c00c01c03c0580c0c204041714404018022031451078010901e4802c540e040842c140308000d401d0703040d90100900040500390f0380d5458400e40c28441c1e002041201000c8005020254141ca03101d8000c1030b1045810140301f5940e030128101c6480170003128010348400c0365801040c0c50b14801c3c3c04c20300c880e0310405d503500040b49007004002400f203d00440c1c8444cc000000940d800e007820050b10307074101e48440c0102008010b00d03400c0040e411 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 316866618 1250 316865368 316865401
    0x601080c07020108100b0313050f01020412141e0703020f010c05030a030b060d060e0402030607080603060412030f0e1e06160e0d02040e031b03090d0222050903070515 73
    0x918201d0303c1600c4444100380c02c1841a009551b403a940002001030b04c400c0221914000c600c1030040301c82c080c087c441c10038201d00480c0520001c0410314508130022812000030302d10303050000001d0f98020f8a20490782001c0010040c2103c4c8107070003c1c0f41c10825403038100c104800050003030801902900f030b9a80d0799602c91103184a500181a40c4075400070382d179110002502c2e03005440c080100314042d1100d08000111030b048074100d1083c86140d0003d809240310785001c0d4040c94014005082d562141d554a1615206400c100d10406568440ad8640040640950a01c8800a101074058401d00440c01800d180003595441002d901c004c05100b41c1080406202c9d0788441245001411402c140000843c1e0a41c28035019612506203410701c040c0c8007000c4004d05000400c007036071020800107500c4440c1c80e4002c0c1ca0007564408081c54202000d428915100c001d140d203d68a1848030030441c1c82c852040320015a03210002ea40040384541c03c02c0001c016111816503510019138592410b030300c100c00e02000303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 316867868 1250 316866618 316866623
    0x4020a050d0903181701061202010c151e021b0f0d14040e0a06080d0915030c0e09090615030604020a05121f0504150218090c070204050108030705060601080c07 70
    0x6071031892405252060b6135041075410b40700aa0140c3c19a1007100b942e131249040544030703055213050400220b2001e8071500f42c854035410703104d0700007042480e121031440c200f01808031241d03031362507844a15000c1e00007034003004c0f48600d28a005031644001d0300c5124400c80c8014141c80280e00aa0b40c0c03002c10600083c00401186151030403d619550341c55124102d802190301c066002503001040c884007440039001780c1d0990b0541382c100ea1100140c500116488149441441c48040cac04070303c050790701f510940140050a40720b05082c030303040c60036a01144042c0313422070b50742c01c0c40d81141040c050048890010a40030910850003844c46080c19000601920524800d291044448410708400f40c1d10502c070440740540048640e031599410261080c0c040c080844046400d08104460001c443d800c500c00d039510314124154100c4606a45030600c1a0040081c0c072940307540300180002001079403203015680c00380c80c1090155403203041525001f8600b44020301200e060000540400a0721406902030303d42c0c598 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 316869118 1250 316867868 316867871
    0x60f09270f06031703150d0b0f100305031b01050a02040302090c0a0c0506040609020a09050114010c03052b06050616110402190806010f030204120206070602090d1a0604020a050d 78
    0x1a5800401c0010b0280d90b2009150b9210306a82c14009840e6101540c40740390104105064082c0c920300300541d82d0885000142040d01020108540c020000e04082d4042c0032280110301031b50312511035600e1608034000f000100c8410f4038020150410030b020340d603042260040d0940c14a4107540c006024284000d205c10703040403000c661404a03d119002e001416500001074600e142005d040040107132039680b5080c2c1c003030100800d002880d405a481110304a5a0317014032494a11030a00045a40e80c816010a81c10000107000200c09440c1070300b91803400b20429000000b100506014400965450b644014400c0d4024412005400781c00d02c8424403080c2d0200320180940340c403400050090048507950000d000d5030340000701510390004101802800f00340c80d42a0308400501044059124a0203500e07a441c00e005040c400608000c4040d0180034806c01c2c000d418140c00b01e0114680f1141600c00381ea800010f046038480910000450796041802503c05500d00400d4250142c00c620034106c41d8210103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 316870368 1250 316869118 316869131
    0x18150605010801141e09190b0102030702012a0213060501020c03010b24070c0b030717010f1a0c0102030a020301031505090318211c030608120705070e01060f0927 71
    0x3075100340c8894003021005001c1b49240c00c1540400304001221090002594a0050441c03a158000415500030580c140d603105c06001e00d044003610380e191900c610855181b8010310820050762030041030b55240d1041c3c0700004203a842d10000a01d0820511003a03406a490035900d901944c0303c9000b00b040c82031004402c8407014201f1180b2070074510900c9405052100180d2003c01c00241010055000f601e86554207884660350005d00446070304284105260110880800c0191480d4041410030800c1c0c02c60f141820705034001100743c01e992040f907059008603070000061003044000c01141c0c5c800050b06404106034541580f480d5030f1ba1050300b24544089198034910700c0e055440c01c001110109440003c3e0030004403280e0490f903580a46480025013034848600310590600c28803c04e07040701c800000414441141c0009100303981d02c2a001510355000310b50012809103000b2810714000d180c1a580c9008001e841c140081c008605900607050f11100303101100d800039000f26141c0c900340a03070840042d40307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 316871618 1250 316870368 316870399
    0xe01050a0b0306030f010e010213170d0809030c0f01061d07020601120f08220b071502032511011116020f0111010f0204030c050a12030c0302011815060501080114 71
    0x20a0700b000345e218020b600701886000c0415064010304410042000b403403c1040d1288516002c2d80004c1c10b50b0000c95100c40c9080720041d03c03c0c3c5480384c01a800009683c0b4040d1691440b81c01c0c01092181048560f454040800500000c0500259001d2042c8105445410308060003034685134184504000f0494200b40c58050040c0f04000000166005002c2d542d1840c51440c000b00480c0c9029042e54200c040741000250202104212102c4661203000200340d12010003442c40290406080000c244908003010000d400741c11030a0304d0b4a40c0c0a444804031511502d04460a41c2c0b03141c10500354448082c414160800091480d003941598103e550068620070000102c404da11a51103102256080107416a2140c0306603000300203490003202035507141a211420300a5480c024420540600c842c16a258080384c03103150308011aa100e4030010075219109450701e5a141843e1070140c41c0481040b0500c0c810300403604c19080100020b0030214030a61401600c400d012103110540b03405074a030001500381 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 316872868 1250 316871618 316871623
    0x207030804110a0f030b06041a0102120708040e0403111902010816110d0c050c0913202707020604080301090e010b03070803040e0a020f090d08090310150e01050a0b030603 75
    0x1074084c1d401d0791a5000c0d5282001241c6040075544140950700e003892410042c110f00f49405010711040c0c0040c0200440012000a564040001980d1810040c400810500620386180c0d020310700a039035607541c4105103170313095080498281004030361607090500c140050340c005611791b80c01a041841c0c1c5c0c074007050125003900d81254003401144d0034040c401010740c0903030700140c120b41c07160301800403582200602c905000e20305034181c4408007850b500c0d840540024500c00a1603401281c054024901d0510082c0420b44562900301031300b0310740b035441202902049500c80340d04d600c020148000c0c811b60825484001c00c0d4070041c0140700d0038540380c03803001c0c2510800350802da900c0704028045581741d680d07840003581c403900a070082645000810000c40c50303a010724000e46005400c2010200e1604a00c07004000e82850296011503481109100400c1c442e50b080c00340504c800c03120000800c09488003c14030000c0d000d2070700b02180d00c00d000c1d0014091a02d0340c80503071040d180d80310340c09692626080c00191 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 316874118 1250 316872868 316872889
    0x30b0607050709061508040809090601050408060c03250f05030a090c0b07031412310303051006030c0e0625081305060c03180103020418050f0109020703080411 70
    0x7091441000400202000d01c0d9000c40211614003079200700c103006900c022118100c06540203407000f0f40074022094980b401903a980c0d002101414100d19265598520030b08020003101d251410743c3c00807040054010304442116149104040c220201914400c000b03000b40c082500040c040203400f00001d00d040da02d07540000740040c0c006800b4401c030b07503a0706140c012907880034900f1070000d99424143d8200c07005000503561030240b011000000ca80d42c4525101d01c44c40d440c221050204284840000c3d582611080c13805024001c2e50040345501e45211300b0060307040242c0c003c0040500d001605e5411a91207101181c40c11800c5408a68500c00c02c0072108442c039100c402015440c0c40da04001e010402c50000424081c44080c0c2c0358101a07550310300b0003215006e10304550350a500200300b6104440c0c60348a000042402c1410014109621100d081c40c40e00c00d44d8024072656035484041c884600e004075165401018240d0095290070060f90380280001c0d006032000300b40c00d2110b01c007a4510b41c4d4801155 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 316875368 1250 316874118 316874123
    0xf060406120602070614220609080a0c20060708031e090a03030606031401030b1f09090203070f1212021c0c120908120a110d03060f0e0610030b0607 65
    0x312001c803107810580e00951141508803003041c07801a54280741d00d100300d042d501c98566200c0301d00c0421006a40325120401c0d402040300c0786a82c9c0c4d40c6440018010a001e40303444840d642d20360f11440b00c98900407802c032006d1940c0013100d8203040c0e00c0c224a96078490031640501d074087c0c12a0b4981d104c4201c08842e2004025a20f45040148030810800341c60009061640600a9405001c0c191741c90400f5411110f1500e0900c007100d480c0d000500204000c031769119041300c0b04100004d03002c48903d09032000a00280c000b4118651070b07441c02c4003913140c100074107030181480c00101d40c4a00d03d01114178140040040000380038440864010785400e00a0000100301c4a4844031a007030700081400090414180003401c071024686081d00c010014441c400d20403c8e10601c80003408007880300501c2c100746801c107410000420418070407940c41e420b0140106a034604540d1404100e040c189a48006203031728a800041c13030717070300310b00200030702981d80c0c040001c07903042a81400995150724070041360301380c41099400f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 316876618 1250 316875368 316875389
    0xf120d0c1b0326040308040510170108062a030a0903090b070606030c080105060112050907050607050706091512051e0f04060f0c0503060f0a0509100609120b0f060406 73
    0x148900a401958044207504039030814049543ca080150b0081d400050b1030082d0a00050050341001e02c400340030300105082c1419540c401000005961409820449954000c001030000320054000001491681000014070340e405486202505000c010a0484c030562120342410600d0301445840700a05240210070f55107001c0d906106002d007007503210440d4203440b03800001542080600c111401010140d640e400524803030ba048602801c40541002c059001c0da030b2000540380e80d01030062218902c1180500049442d041c0b0240486525034800c01380b00090100d400007040d0f2001840d40c080e102c4000018654480c40b884a4600c07000b618417844076901d07031080c080c4040800501030303c500d10030078040c06040000310890090326010301079900450030074800300710940340c00050039030003101c0600605901a40d5000040ea4042d003500c1402220300d5204050115036440462a000b42141481c3d04400c800300e555a204421001401c548200301500003144241e580c6400a074001d02d0031001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 316877868 1250 316876618 316876673
    0x302180a0e030318120304080a0309151410050301050115030203090721020306060f0d0209040510110406030b010c0c03080a121a1801030c0303050c010908040e04020f120d0c 76
    0x2402840040e504e42c029041d8444d4501d9282c03101d01240c1100e01c2130f80d02c110000d050a0030350300180c0151113844801c455441c00100060201e40305486040c8407200c5248100803141083e0f5110110303400a50802c5003e64100001804260215021074008000c00d180040e56681d9203108142028103540001185022808183c50b00190080c00c800020b030007203040d116191144000c101c1c000d08036803401c6821400446400005d4601118101e5025000b502a24103001216107008203e4108030104030011001050a12405505101d0015400000c2c200341c01c01a0107601c9000c2d011056110090101c0c0d40018084e101c28482c6012a1050004c0b000038000c0308000c09068004000300c03c03c0300d02400310380492100340e01000c0303401c2d41220707004060800410b00b0342c0c500b210b1070361042410b0040da649a002c00400500da003401400149441071045241d42068030401c100000c0401c00c032841000511400c02941e1004134603c2c200d910325081a541d01a00f0b8070340448034904079010406e450300000c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 316879118 1250 316877868 316877881
    0x50618010e071d07080609131106130e07030e0a1e05060106050a0e0301180b09072705070507120e0f09040c050a060f090513110d06150203040302180a0e0303 69
    0xf00e90341c100c40c072900c441c260f03591070707240444d0613400803100075a000039a0740c0490141d40c542d50391440c80600032100f00700d9501500010400c00e6105c1d400d4102684174013030303080001c01e043c49a01c58000c851440e042c000c90030803000c103d648050030400078103d8126001c503c44510380028022000682c000b040d10301300d41c0d45180240007a00942c0903c004594100f4041c0c400d468180300d201000f880c060b12078850f0f0400c5454060346210014410b100611a0403c01f0400110000e5071101e030713842004000b40b50500c0d030340c41102691406084801480014800200000c1181100c100d20460518044406103a4800000c0c800310300b0502e0b4981002c00e020901060003150924081520b2050795000780c2107643e002c0032a07801041d9140200000c40241d0180864540030101190302610500081040030301108c11020b41e40c8804070a40c410756882504012110041c0c0075000c02d0002d81c0041c42c03c11b40b550300403521600343d0764050b0840c41c2ca40d00001e50041c404d9071148014401c441c045a44a00c1c082 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 316880368 1250 316879118 316879139
    0x4080d020c04050117060c070602130b09130c0e30150105030703081227060703140606120a180308071b031403040c0503030d0903080105040207050618010e07 69
    0x1103500710300442c101000851a08403c1c1664030f4480b00c01002403030f065079524020041e03600100011500c49400300300c82024622017041d01c0717014240e10030810380d840004c3c40401c0454442c240f1803c101e5410031f00741d045116040404d41c4211340d002e8812101155a8003140c441c16450280d111040d0110f849032029001400540d4543e4800340e05440c203100d0745c03904209030342c0389001d00c8010116401044921404888410102e81081d100410070400da42c0340150790785c900301c0b48000e1044070b600c000200010a84d16008002c540b1107a01601902c6040074004100b040c841c02422150a0f0450008104038100c664083d51080c503200c4910b503981d000c5890000c01007001510054000b55000000304240d403000c2031803510145d4140c4801d2850701000e400c412094100410640303c001218000040b01d0b01c00344010b00d00d42c40106400a078078070143c60003034540d65046e001030f03000d18818032103080000c50015440307030004428201c458890141c03112032400f6040100c00304503c0c1c01031090008500542 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 316881618 1250 316880368 316880383
    0x5041802031501050f0618090c07060f09080a0c1b0b03070906110712020f10120f02040e0403030908040b04150e060c060f09032104020f1005180604080d02 68
    0x300d098a00c1980540d0032206002c2e0300303000c0c01e40d21000060035804c441c50003a0080041400e1040c851170381c2410a000206e07061030032600c0489009000a5840412680307110782a10404d107134100300040c40c22511001c04034010a801c00082c00715140085c81400040c02c5001c102000c0381380b0b000c5400340c41e6088180507400c1590807002144034690003180450003184041c02964410008148842c03510122044031107607640f013641c10803080443d442c80c40d01c442c0401c8a82c1f00180d1105047c5e00500003000040314582c501452003144144030502c21030010383c0d02960441e4042c5400300c1c20340f02e0b500308281c0318803569101d604240400240000d141c0269100108041c1c500e071030b01c980941c09103081c003880344100026004035070031000c006941c2045040b1065040094031046900b40440780305480341c040003041c1d0900092028030704210440c07a00c007803416036400003900d8000c190a19000302818502450142202009140900d40c02c15100c6030b098500030318030750b0100c6501c500c422102035140c40c1e5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 316882868 1250 316881618 316881623
    0x40503030f130e1311010c06020a091e030b0a0b012007060f030522030e0a060201060503060a020a091a070803010303080f0a020f0a03020304050106030203010504080d060e06060a0c030306050418 85
    0x115001c2c00900c0c000d42d03002e0315200f00c41000c40c00007220810350316881500d40703e01c109410311003034840c40c1c07000c218607202401050900d81c81d4100c2c0f50f402c003141078061105120407040390303e221050500000d4410310415821401c0783d00b0100310b1103403000060304c05d070030306e219079407104203600c1c808028542e00003030b80d04111140d9858180801000c44012416550126000001d00e130014801181c001c000305040d80e01c4600031310300b010300004518009500d81e1616841440140e445600030f100703524003444060382207102e0110131403030000d80c3c0401130a0198544550100744161000d6090084149012603800560095500341c1d42e60b1640341c06040702d2002d64000c0c900750000400920700480c0f82c82114007189440c002c1c94100800e00108a01a5000a00403a0503540755400000140c03024000e080c000e9100c5c100742c644a81c5020f4040c4200e40440e400f900300400342109111007521624100c68a00c255841c3c51070101901d03040c164050403042e808181c2040c80d201040205200c0855000081403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 316884118 1250 316882868 316882897
    0xc0a0e2b051f0504020a05010c02030a0b01180614090105090c041503020c060703090309150e06070302010b330d1526030403020913050f0a0510060603180b070203040503030f 76
    0x149070060b0242210301c1258000e422400c42035080c025580260070100b40c0e0f80c801011140b40d8170882d51511019030003030713000b41500c80d08820107500070403080c00303070001400d0320f440c022040d10030010019060520601c1940e0140304000049008860020219805008841c0d10002c0284852a0043c000c0d03011050a0040c0d00549c03020610303551080c042c0940b8180c0564420418070305204c152920f520300c01814205220485030941520385812020b003100705e0182c2c00000d441c9900c4003e01040c42c9804e441020400e40000004011013041780b500d414605020740f0880e00c4155561040d0b0050104071100c111450242e440092480b000d410303124012074000c40b10b0304d00c806011460035034902450000940c051805d40008010b40310496154000c14001c004075500611408150380c20000e051009440036005074129058400047c02013034020817981c03600b0002c0c00e1801da4421050f21000e1130040c281402c480c04190384510810545002e0300008042c0d903964220118100740c00d51000f4030880343d0705d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 316885368 1250 316884118 316884163
    0x3124302010f0c030c0314040f030507080c010525060e0313050f06120a0908090607030305010f0b0403050a0b0606040f2909061615020703030e060c0a0e2b05 69
    0xe00c1520404210f0764944c9841303c00c1035595070142e0308084645403d03070b860f0005110005440140000d240004c44c02039014140090900d01185e0030460310f41d04030750501c0740400c0450301000c4c4c088041000020070003156086548a860814042d018034240c0301c59603c0082410240340300311482400403260100da1010311004407609001313843c040c11111000440b40c0c0c4001500004254019803a01803003010410f2501495600241d1540c009000030340c0000c0d1307104018801d404580c00030001800c003c00d181c906091540d41c0311703551000000b07802058810301c0d030081082900c0d08000d0310060003103c80d04204207612000c1c2c014258180c541860310118001052003000410703c0111001100c000e000c880c0b03807030b411510070903442d03002c01d0040700c42c1c0380c404101007010100e034405840074911903500447c42a800c50100c42c540007020700084c0c2800340c104120b402c010740201030507246004c185c40414046000b845240c454040c0140c400c000c010303101d0134240800c8008642001c8000c056940d25007203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 316886618 1250 316885368 316885397
    0x14060a081209091b040803030a050901020f0f0a0c1e05100603030c030f02030c030a030605031506091308040509010603091b050105030103080c19120e0312430201 71
    0x2900c10126096110400812441070b40b400e00007a40741c0d000744240e010640d510362500c01c42d0304507070081d0301c59036594101005020049105000741078121501718000d504020420440b0a1903110b5050621104c0c6400500381e00d010340188500000940c020f0040c1e25046907814140068645402048800740510301441d6081c40d070600c1107800381e0750107a490690103200c03036030300b6900d03106018244420741c07200740f05401101c00100000c080f000c0d06030382c0218001d40703040d0a0526010b140c0894101e890728010802c9003030b07110000000e03802906030741c1046802d0103d0414034540e00c41c942220760010384a0001064003a0184c00c1403c42600c82e981e41e101130300407840b01d056071520302c1c0074007030008030100010004142c400c0042c000b080d0940b01a00c6410b13401c010100160717140400c0841e01841c9950203100010f8210f20700480c024001d90142c40010030640e51004144541520014543c0049201035023400032503c98102d030b80460030135116003206401c0c0304080d02d18210022400540d001d18415403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 316887868 1250 316886618 316886623
    0xf06050c030901141c0b1c2004090804080102041d01080304050904080d0504050f0d050f030612010b0a120606050105040b03340c060605010e0a0918020414060a08 71
    0x140e40c40840245003000005001103031400d06051013101d804400b03008a034544090300b4000307030111200030390000d0b45444140034005907809942c2d0070240303030501c451074002244003041740310314200d0100b05c0d10b01460050b20000d8014880180003400e1680040344c04244c882c1d05600130001ea404c610701d0301d80100e01030705120f00b800300d09020ba00c0141e002840308010605180105e1500030f44211055420014030440325070032242c00f15420b54041c1e2200c048440f14040610590803400428a8483c0c90080d0304090702040c0d1201500c00b9005d09078203c200d0707202040070350009603040340040001d03010a07a07601c1d0f9070001c402e0701303401070341c1c41071601000007003d46c098401c0b01c1c200d03036900358424110740c0c594111004410228540818045008a440300c1d0100340e421190b0700c81c2d12a4581380382c94101810450102c95103038120300e050000f54071815503d540d8102402c0101c0e4054507005c680d4105101ca071075441840b8500081d000381c20121100d11385848081c07486d20a40007130316042a07040ea154002c0e503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 316889118 1250 316887868 316887877
    0xb0301020c0a06091712180c01020a080c010f0204060908160302012a06060801090b010e0f06130e070b0405030c0411191e020d080c090310050a0b0d0c0f0605 69
    0x1030070781e0088418600181e4a074000050250003040c00c1e1050680340c3d0310035440d55101d000c2011906000104000100d10500183e403a02c01c201d00007040c0e41c03148440080d544035204e2101138010600810314508824094000384035218000c0e90030b644450351000007424903180c40c001c0603054000c0241e086002c41d01c0452130003c0303903016510700c0380d51000c8444030950b06445030b412440342d4020b900880007060f52401823000620041000148800c808d00348003200350310681102040c12000700501ca04258480840c64001c3e808070b45120b4940c9841100380c001740102d0320b8654440c0a45803000400814182c00f5004441d0305038292046040c61070100011980218145e620344141449400d00c0544448140d54000d0100e051442030308030012090b02400c0000002400160b20128000d400e441d8000e900e175401c01c088004407810605407000207519490001c0414100704e03030b034400003018002c2c950081c26031050041e0508010301080d00385024401000e01035203820318020240007640520410855 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 316890368 1250 316889118 316889137
    0xc17030f07080711120912010b0d03140c060405060a3902010e031b150405060430020a0c080c060d0b01021f0b010e121009140318040b030102 62
    0x40e0200d9440c00029a0308903005021035041003403100d000d043d1110100803442c401c0342e2482c9065110400c0c00704100801041c2c80401c4410390405000241e95202c02d07907500d10f000e07890704007840840c0014500002a01540c0d2074110b06102e03c5e814042806000300d60f40f40208090760050116862441100352401d1b04c0114480650954460207804c00e0750403001480044020b200201d03039000c24403500c900d190050b5a0110b04050444900f0750448000c0120900e50f500192000f0528542a242c1d03035200c200007040501512480c4c0c40000c00602c00300398032110380d40c038602d0f620314201440b04020340d100303c02d007000c85212120680102d0091320000d00e9031030b0200014884c0e03160110070311490016150340c04550341544100b40410280a2051100c00886c0682010005010100e00001440c2e00204480a4000d400440c0040034454000c109105040e550b01404244020030349442e070003c0c012640012400d00010490341010b2019070010036924a0865051000c0100786040600f00e108040c081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 316891618 1250 316890368 316890391
    0xf0f06150809210418090203070306150b0f070c0f080c130209040203040305130f06080a05090a02060316021e250302060412030210051522020403030c1703 68
    0x4098140d4030940030640d00400a0b8203882160450701151155000c401039007004003d40484c0c188288001e000380b030003105025071070034481c1c0e00c2c1c0c0e600800d4232400d4034000640342c9901c5440c4440c40070159070f4084000d01451441d2a9203003424450a00c442e00069412121910140000100da084440303a0a082e2605100139107030116503801046056040d0540303141c0415024821180030350703030750b2000e580300343d0198684581d60f0740307040103c04511466810044072490100300500540e80e001c254035600c0540c00070006803e40f51591003902d0720800d0207009501c03100000800c00c007040051b19211950900d0740840e602c01008415100d00d699281c021840c80d64412001160040314105003c0204e0381d0008000e0304860b01d9402285041e400307600440840880d80780d14500301036042003500e01404104e1300800050400c1452801c075144e9032203041c1e00c50306110091501c90314560401c4040703d1200f1381c04550700d90b600d140c0a020810380d94010b40e40c66a250302c400ca1062442c8003240d1069000952 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 316892868 1250 316891618 316891649
    0x5011701060f03020901020f1b120316140a0510021e0f0706150f06030212062d01030b0406030b01061106070504050d0804050d05060a0b0102010908090d02120601090f0f06 75
    0x3c400940180d12510304501c2480406420000c080c0301c008020303041d52520016905155040c050108004181c0c3c0ea0558020044062484025002103140c03582c015951920b0941c0828524a00084007001034128007501c015500d081607598018002666401b42c1d801c5806a80314030380600c0e0044008411060303008010040006e4440e40c0403001a00c030101072404880e803120000d282c06809604004046940003d4030101100c440f003034690721107401c07a1040d2003400003007a5010801e4651104a004039904e00300710001d40c1c00794000b40d4441d0006030040146542e80e04092824080070320900b00850140100e43c10251808200c03248139442e6901c0d0645094503200501002481d000010740c2c100d6818807001c03400356100001381200500600081646041c640070060407594240145030641e89442c881c00002011281a01c0c0c00760401c41d031400b980082c0d80049011501e480c4105410b80c001d0400219441c1e06a41c000c01e085054003008011201d040260b45046640c18011999500034001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 316894118 1250 316892868 316892897
    0xb0a23190c14090409050607030f0f09030e0405040302030409090309090507170f0a06030b0c03070f02030301080d12060b0c0604050607080105090103022202031501080a06030c12060905030d060501170106 89
    0x1000f070400e104054400540202c00d074643d241800360070396841001036203401c0c138a16107523854010200080c0c0c000d05d04016002403a074000c1c0860121112a030b010b1511000003405160080c01514002c0100792003d11034000d2030300d802020030300c45029410750300f86001c021522052043d00c880d54006800984400d0759120740c803040c50108001440814240d40750300340440000c01c00341d84140560300c42c42000e6101d050030403014112100c1909020304543c400c1c401013000300b400141410600c20142450f1340409000ca4562024043c15004541f68110000c0c0500210074000f034503070300ca00e0255003541d002d91207005040300d500c9420700c00c1d1540070643d2401070025240528000c03d20400910030005585681c103081d1090341c1080b29080004c1011000c440419600590017641c000d2030f44908101c100d095507282c030310030462409000740b2100d226a03c1001c000e03180d404044500e1b041030489442784c8038400d240010706030a0003054005440000c042101d03403202034456040c1d5032a0f8480162852102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 316895368 1250 316894118 316894157
    0x32303030103021905031f0b040c120e0a080307020607080a110405060c011509020c0f010902030703030c080403051506042315040204091a030105180a0b0a23190c 71
    0x800c2d125845132004a8001541d9400300603074220300e580b2074421600e0040c0c82031704004541e4202d241034013440c01c2400060580c2c2c1c0c007400b00310880d0244a4009103a14001440341d240041d43d05009144e103c0c00010700119a800142383c5c2e10070078050b5107d60450303a8441103501030f00c059003c1080819428003040c485850008060070107c0310745d10001500c524104440c0d1000710041d44200fa1060b40090f6106060308140010101c414a00c1d00902c500085a0b0200b0f80e980c2e5a4070000e410042507508050070803103d441200c00031078100d802c40d10400c2000e44e80300b03213540e02034400700d00c114641420014a010004100d40c49211590b1100ca401d03512000d9600c1e41264906600f5800380d401c04c4003113041304a5208400c2e04492101c00742402582d14400d06084036400f504072180c4ca54904d03139818101200040a2036090b910041c800000e407600540040540300a6024800c8001101c401050b01910384602c18420702000000700c0c0ca41407203800403401c03200c04100550001e600d6040e40a90035615 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 316896618 1250 316895368 316895389
    0xf0604060515030d0e03060a060f1e1502060717040807030e040f060314151003080a0212030a1a0a061d1c030f1101020f12060103090212030403230303010302 69
    0x602d03440e0b8282c1180440000e090108050090001c16241d020120084c142042070560014145504002140c100150b0601d400704d142701c0c1203030310781140c011041d40d403410f0f0303040e04010710000da41c88052140504019440320811240c40000814100000c07100c40c0100020f54040d6401040c01454140e043e20111103c40c1d0302d21000d0b8200f43c0ba1003002c81389800303512890300110301440c82441c92a00c81000b6a041c1000a01c00d10395291204051140350542c0c1c4100708200c1c1d50003207a480e0344000c012402c2e800c04182003014001c2c00800300801060403100d8002944100c610490b502d02d0030140c00401c0344002142c000c1c01c1c0025050207801d03094401e10300052201c090010500c0301000f0321400c184526146640d0110001924901001c48642c0c12980090f6401e01080082d81000407041c40340b5030500405400c540e680c00440c01007a6980d02076403101040741d4010b0708100c1c1d0403001e1000d4583d664000e10040382e5458182004c03d2452910415050200808202540c07442e40b0b50380805c0590380301c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 316897868 1250 316896618 316896631
    0x10b0a0e0d02030d0c03030e0f071e03080414040e010c050d1a060a05090109090b0906040b12070807150c0b0103110102100204150f1b0201030f0204031e12020f06040605 74
    0x3468081600583da041000e04031200303069403030740c0c3c9a008602d001000d8643d60301d09480c45920502030100307820004500d20703041d140400009001002d90b81085040e1107130650018280d40000100406e021404030f40d07244460109440521540d0b0000c00c825080b9405400c0c4600041d03014014a034404410b0b0300038003c928141c2c619581c07041344103400502241d004107070040c04980d00240e41c0c0c140f540c100140708024030000c0801c100444001c0089a24100000d062074812079981a00118940d6148415018000004100c0364410b455020303090b5600080d004910029440f44506003105100f20f036001d20581e4071100c1c03111030b40d19541d550180d600002c0c1115040d1b014035031503591441e25510107407000305a80f07100404000703080700303010b480b070440452a48100800503901c03400e580b0301e814409c00495030a20380007803c19081c0300420028001c4d81c100802e0801d80e41c440352000083d10418414444c0141118550782560f0381c000d0781c1e260381d1082c60f0415030704504001008106150300541d400381 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 316899118 1250 316897868 316897879
    0xb04050903120a0e0f0f010b01090602120d2a08010501030f06050a030204090f1b03020a061e080903160303020403140d090303050a0c0b070522050f120c0303070c0e09010203010b0a0e 80
    0x55494009508007840246940c0c6e16a6440b180b1503400e40e0b015901800501c010b0000d0060800c04000e07045841c441c50242c40c601a0712045061075074217900d1000c1105d4504480d4040440d01d400e40c000b0329500c0b00f8422580040d0414038200041ca00c948950381c102c50004040805042c990360a00000d480081c10030780e0080550f2548a002c00d0503007070356100b65100340d80151174850440c0704110a82c1c1080e04020108004030400c0243c00d40200c6941c603078500c00742001c403003030364503680d1030f500d184101700302c2c050010042c1d944d013410560181c02402c15a4400c0d40180d00c0709090800c0c299882440c0c2c5844c2c00043e003405000c2002c24042d8000342015582458100d81c66181ea48818071180815500500003500019416a41c01c054400700ca0340300c00751140280d200c506c0e18000842404115424511404c0074030448440c0304000c00412464600c09419280c8904160a00c14600e0043cdd01c288004c25402d40006025000c042c8212410ba51940c4074a44c200005000211862000c0080d82c94201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 316900368 1250 316899118 316899133
    0x301060503030d150909051501060e06030103020103200a050901021002090108070f03020c071d060d03080c161a040302072c090f07140109060207050a03060915060602010b04050903120a0e 82
    0x3003480c0c055200d5547c0035200030041d400c189148064400700503032050041005628a10066954140c101d0741180c6d024600800c140b044401840381d100c15039070002c116050001090302d1180e0b0010f0180080800036007d0301c8103001040d070804103074031803803640f18009040900064851342c005c103003a10316060549001402c0480140b401ca1801e5460380200c0c004204604040403400e441c490301c964403803426200305000801c01c0d0b802626aa0014180b401c6542000c104204460b1a40115410581c3c02902204038900ca42c90101d01e0f4035000d45050b801400f070148086121400300b13103d244145051000000c0d040ca2441c1d8a411681010304443c4150282e0b440b0079000382010031039040a40350b05a01148041e2400f40050315000c00c5900000a5400100c020040c658417804488200c1350044400306070045503203001d40d4610601c940703400d089450500041281ea605510001c6803000648040100d038480d500c21a0382c9004001c00845000c1d00800045c205414681207071312007001050882d80740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 316901618 1250 316900368 316900379
    0x2a0c121e1e0138060a2c15040806060d03121505210601050402070503090d0c1503050f07140c0712060b1002030f07031e02030310050301060503030d15 66
    0x8841020100241d680e450f0384000c1c43d142181196108050401015001840140030049103024501d03c2c115200b0400440d6400565024644070306003171a51600052585260343d008100c00310002180074042e9480760544910812808215002c0e02c00e601c004000d01e5441e03030300304104500c540008504000700e645200700401e141d4000c440c0d400c410403c41c6a55076040c9814459a000c1d280140a028203410a01040c50b03100810454192a0180d601594441090510624600c43c15103680c1d001081d000003401840b100d0109082641d814144144a050210004806131141500c0305c02900c520a4082000b45000310b860090711103024050f5410950016040d07030825410303a201ca194400007880d1b40c5c04011042c411b45e800c640741140c5040980c0b0240c0c4000b552405403030f60b4008045800140f0704149401a882010045a418040500c004140800a40300c0d082624880f5003014408408980b501d41806030006949000d00114200b000c441402d130080c5c2100110045a6000c442c0007194 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 316902868 1250 316901618 316901653
    0x10f260406230a0c0e10030c02010f060b0d020d090203030f0309100c1d0a09050901020403021305100506071a010314010c020705030c1311030103030201090203100507050403020603060301022a0c121e 87
    0x922511035200002c010550003408ad0a44a100501c107181c1d40c645402404035002e150107480c240c0900f41d034016201c1e950341216000030002c1507406540343c800468921485000c4c803005501c038205000598100c40d01f4281000195130b642c4c1210700110b03400030f120b401a803400d800920034801d030040125141d01e65558151044800644a28207a40d4000a050066041c4520200c1034884141c40c200003e103000b00707401080c003d49000e040e1140d180003481009003c520038080810001b400c800110300c3d42d4903d080c00e09100204c9802e030f030300e5007014426130119002140400480f403018014102d10003c10042001034440c00c0740c02d404699440285000e80c520003800b0314065442034000040040050040500c1c0c03041c40e104150302d241c1407208020005a00c80d040c2e608490b819a106602c0c1d40310031000901a0050325034035030350850017075040c0101941003401d10141c1c0c1c04445c02c1d00c410000640c1400190000c51582c0030155103c145072070040c002110740005411501002e0346d19460340c6015800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 316904118 1250 316902868 316902889
    0x30d05070228062613020d06050a0f0b030102070c060806010c170d0e060c07080a09050d0317070507030804020d0219060908010501060815010f260406230a0c0e 70
    0x7400c01480d0710381404034a800403011841e04000e400022213002207814008400b8100422400c0c1c0000019088011900d9119542040c590b101005000ca8500044604002c00d070114001c2e1003e810301820908500f0180700312088240c100c41301c00c500b00d05221098a0b280d00260038a030412000180c14000304a403c0307100340010075041c10241da216512180e0300140c440402100900e03405c01c6c814000e194072102c00301c0d030300e41d0741c040c0800341c40d041c3c59102642c150209070700190f0070110b0700c0803007010180e1208007032029403101000c1c0074003034580c0203084602e400342e00d40c0103001c94000004100513140003110030390020710041c41305d8200030b00060300d0402c0d07480d541d201902003003400c60284035281d400e0003003502501403890030116500d002340340c003032210300d8182607207040c002150a101d480714410030030f035041080304108404d80d50b0030015101d807400e502101d0545800d17103000c80a0782040b01e0820598501b03e0505c84004413915401e00c4a4001d001d1a003074030043c007100038020303820b5803122510344 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 316905368 1250 316904118 316904179
    0xf0f0d05030d0c09060206070e0a15080601030f05151903082b0b0d060c0314010f05120c15031009050f0601031506020d03020c0c1306030c14030d050702 67
    0x2075803100100c900000035904640a100140024900c0900c01e0701e1380007540c00e07403012061500020700b00c02d00f8085400001107401404c60704d24056091401150052400c0c0d0054400780d03004c100c031104403a132002c121603059a0703040c94210001080c09145c03403c0e40394401155136202e034220a146d80d030b564400b440c1c0d2240d40310300c1003011220009103801e00141e07803041004950002c184200c0100c440050003400d241a4004e0030580c1e202c01c041302c018401c0d840840400c02e134000c5c01866507190b84070b003010785045100b400d210b008070402d0440d050380f012950000b00000a8400c0905a01e90718200f005900010300940b02a840c98400040c29140d50003a00d025450041000302542000b400050986401c0401105014840d1004112036030f80080c04604881d45c5207030050304e030b0307444200b0359080c0420650050381c030080e004d6409861000c40d902490440e0700c82d08116803165a561140f40e80820302e000034943c1504027926460005000e000100703030a500c02401c00100c446404201081101c0c1320b82c41 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 316906474 1106 316905368 316905373
    0x2060a0906091a060a08070b07030509011103070c05120105092505030a050601081c14031b030a0905060106390822090e0307020f0f0d05 60
    0x180740340ea907001549452120402e80040810142552030300e05c00d003e44100041c036403c0c00a00c1500b1100b4001c0007500f01000b584081d0340030b400180f0301c581448401103c02440b2542440103045c91841843c484050505120a2000d440a058040302041c0e1604007842110100001c45900072000130240e12294042c4503020700210302e841d80101e42610440c2000c1042060209519058640304022108160380c01d10741e804000214001031408103207240500403420104000855002c0d4004030342c20350901c44900b0700f800030742c0101c4540d8516a0f4600c1186d080113011b11619005007031500e08202c0300b02044a002120940c1210400074200004446154160b2600401130f05560007916041c2c580b80d50651032600d0f07004003154401f010540007000710f03075121380f413041441d40c100e100c008604003480c0341e0901201e19109202c040d4000007403440b40340b0b20750310113248200d1280305401 = true := by decide +kernel

theorem cover : BRFrame.Cov 316726618 316906474 := by
  have h0 := BRFrame.cov_init 316726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 316726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 316726618 ≤ n) (h2 : n < 316906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
