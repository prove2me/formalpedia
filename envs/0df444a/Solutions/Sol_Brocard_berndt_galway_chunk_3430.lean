-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3430
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:38:16.856249+00:00
-- url     : https://prove2.me/submissions/ba9eebf4-83fd-4380-970f-f6b6acf85b4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 616726618 ≤ n < 616906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 616727868 1250 616726618 616726723
    0x90905100f2444060a0303021036030f0f080f0a060e0c030a11040315110408100b0f01080601200c09240118030b0c0904140405010c02 59
    0x408044141d40d108200c0090850701103507002102c0070403249070b22200c00c031001c10307405e429924000c1d40c030300c8014504240b0581d190246c0804501c00810801c280008840c0c0c608003003c1841c403001c5010b078008085001c0345c40074911600d51030080c0b00107101c0d00c86595600d8219a20003424400305040502002d4206581d40408502468020b111520a000008200b0b07540e040c245030150171580c89030a0312100b5071080c8000e00005022004a1810800000003c128015034203804080b038443c40e4820400e500c5074070549003040e40c040d0403040035040c003103490b14140c890001c01940c08040803146603001880b02012408982141d40a651002d80003c044840d00305e084c0c800300d01c00c0d0000b038655104941154000400501441d07100707210568003843c090303603941d890580d2220042d0f1607010041070440003900040003500304605461a4900091045c80300c802881c07000e0440b03107400e40c0c00380c13031550822480e52607250000030079107103401d1061081100000411038100e8044c8050000615102d010724 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 616729118 1250 616727868 616727927
    0x506062b021306090909080405011116120303050901182010050c01050a1a061c09080403211202030a09050d0201050a0b0109051f090905100f24 63
    0x4007a018026022890142e10382c10301e8000f130014200703940070585603810240c0300b100155010003a581228000e003027218403921044605401d185c0035040c0300c80d502040450000d03601500001c1451514001e40b82000a03803070303102d95070b0f0036035640c1c3c0035030900c40081012400005244000300d260790005011036200a2403200001010400b100d0030382c000090000c10558402602031050350b422443c2c0107410081d8030303e00e04e0350702d02c46134171a1307890780c40b8405c0401c60b08000f180d18005a9840010002c003001002d00705d203850611074005001c207035014101000101d100c0b101603044040e035030006840b82000b440300041c900010f9807005015a8040351210f1310400003800410036490040002d0f0008105407410b891040c0840703548a840303904008061104004580740d0444c00040080c00c0c0c0c61540310042d074801c0550748201c0503403102c890707245450101300d1030070700c80640d24040e03a040780c00d40c6448960391001d42a10404d280518041185004015107101d4000c0c02c0741100c0320400d01240f410040d050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 616730368 1250 616729118 616729121
    0xa030807052203060e061512030c030c0102040920030408090f3c01050405040f02121e0f01140d030e1302040e0c0705060106050904090c0b090102100506062b 69
    0x2810703248040304556050040100034045c00c040d01e510400181081e26104510400e0307100c00001c468028036085124880b61001030013140d010f10100e2080b01c0e9074420741088507000354024811483c1480c07500303401a030341070107004c0c2e032001701403040b000d1700e0850301c031500d651106500003020280d00c428402000006e689401a005284d10440c006011050400100c07040d43d09080310140000d0b4920701425250980e0024140c0341030b65030640300080d8110000310101e0091184445109555008800f00103406000f0084200702e04141e074070740c14003901e8100744407034400340038081c10105010500c0c03c90f0300e0b814203600381e85a60b802481c001015031201004100608022140c4e02c2206400013018020400032040c0b213034010800d610341900d40081615101e4070b644060080701d04001c3e0010381000c0c00d55558221541e1550441001303241c80d95031b4011200903038000c0e03802c036016000e40000707010040421f101d400d1140d1005001c0a240c01080c4a40c5c9520300c0b07032614280038a9040c08002c14901000d0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 616731618 1250 616730368 616730407
    0x20d0b07080f09030a080a0b09010b1e1611010c0b010f21021011070b030c042945120109052d060a05070f02030702030a03080705 57
    0x14040042403030900c024000c2101c100140740719498101c00050100c100c000008a96142c05540380c5020191102e00c221030246c0940d040007a400b51410b00003080b4043c030724009150542a608061481103064510b03000c240c0038000001d03282403e80c0170000081500c8140c9408034a40501d0880d1516050707950380100e204007a0404004d4540d5a0024842ca2100c0480d20040c030804103002006446150b00040e12500c0e81b420310b80070400c44c01c10001e018081005014040e0210300740a90b103d1401c1010381e40b568116120b040c80800c04c0403200c1c0e840201d14112100e10503000c840491902e120300c128000403481e82c00b0318031038003c0f503d000c2c00301821030070b444010701103000c404c688a10a2400204011a4294009010309916010706200051000100e025041030003a10a07840342c0150044004288451000010340340201e4081242000490740024400e035121303102d281b181a0803400807a501d0045102c0290141d1145940c1d0010a002c1d0030100d600c2011880d1183c03601d030f04580c00300008840c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 616732868 1250 616731618 616731623
    0x150702060601020c030a110d021306060302030f0a0c0e010f210e0f0d09050409020a0320010201051b0d0e160b070308011a0d050615040807030b070c0b070f0c020d 71
    0x420000d001042da414000480e002a08900602c0b034001ca03511751912042041c40400c0c81030010030b04080864584070403c030060081207004015199460300041e019620407903444190401c40400509100c0b100c5c414800444040e03500c20484114460054a499100c610090300b403210100100c03016a41c09030708503850400792000800c4000442c0881c510748440703240f4841c81a04200a882c0049a01007800004c40740115804143d45a05001040341c8a8003500041e06550b05401d1940c803616185400040f5140280d008100700d40c2d40100c101c0c10305901d0f841d140c03080311040100006505041e00003020343e00c00e90081e07c1c071815010a52959403440ba61001c144080c1c0420050241070700145018014014884600301107a0741400503c2940710307042030b03056455a558042407540d12654036000440e1301401040d90754a07211401103694204620049894044c0c1c100003d80d0140b0a244a4099070390001007070115403940e000603140c290280d41c1c100b003000410310500e40560b0303480c1c503001112030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 616734118 1250 616732868 616732873
    0x1c0b0301110c0d0302040e0a0b0a052121070b0604060b0310090605010f3213090b03010926070f030509011209120c020105040833060a0b0705150702 65
    0x342541810f400c05518890700000c0c1441400200041d0000f6010310760f02002081000800d5419440000c003240d84d03039008550480c0c0020b100c007549041800401104071b01c240200d0301e060f003151640f00e07030603105454007e21904090040d440000c42d006880743e005000204085030444c0c0b1034400110355002112142001150031608000321140b9101d840094102840c00da2680d83d84c0781006400b41c51a003a00c002c07800701415030785003c00f100030990100440c1c1036008541d280304d0f1028509000d00c03203010b640f140c540342c07188148040c9014440d0381b05417940000e1085105a02c404040d501d8596442c1c3d108650317004104080000b03500d4040c4101c2c180c401d86801e0703148c4d000ca0000504003a48a008080e00d0351800001c003012500d8801c1e8a542400c2519050b094041d9a1004a41310b000d59406140540b0907840010084944802002c0e2061410b02281425004094907542c03010002d592082d04545410001d20290440f50024541d09003d41d0845500134598148800010001c0b43d0080058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 616735368 1250 616734118 616734127
    0x9080705061905060a05090415110408010e01090f0b0405070e0910060608091b0604090905010603060c0915030c141209060c1e03090109050609160512031c0b030111 72
    0x20b001a4035024900722440c03003044030349041000f280c08004113000b0307240b052200c6000142000b441003004148071121520501c8450b100f90051030ba590458041d0f071000c0c0d420440f0740203114505215040310950888841d440300c221b29102d5440141000d0410344240c014450b0105a40c0b084500c900c0c02404060020642d5102e010610f00403549950002020001c2510620046100006028440180c01d007420001d28000b4130006060b8880e603444158603900740600c2c0c4003406019841401201d0161030248a5600d2000c41164428800e0242c0503004000e200700000c0e0300e01c607034841107607030a450400404081e501c01100b00030790008000815441040070400111311000d10100d40c10180411115080c8000303990030001e16102c100740c5174440e15011000848180094002045894000080d91803c3c10132016881d200ca034440561700320070b04841c030000740a0a16643d800c1c0110340c903002031803c0120081805100f1040c1d00d088820054481d52800c800365400c1c4100400c240c088840107994 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 616736618 1250 616735368 616735381
    0x23105090705180f1c05010617070b1806211b0f0405014d0d08010605090f0406090c02010b0402121902120c0301061106010303140c010908070506 64
    0x5840c020601e208018041c03004045103040002507101c2d41c0c2080340c01d60b40c221260f5000c03d5070b07a0042110160b6141c00894801c0a01c2019400b81c016503040104400d056543c02032210b0713503483c40d8400c45004800800065054098201c604182124020f01951400f40c4000c4055080350144410640e400c103803a00340f1941c0c4404c00f1403000d1441e409943c45060034180d48212450f8025071041905002000c808808032000c446800420040d40d40c1081e421700c600c010070008017403603a1a452001000b07140c81c2c0c1550072000600f010500c030300d680c1c80c002980c5c00c22804403603541258a000e40c00c403003d801d000d20259158001c40000d41181080003500400301e90303009003501d0102c1c0516008038810406902e40400c40c1079900c1d031041074522036500711440f82c05608000d1081c01c0f280c0380e1150210081c0000009600d00441c101e45207a80d800138549210111503441e80401e10009010a454820034040c0547e1a0054400f0002c52400025000c1042c0c403841d481b43e00410080380c8542110b03042002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 616737868 1250 616736618 616736629
    0x70b072004110d090503070816030206010812030a0f18080306150412020120071d250e03070e0a06050405090a03090621150302010807180504023105 65
    0x414000c00c541c107101050030080c0d005180d2050805202d105a181d592100501c60100100c0e007a483d0301030b00481d43ea40c85110f87c0c50340302c0742c41d4000b180103004040c00001c3d080030000e08003c0c2c496502d41d1a511719180c200802c4018040f02406030b100d10707203841581c200c41c02480403012010b4001c6000355230728070f0810100b002110300311100407038048003480107000840380704425210f4a5820300300102d1028080d10500070380c1d054250407007d548076110300864000c60081080f5940a0465601e000365119021419103256031054a040c00f140140e050152251042c0e020300070b07021000d07041d559001d0711662000045501201e00601c1c80b41c8034101080325040600c0340950000c1420301074a9130102540d00100398017a01c5c80b0342030810070711084010140e002100360020080011004009070501400d44018040321031001b81d01146c0020000b41d5450f014800000340111803102801c03507141450200002900401e40341041c803240703482c0f20518080408188000d80e01800005820f25140408005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 616739118 1250 616737868 616737923
    0x80f0d1d0d08012903091204080709061a190e060706060e090a0206042304091a06030106060c020904061103190b0f0a060c110a060c0c091107080a02070b07 68
    0x42d0b100b01e130300110844000030781320044842d42070240820b5685c1c894403105031500b02e00c00140c1041005c0040e0004808900040c00e00440d900c60505029480d80c1d800c55503d031610441303803294002403c1213400b008801c0e0000800740e04070103082901055104001140d4150131003201119603230ba0343d400510440c14101c080c036a0240b2800300070120361040e40c0c0400d505010b148a0080810021000114038081e0340e10100c07003c11002c0d08c02c00c40c0011a00744400c4c403640c841e6821441c0041500495814101030248200b655200c1d210041200380e20340c00d00c408007400410a451b126500c80b01c0008104004000b1401104a918542100e4040c0901c500c121101c504c161b80c804c0000ca00c5807030f03540c0c83c0d0300c0707120003219200d0424600d03911050404191000074075144a42c086030392100803030b4680d01701921400c0107029810404c400c989034007880302201e25030402800b0740002481444001001c0800400300210a841510106503854165a01a8015000c111000440b0300424021041050081f2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 616740368 1250 616739118 616739129
    0x11d0102070905191109032508100506040b010903110607021c030f08130b18010f06090606030e0303010806040f03120606050418021801110c0901030602030103110d080f0d1d0d0801 79
    0x111b1030141e6000006ea80d0f801440e09440036059482c1080c0c900c514916022002010781070b050301c0641d41110f0f9404c008010866006102c0c902e04030074682c4a510403808c00c41075179031061501c03000c0c801da00100003168114100481e80054440e07010f0480310400800c1c01d5200348a51990118040b00d982e0152403488000c185048034440141164081544d000d4416000080030000400d0701c41e51004d01c2d4050660511200e44507400c01900190003c900c1c0e1064003155002c0c0ea0400c00081000381d455120700c0700b841a014503620820118010070951641c03400e10510078100500a01d11507060f100c1074030940d03440f20020031400f00c1d0421000d4a05280300d44e8805270800704505d420100703610506c0e2091b0300d80c241ea0401c1646144003411074410050004129402071031134040c1e40e580e19001005c0d50003400120746072500d0307400342c8596040540740200403550000459003840221114003100e40c1103207005240054850710742e9007010101400c112111244900544584a001d12000d4801078060703021 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 616741618 1250 616740368 616740401
    0xb131d010302011e05070f0f02032e0603110609060702091815061e01050d020d2009090c0d0f050406020705010e0609030409020f04080625030b011d010207090519 71
    0x40da59142d5000044900141d40041c0041c00d0fa422800c211901e485000c032300941602c41c1020403e10711040e800d20301c031143c1c80d00307080c90000003203020400103031266484020098132410006096a2401001400b900400541428200140c5400042c01200140c0d10307010500c07400c0c41002c021003424082e04e0b5680c4040303414903c840c103012000ca916a07400c05540294102818440440c0782e21840c02c41e01e011641060039522031040c010f6910083c110360144210303004098015146d44d0903000d080d80e011000040101a4558030008005490b80c4040207108130b0302d0f500c1c00c0301d018500b201d1040c82e005600403600107803501003c0c0f43c1385003195400f0709281d1150340302c2c404024500380b000080350181c170081c03d4056110881203038551140d00a58100c40020300840080003251441001002600100e108410b02110000b450650846000b01e1440e400110780c4110001a95081488040341c60010b10494205941c1c0c0d110440072540c007510100c003030600b000d40d00c3c03201d0031950003041212128a02d6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 616742868 1250 616741618 616741667
    0x22205011d03160e040605071b12030f0509070f080607020715090801150509180c011b060c0f02120a050322150b03070801020f090f12120d060b03100b131d01030201 72
    0x1038452118800c1e2700300a00d5a084881d8034644144290005621801d441405020130b061003040c0d55103803803090081807000841103000003180e000000f2154000ca00c10340161880030704101421a455100e46201d00038032441000002e020042482010007400c800880e80c0401410034040001c103080207802d10742520400e5042e0180400c0228222101c3c4100b401c003000444c1c0203010910004071560307405810b40f4540314052a0381ca801c1b100e503014000c070035802e03101070f400c00f000240c05902809540400140c014000501034a04c8403814428001502030484680a910f0741c50210b1400b1001c1c040c04415211004541c090400304107100c0030f0306d0f040000750309000c0d000000e00d503980200c004070742c42009540c01035545606c400320f0140a103081d01742505d20303100e00e80d050b01295501078000958000d240082c00154000d01000b41ca00910b074205140136904d203840c0c034000041c1c1251184040c28075400400103a41c680c0d0056100d6520182800800d0a40c9180000b42c016141d805491000c21000d02c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 616744118 1250 616742868 616742897
    0x6021e0a021003050604090c030b15270406020d0513020103060b2104061407021f05060f10020c120c1801030819020309090901022205011d03160e04060507 68
    0x10142c201c1c2561850009469540c0c440090050305544201030885040d4140200c240710f180c0c070807140314040b41c2240c40f0617074032103809000200000318002c0d0016054031941c2d010100101c400725812a00400000d414684085880307401c03906d0a9442c0918a1a120000411560507004400081c0149201d6904020240001302013404103002905000e9180d000058108682584040480c0c01150320a03035203894803040280da03039030030200890394145800c00c9101c1c26010f1030150b54482c0d84058a90560f80c078038401170103003182410310101309500a0b030340484070a448805010228103001c4006010454141c0207109807508290f1440e05001d41043c0180b0200f400401265a80c2120702400880c2401c1d29400b05c1c01d40c002d038030b001680810034000703204070110150084c20300303013031214038490340070a10101301c11b100082441110b012881c0110307a0800c2180f00c81c0b10043c58100a0140c61003160200d04625056000d60480325074001110280014400301c0d100f0b9581c0000c00741025844c00b85c0383d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 616745368 1250 616744118 616744129
    0xf09023d1211040b07120810031703041119061106070203040501051803100f05061008070c1a0c0406090602070513050705090405010b0d0f02130e040f0c06021e0a02 72
    0x541c1c186907400d446003511480202e42030112802041008051902e911140c9000e0507078410785d01e148070002d051038000c1541c0c03001c00410102241d90108074130b8a084441c48031030009030401001625000c04840f490001611210700358a000c00084200908080c100030015051054920000010b940108200440980c00000721030544509080c50764807405030070600f481d083c44081e80c25405d401000c0700740e80c168800d50410380d074403008440b0512943c0d8500c01840010b03908428600005a01c801c0400c807141d0060720080c000e940180780306001005003200386044050700b42c600b00308292000900300641d0364041c4500b00640341c4c0c0e101500800d840c1800180b07000c0464200300d407450ba5914045041540240f08990310500d010344180200d60755011380d0f01c4c041d084012480142c9041c030401c29031302603c40c422503901c0303920940395004490800604070214600203108413000200007400d072000c1035011402070300824107540203058143e050030101034150840c00604c20194001c05c002e03401039640 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 616746618 1250 616745368 616745387
    0xe0c0735071101110709020a080402130c0905040509010204080312090705090c09060a0509030109140d030b0d062c03130b041d0604060b0a0507021005030c0d0f09023d 73
    0xd1801300454681242c00c0ea04042c142ea12140459100041441d002a00503084600c44c0703000300c43c07000c0d40e145111200d1065039039011000d400a415200244a40d103402d500140d08038034200c0006050035120302c3c1c1c07540b030350740101d104080140c5000c01b0404003c42c100100c0c0080c10050396a40d40038108000e41d00708900400748503e20a2001140e482c840d0341c421420380740d1400008009200341117250910f4601003080280c3c0c006140184070391210a02c0c06405a201c804901410840320902c264071800020700e000540c400300c2c140029040200380b019440d01c40c0456481001a5503140021900955400e000b41d0155140705414003040150a2440308484101d0014002c800815903c02c00081d00030041c5e07401522a03808041184414907074000003a1400341d109840d1004510b42203402510980811560031450041c100050002001c07640c0202e801540000c101040d40000e660000b11030200c0c101c0c14421a000000d03185070f4007441c403550034914008035035007401410350307003c0d00070480d410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 616747868 1250 616746618 616746653
    0x111803030c060f1312170906270a06020a12050907030f060c031409030d06240f12021206040b0f0105160c0f0602010203010e0c040806010e0c073507 65
    0x20b00100003810401c00700b18003032074185d0169a0310383d13503001100040d019440c40102c0850303000f94400060351158000807007500a48004500707070100c10742c441d00311200100c8408400e446020721180e00d000a0b0300741c0041c21401380661141c0c5042d00d1800d801400700c2d04010454551070740020010000f0030704c00900d400180d42c1158002c106800f42d0401075015102c100010450200030b042044007054010000c3c0c01d0310034510000744080e580da0791903136a030400f80e100412a400c0301140130381021401050340816005460400c0d9084905010401089070040076036401088640010010a0b25281c82800102075088503600c1c84e41181c54002029070003a94038010a00142c4204482400b8071000000024212080141010398403100c00034041c0d0002c6c0300b65900240c0210208841c400804192404c0e00c0ca03240090409a2a061451800b040040d144072400d88082218001140c0c9440c81500446110007034100c0240c880d510800340328108005500324403000317009910006000001c089040038 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 616749118 1250 616747868 616747891
    0x914010b0901031e0203070b0a03230a0c1701031101080f070e061303140c1002071203120905100509060a151a190e010207050406031208070909111803030c06 69
    0x4c02c1a081041540b911200195040c45400d600080304804040244424601c030342d8244180000980c803070024010600d80048030705410000210074a090b0341c0404a00d00c05454440001d03504543c0050f0342110a030019250681c00301404162540c11003070943d00300700001602c400b2f43c5425040140303a1615007480520a800c00a13500c000381c40342d18210005950408840031808600e07800c00c80e0382d0204100498011203818954148190000c198681190b4184c101c00006010645e000c50b0119040150300d0300d8241d0b5040e60790045001003101d04915503590a00054a00704020034034a0f01900a22010306541002951081140030301003000c102e4107044049503180c0140000c0701e595000c0c65006142c08400d403640c9441c801c2c0e001d510710108100a030242c0300b01d55116014881540c2c901e00001e8040d42102c100002d096214441e61f942c031203014074116215a4032170340503000b5102c58096410740360350082903001c1005411a10600d0381e11045008620781641e542c03506d07171581c50051504020b071 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 616750368 1250 616749118 616749143
    0x61b0a03240611060c040305100b0a03080a080411040c050904020331030e04090c030323040b09030610060c120302040801020d050a0c030b1c05100606030914010b090103 74
    0x2111000d810000c01501070020a505a100d8200500c080d808034100440d900ca2207010500351502d400480e415207411401a100132064030040001500c40410301a0300140003a500001060a41c0050300d0042116910810981041d003001002d544c048480284a07a250500c144d00c40f5810004642800c04165800b42e00c90b0b94030a240342281c641e8001c1007441d074000e5403c582000a04150782d240c014400c0d1621010103281c00280302c02c0b5411510010a058079a6100380701190298030400c1410024101c00c1c06452641803607001c060300144c2c80b4a600303020205151036145018044d042d400440754070104049460000d0050102e04080c1c80900500610240203048038070980484014102c0e02e4001d40d954005884c2c628000c00c01140c111400c61b1409500c1345a451280c094078103440c500800c050b00c01c80708960040281d242d680403c03200c61144e01208030500c0d0480c00303108014181914006601411800c0c0070070310f1440096214001c0e4034001300000d01d03984503403a60b41580d03088944041d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 616751618 1250 616750368 616750391
    0x70503060411043c0b0301020a020a0b070807050301030609140d0f09170d14220906290a0e040e0d021504051209010311120402040e0c010c020f0613030c08061b0a03 72
    0x1000303045c41e00b42c0c03d0350002840000c4980c00080e0020014402d40350440c4c0d9a441040884081c0070684001c4006a0b04100400c041001078001121690103010460709800401103e5413905402e0185a008035516010040e10b103034204017080010800d0305545c01c5828a5403104503280c035500ca000a00340411102013100210891081d00c0c80d506045814801c8401c081c0c1041c80608254401d4032542c82c22302001243c041c05070550001542031202c0071301c3c40203541040b00d440c01e8000000010410464601c0050b1300d50f80c3d802810060704c0c41001401c42600c991000034100998000c00c8084040b0b03010501000400008030700d840d1416240480751142d621400480c00307802c00000c086039084001c28070b4034010340302e80312085c001c074401c90f02001912111051580c55020903440940441c0c444c046040140c1040d8218820550008210385e1803c613481e9000290f01290ba00103540001e024881800329030f00421413643c00085541c442422815007244040143c0b0680c2240400c00da21102001c05 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 616752868 1250 616751618 616751621
    0x60302151b060a090c051203070f11060f1b0d0912170301171b0117040f02090423031216030905010c02010e10020301080304050111070503060411043c 66
    0x707001d05507905803407003410003a500c480942820103060328084020b00c03000840b807500001d107005a940b808040e5081c142d42d6140d8003490b07940e40c0d60a803072101e1013800001e041d07600e8100400c0001c891149480d1104408548071203950740e1034003c0e000c180e022604841070782c1d03009620030007292091300280d10020201d1030020000d140c1d0f0100c2c110060008000440c00142c1542710f010101400d00480c1c140b52250760750121441d01072001140419400c4084800d002000d00405622500944003c6c0d11004e6640c04600d540d41c0c1200e068074415050155955142441041c0052082904005600f0405807028402102d8406018400004d62120208081a00903007003000c40c95013082c003c02c26401202c402034040c0c0540303540101c550040c0030300c10f040c0388078030710a590598004400070750401303007041c0040d29903000c000200e2031a0700c03c5403070004a940e03003003050b50301c00d078462101860310311961001c2c0300a82da9a8640e050076400402c0072003c181c0c0018030441300c402c06512000454007482042c040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 616754118 1250 616752868 616752907
    0x30406060504140603010e341502010b090a02070213020702031624021b040203092b110607140a050909040b01080706230f09040f0b03070906030215 65
    0x5401c503041155060f91242d11049003031040509500034848011440205510780c14030b1581c1c040242e011606040310b5030242501180014150f8165980c00c907141c501c0500062070010b04140180c1d19a14045268105554203a40000d1010400c0d800c2c403c0c07a5002455030010b4003499001140d011510f40d05550703040210341200355889101e611b426445901d8075440d11750141500e1412848101416581440024038125808000c1c003022020b40d002c00420010303500141404200307100d200d0318010794210600f01c002d45d6641800017010304007141203015007000d6691200c858650001d104102010341c114411300c2012920300c60040d680c900041c070940c2c0c43d00503098040c0e0001d004800b00000c200107000a141640c04007411640040d94401c0203d444a1041d549284841840a0382024042080016080340d40e4020103c90400c0c811001081c203e444102089042584071198810242401d1240c03201a000300ca13403d200e900c1c2590040b41c0f200703441e14090300011000061a0405e22050b41d03c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 616755368 1250 616754118 616754129
    0x4110103090611030421020307081b2e0507030606020a0b0a110406031a030303070f050d090b070503180102040f0501111c02340605031509010f090b1503040803040606 73
    0xa44c4c40b400d25042801180c5128000341030403601681c41c0020240c000400d84407880d5000443c6071500341860200312400b0104941070b24144107051001c0c8807640d641c10034206220091069584245203500c003041176800c0500b21405051506000b80502c640c04100302c0b003101d801c0f030032010b013540310503000c04c00811030b200036088640740208010400c2a4140c000c2c1c0480d201c00b20400300d50800b9103003010307201d1005a03840400700b030411012100e45802100608510440507100090f40c1046480304c100701030084480c2c20000b00c00004100c18913240300041c808003070703000c00210300b45070621180352080d0110740034180c10b10001f00466945201d040241c555409440304006071000e0b42050b02941d0b480e5030700c9400e4a2400c03030265402c448940c0c0c01c101c0b80c0a208000c0c100b02c1c606d00d0b103030081c1c1d02030b40007900001d9020002140a60a92500f0015600802c10801f41e150f800345481034100407034840c061700c81d01c5802e81c21a4244105403a0068907000b50300a01e016a40c2d071205d241c00401080c8581c0704 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 616756618 1250 616755368 616755401
    0x30605060d081b122104110a091b090e220501090302160905040201140a03090501110418050610112a090f04150b0f060f07030314041101030906 63
    0x41c155248050301d124510654804215428a0319264554070305002d00480300045c0075520b2409800643d07200003d03034010340990202e01800b0440400b007808405c0d25080716480c1d82d1103030700c0882420014248450a809c4520305243c41d1802d101701180090b4011b08214226180096610786546440400d0b6248a92100007000154490b1070041e4592003902e012080024019000080010031405030790701ca594142d48a82134500019020740c03580c0c0040b0f0801d0105550b91042e080060001d10940800408007845075458a10385007600c7d00ca01c11242540d020741e4102001c1c0f00c0384d62510428807040c1031840c18402c0004031040400744c41e003005440c04044942c600180510150a04003010003820000c0d00c00d5551551384030494980483c05030bc004240440c401480c0d10014403980c4030341480480200000c104c0300345e010004505800850503003402c0c6000084c00000c0542510403010003402c4141c6005a501d069101d10854036403c01ca254181900c0f2003002c02003001c0d80d07020522140b0680c20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 616757868 1250 616756618 616756627
    0xf030f0607030b060711010804140a030c050d032a0c0c0b041409090607030905100222170706030c021c050702131e2a0c060c0503040c030605060d08 65
    0x40540e40d900039150400442d1030003180c0d201030b00300801203403103040e00f013018041000c0324040111101ca00040050b03802c03000781d0840740c030114428001030076418081d5680c0b154001190501c1c6081221100480b41030520b03140c2032126100a0504003541c211360340e5021f41c1c6840b03184005682e11144001e00a148000e4180082181040c00000d00107032140c0c901401e5400c80000300f441008801601d007002e8940c85103000a0449220360041c1010a00c0f850a0304c3c0111241c820300c0f0281e802c111010920510001050342540c0000c1c0c10f00d500a10b60410010b40d84000c801c0b070652110341c2400703120100360300d66510820050081081617480d1081c003900c50710307080056000400c940c02c0310604030303c6030704110034401c4417030694004c020349411045880c41d086003500c61030760000c00003032a0400404440a008081c0d0300c25903070203660082000d4603200030b25440e84c9002d0307048074200d04c122024071600340140404a800ea03400c1e942540c0d4081d000080d1a100d801c0000c0003c0c5e89120001e0400b81d000030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 616759118 1250 616757868 616757893
    0x30d140f0c0d08091f050a1409030403030305090a080306010513330e0a0b0901031b030e0d020102030412030903020a15020a020c0a05030a0204020a090b030a02041d13110f03 76
    0x75142d1500b64a40c0d078030115130701d902d208a6141c50082d9040348008412000c1e42d2090701c05a03000b10780020a400d0300003100b0307140030718412041c10211141a9181c1000c101003091603018055250700ca4204406000e02c03910a40d24105036000140c00681044404501c02c00070b0098640200040d00002c4855003006074070107401050034000c03044008032105210240600180600800e001d1540024601c0b200305090100a01d60fa8000c1201ea43c10582c444980f515808826012955189101d40c0d0114030720a01e51156403a001100d88a4021a88104100400f20314420b120b000050b03010700d0040b84000b06420f0482c81c008048002400d44034144032505a50240c5900500307100301300780c09581130808203070100705c84000035120325905500300080320300040ca004e600404204459041c0091200e4581c422840c0301d8100301c0340504143d90001d0140608034060300c9040564460001c400401c3ca404074210090403501c9500529540b580c007103062195542c481908c10350100034044619820400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 616760368 1250 616759118 616759123
    0x11130509010f0b010507030f081e150312070c050f0a0302100806011b0b01090510080708070603110a0e100e03030a020c0a0503120f0c0703150b0a14030d140f0c 70
    0x1030302c0380745a20b4091055000d50081050b91103940c1c06843e400c400d07141c0b210701511406401040d400e80000302070240c00458900700754a901031040c3d801075818500940d820306241031150090308100b036005000c41c500003062580c000082c0c60003a6030082c032141903100880c1006003141c000940c00321405030090801c40e03012f100d161107403900340ea501e001d4103600349440603194416180903001c0c401d003400504c01d42942d5081290401d1400303446114090b030750200b440c107100b01c9802070165a0030040007048019814040e07091613480031102e0500e4040ea0362070283c181244003114030300803403a03039001c203088038000c100407120b452015066903942c00e03400500035180e00103003034594400d403483c9502090034100002d4000740f2000010105180101c4040405070035000506ca10315144030b0000c0210000b4480342c0c18031080141c50601050300420b100c02c101c06181c141e084001c082c482103403c11000e1f5000510305400401e10f0410700d0710892480c407240c026100d01d00c802081b613407000542c02d042d00c900 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 616761618 1250 616760368 616760381
    0xc05030d2310050a0902091c0b100806010f03060902030a0c1214030705030307050322080304050105090604030f0c02030c04062405120a0c050d24080a02030303041113050901 76
    0x200a20400590341d1880d040410b08a0780290358100c02e00761010b01c03851402d68010204440c0081c05003070000c2080000140c031094226045442e0389050b0103000007030103400b0389400505020805030079a503041140c150302251183c8406008242ca4040c56429520240803540c1c04907003090010214a032100c0e51490f80d845050000c803880511040220b4004030048251100d02d980034002e03501d1074503420401c40c0d050300050010484070104030000302c0708107038041c14510154460000146c9910306801e013503085420041c03000166400070402c0100085e030100030418072030040c2c10281001c102c035001180c42e150702d5140712600185408008902c1420b40002c42c0480f1004020031442d03030241c40e2040350f0502501e003100200311400800304150241c1c80d040011450b229181460034030075001c44201c19102685205002e131300d840480102e02c01d24070b182c250007034401c082c000d100b480d00355030109640f0710005001904040100502e007c85944103a424000064032030428080c0d07040042c1e4643c002d010307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 616762868 1250 616761618 616761671
    0x18080a3e010516050903151e01060f1e020f01051003060e210904090204090f061116060f020405120709200d09141e1002190c05030d 58
    0x61228061030a1050007854401c60100c2640700d50240109003d5809800074070034143e05002d62009451001c0181c105144070f4600281c43c4180b0f00c1c05e801802c441c005040c0c20032000c1005145240c502607812060350400034140009903070542c0340c014400c90603c0050082c1200c194284403e00800210701740410041d00d0166600b0402031900c4041c0680c0c0b080390080c031b0076110141000100b60500004080c12015601500116a40e00c040d40058110f4060355821900c0d50441c180180603c900b0384280d08901a000040c44e103070034a200b500303407804054808000c00550716150038a0b2456210340550700100740281c080c02d180c180c0703101004d03203c1440b4005d05ca0300b1481c1480110181080c64005003814020000032442c0041b20000340010700b50a810968014603c01d80b681100c070300401071031041c5c41440c984c002c04c1d1140c807508141404601010300f00d0350350043c000a2402002c121040707401a80781c0c28415809600307803419030700750b0180c406034202c05454800f120234960110940c80100e0070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 616764118 1250 616762868 616762967
    0x50117090316050a051507080103030e18010b0c100203070e0603090a051e16050607030806030a0b0a0902150306030705091302060f04090b15030118060b04080c030f0118080a 76
    0x41b5030250415040400b246c103580001c901c030004001281c0141d42c103c541020140c6040214285411038805030380302a0b00020704070300e000812098400c8213001100d81c1407520030f0b0540c5182404180249030002121090b8071407000000460102e0030100000c213860b60f405029110007001172454106034806c4040716400f24002c007010169000c0c0081240e60544500038406400c00265840489448800030072154040c800c601100b0046190b100505225082a00780030a81c10a64418001da5036090507801c5041071046c8140003140d41d001c5500016035400b80c40c489519070f54500000340f44180820301a40240f80014146010f8a814000708161450a80d09010b900041014441da841c0074a25505480d88180014441440e00da800c12803080d200040100d011a15034500103540c3c3d00c0b83e4002d8149074030022010016003002e000c4000003244130b50003046905178100c2c1a607401a00803d00038404140007401001c040d028003520499212041c0d0300080064401980c3c00e849403013040a882c04030f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 616765368 1250 616764118 616764133
    0x6150809010e071a0915090a0b03010e181c02030403031e0c12020102091c0209070c080702010503040218040f05100c0203090402071722050604050117090316050a05 72
    0x1240c14000c2c15a044070a0000b001410724002440341c200340f420300b210409010401c9050b0050791741291206055032440d64841e516501c1808121a20300107501c00c4110032030a000402a2070000c281c101d511030b09126160380e03004101100a402c0c01000d40d400d40355080d0b007400b41910b259002018100340ca12070749650382189860703043c010488285444800003d02c0c00d00750540000e1190442d00100f40183c0005410107024400017180101c2042010000307142c011038280c150715224660a4010b8900d041c0306000c01881e81304d1091038070030410301038140000000810119158010301315030f030f00c2c1e01032418081030030075141c1201e038243c4107a010380f41d41c4505500f01000c80860302c1004910b515580045103804c0c00c4e203084c40301942003a402503542480c04a030030450a810080180410728100709000702c03828aa503030f090001040c60708420300480d0140414407880e60003a075860010081c5003081ca085560722401245188035482105800c84025121039041180c00aa6003000700d1244c2d094400c3c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 616766618 1250 616765368 616765381
    0x19020906121b01031d21030402151c1d010c02030f09010e0f04021306091409040b060a1503020d11160f1a070e01030b031b0411090301061508 62
    0x30300140528800560300410010100b09020340d14090201906040200b21407401107000315003458902e414040030740103040f100c003407100c40304000340712507001d80c07011130030350809801107400d01600e584d400c107400e2800103080781c504a2884003446103201141d018002c403c00842521072541c0540e02c0c0741290741c20044040b401d01d0010060340c819040e141e90603414140504011104030f9100084203800402103c14400316445034001403c03082d5800200d140401d281c148000e00c41c1003d9801760308001c1c1c80c101d1004066840413852500983c0042c2e81a9a0340c9513000002c85200ca16840000252908a081c00c5000e030942c018000300c0090000c00c2040306d0146005070031522800381e00c0c2c6944c50000b0b000c9000106251200d200c640d00500408001d007802c0001160a1402910b500d008510646820b072220341c2d141c00360102703c11080d0050641c444c404890420a01d0f101d240c0203201d15100d0946d150b0324810b8100340c90101c035000f8000d0211039903c0305005a2a2034001d03000e40002d140400007900b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 616767868 1250 616766618 616766629
    0x40f05011107050f191a09030d1b03030c051306270b0306060a0c0c08011d01140105012003040e04060b1816171f3c0819020906 56
    0x1214409002420000c030320004002d1210760030603510900718101400818080c030030306c014100300e0040f020b42da69524004010580b50003040a510806c0021145003030b80e282000300c0320032811ba070303050402050710404a501582c260003014082a01c0b044aa4000903c855000841c400060f04c080000d2103140d85102c00b0803c1c44040d4006c0b503024a404001084260521000610000e0060328056010740303c1951095511115a480803c5503910f0740d03484c43d501044089040e00d00e11230b00f00208140c0006000700d840f08001481a01e0600c242a024480c3c4151001e152113032101000003900d94a540391660845500310a4505032404c924109400440f030822025540e050101c068010005949403080c2e4906541031120800420481a5030300c189403030a40b081070300450445a0410314014400303d10030f05101e1961281c1120408556002c0c0034182c00c0b001c2000d0280d00d1428104d044480c0000412203816540c80201c0c02d10030940c11501c00900000c0b8413203010302c226681c07029038488100300700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 616769118 1250 616767868 616767883
    0xa0506030703091401091e050a0b0f0f161209080c0a03080f0105010f080112030302070c080a0312020316080a150f06142a070e090d11010504260f040f050111 69
    0x4000101f20703103c00070708102e0800c03600482440ba10840ea002c3c0d0f00756032aa07000c0d0300251007003c544080201404012141d5001c507035804808081c0b10705101d00c01810040040c0e1601ea003080c00d81d5034035000c00c02409010000c40e0f003011890340886200c0c0300c1902c2d0003407d8805c00c40d104200c0c0d180c1400041020f40c494130502c0c009200581e944c50f0f6607420900c40405070078500134210309150303081100000198500641a0082c0582c001a0a0100c0d242c280a450949880d06908045204200700010002000321207820f490292802c0b004596400100100500481e0100d0f42d07040201900000d605004034820416601d16030303034080c50314401c2c070280c0c1001c0c0100e00099243c00c685400d09020b080480380d4603c40c2a05000484094954a0702c1101c54645c06480e00b0400790400e01c1d10350b0180e03402c149004100440400204114500340e1102d80d942c1200d00880125444480e980301c3c83c07409024180c80a40d981c07950320b03d664603500e05030f603844448075100d00343c04107080b5402041d4104000c600c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 616770368 1250 616769118 616769123
    0x10e0f0102060117070f12030216081209010210060e0103121e030c0e12060703060f05060a1407050609060a0507031802060c010e0a06062612090a050603070309140109 73
    0x50403181d01344108110145114074002d00944100480003801010082420001b40507021070580c5603002410001d04040d0806500080202c403210300b00f240540c00140100c2e08013141d5551601c8882100040f806c2001140c2110100d6040050200e844075039001464100c1e0302c101114038000300c1110041c1d510f8210010503980c49c4e19130030f407200500341c020381105003111041e00c0e1910884500c4030004010055407501400d803076104004102980f60548100b0340a0003110140c920840d2a1000141551203080208020000d000e141135820007890420b43d0310056200050300d00910701550300c15503c06e000c0b6103001302d1a0520012403100e038001e2240c2040c10b0108030303000c0da100c150742d02800117a50000f07110800e95035803900001c401c442c0900100480b0b5204880125039039140c08203882c15110190b40907150310b00402c131003011191001580002c0800d860b02029165191400000d06000c09640010b0f08808000b0811410341e9160744003e180c0d41c030514501035070343c131a00c014174226803948800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 616771618 1250 616770368 616770373
    0x11e020307020103090213050f010905070518190e09010c021e0a0215040f0e060f01080708070810030c0801020a030c031a01050304060b0301020c0a0501050c0901120b010e1905010e0f0102 82
    0x510740994440d03002460f090740060108250211100c0c030010884404807035407000460038000511100181c0c2c0600c035040b41c21490920309208403449800c0003260301000b00f0340300345481d01910408a400c0c1030040000c0007075107500400d914200c100310313018110b0310344010014050346060301d80078201c030340e40b0310100c5c204000182072018007a4280240802410541401200c09100c00500b0390080d50038180548086000785100d81001410f00c00c42d83c419420380c0341032008041c200144658000441944140755203080900703600c505045800060090300f010b48408040340c1c000ca5482d00c15001021100980e98040288841140e4200c00301c6145c0c908120f080e8404216078400307584104043c42d085809411b0000d42e006407600020300b242d0000704a0f80030391300401401c0341807150a1092541c0540740305c1c0103510b0981d41c1c0300001c0081400320030703076200b86544520b00c0400340d120703d101c007040d514003a003c100f01c6054162644068550b0788502400145809035600b1141000078a048107148113800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 616772868 1250 616771618 616771627
    0xa1803030c030b03060a0b0f2715031b1e0f10020f01090f0524070f0e03010914070906051309031e05120105030102070f020418150b011e0203 62
    0x1000c401a0000401c0003080545a0010701a29501030004a009010440c0b000480405000c01e02c640350b03860750a0503110748a46020b215140102c440c1d0b000a50120241421940d0369400380ca00b25400541c0e07525401d4030904401901e100007a0b20203400c080c4c01111880b540d40c0134110005111a56410b40680010ba640c415001b00d042c00840d59400c403210b801540c2070030156100103404c607002c140040d120584029840c1007800710070b0154070b00305500c1514107038a1030301001045402503c0030b000c41041102a02d01500305510900700d00c0352501c0024004d000d084241d041c4007079170803034100d041c084034000c1940003d601411403050404541010380103221640400d0342000007403004d000c068061140070589404a10900b00345000c182c9210345405c2d03114607180c021228510f40581105000741c0c410404400440c28840700004225412a404604902c040d0100c030309200c0d80c814010121071030400f040c40040340c1c58010180c0d051080e0380302d01e0303488a0043c003807005000440700e83d005a0000c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 616774118 1250 616772868 616772873
    0x2010905040c1103030a05010317120f0a06080f0d091202030a080c010e06010b2113061a1009150504061b02030a08070b060a0f1805060310020c03120a18 67
    0x30880c091010403802d240f08030940b192551419039000301c2d0f130310380078940c0c40c4018010030074441c110b0071248205840c094180140000300440500000c0d10b00c81c0e01d07051900000784c14081ca42c00007000b130030000064030034451000c40d4140d52510a0a01c800209030484004103459058207100c001c9560002e00401c043c6000b900c0d402d007140d10260b40d40c203555407100b180e079041c85c40c1004010300810042d08025070303e00c080e242c800340c240391644054031422a5801480340c14942d40b540c4141c469009030000070303a100c8114001d0305180082c040c09400040c140d014003805a003001001c812078880902c1c250780540c4010701291240711358040d540104034040982001821034100340c0f80c6582c805400c0300c9401c14030b03071111030f00e0340c0140408440100302c520400295042600c20880100181180208150f06144800080480008071820b40c0d603606d07400507246980070080c01420481c142d90440d540d00d810300340152a0340c0180018040755100c180458007086041c03045000c01040814141d405110303c0c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 616775368 1250 616774118 616774121
    0x207050405090c0a030b0a0f050c1b2107140708120c070b03101401030e0303061903020d0b013303050705070c091b050c060601080709080d18120201090504 68
    0x40c210015a02c918041c0c03185a0f01d4640c414030217180920702c290404c0c60258100d81c1a02c003803003c04c94106051400f4402c000b100308080e40e8909207400c10b44000c01241000003450b00200d01c0035402031180700d658411904d01000014030b41503000d00180d9080e2140b20020360b9071400c6600c1074240c1540400412462200f40c2d0015055145500c01901e44c3c003a5107550303c0700036070016580301c4201d8810200c2004640780f24850210744003030a08080c000724640200740e0b601c900005140f18007805115000c48948440703400e143c4080c5a00820b45d020024880c24540c503150001d01070f40d880c0a1100159000b400c9000145200b60b00c04881000c0c004481d400045000d001c0180c501070500030184070b010000340d0088440c101504841600040700c0202c00000e603130510341e4080c1841804401c00440c800200c001c1000c40d40418282886001c58440380f81c215034036a0154080240350150002c51603203a0b90103004101d282091a000c0e82820751100c02610480f038074454001c0c08030b129000c0800842c00d05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 616776618 1250 616775368 616775371
    0x61507030c050313090e010c0804060f150e04060506330423010201051b0910020f1006050a0e010608041502190504030b0c070c0e09190b061305070207050405 69
    0x41d01d4540c100841039614140786030898403aa0310084110038080c007404104d441120440c40340b1000070300c034004a0303000240039444041e101400c1039446040e60002240c46800c00a030384030b002142568003a581c1d01030719011180945080b81c005041c070003c81c0d604e18009a501700c002d681c407a10b001d080403400c50128105915440307403145000f818400014191402a802c4840d108000e0a000c00c05810340f000a007110801841c03420f10755511a20801c08200d035800b03459941200340d070620f103401c41800060f8030b01351500b8026406440303001d00b03140301030740c00e03402c008201c0c0c5058503d1054103071074401d510a20f203c24000c44d00040e20400c00100440e03c000604826808140d02c014981031150504802c10010008154041600000e0030000c10201040d2194420704101141d4148501688c5100b2048183e10541c03009046117808603111250500c04400c0b0139511804a034650700303ea16040b00f04040440b80c1034072071030900c800f000c0d05460b40d0046070700c0350000e40c0c0501200381c04c100410004120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 616777868 1250 616776618 616776623
    0x307021c031808090a0b040b0d0b041b0c05010c0c030e0904061b11100e12030702120d0b0111010504031e02070e010b0c0f0d020601060c140a0803090f010203061507 72
    0x4940040446030001c0400403110580900c0f51550785050b070406002c0704801036032041c902d140f010003040007901580f5041d20030025040e0404140e0040640005e00130342901e0a4803d20100e0301c00c0e0496240d50000c01840d80980301754004e20030120f000c003041e80d215501e468081c001c030b110102c8003030703103442c0071101651701900c01c0000141e400e5450000c2d141d4152110040004649a0444801141c4d81000301d03803144c4e21100e409004001030360a0451704c45103c01d41ca114050320201c04036409600a000803202142211031550700c540c90f0940da04040c085c6880308034003040012106070040300044c040e003841150035407207030f101111040d006c90118003885240032086001c1e1440c082050380f41c1c1080680200003c0c000e054840d15031042d0203040c9501590607920700d611100c00c18500c00d40200e0401d04451903030918040320b284c0750500c1100b0301d4207142030455500030703030240c04104511038001e903005440703003402c461035500c03155451404c030f1000703541c042da0102c10141d0b0040300d41c410600501c0002d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 616779118 1250 616777868 616777871
    0x40e0c0306060d060b030603010608120d051e0c1c0c14092202090f01110733030905061b0405090c090901080a210f080411180a0e01020307021c03 64
    0xf4a8102e80d0012540140c001d10118800042440402c0c502402290040e1101030013030646c01c5111701c4940200e00c6540c4100d501c103519000054a001c0e85c40e07820702d02c01032250301031001c18507152404094681c00512018070f1011480c40d50400ea01c0213100700c801001c119140e1300049409c03000700410a0300840059130b44120880d404800010360f030075107071040300a40c2d078026071522030810800900c0d4a54001cae40d410441d4a1041d604414000141e0100f190321041800c40200e00c2c08091074006d01c0b07081c0c0807000c100300040840f1070680d41507014200e428040e03c251101911080c108184414215100d000d80000c203100c140520700c0c0a84180307070400c114240c010f02d05840780b8003040c0182d400768040e000b43d4001000e41c10a0091014648490402e0300c61705403011805240040c28041c0d01c1c130b500c0e40c10004641d00240c00c010f4050b10b03c000c510f00c02840c18080749195000310700d149800302e1303070765900318204481900445814001d580c0110219000f0709074807014410082c003041c00c9840c02d0000c16 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 616780368 1250 616779118 616779127
    0x120227030709110408010501050303090603070c020301060e1e0906240f0a080f0706020d05030406150509011412120703140f1603030e16120f0c08070501090b040e0c030606 75
    0x850b41c0c4114900700302c02a001c01d440310320b010900d5003180d1059000707501035007040082c03a8290741c8100490b80d0140490800c414800ca41d0f0000c00e0041c0100c6c0c010105100480040c001c44488040e54800e0207140030020070407941d51500c01d180c554034182c42005050394900075250f80420414080d40c0301030401781201c070a070000400001c0d900701d0942d0141000342c100a034001000903041c03014402404460004207094101088000c00900c03005001030151540c400840104c810702c4401c1034001c16000780081d200e5611605503440c0c030030541050074844c0407018070a02c2240e01c04134210103003541040c20300e41040300540742929120000e0743ca040103034800300300d04115130f0700d620301506089910b5904035100c0815071030003504031119050020f07419805085030940380107400012100b942c01a5005030b41c1244c60f8508401046a007071801080b41d108848041802c00b03001501030200c075400d90718034054540d03030328146010b0702c10350040c84004100742001840701d0440ca0019500a2000343c10140781 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 616781618 1250 616780368 616780379
    0x9010c1b03111002060402150903010e01090b06281a1c02090a05181803070c080c09010e01081b0111060f040b0c0f041802090306010b0a1202270307 65
    0x28400560811214161081d42ca0301c80c5061603c0c904024000c180020003141c01c00b07400081c100caa44125200d540d140004c0c45043d540c6007074000c600c401200f00001e002c10300d0545001c1080501c21103c680c02100201c0c0c03d650142001241e60386041d49540c4400051400e001d41c4503c41170000e8041e8881d96402c018900b12450f0401d008008407890038401070702d42943c10f00700452429641d100307600c1a85030307400b00c212860b10710b490240c10074144103199040440300c0c183c49085016011000d49200014000001c501801060320745008404803149401c40c1c1e00e0300814950032500707024140442c1d004100c0c100d100c42924150038041c80741410305a1005030b84984a42c0740c40e078100c1e0f511201c00207a2061008018002040c40d0300022074024990814000d82a030341650f00444c4038400e051a4440c0b124407620b02c8990403201c0060000c4c00f62910780d82c403454160388660003100c07440001141c03810a4002c65040d4801d03522070055042140003040280554101101c4043c8800c9500d40503c0f200001ca = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 616782868 1250 616781618 616781663
    0x4140103030203040e0c191110090f0606091104030627050f0f0c030c1c060905030a08070903021e190602011d010608030f0d0902090a050402040c030605010509010c 72
    0x840c8079500943c1e4407428200458103152000c6d000e103421001c1401000000c04165000b00c0c18140586001980c0c558410340641c60605424214100c00c0d181508160a010ba80703145203110074080c000c1440310030394841419084a038074411703170000309e60144000d20004d44190010032240c40c1d0b880314040c000c603103480c0303440d00f80045002c102c60b59030040c201e0b100c1d400c1c401d0018203205034250021781440d505450200e80c0391035000c2241031003022f0701d40c0062081d04904001041540c0c00c0102000800d505c0d140c925565030003400d601010808a000080e14184a1035004080e41c0d40076019a031002603514046540000d2a680154419100300e4140c5c14440c05502c210001c0200342d0000c119801d11038030107654842c10240300c00881c3d04002c401d0110320800000c650500701b84000e125610820f507101940240464040254000c1c112420b218079005640c02040c0128001c40c1c0802c20500c20f80000d40032103480340704c1c09001c03030070a02c52156558010300d2020200b40c040d5413420804249600e0002c0f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 616784118 1250 616782868 616782871
    0x904090c32300f15092e1e020a020604031205040503040e06030c03101d06010f120302030f040602011a03010506030703021e0904140105070908101d010212090c030a200414 75
    0xca10319000010000070000800211b00d442d181441055107145400e01507102c03840010300341503801929000b4404181c0015242000310b00074100e0115141e15076644000d4807500182ca0907400143d00120032104e00c941032043d54061503001c4001c501d080c3c50247c58240d100300080071558035010f81d0b000800143c5050007a50540f95804a0004000441c18003a550841e000c1280350501d922101c018840301c0b00103a01078007951030540200d03070600f51501d412071031403290703102ca418960740100303002500b07a405422481d007060700d10a0142d031211410043c07508960080b50000d40c9a0701549040015040c0a1003012520b414481d4511318140703403902062002c07105a030b007180d84881c1c0c0181c030182c60400384101354002c0a40d1900b1030700c1500d4032042c15611404000403140f8039540d040303240801c50030070060b000240c2c0040b00940d1a403c0150715544010000c0b00e105900c0d02502034040c400745400306420101035070050110700d101c08400c8070642c2c3d1700c440b00e80060300940c3e6020f100350b09044945166 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 616785368 1250 616784118 616784143
    0x10e0d05060604180201080f060a2705071e4a04020a0815042013080c010f12090b18010e010b060904090c32300f 50
    0x910103414142c0900c421286111000000d6400d803591160050780e1140d40250005000c3c1c000d10155121500020f40e5080264800411856403804810100d54048030f04660f0200d41c030004c22850344ca417a41034607401708606d11031420a140502103c5514040e510100c8040b10b0b1640810350419420055000240c030743d0101091700444101c55400d44414290460010300c094606600303003080c003000640f41d5100030300021003901c90500b04c44a1902d41d039001448405415502900040305100d2940c0f9035800b00c0041a4040729982d804900d009000036040b0702100706039144208142e84010403a10004005a20703412582c4498010001c00c8646480c1c6014008600016007442c00d05041e5508465a00754100e05036410300900d11b04581e24078055910007001594089011542860810b088000300d40224004000388011007100040d00c1204403140a1150207408641c200e000804c480242125024045401c220003003040c0240041e41003125040e251046500c0b0001500e03019046c210ba0b04441e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 616786618 1250 616785368 616785373
    0x2210a09181424010f0201020706050a090209130b06010c050a020d0614010807030f0204020f0903060108060106032f1c020a0309020f0f0904032f071409101202010e0d05 74
    0x59035000200240c00c59000a44000201c60741c100c0440310400580002070b405040c4001d00703041c1d05c0018000c1d01204c20b040e610001c200814980a04c100d40240780600c0182c0c0950000f400244e2482c0307003114a803105503000070814100781d40c4c16004403a0920100c40880d41030050003036400058a8172041015001d105510125804c528426000c20700481680000a1940140f0040000c80d4824114118054040d10003680c2e801c0c030014000420700c28060703a603030144918000003481190114099060b110540d409214403040007100f810f00d4200c0c5030740c52000421440c5502c0c41407241100624807940301003030090080d40004c4807034040360000000301000c1382d25603c4e00c1c4110b00d00b54500c9a13004400322807162001d40794602240418400420003003d01070701c02818040300e41d01c500491511003961858600c00a41045816281c0318644100070743d0a100040c541c0091a14101440c07052140c00d91040800b460054144403c41d0040c0c010303810301000c4040000940c85038464042000d014800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 616787868 1250 616786618 616786631
    0x10c1406061507030c0204020d0b060309100b0301020403320f0714040e0a1502041a0c06060f090c03070302091c150c050f1804021306080702210a0918 66
    0x6002c5600d03a404a0119030b01c02c10409000060341214240001c2a0103440061b1280c45000454000b80100c2c0d0700d65174003a10103c20018a90382c0040e040102500548080c400e4044400c01d05090b4051400010b2501c1d5074007010100440101c80001c50150080e498a802135246521040c203000e03400411300c281e40c03ca00800d0008847d43c08028055035000d0f0b50400603030807482c0404da1260141ca000514003000e0034a041002e420b0f9030180e80240100d03200c2e1b00c1d0703620403241134000daaa0ac8032001c42442d0041c00f0010381c0d03c2c40d1503582400310042c00383c0f9044c83d60b03850441c4c11030258001882a014550b0911a21000384c403400f40da01d03082490001042441d03060350a00c1c1102084925041c442981003440825425078408199250f00410328851601d80e02c4c2c5450030020a0308035080d40350401d1010511421318130900c0200b40c00c1760308580300d03420303940c580c500e040381c0700c001c42c84a4609554601000b88005040c1c00001d01c4000e5183c50b0035013400d40c60b4080404441d8100c20407065480d00c950 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 616789118 1250 616787868 616787881
    0xf0103060f181401120b07090f0909030c060501090603020405100302060403140f120903011b05090d02011202032502071a03040311100c0f020a020a05013f050a051311010c1406 77
    0x119078607003200c00d509020080c01d127020105281075143c0d01419540540300c20040d41058041c11036040310b558400c10a0002e582c444070741000a294512040e842242882c000c15196400401884e00b038980140446207040c1c1141c440311628504070414440903c0b40001c801200c5805010103540090309902543d91403881000705800c1d2420256980d21210090810120b61034110707046401d0028280c1d60a24844000e0006030740c00b4080f1550040e501c2c1c000400c000340c620351081103241c2000750440346041075000800c1241d030303031100740100300d1804002c00c1036552482c0181d01950740b1610910f41144045205045c990501c540c09200e08420f6813078120808049800194400302c8038081e100500310301e200b40e00010094000b5200301c505001031403881000ca0510124112101000c0c80711071505006400e5040c2404900100078402d920b01c0c000c0443c580308224083c0390b000d0181c3c0795500d0504034142e02c2e514002c0c403642c03401d81d051202800b5400009503125103002500b60711000500020701c2c110 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 616790368 1250 616789118 616789133
    0x30406050f0f060117060102030f04090203090d05030103120516051902040605030c090a021305030a0c030204201801022401030b0906040c1a0f0403110f0103060f18140112 75
    0x50844490b09001c1020042e1030f0343d1022004071003409440c07950b201611403e00607402d51150204c2550f40749400a0089800b01c52500210302500d0103200315900c0800501c8101d070b09010a01008110103003148080f04803610481c05040c0380b24280c2c50080745d00c8001d60341da0707140c02461506d900c2030800085504055180611600c0c009140a4001e0324120440c000019000311009124482440e400302d080c2c0c0403c411032003008003801000e0200c40c1d10000700d04009505068a1104038411030400704c210610040320f400049800007410519820543c0442e040034519400030141811485180b00b11150050300e0b4400c49107030700040c41c0000165040d400e000c1c0300e060340186480450303480710051100140c17504042d80c0840b030201c500c50090b000500090103241c41203190150782c1c00700100c2e01100740a50607917032901042048807010014401c80c1d0064003a1001ca1050003040f003812a0200300040a80713654030b4a41065000c0068884654440383c0b1400a0a0304495004405070b000d00c1e0800010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 616791618 1250 616790368 616790371
    0x190f020423040b0a080a0f06090204060e0a060b04050604090207030e1005040e010b030405061303020a080a030203010e06040504021c0807021203070201020f0102270111100506040b1504050411070602030406050f 92
    0x3581c280c032130075040044c81603581c21061401400c059a4068400c280045035001034800e03680200140a2966540c1c201c2c1a60b10084e150500e000d8580b003000101c5c00f00140450b01120000741103141401e29244514009400482041e81071051101d10340a1560f80da8120010300c008584416840303071300349a8102c000070b10580052408400400a0002040c4001006513010001e101021140f034050f103000c0b4245400030100401c2c01c0804a04551400d4054018506032502d081c4141966030b1142c0400c025240240c074080d400c0040354085840c500e1000321100d800c01d01500c1614541a41980410310040100014055642010610ba011982d0600c0113101900d441c00c000c0d4204150b040c0800201070700007000d080e01001c3c8a0142c140f41c0d000f5028540c511001d042034036641c80c280c0580f80040c10048800303a116a02c1c10350399406e10b02e400143d41c0c00300c9007445c0c20315040900b80420f21004002c000c4585070010014826500010700500041d84964491503021a05041c188802d1039332040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 616792868 1250 616791618 616791641
    0x303080f09160f1a0c06010927050c0111010c0807030c11030f043f0309081e07080a0b010e06010c0f060f0c0801031e02040b1e0f010305190f02042304 66
    0xc100704401007805d000800c0c5042d40d00703802001807000f030000c400c4030a02d22025a550361954014007400d09000d00410241990b00080c0c1b07400205040462450b0f00701d450907544040850010340c041104244280d004441402080c01d10f01d5400141c08555440c60308404075611070100300240600010f00501902c0f00d1a000060102c0b030124040001031588070304800300007214185050b00c038000c2c5485207a64400401c6010141d42c0c8840320b1509855a0020750315240c2814401e42400140003a80061050f0580c0e40180700f110f0544d0811070040401d1201504650400c000031550700081046500d21402140c402e00000950500b2035401d9000c3e104020422002c4c460881c0c0100003040f1005195401d130740d815200840d508000d403001a004020700341285801c480484184803500c4260288090860710880708448079240c1d0b00011000d03950129030601041003546402180514079400042181042c0301000d404e041d00d4242c51090b031102c414055810301c3c049004140d8605192117841940034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 616794118 1250 616792868 616792919
    0x6062d030507031503231f090f120c12020601050f0915180a110a0e010305090a080414010305130201091203020c06070602190c050d050708130e010503060705040303080f09160f 77
    0x950032134070b501f500b002286048126a11000d4143c1006001c4510454150380300300121089103071550000c10009041004031000d4003110070744500103000080281c104c0364010510202840c0b018240200b81e840500856902224012008929030750800f0229100443e0280b0ba1000d2400c1c031020000d65407401c4600381205001c0021015a692118240e0f1441c02e00382008540ca480e40c842d800c0c9881c822840c060110b420124000c140b084290010b002d40c6078090f641401640c03030340000d050b000008014000c0c0458200c034410000441c094548540c2d2038000d0040c0d940c2c0000040200b0029032051100300e503d942d000641041d42c3c1c0e05003194600e103c04a1070050003080503580c40c159101c5046030340c0f4080c003070007260b2002004031410454088074080110011255a1032445911a41084c011648a0300580c00040c460502c030314148c2d401c403a05580d039a212071b00c404803c1040000003a018503030f10f004003680051034040c2d000d1450300405191080340c1c1040e1500d0300212403181401c00c0d501600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 616795368 1250 616794118 616794133
    0x30203100906050907030507020c0d05030913141b0c01020c0a0b13030210020f07022d06030424020c0d02061501110c04020306010203040e010906062d03050703150323 73
    0x1910b9100f404d96004c000c40c10005050340f0b4802d4140d150121003549140d101400d15844410000044094103903010252903180000c01c1180341e40041d940000e03861a800c052250004590190206484414015900304203182000c00310f182426a0711202c0d08502d20ba10000c00c0c801001030303220800d035024200900080c005055950001c2d260b4018090040813150041608401c8105c1002100d41250b80107114000c0c514000c1c801b0500f400e50f03445141e418441400100e109820494120381c80b955011001d500d001c08844d813500134446d0110b5007102d09503400c1c4072510cc650400c005e8502034606d641c00070b00062034001701d10283c4072042070f034050420581802c1c82101c0400050744900c580401ca03805030700c95a44d400101e00d140a25070054140040300400040c003141d26600a0098509035510882d0580b2102001800350701c82d5030070000f80768280c2415440040c4a503020a401001500d000b2801c0004800c00c034904103480c0e04140c9400342843d0000d44403028501d41d1075091007a000140010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 616796618 1250 616795368 616795379
    0x1302060702041a10030e06010909020102030403030f02031209010506030f0c03070e0c070501051f06031107030305060a150906120501121b030c060509010f030b131a040903030203100906 81
    0x40c010900d0081c0901d442c3c510080c8807000c5403190f8010424007801c494240f031001840140602014010245180106000440c482255000b0f806405806070025458a440d6a5040303480007030105020702140401e102c00145203040a400341d00032074081c000840c071070804c1d00800d402e10340114500d510540c408003c200540d10042034900403200e20400e5000e665607031110300101407080b0f0034001e049510b408200204035000300d00c40700e5880d0140450b010700544840d01a0101c3d01c1e03004420f40070344801d0043c040060700c41d420040d80001c02400e400203c5036129001b5a1a00b1480b000f800030401f1178006200103036205114040a81000005218551404458040c964814140a0720b00c5c414440c005403807401d1181c454000350b41c00614080350a0f074503800105590801c0304128001001d244481100781d10074040c107080580000e1550062a4007400c0000081c19121201500011a000d191103255030f02d06c144040d590007a01c02686d07074a003c0c0d14014a60140e500705080861802405200 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 616797868 1250 616796618 616796629
    0x31d0a090209030c060d0507080c0a17090a050115060e0a0b191b0c0e1303080106270b040e010e011203141b0f160602210405100e091302 60
    0x1103445281006030340b4044100864140030520940b0398011100155502d620309056114501c10315040d0b07a4442e01383c407004200c0c5040c1c0b2502ca803020000324a0350701625010419904035030060085c5044401d072040766601c00b03007541c4403144421441082140104903a90b0810b4440002c580201c49643c0f1041c20084c10180d58041c01e0340380000e60400302e4808048900412391b40001010101c030740700c0c0c01c0003d854410411021402020043d00140c004103e80001480020285035810389803c031403a070074146c04841816840003403480702c154000d14a07151803000c07040a00900490349a10756154105511007000002c1a44022100b491000041181c1c0d03845400711909130360705103407040255440a02181c0540554080480418001291740c46014400200000c824213410180c400f00c854107040c0300e80c0069203101383e4003d03030043c0140501340442400e1442d04c000c5070001031400c0a8850000c181c880f528201c941c4046003185460401c6840c0c4854150b034003032100b504010704e060295000c1513 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 616799118 1250 616797868 616797889
    0x30207051011040b160533150d03050414010f1d060702130212090d0918090501051317040b0703081321030501140a050105030403020c0301050a09031d 66
    0x1502641e56594214242c2841c001c880041c0b01c2c42c4429a1640480b101c103021941444d4002c4a191080d03107900c3d21001c4c15040381089641e150095940c00003221400300c10303030316002041818045041e03541d00c2c0c02d07070351140b82007010703540240c0d550361300da50134000391560502155007241e0500207407001c015080d59104110040c50050029201c00b05144400800c05902464000950000d620b9120b40c2c082051640907096a85d0030030250441c0d901c942004540300c015400c00360b0005041080d06001c50101544558042c0c09100300000d15500386032511400c50b0002d4451410f50300a20821005100e00c1d440110344030204c8500d0a86081d107444d440813424440d212004092115000c0012902c82e00628410f0f51507400034807280c480712841402c0a0301c1e1032603100400200745040c001185002c045916014001000b030800d0b0191410500103403841e400040c821811842103020040c1152002c0c0a100d019005034034020030700300c260780b401400c000302280404840e80400c99904056aa9622424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 616800368 1250 616799118 616799143
    0x2010b091015050c07180209100c05060130050c0a061d01030f140a0c23030105060702121f0c050c0703031409090f0609091c0f0306030b16080703020705 67
    0x980d03580d00d20102c22410b01c00e041c0e10060014101003600316410a147c0c00030035084008585500014401c404143c0d2040c0d496040501194840001030200300780c2c075000e84111100c8220751400c8151400d4842d41d007813071000c2c07041703a2a400c441701001040c240100550080c100c2c0f810f10541f04a0640e002c2030b6a1200c07100c5032810551140740d10b45008045a01814540340208500003062820305205009400c0c8940d2810002c1c0d4370750480121019038100b8003281030300b03408480b031441c3d28040800c1030326001030300c2c1680d1000e0701c0c400f00f05500804110b041c122103d10740418403001039040c40034048604500004052150800039003003e0710010030030106996150421001e001d024160901c02d0b0f0140140958001000b10140002090160320f190320840044520500a94604803115140ea107003424414450341000001903089025003074124482c00a450f000031039a44e01e44850001035816507420507185407001d03a0f18100c030b512584503507018400341402c0d850003e0543e6140c3c2e4580d051443e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 616801618 1250 616800368 616800377
    0xf070209130807031e050f030f0c0c030a080a0c0e010e010f0909020a09030203010c05040303120207021302040603020a0e030d020c04110d09050d0201050105091b030402040b03030a02010b091015 85
    0x10744000a440c9800080c580c12840312a1610725515000e0419455214410410540d9064000c1000d00c1358088820646040f40c1040c29130311250003c0c601c6400c040d101c01105681400b0817664000100046c0c91894a1070f03a81032168141000c0c41011140398141603410491007a007142d1603a6000358404c041c9440c00c0ca0070440d42c40c0091000c035900b641a41000b68884e000240000300d01c0d521894032800e036030007180201b00220b0228401e49540c032131444001c0c00309805520810300380d00958064a08240007615200803002c1d410710100880c2d100380c0014000c203501080c400d280e2540007007804100342041d03004100c40148048060364550b884a540d51240e6181c9048205a0f0480c030159600b1100010080c8a0b00d4070b40c0c9403aa480b0a41d001c02070f00158605000040c41303203400441c131801000880c0c405045404120a1401940c1c0000d00c1a43c219071585001c0c6031640b0b08000900f00c0e027010340d00010740181920108205150040c00030443c402d0110020702062260f207440b200c3c0c089041c20b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 616802868 1250 616801618 616801621
    0x9060914070e19140f04090c0e10320a03020102100c031b02060f0f160e04020c150a0c080603120c0a0b09010606092c06030a06020313050706050f070209 67
    0x40d08803210101c48507400ea0301c0110019008010104011308000111108584e000051090000300c9441450140c84001042410012032030b00c65413a039042503410856035203aa4888102c0243c40751b2080d01e02402128044e09200448445030102500c08002c4403001d008500c0d54000230341d940303019000705504650300d0225080c000d00a034400300301101381c03403500c541c1d40681d240b029441e8030044840c81d1a00480c0e100040c0b80b00d800216240c82418506040c112010f81903200b2035170b1108510070b542d00107500304002a01040304100e0740140024a003040061850100041c6042e20340d950911420f00110301d06102c1f880da408030b40040078481c3d040c02261140405203d4910b01243d000002d00040008070500043d1101900240700340d6607503481c1d1703203920b590b6240000c10004980306003282c07041c80081902c001601e4548000c0c5c0091005040720180b104c0340c0c4520302203a0007075480e025800c0003c1c1601042010a004480003000750382845820103511040d40e4105208034140244511000310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 616804118 1250 616802868 616802897
    0x70c170c150306040b030f03090102010c08070c11010c060e060603120403020315100e010b0706050112080a080a0e0f030910090f0b280c0c0b1606020306030a02040c02070906091407 79
    0x81c0700e05e0070880005d044031350100201c1c580a40b654084400c0c14015400d03d102c059100c0d00810859001c0e4480d076843d403c510b00b8070349a06c1c0d4801d0700a006c0c40d0402210030540c00c00310340e05003e00400300720300038003900c9070341060700400d0300d07010103410340c00d41d40041032200300701603a00410203803040590a400504182d5694103804038080f8281c10500b40d185111001050031842203002d090180c1c860403042005980340d441003032a0703c1603403c004010407810072280345010321503a50036400604200700441c04060712500c95041c000250031000a6610104516600b86070000d136603c51509a0300b030500d1b505041a5900ca000701050041c035000322400581801ca60000c28040441c008003000100a00e56010200808030305c615002601c04911460020030400e440d43c003200c440c07000890840d2500c0e1071642d07a0030040e410043c003095150041c42311040142c1c88601802000c0b0010368060b0038154140210300080790b03065042804600d1034000500504410750f44a2604103815090980a01e51010b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 616805368 1250 616804118 616804121
    0x160f1d0a031208010f0909110607030921030801090c020607051b0303010611100b060d0b04110d0516021204090b061309061a070213050702030f070c170c15030604 71
    0x358801070030b0500b119140d0902d2948084107506075055402c011000f103550720010002e41d03070f84100141004d08c10380300104031480d01d10300904259220342014800c20341d8034200c071805a10b82c0b1a00041c030b016800001001c25901030b1030355000d0202500c2c20002d100114200942c1c400009040d4001d0180018900d400341840d180001c0021343d0500485ea038a40e144e26008050a0f81440042194407441c04402e226014601810403904c0c006030446d410004190f4100e4080e0540b58140e6070043c1d500c40d18805131906540c001c00742d042c0304400c085590b0606001e0741c3e84880c44201d501003103420420010300f10210250407503040764481c5001244030750644001445a03c280040d01722000f0702c6840004000c0119000030701103130b80220054018960708642e0002e140b14030381000b0740c040710b102c08401801e249584000d400080d5132048a05205000c10302e500907500001d81900e45100c8013504108180c0396400d000032802c0c1d4480603024408080e4041041008a01c0070440e1104011000801c140c03210b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 616806618 1250 616805368 616805389
    0x803060a0f141c03020d05091504120302160b04030206030c1c0c0311040308040b030903041d0405070f051f140708030a050c0c1e100c08160f1d 63
    0x440352141661a890030340e02c4031403020014000c0850f60b02d14002e803500c0d50250000e050f00f58000d050b84220f09001100c5542c00400131503486549c514508010482c0c100c040c2010307003010503c1d00068440f9050103440c01f88521403210115152440a100c804801011b59044944c19101b81d1341f00e45031902d61f100640503000041a00d29905902c801b94010240c2000404854a49081007101b111000080c454802c60101801c0c071103042004000d1080d41030000d69000803d0000d61381080d8a920400001800b403500c400708460402080c0024040140070000040529407111204280782801050041101581100001040c2c0614880b8280100d80803008003c4910200e5a50314140c6403080d000d400643e500d0010a143c000005d0545245900b180c4d291040380c0001d11905600610108235031248070605e1516010300e01c03116080007000d000304446441107856669051904042060600450070f00e28020481181408200507401c00c0b001610b0030740c040030945107008003c0215031510030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 616807868 1250 616806618 616806629
    0x1008090312040308042a05060706180f050c030a030815030a0c1805060f06090607080f0f0c10090c06270f0501021009020f2e02072d030803060a 63
    0x35000b0072080561200ca681d00c1144510119003044502c00303100c1c01214031000101d00244c800b00c0c07091002d86416400340041034130410000c0307400000c6043c0c2c07603200100450100c90420240f610202000428040707040c502c0c0f400d034001c1208090176200181541d201500d071a0b208c40100c0407503c505e4500784144060300e500001c11384501640c1d05004100d100c0c0781d0414100d8035240c200842c205140c069101240c16100901d41030401d001d96041003129446040101c0c1c55050400c06100310741d0b9681c01800d00c01c50003800f200d07110500e41054a060855840180d0302c001e2410a1210021301d02e0744e280000d803041072401000c5155010500e208100d140c980f42d501c10002480e00056005103080b524040d1603003a03081d10300d0001e00046440503250101402540407032001c8600c0d00c10304200d011050b0079603450b020040501a030040d00c0b0b1907580c000c0c01da00010b8005a40c140002e0f1650710b5010301100d12a40518404440c1519001c40c58032640001819960b0001c0868800c2c2c0d15505580060314 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 616809118 1250 616807868 616807897
    0x20319060e010c210b03030403030f11010c050a090914150a0504050c130512030706020904020f0c010b030706051201090507020a081201060210020c150c1306020105041e0210080903 79
    0x10114038010781080c460313554100103040c21319a81100d45010340241c40203920017400650800d4155a4140d8101c1c16603000300c2c04004540d01940900b007802d01549200309401d80300c0d41c0c0d803031000036401001d00e00641c000420035401c0c0720b00c0c00d4114000410709540610010f00b1450440c10780030000742c508041d940459030244c200350034080d6017100c40c1300803c0a02484140c210403950760b6014000d00c0c10303140d89082c0b8140c000307000340c1002c40e025400400f01000700800052420030070001c2a8502e8000248918070f681d5905415811420200060400307403a06040c0b480c1800d41070a50003c1401050103103a035007980300c1c0041031545000f04600e00c074041c5e015141030340303c02140081803001a4240b00301d10062003421171000008a02307100716040c10803448080c0224500612200c2080d003800741418043c3c2000302720740c441c100491801003001e0000c5500100706401c09041120305021405100b24112040c100100b005944180942d2360704603150130142519510102418210b0182541880842 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 616810368 1250 616809118 616809131
    0x415111902032116080402010c110301060f090c02060f01081b030a2a050103020f0313030c0605100f0b090f0d1401020403140f010e1b030a1416080a020319060e01 71
    0x50780003d40407480f5060080d60306a16050140c811501c030b039015200680420840c1a103040880c00b070100c60450310101900105020380d80d00403011a06600c1d03408118096a04c2524402e1a80d06120542e00f011920300314030400e5040003070142e21440c41c040d010701140441c82c1c018040b901c051217001f204942240510300c0b00c0e50710320100028110b0424035101c40424032400810a50300a100307641105040c2100d4908640d99400000c1e2079481740c900c00d40c103010209200d400061240d015040c858200c422800c204149494000941103415400944c1c212a0038881e400c0503031034644d0460b000900845440300500362605181e442420030440c100115400081c0100900c08649035807040300d8480d800b201c1c000e104a5181c0360072148074400c4a0400e82140c84103811017400c2c510307040c0b41c7c4907004054510002442c0c0c2c40c0310444000d030040743c906401440c51381c812440e40c0e2041400a00d0a007002d004c03490407030340c0029201d40d4040204628400d405000c00700703000c2c01e588101084900c10008100c1c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 616811618 1250 616810368 616810417
    0x121d0a0305010902030d080709030605090102070209070203042306121803130e0708101526040317091f02040b070302070f080304061707031b08041511190203 69
    0x38007a03402013640a48107214075004194401c1309541d1080c011a41d8001043c0d0850f6160300c0030b00400390080145640074400c030009070b921000f0140c000e40c0b00760000c40c1d03501c0c41d00141c850000013050728000c90151154907050716447c2c1d01d0445501e54a4540da0142c669202d0b2039044e5004412a450070f1144004600300c0c088044039020102510716080d1295565a126002203d0741c030411184054007117041941004000c030380e1b1044010036080ca040140c00407020314032084411030307501e0038414440c0c1503009200500d50814260043c08540c243d00030142e180c0f14250070f540c0c03030600030341300010102c00e010400c080d0641c1d4182c5024110036440c2c075640d521300c0d00b402955441280110180f01400f450002101a0000b04440403100d8984420f0b80100780f221450196490080c10780c400d1640380c00d50049090f00307201800750310b00c00700e486a28980c109801c080659140707e109102c91245041c0140d5441821681507500c0b2f8102e83c012040580c5100a04900750f000d55820054410b1152421022 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 616812868 1250 616811618 616811621
    0x1030501020409060918060902010320190206060d11010903020904060b01030c092d08030304210201060f260d020d1704030512090f1c020606010c121d0a030501 70
    0xca403900f07903040c01210340341c1e03425504980d484e22624401e10b0640d800100010415002074070194014180003408100a40240c1140a44600c8041c0c10130300c001110b445000030906154a144064401040289045004607039840f4866802805400c40c541c040f400c5030384129065400b541d4003401c100c10900b01031401c080648032504000c1d003c2801d2030303080c200d064400c84000c02110180780501c6418103415003808189a07181d105070f00300c4601a540420790a030300300025405180f00f0301d004c0c640e508103088014642c1111203509411641850000c00011100c0d00c401800d40c0d01b000310004282c0401007030f140740750010719170994050184084205850350040b0743c42500281ca500c0d01c1607002100c61801804d850f0031100100841c80c1484214503a8003240c680c60f40c84203140080360f0100194a42e2540f9041c070288140091621040440340000d906201140c3c1261080c03d100c0c8c0d03004000e6650240f50414451030703800300031400b20506020343c000c01004022010140000b580d880e02d80c1040b90 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 616814118 1250 616812868 616812877
    0x23010603080a0c11090705040b1c06060503100911030c0a200d140f04060c0c0f140114070f02040c1b05030318030a0206160e0301020a0e0f03070305100905150103050102 74
    0x260040711004510240e03051004449221b40c419913a1189428244140c400381d6400010305698140c6100410780c10403403c2c1d1007900c01070600d9840b411340768a003140031040c0c64000750700f115019a003880041405110300c0340c2a2074103c00320560680c0c9824080c94200c7e00002d02c034001c0030050000c89000204210023144104540381c0e207a607407158650b417840321070003188521180390424400070402009010b02c01c510342c04200b44a4258070307240b140e60f215041c503a010380303820078100000600100c103150342c1c11512010a1840b804100b5080915540baa00c6611000703100c064011501c030030340200310707910500ca0300715255128420914001c4190030300c255242c0048481d45841c816030f0f422114102000001d03915008a81d42c0181101e50300d0100048206628a95010911014500c40a920b580a0010b02160303e00f9135208510b0103803280810580f1603020b40d415000350000c1c18107002082c0003040815050300940380c0894030460502d40700d40740510606000111990790000441000419002807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 616815368 1250 616814118 616814123
    0x13020f120a0e01180210020c03120d0b0109180f0b0406170c030613110406181509150e0c070203060f0f0f271e010c180323010603080a0c 60
    0x20000c0d8207002009601301c40c21010700ca04515015440300d0010b01c0e010311901c114244903c1500c100003200000700349404416580409003403004940100081080e215020603468240b074000365031031424044999040c1d013061295105074844064200c407409a0b04544070214000c0c00800115076030f0b24214004a40006d00e19005002d042407041882c40c000031054040d09081152200da603880340e5410021827a00004030360413075100d9000281c50303040c0c003000070400d40d00c850000c1005c1140a00403548030344580c1003c1c0795645801201d101400307401c05040242c45104051880c00d444003500064070307001c0e60320001c0d810300c00ea208005401c401d03480001d02500d0301001c550040d0b01c40c2c160b111030740f01c0c0844039084800300041000d4840785858100c0a452524081982d541b81001c01055204408120013140140e460b903068001c0c0c0d60f0712071503d030b0040780603d00c81441c2a00359640c40702d500c10b607000d80001e07041e044c0300344c242184801e40c0800d00031644401c0f05070741d44005180240440c0e02510b000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 616816618 1250 616815368 616815371
    0x708030418050411210102070f0209100605040b130e0c040f0f08061902070203010905031c02090a0b09030f03070f0b1e1906030804030c080105160c0213020f120a 71
    0x19001e006440c0030700d038007965101d400d070420307807031aa01409414010000b6000d1000c0c1c1600240014200a10040c602c4a016074100095114a80140060102c0103405100181e120b05010410590b000054905842e9891055640c800e600f0038240d920403126001040900e0904007440200c0499030000c1048601d0b00104020960345e40429440b408028400d880ea0f5400075000290820504a10790381004c01440d0010709150b15038010a08440161400715015407000940d10700c3c00b03100016402e1040d030306a5040d0f1410300e80102040b6900141d02ca0300341a4540481c480649075070501c480c10629104404503a12910a030400880025029030141e03542c0c10300202140c1401c038203000d07041640180002e0340710039403942040250490003401c4540c01d216175480c004400200b552005200071409040748040690504043c01d0031610042d0114818000c5203213081412504007a0305003d03030740c0417122085c0c1190402c020038041d1241c50b00c0d40d0441400000e00700d034600070380c13400103000701c04000c030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 616817868 1250 616816618 616816649
    0x90115030c1706061303050607090302010e040b0102070b030702070b030c07020a0e061806040f020d0e1005092e02030115030507090b0f1303020405160e031518070807080304 76
    0x192800b03096000c50100d424540e0b00000d40500703201c0014005030803104803500000d075603510340c1400e24400361801d10003e0000e950400039503030b200e00e032034440e2102110108160013680d00042d5540c46a4480c1071180c0710080001040d45000f444540010711004285543d24640180e401c422030780980c40403842484440c00114803001c0019a0307a200702006082807a41e001e02d00d07690503012400074500f9074030035103501c140500804180054004408005004a40c20000c0e81119045c071441c0c1001c0345800d49420f081055070040040c910030b8180e010504101c0d440c00c143e201c0404051640c2009540e1400080006220b00c0482280c69040003190b03002c02c8181c44446003140c604180384100200b42e0028401c0090385030f00d001c000c112915544801c250260380e25404102510300031210b020400c02d6200d580f010060700240861491841180270300003c142c211101000751402800b03840010080d0300030700d03580903400c010702070143c04003404a50070181d0b10f1b00c680c4c2e5654858040c14452842a00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 616819118 1250 616817868 616817891
    0x6090303024c0c050403020f040b01140706060f0b070b0f270c150918060d06050601020a050f07060e010903151806090c030b090d02250509011503 64
    0x200380901d0a06644800c07040c40c001d0b0382d11541003030541c0b2000000b071403a10342005030380b005903c940080316425444d11622185140100803c5001d00481c0790300541c104240d4400580c4c2c0440240c425a04040c030541c1c480c20241030400c01883c039030700442001e0031444408100a08200080e011444c4507072030780041783ea03480011035501c3e4401c1c1e841c01c8002d940035445610343e18214450b5040800760360100d410500c03140300001c0c04684d10090058006000040402044c1882c0031844420f180300502d160075420301d0008982001d41100020303021a45d160041291684203105407400d05130440211000c40d40031040e01500c465480c4a400003140b149034150300030703500441c0c840040340d401021034648400d86800ba90003808018078245080617000c11101c000800038814840007130300072613448808508503c0c012440c18030242804406030300881007a03085c0c0e03900103400c4c1c81c924041d000c01c007959450380900e14454030345600480d40c030103040c1d800030032000c40c03142040090ba200d82c0d8041c02816030ba603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 616820368 1250 616819118 616819153
    0xd2604090e0a110105030702030c01060f03030906050a05030f04020f0904061406010e130218090a0e2e0e010b030d2a020a09200c0d03050a050907060305090f070609030302 75
    0x30b041c010080a0074144800d001d43c040c60145502901d80c1c01901d1030b0104002c800c9007140c1094014130440c880305d0b20103005240c0d00001100140c5118244286040e00540020f8180e000040c990038501403200001802c5445030801e1410000c405015000d00f418540380c0030014240910601d40c0210340b0300c001031081e40c4911200b00140c04003401c15145054504040c0010313500c4a180004190b0284071600c4058451111840c4a110001e100040e0104041d021505001c0d81300c030103103140914125040c0e030b9210b0101452010408001001070015605407146000d00528010300d94180070f08000e000489400042ca26540d400c026076048c0315526000390398540322042c0300069003001003044107115005070f90f40301c0151002514189410003c501d040d2542a510110060502c3d402494580803442e801d0300a00e5002810001c1c28040b510741165080d50320b031024414a005c058480c2e0100b00650030901041214120030001d03140b2041d11f8810242020420b4881280140b00c0d14031082c94841d802c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 616821618 1250 616820368 616820383
    0x10110715110703081323070602010204060e0f0d1502040810050f04020d03030b031002040306202d031810020901021911030a060c0f05090f0d2604090e 66
    0x2649420b4140350382a102210342c41401403000c00d5411000069401007550540c1654240700307140005040c2a0005028504141c1075034400303820342e8014002400250f8011203080403800c800d0f5070800400708224000b0303525424040c400303001d1030040340b520701900c41150002d105884100341210800c5404580403000c5a0341140c00d1080d47c1820008640140b9008800301c0402d40686004142445400002400d20b651032000252503680010208100843d5000c0d200602d410111048144002500303419194429030a80310465044602000078105c48591555940c20414964941b00e1034003080c1d040320b034401609082024820028aa211140703075008542000d1f006074043c20600b100d108500c103070f000c3e0103401200c0c03010310000c4114043e1001c000c001446801560302050f0b8101402c5c01402ca40482d03042081003100401459900d9151007036440200202961842172254407424007805070000c4508811030703003210100c01241100414042c0080d02e10100b0100100510703207605940d100c62 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 616822868 1250 616821618 616821641
    0x1060e0f070c0c18050402010f020a1211120f0417030304030509090a02040e0403090e060a030308310f110f090406051504062303070602060f040510110715 68
    0x14800005000038030079030300d00c40d1031842040b501000f03607250b0b4142c82c0a0000610b407921402d0307481c01000250f607400300c2000c0184140d400036240006d0300ea101c54030744d40001440c0205114107407454080d0031004100c00000210001a41502c44c803200c60000d6003035116214020301c40c03801d0750401c07001300400b0040f070740103c3d0b060310b40324039207030041003401183c0c0310052100c544030b6070a120016900c03441c5001580f06030310036541c85014030b080800d44000c00301d02410250189003100700c1480002c1d0030480250700202e01001c50f41000b501001603102604402c4515030030200032104d08020400d002c0034120015115085464038203c0f24414042902c08040b25194000c07060004500414001d51203181c100880011000510a1541c0070a064900d158403081804040c2c03c403214020400c030110104000c402c602602140b40303003600003599154081c1010b2580324042c00860100301080005c50020501c42000f0300421404d11040c04d001e1700580402d03603208150702d446121441c078902c0b40e418001e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 616824118 1250 616822868 616822891
    0x8060915040e100c020127060906060e09010e0615041a18090c0103020a0c02040203061305010f03030909020c030703140909240d0203071a21090d02030301080d0e040f0501140301060e 80
    0x500308044207c182203081c406540700761344d0701115400314004d8042e03c00540900351010040b418264000c6003110b10301c80081d205500900248440b1102d14082c030700848900700c8002c6901801440d01d403c46402844240d50f00a1000500802e01c1031a0040c942c400c1c4c60840c01e4a441001080066040e03106081084001843e414042c2c030051600d607010b15003303038018121040c0114103001940817140281c004c550040c2aa20041041541c0001c03500007070000e1110660a0500fa010f0b090ba40b8010030a005050015840036014012400c200b941c10080005002030014185040203c04130038100c3c5000c000c5030540d00c400402d41c00c00d4a540e00b50310794090024020b05250425008404115000003001e0106c01c10001000c0c0c2ca8460450550301526500c0d40c00d203003084070400d0314141e0f005078070304159001030004000390600800c007043e0307501690402503400014400003e00500d107464029111510b010004507441310042c2c0101c039501404d80080040b940c40b160003c2010008840801440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 616825368 1250 616824118 616824161
    0x712142b020c102c0a031118102607140a1d012d050103021b0607110c0d0c0b0708090a08060a150608060915040e100c0201 54
    0x4003854405010011103910541e0789000c02000041c0d14119094a40c000080340c600c103c02c0c101c44035104d80c800003881003010402602442011900c01d003407038400035003281d89041958185850b60385001c0c040c00e82101209810f4640060360000e44800ca006212000e5284040c5061000700014150103c0b401c1d0001003407200c1c0751640164007000d9650150360802802880051401c2c2172504601c5044020b04803a0030300d60404040c012000d6421418018000340d500b001c1d2007211b110040c00e0281e43c020f180269039091018046400308122603040c1210b403080000b0040060382c0503100340d0710b100001003994404802c1c40d0400c1080300300803401030148045c1380020051100305d00000c116483c480c0c3c3c003190030444000300180d20101d09902604041e04031030100460808075109540310543e00c06041d18005050440003042414000c002501420040e80494600400c06440300001c00c4010002d01041c5407054445448440c01d080c540c00b201d0030584241809070040c001e00300f8412003000310f507986 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 616826618 1250 616825368 616825423
    0x32010c05060f070908030f07060e1603060203090307080c06060306150604270903080708010b041404090c05030d030204031103070e16030f050f090c0d080a03020d020c071214 76
    0x5008000d0f000c00c0a100f0546070000f4018414405000c4250000480d00e44410440c20818191141c0340e0034044203811111600049034071b91307603120055907040b0200584a68503030b45018614442c0142c04cd0001c40080b136400b00c1d41400040c840d10503a010380c2606e01d42c2c2c407009280e80401d1180b4121980c0040248400e01a0300f9005950124010440203a8061980442028400c850302001c090b0001000c24081101454001a00700c3c01821a0305401d407500e89000c00e0156800c04a06001c2c0c861502e402c04a81400388001a00015150082c1501e01c0c0c1c81c01030350068000d5005220032103140000d80ca503580140381c0402c0701d804441c2030445000040da0b40002000d400802d002c88803003850303035a402c010b0030724049108491240422045410b0241003002c59145802c2245900750b1142030102c60105c0001c07254016508225464103001d6103a0024140d51000b0740a4808075211911a0b01000107040707035120820a02c4038021080c01c0004010604030a4444c20141201341c1000342078038079481d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 616827868 1250 616826618 616826641
    0xf120b0a090b1c020a3305070b0708010f1a130906060e090c0a030513060911010e04020c100f090f06140919120302040806070809010e010e0618010632010c0506 70
    0x9910f04582207141c40e8040d65100f01c090414807516160004101003026010045101c00c8032b03810140a00781190030350316140d03820f00c0040c0b5602840d21422100d40008000441c558142c0300859a01f000017104030f42c0701c0c1c500b07900404461042000046c03100c24002014241102e43c5400390f442031407038030326100482c0c806502400000d000707420700e0940700d0140804200ca0b0312484900174400d100600080f08100001001c29812aa000e031140788100b002d031a0102d80040d0548000750245e4000c2411585c1108140080600b5400a02407240c034171415000c001451740012518444850580d5072900c4400700a40d480700c031075541c40341d03180e00d50a903500410aa422130071181d00403803402520f004d8135014079074101351007564580c02040020050044c00d1000380642d10040300340d00700030400d1221140a00b51b45000241c02c5105c08041e511a8000c100e20a412000282a0140d5507050769900856440201341c40203010340d80303680c1c000301d1441d5658450101e42c00781c107030007600809254484106405 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 616829118 1250 616827868 616827899
    0x604060e1216030f060c030e100b0f0d0602220e07050904020d060306020306040c0e032d031303120c02100315030507140906100f120b0a090b1c020a 65
    0x4042d108100040c00e0100086070503a020314841d55a00c0310f0340030a4607049040e20b11929140c0245414800c0c0d08100030400150664480003000001c03440c1e81528020640401c0c1e5041041e40000700c13581c0c25000c0c000d05070020604e2070801800070004000621445980311290b000d20114000f0714004180924441d50150501503002040140b6200b401944041220b00369801180d407941c0200820401d480d080c030402441003020304007525800c0c80c46000907140c5190f040a01c1d19101613100303400030b4004074004030034002c0c440c4007141e5035802e103503a840c0300205a0784001c032801d152542c1c02c20542403040e40c3c042420303903003c1d0142d00d502040f420164082c02c110b824140340c48031800000808250308101c0b41c40105401109005002540000c1c0440070310300034081e9009061846046690a500054dc440d00f024289801b03019170810001500c0a0701c2c002900550143c43c0e0140894800c00c40da124000f81c1d04111101a406007143d604e1000f0507242903800f9502c9203141100b009003240c101580d1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 616830368 1250 616829118 616829149
    0x70b0f062107150f1808061603090204020c150711030409020702010302070f0b011802160303020a110d0e01030624030e030c03030c040801060b04230d020622050604060e 74
    0x110003642d11a480e15a00d15411084080001c241d12203006045400c07046407500b907480303c10300452503801d181b81d403643c0364409040185040f540790845152540b0a0380b14502d0582d008100795990015000120365904605500c400070100b02d0002c103140701c0c00340c03031008200c81c00e80c0090b5007014500540f20b0700a4010010603414103400300303d000005809603005101307142c4501454581c035410400d408031042d8080803000451441002040208a01c00034980101a810316002d65202d070f40c90809ca80f801c0f11000c0c1c40680d0f10035010600002c94010031034802650003aa420086030341d40e0010101b001c80f09001020003860351012b48440c580c40b942260420540200880e07280107084105145541e0040b5211a00d60a02080a00607050280030b4800182001c644d014103040c100300e420300d07180035155607907007407880765104115032502c51800604000740c000702031549601d416803001441e100c081c7d43e07010025040800229981c80d050040d1001d40341c07160b4902540e5888201804805503030b2528a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 616831618 1250 616830368 616830373
    0x6111b061c1d0a05060420030303010306020316050a3e0a1a060315100504020c0f0f010e0d03020c0c040203011203030c09210f0b0903070b0f0621 64
    0x1800940000c40740c400c49088491080065400c0d042c1d9035072100303400d1030010b02519811403804000031400000e10b05801a401071114280c800000c90318070a4540488410b580501001c0000010f0207020360155202da600174a03500c03042845581c08a45074480d0000b0800031549400010b4480441c0000360a200400f00d8080c114280401c040c2518003010907034150520f83c0180340110400c14108100038407003943d10003001d2281015000031380c55548405800c0c40301c40c4108001000108100c03110401002c024004640d40e4160034085034a4410003000c1d0f0308203100d0070030000c0700f44d041486036840d015003003c094400741c10300314000c601a520040c0b02c41090b1250301004825540c4901c020344c020224610042e01c03140103460041c003614450640103041c0000410104542503410300503a5080f040c0c0041d144c1595403d160a0b1a4101503010141290f60600100b0691210000007403801138099210701c1013a40c0c54070010f6925401c02c40354180c00100901c034000030894800042d0100d04440b205 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 616832868 1250 616831618 616831627
    0x3040f08040f0807050402040b0306010c03140a0305010501030b030f07090c05040305010612031106090a0305071a0a06082e15180227012309090108031306111b06 71
    0x2a2003540350040d420004906510b0300b01008515001c00c581d500405d01500c055040a00d460082d00050000509650610041d11300900c1054411400f403d03c05201c41c0196032035003807185c0018001d00090040b40e002c03034506624040180f0340019140c001c809040014803106091541c1080680314900f9100180b0000344400701c00224203006070405000540c08460048c0301c01d050080c401ca484c6480316206800002c144044000c000c164241503940508209654003107624120483c0c444d0740014407001c00443c01030240d010314680003801203680d01011510502c3d45801d0300150091440a00038055040e04841070620680b608003242c0c40004100202d1841e0341c1355071210850a0b0494107442140d8001110021421003170b284040c10109000b0f40c031020b43c80940060440845054083c1e0f2038225a040142c810a514003203602561014010080551b07403800f01584c0c1e0741143d0390100407542184030119406124450101e0032405a00040040310301c502e030509442d8120180b22608485c0800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 616834118 1250 616832868 616832873
    0x323010209032a090a0f050708160e1305070201090203010b03070b070f11030d030b13050c0d0509030f1308010513081209031e0c01060501181406092205130c060503040f 74
    0xc01e80f060b9500c0f45e0101d0300f0700804003008210341e0014072000a1015200611007c960f01170010010100c43d0300b07001144020210006440001080c20900d4042c10141041511603064100303683c42ca10981c020701070510325404068940300c43c1d0081b03422900e4140035030008224651101d40d403ea002d0044085510810004039023803695001d100700110f0340740c1d104c030001406e11100c030812030400d0800030482d90070301c000c412086210300a2059061a20380f80851030340f001c24400c0700c0c4480800740c02030b580c1b484808484c84d48440d21b40f152205a510b040001444804000020110940d001e492646481c60403800610310400291030704140f44030a1000b1505081c0c1145031401c140ea95800b202e449a480b00065425075205801090411019424000c0240700c44a03410b002e450b0b04c0c0305080803089200c404140c46004008125600003030301c1001c00070a03c100f0510140314181c005040c0110b594180f510f0249803079a2000070000c4520101c10448148214003564126100c2c05103c4d80a10b0543c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 616835368 1250 616834118 616834129
    0xc120a020909010308030f010b09060706020a090f1d01080303010f2102042316050d20040b0a0207080601030c12110d0c080106080c0f0103110d060323010209032a 71
    0x9801c211401000003007440402c0c4005a07d80703004001266a8914012098020561a005901c1d00070a45500410442c0d040c1c2d020740b8614000c3d00050045402a560b00c40329414941c0c3d01c0c5071400c0e04600a000042006d2001008581c1a00c0b070b0080c051521500c0c01456207072186004581c00000e9545010303400c01a039035405406181466200c00b4089075648180340c0302881c1001e4201d4000500002c851141d507504070065030002e010044000a5070300718001221503031010300300d8401c1440000900402c80400f800701901d6620b03a2603088075017644d2070b258103595458081c00007402e40b0544d42010450204040400124240f1601d102020700c4140804680c854a140d042111140302000040c1b001003001d106900040640f0b9000301810380c0799802240880700106515030405440b4258400f801e180075044a0886506100800c034041d0b81b8200700040116582001c03200240203280425595814001c0e40d44030030740180030700001c909004041c000d0251001000c4c0c002c14025481e000706039900b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 616836618 1250 616835368 616835371
    0x311031e010f0c020a030f0509060702090a020721140307090b0d0b011b03050d02070f02030f01020703030b0a050108180c04140405100e100e100203160906080c120a020909 75
    0x803a0010503002c0b0720100300c030296042e5000400465200451640209a204902c1c500203541070910390360303d854850214101d8030506501940004020050217049060742d0f0046c4581070107140441d5246103050a62100e04444030200000102038021441c0c1c5955031500560308840070741000303e440c6c1ea0b903182400041c0c101041c40364515a413800319011558100200c2601d00d082036010320841c00155801404a00a61100d000042c4c0c1c0400c400701003005a100c510034250b001011a01e21030001d4000038043d45c09418110f000a007401d81c0d4a02e1810190f01d1042605c0058440340a29603418440d42515003c13091207010610070484240d17140d881c0d6218142040602d41421489490103040291034041c100c0140062a07141180c1905540303800b080028044040010200303a40020f400c3c49480c3c2104103420f400040d03c00803c1c400c40705900f520588100b1445e840c0c100f061543d800c03081d41e58620803a40035080c1c00302003059208200b06042c0080d401b40c22960010700303290b012804a00310100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 616837868 1250 616836618 616836673
    0x60604030b04052a0d0303180206120405011413020d0c03350903030915071704051810171507091a0f19050d090b070e0406030c031103 59
    0x450044003d0011138080c00545141c1c12200703410440b9280d021950f6400021806400c04d6510b4070303a1025140d4900004c0e54054005003e10b4541081c03004010f15084107450440b01d541c64030460605100c1030311056445100b05455801d154580d0350248400480540b00440300400382d0003020000920301101614984401e03051029003262900303420700300c3c02c5940103187c00c04409000c80d21482e0340000855072a00825100c03420789182c0788000c040c0303500030458000c142c54089400029510900c202410840300c007120a007510904050042a4030380040e1910048080922030501c140402d440f00700d28851240401c4030140c504125024882c0001070707c60400207a080b00e000c01203a00c1080e80c416100304607403481480c081078481026071502c00c04e15007001e040c403003035803080d4401e0003103050364490700043d0018010310000307142c20840c40e8070403284c0d040070507030022a00c4018100f40c030450702038a1380000e1303541e0182e0458503904600310304095501d0341031203411b40040c000703005c8410801d103841 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 616839118 1250 616837868 616837873
    0x5090c16050c030c0a0308040b0a11060718050f0d0b0903070206030406020d0c11060103031206080a060b1e03211c0b1302070506180c10120e03071a060604030b0405 72
    0x85050342018282018136480910030918800c06001040b803101c100c5088501a004059540d2071031241559142101301150186005060800222540207407040e4400e102c0c1e4140a02c203281c0b19400c000b500e600c410014ee8000841d00030310000580c143c0d031615001303200102101e0510200d0307400a101ca40c02118201c036100c0c0c0100346244500e18501514800054904081c2e070410300d080c0308656159014071020301000310200030322550002c95401000035008041c00da030000003090404030040c0084444250240c14032824034203c4818012155103400402805030140785020110070900460700d01181e1001c90381080310000b044801e41c40c4840b150340c1b4030008610810f81804224035826030101110ba0b041c01001610006040402c03465270008a1000e00c0800c01850104a860800f15a0707a041d0865042036411500d41d4110003d080d8151407505d0600400c03004625480d203900900c400208000003000c4c034003800c24441d080d031643c400307805401c850070702d03075aa01c0d500601c000542d81900c454 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 616840368 1250 616839118 616839133
    0x60f0f0307291c0b011b080720210c04141005090c0a0807020a080d0b0f0a030308012102091003020102060a1401060c05010212010b1b0a0c05090c1605 66
    0x100c408012800d0700041c000b616400c001d9840082615843c0080c203001590780e445500810316800740d501031a4000100302884600c20003403800d00f0666102000c213031a6128403400d9820300d00c0c40c4401c80c0c0d4080c0b001801d01c40403041000e19580718641c2442c0c1840c0d0390f004031204811551598071907a42c50903616a03c21119091180f400c41081d04182c00c03240c02000400108144001c8003003c0b82e03215111417508000d103a8402008074208034801900400c1c4501c0003e22030b10074051034000240c050707001c07580003a8942c0d0b81e5040020100c603901c0300a000c509600c00400c480e608071418100c8913200b408580a0780c0c1d9031035000030510a01120031403102d5038200030a2056503410054035500a01c02c030008c11003032140c2d4454204580f1305110b52001c111600b0103e4080000a4041e0390072480040c0b450841541c4500e81151642c0105005050901d1044101c51003a030001030303880300d916040707416075801500340024070800300300081c152618210100103081c80032850701410350286015001800e8603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 616841618 1250 616840368 616840409
    0x705010e0f031309180b0a090f08040609120b150102030d06060503011d15370302270a0c050906180103050c2b061502060f0c0a020303060f0f0307 64
    0x86100079084180030520f44190890341030030205180c030780c46400246c07122055032140c20080c01b401c1035142c010035100350702034005e08111502000c1c0c000c0e1585030319804040c8c4d4890448440c260354103071014000e040b245000c120040c510f0a0007070b01d80300c0180305585c5015445c40c06001516881e40c031100001e4070000040003c8180c1ca581080c9140c005c050440b16801c01c102100c40810781d41903803910801300c181d0746112014081d030342400599040307150b42000c042860346665078180e00b80310503806919030540940e0810003d100c1e484024003072207860145903d80e1101d00e0024010300b2034040c1071007003c0048489594440e4098001c204003110342c0607141c1200781c001003d44102800c0e03003141074010304c03084061014020200c494000d030124112061104941e0b0800608155030003801c6200048030784020f080e41c080ba416118141806a04245403140c041390030035440303001020b500503042400801c10794a070a80e40c05c2550100104a00d00e140008000a42840e00561080c10a8060b80d04000300c2c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 616842868 1250 616841618 616841647
    0x3010b181f0302180703150807050a080609031e0906030a02090a0f1415040504050108240601140d0603060f0218030a03170c070c0e150a080c01050705010e0f03 70
    0x14210418007041c0d16650200c0e0100d070382002e00351544a0f4860000f0865403282e03000e2a0700a10000003611030b55951310450342c8407001400f925000c1c911050010483c0305002822902448504008528000ca000d0702210f011422241c480d841141c01c100340a025540c2e4000396020320030002e00140c0d00e04509040101d410b10360b503c074804109030140200001c200f8940b8007a00800c05845d0710310320a100720300048451040b5003003a503200d840e200000c0b0303e0070b41c001450f80c0801c42059020b40181c0e00c1040b43d00a00204a403050b002071000545a40e40d05500f00c00b6280e80b6810590101d50302ea220781d41c2e54191003451100504050340400c1e06401100c88400c03040b0300c4101074001c1e00000d503054400410707101003400558120000e4101043c2003c000301d0440d11600d8005608075a0243c652031520070440003a580d046810300084441065490407140d00c0c1c0071607181100030400d041034100191010342040b00c09807a555a1038541d40700c03030102030109444c1d02810b135024580d1010204203855 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 616844118 1250 616842868 616842901
    0xb010e01020f0303011809020d082508070f020303131716150813060504060f1b0905040c0203070609050d080718030f110d06140901090203031803010b18 67
    0xc0c1194494040907084000100440c2c0c152000c0580c0403401e40e05161160001e070501c031400030341100715200c00505201710200500801901c5040e00012000320684601d06103030203900190402030100400b400140c01c80c00750003815480034041e03d00708011006074038515092588185d08154000820080b1105c062105040034566151010034441c100080e20002c0410880b900d01072002d4580400c074240051052038543c03603441101800305103043d02d808005880365850888245040c8850f880d00b581c2c000039455010582e50782c495100c0e03031803c0301b000094081c000b0002c0075030008010801c00301304540100400c4a000310010b2042d0390007000001c0074180000c000c4020407141d10190404840081c5142049036040341c0210510207139804c2404010580022807035015024146440030040703a6001300d00050406080d141880d03030717900411800c0e1000018000c1d85a00704000a00e9189440d015042c00d102c4040e0000606410000c003060b5400404001c80c0c042403100402c00c510f8070000302c185c0c0e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 616845368 1250 616844118 616844147
    0x61d090c0d1119050604030317010506040302090403030902240417070609140112020c0a060e0d09031514071106220f03030b090a0b01080c03060d1e02090a0b01 70
    0x101c640e1454944a080e80728100005104100b011259800c0c450340c40300e41d0029090042469541d503039286409402d900e41c01001d012880100000061245003900660303082320f80103030170003200b039441c2c0e50100c2c010007080317004991144120703440c1440680303440035805007520f841200543d05c03800c0c2072400c9040c01030400c07040e800c0c0c2e020101c242300d20b030741c4124984212042c0c6070400c0300c0b2224036030043c7c405001c5d401d0310031041d0341b000c15130b034950860000e00003800d640144401c10452140c1001c5a80303134030f42800f08001103170510601f0800698110000c080000010400180001c180c40c0d8582e0001810341d44100001c000703460070003089005101c0203410206403885140c007004000c16107250b81c10311341c402030309941c01007003100c0500d406500040f9010030014645945442c0c0481943d005208041a40340010032180026007084070440469000d514001e0119508003099074801a249076001034150481d0a92a007081c0140c0343c0300c1407903000c0e508070700780454079000d010001041003400e02c800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 616846618 1250 616845368 616845379
    0xc040603050a0b04050a081819080718060306051e130f030c11030610081225050709020d0f111e090301140c070507050603010f0513061d090c 62
    0x810000d80c001510515240d0f0114209540395900c1c2800d9050010317945015201c000001915000c40c8400d5107082d005d407500b21851403240140c0344c12100f550950340540c2c185603129020500640301c0c080e0705039110300251200410220b44035507901c030640314252100307044a009100e40718481044d034070400d50720000d10161950001c596855103803490b07807188406403d21071243c4040d13047c40f0502c0507007503000714040c040318000d0612101c0d40c0e400f10b40c14401c0c0e01c65406412055a24106000201d6200c20b09081d41002402003d02982c019805600c0007160f00e4494007000003084490341c005082d5048168070001190b60318040d15409940c0350b01203560f401c500402c124201c042e2084446035585038a0603e664490401d4004240101100e001448a03a203003542001044c2007075000920b030003403044c3e0a5511069803501880602c5c0020b001c1e4410030351004038248000e0030140301c0c462003400e03040300100c1e1965486c000f413105003080f02c2200950121718010031a04410401480840034000d484 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 616847868 1250 616846618 616846631
    0x603081801170f0705041d01030506070f020c121516090501030209061b011d010f06060206010602060a0c031103090a0b0c041a03060325080f0d17062e020c04 69
    0xb944125014002c2c500c0c55079000f05000300c1d4105210b00151409481d01791219011041c02c148000301c0070702d007448125828407072100001c1c4894032a441d007181c0b01040d50014880031801c01d0400c02e45020352044040a840b500603134460f04001c890000d4000c6581800161048944007001403004400c1e03000141814010403600380e407a01c3e4401100c540300181211030289103a16003006000d84181412804004043c24504901c02c0040d0f001c8404030300f01d00e030700b080f09a50304c0c5c0c400c1c0e845010920400000d6001100010700d030f009143c00040a0032050320700060741752036035016000d554000390350302000c0f40e1011001c8010400070300304c0c60341c0050307805107640e00b000e01d41300c8400400fa0650100c0446803202101050807034604100100001d48007514220b8000407509840c0000400781c440e1a132030303109801c0b81c42e01034040441c25107400c00703680d9229421415041128070040c10702605047e0004141c40150070000701d2102d50321022601c075404c985d40040b088900a243c0501c18000c1d40c415882d121 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 616849118 1250 616847868 616847897
    0xb1f0206061017040c05040507181403120309070806010605070b0f060303030601050f0409020f092d04181a190203061f0504030602130315090510051005040603081801 73
    0x25181d0305a2820000380f524183d4540c034180d80402e22690001d0740080c10300c82031203160b81c0c0040f11a01e20840c0e584100100d540e56020380242d0f02601110590103070400807035030300c10090000045602c910803070103c50906980b102074030315200003688090002107010843c501003086501c0701d1900001c80e00000402c47c1407000000e80c0f00e10000c2c0c0074605118002070034054070042481620000c0c00d00040440d02c90a0b182c001880a40c8a540e100703104107001e0144005100701119210b01725190300b032205502d4130352103040c00300815801003a001b095070320003c00c170001040c10b41c1898038402954104c03015030800d007000180109800d00407009090041c410409240c50b500401410a070841d028008902c2c01ca4000351018450354001510040c000510550810009420101182d01c20825042100301801c003000c01c40d1200c9400918942014210540c4c100a42e0802900109000b05100eaa581d0700d50000e01164041d52048601e04804105041c010315280b00c5103901c00c8003030810028814418 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 616850368 1250 616849118 616849127
    0x40e0c1e03270c1215011203021c08040204050a0b040c020a050705030c0105190314010303030c18051f02190606080c060319181a0603070605161103010b1f02060610 72
    0x7605001c2c091540790050904010821200c8100135540d45e08801e513180c101c2c0800c0003084034001d801500c201d1600c0c80c8003460704102d04102c0003a907038401509498541c20000a001b014203101426609d85c403404d04550764901c2960f009102a40041213004ca4030324006040028aa1100c1c4c0309400041205125903041000c4a071182686020002002a1054290010142414034006261000c0c0000c8205909540030802a40090301d901155142d440b104203102403007405401c0d04645800f02c0740c030031211141d447c0c1ca0303074101500584002020084441242400290341550000d807202d4007007010a00c00d200c006000e14007542d03018554517110b01b07214401c0d141c60000740d64031542d40800c0a0f400c0210381c94603030141d40c004c00c00e2405079070904804007800c009494062003805803c00c0000e41e035029100b160035080c0c01c031511007880301180c1c40d22000f540c2e16072034139034240d500e9108210b02555070008680041c0d0b04869800f404900900009280c29030007024107002c2c0007280c0361201c8041c2c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 616851618 1250 616850368 616850383
    0xc0209011a04050d020d0501060602030c010e19060c0e0306070e090903090315070e03030307081f0f061d060f190e01201c020601081011040e0c1e0327 66
    0x1d13280c0034030311591031010640c141c0b2001d00140a95281170808111603a000c00204003070804040203000d900c011704500341d15600345c0c1c0c3d007052111010359111000070b511504624100c441c6030500314184400300010a0a04c0c400300c1d0341e0030006100941500309454203541454000c1c1403030000314240580717200401d40d220002904e0b000504200b9000800c40e0b44900c151042480e00607040d00d0303c0381004000a4030200e015110f95118490218070011003445440c180401c641d429103075050014501141903503542505010320001001c0f4885600c051b4590030000c1044e040400003440e920055141003198011800581504000e080001080c20360303130249290b14000c10900c400700c1152450450545000350b1944244405450088810142900850240c0c1250304000030396050807003048000b0115003d52001500e00c2109000600c483d520004169038440b40c0c5440365440d01189440088090000050414041b1800010056140310044030000e400d4002c4030698840b041034180e41e502c2c0c460 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 616852868 1250 616851618 616851629
    0x905011a040815190e011d060702120f160c620a1209050d06050c07080c10180803060f01200f0d0c0c0e130209070c0209011a04 56
    0x9403404a0303200071881d44213100f10f011800040100c0c1c440c00841501034106100301a02c0c2c100344500700506040301180b4907215200c2e60b40a8001500082e040016a030412195480048001d000c048080510551040c0406000382403102c1d8003807604d0071031000c00e04114065001da031507075010030b031200c1d03031400c1b0726807500b50171340d0b011003003265004141c2c800d604c40030400508410010848141c0850007085954001d8092503407041c14100000082e94100050300c2142d030000481c41d9908042030596024580101e54207502c00e1400c900c0d80c9500c4450340154a891150781c00c50301802d00c1c500103d120f4a000d01040c2803540e0b001c00707a162103184585c0402400a40a00140c0d00c4d8403440e68804d50f21215500c403d0a00c0a940f04512080c056544005104403900f520a1110134521a4058041000d405034084032200c0094100100c003061884041c0c0b52844d081c8298105000594414001d903104108a0390742c0c0440e00d01178010400010320603400300011154800d04401c812001800301c0301a0356 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 616854118 1250 616852868 616852903
    0x90a090b01050d0207140c060f070204150305060106080124050f0c01140a021e0702060702100c0501141f0506030a0b010c060606020606100306060e0d050a06060905011a0408 76
    0x10204005076801e2040300f8101000503c00542c0c002002035205d04140400c15000448040c40300c540244491442807019514480805101140041c50680c0000a204508220300010f6030390300d940d4140381c103600380c011031701003140c5800501c4075510300c2c10f011055a0954003428600c004860000d08a44500d01e8070007542c00d0001142c40345e10348250440140c044082c01040000d107011129400250070900728100e0b4120803080711400321150000f594500307a0000e03c401d00e06800e0f03030700f08020409420303101010f00c1300c80e210f4500494401e1250394003520b1071090030070342494035526622003410200d5040b00400a064802d110a0312450192940206985070004800d00c0d0440140c46032800c00000074256820300d0404200254041142d42c02507205a503c3c900c0c1040d00300c01a800d4030704601034500002d00d0503055600301d252003610440c4070383c01001070318142c00305a1611400c0d1200707604a20071407070719840100900818660044034444003004031604042c18140290345072105031007400c0406 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 616855368 1250 616854118 616854131
    0xd020d0801060f0f200c040b06040f0519030b04051006080f06040b070c0c080705040506090412030f1b08010f05120c06030618040302071a090d060c02011d0f060a02090a09 75
    0x742c0c0100528200150400301c0e0301140c4180f00c81c1744d55280b910401a6004030700b000350710040c6041000954040d00c2804040209840c01c00080c808c50650480302c04412036281200040810102040c0a008500510203040034030302c90303062002039031410750100078141d12881c102c1c1c2c28a000450020b42169105212000607281c1c8041280d48003400304d0064200c1480c0a000582010001071180031990306545c28003841d6580002c100d2282e4003250040e0604440407000399203684264003c0a88228030400019082000040040c8080094481c1d0000c138044400502915a034540542c0c0207100880d80540411000d443c00380d02c3d0228000360900440011010030700940c1c0e094502400120318400400e400c1c82c00f4100203544140d18172869900b00598041c80715a6120203044ad10b03880405410403030a49851b0391844c4c003d011240c0004115540c5040031186523130003042d0201d041100784024a0507242d1402c41604040e00502030f0b0000600c10400d0000540710320704c1240032240c0440001400303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 616856618 1250 616855368 616855397
    0x30d0f031b1206080a0203070e13200108090622150e0303070e010f0503190b09090d030b03060f06060a1727010501081b0d0506090d020d0801060f 64
    0x1512074503032010140c00303421010031251540300ca5519004081c1c000e0034010345545140c415120780c0440406909500a10310510000c0080c0104030f40050403038201c0651084142c03a02080c00001c201c82183c986160411010150391000c40c4c99041921100906140e0030a28098a202c4561b40301e0000e0a0880601030303c01d2041c0ca80c6d00e1807402c000310b08140a0400b007403e00903100d40c800c445d403e01207210070b2050701300355215003545038102c012074940c40d10395224150060120740099060060b466120b6111200c0c0e5100d4400300c40c000c4000d00010442d407140410003500b07440300c56150700e02035448501049419044000a55000181030b2412039407403048600407940f1a904150003404007400344240459201407a103044180185c00c00e046100200c9142c0180c2600e0003803194100b17540c8984201180042101c3d81040c80c144014040014400340355140c40c20400201d80c4900d80c0d070080741c074415003d40c06011092041c51240b4000100d5170420380c01510381c42844070f0000402c9003d1805451 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 616857868 1250 616856618 616856621
    0x10050703030b0a0e18031207050a090803120103110d02030d1e0c12140d091115070c17101b111903080a060905130c06020106060219021c030905030705090105030d0f03 73
    0x340711f2251840364602031101620552003207800d0f0b07000a145010028209001005030740312203d824008940903440c1d51592203078410fa040e03041d9405003e9450040041e41c3c00c01113201d103a030840e00c50908030061545408182103148101806000b0f0b0601108001056501100900c180c0b500300743c2c089548a05212076280107201000b8081c070b18249016041c44200800d0b100c0715030701200c000d08440040d0840380c0c0e190003402c80c010701c1c8141c800380c20300a89a1001905602d007200d0380842d9401c440307645868090392020500c103510301c2c02d8005130b0551036a00c4486255038804000080c224480c001074440341c0701c00c001901408010045020600101c20341d0840c10085c014241d040c0f026082c04504452000400d07401140d1141c444540011045d00600820003181c0031500030380380c500e22010052a81d551141030480c1e105075082245070003080001075030401c0902941d1846401c504140c241032604d446034102d140308015481c010440381d81c0000300007180c1a4503103080507409002401c250b0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 616859118 1250 616857868 616857877
    0x1509031502041716060c020f0409030e10050909101211060702120c0103052a0912070608150105070807111201181e0804030210020c10050703030b0a0e1803 68
    0x1190703590f03c0360300025926400100384101c0a10400c1d401140c990f55501541c20341d4102c2e400075042549010750690628041d40026500f9001c0c0c00d04444000d110b600189800c4141c0c80944040380001c034440809092008a1036489001c0101e0f4104450901009402d4050214001440034112030441e07121900e5131000d03242810b44c041c08075032104180c800500d85501c092b80f25507000a10b0480050b2035102100c110507449044c44144d4401d004440d461001e00d648403c0b07071241c00800540305103071102410041e04004151130b607504500c034140a02021846d4000105c5141000024001c00e80401c1c68002110f0100e540107894040349150203001c6451105102d0350007a042d481c2921125409081602d045001413040401d880080d107114410031f881c0c0b04c204405041904148010300c0107042296125500111500450300060750402c002442d03400802008000601c0100c1c042081503090b0040303814414040f0743d01150a818960307002402d1200601c2405e1215951190114040c8240f0484 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 616860368 1250 616859118 616859129
    0xa09290d0e030a03090b150a05040b01020316050c10030911010e01030b0307031b050307030f1101050d0e0319020105060112020f0403020406033503040b150d0b040c150903150204 78
    0x407a2120722918016008140048046d512412000c001078501c5800381e88000f020640140005041030900080c40000c3c2059901541544410048451205030852020a031184110004c00e0081035800c103002000703d030f10301e00606045c1408000d00001d0982e40301c144c00c0e01400e2a00344803175128007004030090805221040d4250086980200500142070300701c25103500e030780110a035281e54a2042c507540f2003c134480170301509070220510b00024001c40480c0b4444605150881c1004030b01080b80f41103070004110400a03034400a00c03007601c042100540115040780740002c0041d8544a4000380c810400b00303801110032580007411100142c42e401c15140519000b40c0200b09440c0c41e881c008209004210035040300d42142c0220608040d60780030b0004440700c900445509546999a03500075450001e819800200750725004440ea03511100e840004007400f071003254515003003c0c109861402d0443d08611034010360044082071130f54020318013004407948002d040031045020002c40c4028000d58014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 616861618 1250 616860368 616860373
    0x3090b03041b140d06020a0c140606031006120b04020112020f091c0c0603020310120807061406030d081012051f0603020f0609030f0d050a09290d0e 65
    0x38401800390a00c04081115001031144141d10f031900d0091030a00303400f40209500c88211044000095081d40151203443d0b0385085c80c0c20840302c26a00c0301451041295003011962001c02044600c0c6001c000310791074a100402c041040c0760820b400c3d180c1120081c1006003000c100b9502140031648110b229244800180070210f48503d0f0041c1624210350202c48154403a0840c1c3c18002c00c040d903d001d891040f10340c09040d03580240e24001069019400050000100b004010000104500c980e00e009502511950066a440119240ca842261204840300300c581004e0030400a4944001424400c00e000e10b060414007640d42c0354686100c200c084d00010b08003101104941c0810200181d1408050240b00d14007000d2034541800c1011036416101c0658450440e06890805081c503c0041509103000740680300035a8030b100209240003070001c10300000520014103451000e5000400308040e04898004075621004c3c500001084441405c08100614000401d030b1141011944100c142c0710b0300703806 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 616862868 1250 616861618 616861621
    0x4060209031e0d0e04050154052401200a03020604020a06080603070302130b21011d030a0318050a03020d09141e010e0d0b162a03090b03 60
    0x1021501c840208509401084d2600401d0003c0d15042c02618141e0344682d10b4240160544040c0000000810a000d000b1464001207031a0140d511a40042c00d8000300c180710740d500d1a0b00030404100c0d03030003c000f000c00d00080d1f103030302c44240c3c41c001c1e0300890080c003441e105903410500d60220b07641c10070b01e8001030700e20310684c00204200b5401044180c451802280c0103508075507a1340b000c0d5031000080f913400b945600154400c1c4010b140489a011101103044070009002d203411020a1902044192454154001120038042400240035004002c140c9040000c80a400a03800a680340182c402c00c40901d6114903010400010340b400110b00c141d00a0101c40590481c0c1c01c0c00394469480705034180004881860200b0904a45800d41c4002d000107040b20311302c0b9419043c034258a07803c220506041000c0c000020056682e030b885903210b07090251030285100d00740f9050050301140b100c2000c90078010541c4800c02d07074203ca40c0445d104400144100c00455001b894120f0340243e4640081107803840c040b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 616864118 1250 616862868 616862923
    0x6020307030213170f301902011505010905061602031924060510080411030a0525033f0302090f1f030e0f0d1101060515030406020903 59
    0x2101e01a80000c000d4130041c0e694400a90344500b07103180200f240c1b989080d19000034460402c07144000f00601c03000541400100741410704114426100003005070f4464103001c07140701c40d44201400400c2c003401d15800d4503143c40c000c11018011038540340001041c0c4c2c0c980c5415901c0034010b68001d51040e0480ca044207040703150905611217018101c0c201e048503140d40c16840c0d541403040c1030039918028a081820044e201d02199840b600400843d400180c444034400b41c3e4804000c0e10a50707030310405c0540542e02004500711882e002c17441070b000214032406001c0002ca08010703102d070001581580305000f09031070350b1038031110407840c2006510005140300c105100d0b0b69140c0c0c050103032a94201c0d100590300c03018100f000500c0001b10343c1078070078225103415288030500982c04a00c6207c400d10613105150401041541460b0f0003120b40e4000c168240e0200307007511001e00c6810081c207070864500380c1d03024280c0e034031143c13500009000804035a80010420910340d01013200c2c0b5040c404095500352451202c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 616865368 1250 616864118 616864139
    0x180d0810030f0b0f010506090d02040905070503010608030912030a080610050c060103060614041b110a05070306060602060c0c030703110c04110a0e03120d11070b011d07031806020307030213 83
    0xc48070004a244d440e000800c030b5281440866580e20802414100314407a203408001c0101103d0ac0101c0e8184039419002a80da2020300032140203105c074001840c0c6a85a14041c040ca11400c401c24000c03540040201105181d008510181c11190648090f00c0704202c02c0b009680358424040c0301c20161161400000400400790002c4080d02c3c2d0b0903e03090003081b1240309020036a000d41c1100200c10188041c5241c14034030602001d4a40004041180d09140711600ca5604091060300260b4416440d40000c1c8603c5404100982e007003015082c03990b15007488040941d032203000307807a030090402000108440035490100403910806030700401c10080d4105959428038540d00c04408000825804803407001d191a02294580c1c1224001041a290400d5081d03840b008100d510000380520030140001000704120103402030280058941b501e07103001d512030340c0720200503009101804050030000c3c4d0151185984086203501580036001603100e4440042c01e9010b07003d10b1094a5a01000384c00024000012 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 616866618 1250 616865368 616865371
    0x230c1608160606050616020609060708030f0a0b0d12142a0c01050405090a090305040b0c06010f0506071a09010204180b0f0f03030703050703031107030f08180d0810030f0b 75
    0x42d1100b00403a41da11014001c0d280a01d00a1380c100b0483c22021401608180005202d1904010b1400703150110075960704000d130300309031240082c40c1c0308202002070078072040c841ca25038030904541c541030f4081d040c1d5440e0884810035030301d4001c1080b4808400d0103074842e2000d8800081c480d02c640307680501107142c0034169035409400a28030380320742c021140055000d078003120107891016251022580d01e92a04402030044044100c003000410040010014100e10103802440c7c02c44c40039280340e51428949401090403074025507c074400070010400007032200d607034a0120500364034214102d40d480034041b5009008540c45031030901d4040281c407000c2241c0c0e9000d8210700c481100e058840c24541c80030700c20006181860190964020000300300030074003c03400351420500c680b8000c1032a084a8135200101c1c0c1000c1c00c103c000c84e003042c0b954544035800c40310a6502c010304e40103202c06500c0d09221144d8542c40510744200344444c40022490144034074001e44003a50700000034440740100741c43c00302c50a40c3c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 616867868 1250 616866618 616866623
    0x303040302100f1e0c06020903250e1005011d04060b030711010f050103050a14011e0606080f04050304121403030925050915060d05071101230c160816 66
    0x7908052024080b50303c0a0360104e40d02c040e5620000102103030b403001c2c02940403900855140c032504e40408000c508480a441c002c4040da42c810983e01d1810824005000d00500502440750580005219990f03000b1075414200d840d01c02580603940d82c10000c5001003405800099504070f0000070460400d400001030303480d00320184002c1040e004101e0800d000c58100703002c018440e401500069000c21544c0055050380c41d01c200c00010140c84140c0c401c00380c801001002c2c4441500c0d01003c000d5250000702c810303440310064580700c03003d280c665603e64880c8528041c0c040c40c00e1350811807005000c03060200007001e102c0401101c0e40c900b410f010071955403000c0000f00d048020909540e200344009407000c0002c07114060070f1003003941c9070304c185007012082200d0034980014090001a050548078041c050181c54552130700d0066403103200e502800e559420000c0c060908010b401e846d8810300401006601c45040710b18162281c41c80741c44c0358034a5401080142c50307548003185400781003d42c06040c0c5003052 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 616869118 1250 616867868 616867877
    0xa091505070908010b0901050105130905040c050901090b0a0b1305060d050105031e0a03050f091c0302010501050f150d0e03211602030909150d0c090b06090901140303040302100f 78
    0x20350354041c4500780e580342d0102d1071b04905000010403031940900040c0455408844001e080183c0740d0340c802c400c4030011101546c210360124010015824202822800341c040100d05112900248011816606561282510003000056143c0c245441c1d18102d9014020040c46103645d010061035101c00b400382800362510a000700141011a2440c0619030001c0d06e5000b0041d02c0280e0b06034130300f55407075080307449001d980840402500a1a40c2d508000701c07201040e01d442c80e001d00c0840d050017821544140c010501501c81e25940c00125951a00b081c420f0400c003148050ba80c0441c10002c2c4080d104044002c0e07010301c40492228041c43d0018440c00c200c07200c0c1c51241c401c90b40d400c4c0442041c00c59000360400940c00810440405060108950364400302e040884030f0070741064030109415195548040d2401c030481442445a41e40c20700500368020421580e460406501c2000903e1703401040c0b2400a0700c500f1040030035010303207050042d500250b400420412441d0b5800a0140048000480040004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 616870368 1250 616869118 616869137
    0x3040902030a0e06041226190e010b061608090a03080a0e0306070e0d050f0f160f050108130f0203100501090f050f0118020415090501020709020a0212030a09150507 72
    0x83c80002007041c462a0090b240c1000e581c403103642079403080e096000070b080c15804c06051250840b99850000e0041c24600c0103009035503800b50010702215070071100499941d0401603483c20303550340d07002502e42c40b0720f1903080541881214038120001d4411150040d8120202c002c0c0001880b000c04054081c1c1180350300c4841030480e00108054958204948000129103125100a464140406907091a602c1503084070b28900300000310514110f407215003091740f94007260b088030f94401c1c4807030068014030180d0030500d00b850821002030f002803002404001802c1020bd072060078041e816051180d01900981036428100365008458050032007405087c9903c0e04100120002c00c0c0c46100300c2e8410001080c2041469023800c0751003005508031305c04809034076000e00c80480c4280411140401d0f0400584843c0c110514040c00641004070682c4900038240c414092680c0194010901d01400c0c019070385030541d40c3c1c0d5000d80d100d000b400051006031403280e0100305d02a4000c41c1c0e50145005501a44400c20030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 616871618 1250 616870368 616870391
    0x1f3e0d02010207020919180606080d1e0e0102031c290307050114360111030a0305040c15031401090b031b0307030b15040507091211010504050303040902030a 69
    0x203034841d0210081d04a81000d0010360500c1c132540d60703480c000c0703c04540404c0c02540c2c07007c2c41c1c58002000304169220b90fa0b980c0c0030803c0e00f800300b0112509010a040901c0603a0001d91a81082003100300d05000f4084007501040f150b030310a1041322408081c0d002144a20365083d0011402007802052918201003a4030300c0032a03458103031260384a03421004000300003903800c0c28011a46080d0715562411503900c248226142204440483d0520b600b2001500781420b10420b044000c0750803908016041c044030411a9217490800700403035540c540c4038100820946c8451408048281840d0b1015980540807a55003101c55070540100f112242c1e043e90126403640c8070610720044611901c5420341c90703404070b00960503084000745c50b504500d900130b0603904580d580340c40341496003004a17810560441d6040c000b03086490300d0701c2601d402090303034548441514201456074048094550b405050504445c5000146a00c00c030f007220050b08015090307940792aa10b0701c180019400c1581e20341011360814414185 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 616872868 1250 616871618 616871621
    0x31b0307030e0d050c1e1603050a0209060f0915012c030601050301020a090e04150e07030b0f130b09340503011406010503090304030f030c0201020c1f3e0d0201 70
    0x1003401c17848080c00b0705c0c04049042c1400c01c0d030805405990b502a10320481e0381c40c00789414550046010f1030140c510645a403040041082e0028501486500241c024110a0b1549481c50398480c5110603008012056a00161144602c09072000500442480d505101c100c0038414a22000d50680440c2e400d41d0301d400c1014242d000d20100b860024503101010092001501022908203029070307c2c41c580f2090b50954082078607003482504985502c450000c1080080c0201d586070b106040810385140c90400c2100d00da9809202d0740c0c0603210700c40320300215802c8030302072200c400a440e02d540340c02a0382a00e424101c100b0206111030802001c1d601800090904041c01540e0f946c0d40c8031400840c0590b00d003030040d906900050030301c01003032000780301c003000250109980c02c0c40c01d80240c55401b00c69030b1603c002032600c181050f0031801a144500c4c10318888d1440c076825400d640303e5046c40b01e4103140106218210f0352a0311000720241d1341800e6000c0000c60510110140700c0d034400d003640d22500c81458241d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 616874118 1250 616872868 616872877
    0x16060b0307032006130f15050304023115080d02030301141c0803130b180703030e01030f150806010e0c040909020609060a120b03010b0d0206031b0307030e0d05 70
    0x1003098106201c0c5900c280024500345043c0c0b07034000c2841c4d08040c150764941e0b41154003508225442900071600b030200343c0341045030308141c2c001403800c64610300c0c3c0f0b0360104400c032a202c1c002c140c80d010500c00000d000c41c0d1512500d4900000404104844001c4001c6089260b055110310055070186008a030500e034404002c6074180c03412240031882500b0b00c4c2c42030029140520403a102400c01c88401d400002340042d00541c01081082d401e030540000c1824440700c28000079081c495a4240540b650203118404a940800c403034060030840d0851014030010f0b03000d41600034681117a2031400f0300b04460034440203202400d440c0e40d80704880c02c5a8036121081455038099904503860f110900c010405044150400c1c00c41c076102034850750900042ca40896000c3e08024446004075074103000c024541312040c0b1640e00c18081c2200288060800b020210301c4440d00b100d0b01a004100010003c3e01440c036401c90b82c003000395928a01552031030240f10040050801d5031043c10103009103038040120511480075034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 616875368 1250 616874118 616874123
    0x150609090803180312071d040e0604021e0a080106090c030209150d060308030108010504050c1f230c030c0d0f1e18080f0106120f02060c0a0816060b030703 68
    0x4902c1c54032981c10500c0340c586200b4854225120070003105240843c120740a83c09011035440d00c0c0001c95403a0581d200060f0020480c1d80141d00d890034844040b1780c0000c00715005078044e28a12101c8441084480301c643c1c01d814030607004904100f00103080101540320320102c2d86203031401c020280e0107000450907446400866035001580020a61920b0365100040c00541d090f52130000d0041d076650380300401c41e003090303005013401d9564804001c14000180b10140d00c80608545a070810707240c061801c0008040c3c0ca04240c1004060200d200514a950510140701796800e21101d80302c4010800f4255aa84094104441c50040b0b100401c0814028425280219801d440700045c076002c1442000304403400719a80410003401d8080d40845014600b101b401400b81d501c0a008001500001c160940e6030641c0000a100003104c4200d010400020344d503003505504075201d076502c1020a4826180224694010702000c0c0c0009420852000a04a504105211324400d02c0110f442c40c040648400a61001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 616876618 1250 616875368 616875383
    0x50904080306100203090d030e130c08150406081b01091401020703060902010e3705130b06040f0e04210c0b0a090b0903040f08030301060c0303020d1815060909 70
    0x100b4500e01e0141c0c1e0005221841c1c1c0f04407810f080c84a00007070205030320080d00b030700802e030038403c414050705000d10301c4608151040c01c00c3c40f02c0081d14600610012000701402c2840c03005401c6e5902c6550307607410a500429801d01214200b48017108844504000c400c0440d0103d0084400041d03108081040c2c00c201440507006808803501d1a2590005850281800c90400c20548044005030703540741d4111005d031103000500c82c0d81807024015410311a2400902c810041d0010314200031036520b50013002c1e100d0060840201d002403801002c200c250003640c00130001d01c80510004602240c8100300715118600405850b00c5039143c07050040e012003848042c11000840820301840403840780c04c60181c00035403803040014590348503203a2401d800002d07161404560030000e004c1240718003081c0140c01034616500518599454072070050101403403c0e100509040d0007140188052100e50320107007243c40b400c00030400317440c12480e121200c0001c02c4200d80900e80f40c0303407000c07500c0c030504c0c440d40005590000c1c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 616877868 1250 616876618 616876621
    0x5010f03081801110a140c010513210506090102090102100b01050307230418050109050c070605041b0b09090c391509010c05030402011d010903060e0a0b010509040803 73
    0x205900d0103040410503c1c103000c114440106403640403c461904180181c0c1301c3e035581c800c2d00e0f0702a81400410b516090401905000c81600486400303106400c0705c1c0102c9006018900d04075010a0590302a980940f0600a0300108080601c0c1900105144c0000346e0a913003d0102d00d41d0b00c80d085810300d12000e8002001800000d190b14020301c1d208600e100d0300c0b0405801440a00d0b001e807070a600c140c000d12502c8200100c1640c100e0380901071640900304084042c40b4604c0c000706503051500a6110140003180c945c0041400d0100d013642481082c81750500c8030b802d9507200c40401d07103540e00902d8054040d4005000007842e940303841080d00c914183d9003410076800741c803040800525810312070300c03119040d000f0030b12800c10030010480184000220b80444106180000d600b40c01c40702c0040c0010103003d030801c2003000507a0b200c801c40d06d030451082c026040840340000102ca4180c05500f00414043c541000500085000202031010f58440e041c52805607032a8424081d000304181c5004140714030a00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 616879118 1250 616877868 616877887
    0x14130b0312070b0f280504050f07080c0103150305190f021e030607030c0206060f0303090603180709020403030212031f0807180603080d0b0d060f090b0a0507020705040b011407140105010f0308 84
    0x2001076070428090360482d18156441d509c01030070040070340d01002e140c1d844501d030312502d541c15000d60910034201e0724500f98054a141c680d5611804042550000c8805ca18140310800000b01140701c0e82340e40103080c4014202030340180032031008044590300e101b841080001040103200b405000c500ca200c41d4040d0000d0b89600050112a01e003400c08554140018044461a900c130007028511944424a41000c2c00601805040c140a4103821a814290041000b1b2001c207130009034030010000d4140c0116603960ba0954a09011082c0c0c080c0c402089101541c00078441302c0000c2d9060541d070b00001c00c0d03170745941031490001c22140e182c4802808400c0034004418204891751012000c810080d0a40c12103c0b0203540d84000c1300c2e880c0da6116400c554810f001c0c018424940380fa0340d880b6401400030003060921550195540f0003e200c0d85100310344400700910300307034415030742000080224803105854100758503101c002520401c40c998203d40c070b0100006402254440d114040302e401400b503e15080151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 616880368 1250 616879118 616879121
    0xd0c0b0703091e06061212261302030105010f08070b13080a06090c0e22110402070c05090601023f04060309030914130b0312070b0f28 59
    0x5200c8000d0541d10088200402d2041c82198a000303204100702c1466282c900c0c0210846102d0b400030710440300703880e00102c000f9081c2803080004480e04d0510901c0345082c080210f1010b214a02d807403c0e542503150900c203e80c82484045a0712a04c200c00030300c440d80e00d413048800710a130300307200e54071807640312810810244250200a007a210210081c1c0158640c88580c10780c41e20140f100b007101d40c2592040d00c502072015076089480580b41d816254072003420701403809102d440c03080745445c0001c00304019038070400c82054840d110900e40644190344a02c640d04044030f03005043d1040c3c034040d4440600003a2150f20104003404801050039040f0704800c210307079000890300d040300035008040c3c40300505500c4501c0715501a100805841e034021070071009034900240145481d500000707208402164407611540d60829180c90541041070004414402c403001038980006404a051802400101c40041c044480c02d41031140f11482143c0c125500e03030b03692440212542140344c28603a144e0288004652074107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 616881618 1250 616880368 616880371
    0x120702040b100206010e22110a030b070e030c04020c1c09030f23061006050a03090206070b070f02060f0708091e030d060506070c03110111030a050307110d0c0b 70
    0x36000296000c0c00002081d01160803800740030160f0f2055004021002640010560001c01c901080f0944c0b20031002c1c001805440340001400c0d48204003042070240c03500369103c001980c01c14001a21400c15941c0a010303090080c2541c1d0113405451488103c1e41418001c03100c04030800002090000d448050304401900b050501c901005001c0400001064844441c01038007401142010785210342d80000345d44d03c442000c003821960b0040010440c07402c5250409000300c410030308090b0b43c1d52085c81401c400410724194005d50160011903410f091000e0b070900d1620401d0503840e012400f411741c100503039503a00c04640322100411105c0010300b1035480380e11210340024100341110140d421115419603160540041d100b01d41c0c4c00440d8110207140140190401040b0136074503a840c1c038489440302c0d0411003040c0009090305890080401c80b59100c1c20003000c00911a0003501d48504c0042002041a481610400d0010b00710a10840c0925000314103900e1108803910307004000440c5a5600300c0b031000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 616882868 1250 616881618 616881623
    0x60f050a0509040b040f0b0109020306010306140108070807020316050705030c0d080306220e0606031204030206550504050609042a11071502030d09060213030303091104020c1207 78
    0x100300c946c680050b81c540c031810301074540200003507103d180c01b400040c00c89400354030408910521030081c6c01644d802c0300c0c1395900074116151108090f515940181c1c910f1007030300800502050100c0d28402400004516017060351011030a64101400090400c605001191009000d022080000c9420352400205030b903450880884456810401c005108044505400c500742c0150000c008026061a040c000d40900b43e00741c400b480e04160854003c07541c0c50150b001c0c40315105a01c4003140713008102e18420003504014072020301480301c950f4842e600341d020382044107015540d03c800d81f045d04c9602a4094800b81d6a0140c1250f0801f600602004050484400d144120021b50b484801c0b2088581c0405134420010392906018074100306803c80c54009940e100203040c4000c074800c1130300c43c3e60210844074040d034844008240b6540d01d0500800038810380c5424001a0380d0f181c400000c041d0550000000f1500980c841080d50302c81000b031100313034400c4000102180d00310341c204080b0030880d280500003090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 616884118 1250 616882868 616882883
    0xe09160b0c01090611130b0a020d031d0a0305070b060303030c07020103050403030908043804030b04110a090f05090a0201050904091403070c030b13020d080705011e060f050a0509040b04 81
    0x803000d4a4107411254a155110100c2400142400d03806d0300e06902000188081c0340c40d0791416080c54402912000412a807400301600c1d40c001c4d0958503061511902380c0c19148042c0c843c180281e20300581359602c40b61040b10551880400504149008000c3e00d2140e880203007207078a456400c1c0d00460003410018011010305030f80700e51741000314036200b000d400036218224040031b43c1450003203c0d40c1e4800f91002c4412214000030303005810341542600382d404507130780403080e1075494450f464120241846004125041040c04500140010303054110240361200c03408100000c0c0c0f164104940c80b8085000d001c2d000c0f550800030014542080d6200c0440b641c02010b01030240030a030740720346043d03601c03184d03040c1c500c42490f02013482480403030a00b841c3c002840c074107050000c1485a0210b03490301001c1001801440f0045040000e0003029000f50503000580381d8040401140304002400500340c074007860741030070300b81d540104050600301070501c00c1d41c1c002400ca035a40c0d40e031543c0300101c5100041c021510389 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 616885368 1250 616884118 616884131
    0x50c1501080c01031d0604080904060504051302040b0a0305150601031d0d050a020a0606090b040c181512020706060f0b040e1308040803070305040e060612060f0105160b010e09160b0c01 81
    0x60030130b003c1c1b00d01617841011000e5603965604c00304000e480c240d8002610984c075141c10300c070704c0c0e41c00300440c0d8606917810341d00171511101c40c10004510040c540c0c0042c0503400b030009440c0f25001c142101c0c910800c400d0328104901c08000000b600c155200c0c000c840419802003030030340c3c4070030b0140c2c000d0110301c442881190040019952000107440c81c642c81602e88a84503205900c0ca4581350195040304a11442c00d030700403000c0e441080c0360302e0649215903410881116480e0754210310544a00c1c808081100c800c0d0341d1340e0682d151800062100b4881c112484110342400b085403c64141190202c0c0e03400d041c070b03001c0394903010b8001c0101c4040c250f00312902041007100044c0304c0d00601c080d21045000351121350711140303010141c001d003403c0288520311692040110f014014880410311f500200d0684030200c00313003034210041e01d4a10454425000c81002e0b44120020402e904070306d913040e513400e004008103580747c85820755500c009800c8940802e02003508148003103070611004d412901e800c00004541c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 616886618 1250 616885368 616885421
    0x70e13110418151d210f032a3a0c081f0b030c07020d1b061103040e010605030a0f0c03090302011b020c01120608030a050c1501080c0103 60
    0x65010b5024211000c032128000140003007401d1140b0060318582a4105220b403410685207902c1d40080130040703881c03140c002c200035540d005440590b8088a401103580781c1e80e013010071903001801803800c000907600114a40102c00b440c40001510388801148a140785012300ba0030036a1200d01d1070f0309074500b0241e01c404070f02c9084031282c0103400d200714142d16440c10904289940d000e425200140300178580b61010340401c450100d9108903a071052403071a613143c451245100284203420004c00250041e03900c0038022591402144d0040c0c115100390310350440460440c072000c0d440340264070410060074000c00c0104450b501076001190301c0300c01040d00054a0107906065000c44040d0300c0190002030b622402d882c2010340901c140318150100c2505000151464240250b0b554030600040741000002901252044011340056025240400580ea107660103484014603d80200c0e1100c0044e1041520103280b90007a401c1c140c1c16035550201500c0b120b0341410042d0050180e01c13041084020351000fa1556 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 616887868 1250 616886618 616886651
    0x3021f030209040f050f010e01050a030816060606111e0604020f0619031d01020c0d0e1503092401060903080a090302210d03021810021203010e09070e131104 69
    0x10705013112a0000e82400c0010760148440c00581298480d4003145005212551f0f43c100e000c0b0840364081c446603940c1c1900d000c160401c490624000345080d00307203807010030340c0c42d044200403c20628040441d100110903441e403482d41a08213020a08540124001c42c0c09030410031480090254082e20301c6140c40d10b1814007140c000303038040144002039551003500d0038404642030b00700d040c03184040003581000c0d121110760f0348602d08125000c1c14090007985802d0a51200105410307401c2403102c40a031285080001151108040e00d0040c40711224100f010038982c9540782454169202581c1348212282540c3e900c1d803c5074060030104043c4440703060008010f95414210300c0c1d03c1181c000d0b4100c003203031040400c40d28161403040343c00c0034180140188460850003101c2014008002c80c0c200d0b8001c806c0c01010b85c14034481e08200400401c000001007034103290f50150600480407402290b000d00d0b92608003560407082503c00140d859030703c15008011940b00e01c3c030308403051402440080c0018802c518001d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 616889118 1250 616887868 616887881
    0x1407030c0902040807050906010f0c020a1d090c100207140a05040507050c060c18061308011107110114070209041a01090b03010e060103050c0d08040e0408040e1003021f03020904 78
    0x307500c1c80c1c00203810b2064180c1445104020103083d03d2002a50600c0b400180043c2d141020340c00803ca02d2178014010356517000c5160005290490110003546181d5111900081c0110b4001a00d4461103036a05514100244c4441d178010303442c2d016141140c20700b5a12030500804410711640140c1e030f4040800d66558034450340340100d00396107507560790b40606020b05041c0140105005200c410510035038410491f444203a03241d50130103c42d03582c2c1c0c501600d1001e0300101c241ea0042d205d598642442640d8200c241b030020b00700e00380030b80a0100c5598850b001100c00b5505a580c3c440d4001e418842c01e001814030b000b000341c006100e0300104014401c43d0b0b0500034109003d81c0502c85181e1110080f100301c3c1000c1c4104d161201c0c160019180c80c1d81076803103441e034a140648085002d41100078540b828401c02600342d4020b8000e10041c91035605190030024100d80180c01010780038100c1c000413500c04560020750404882c0d000c0d0500008004191200806084001e080d000707254080006071a150b80f140300d003d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 616890368 1250 616889118 616889129
    0xe0f1608100911071209080706032a0e01080c0301180914101d06100e06010c0606060c030f030c0c1101090e0a0603170a0206150a0e040f050c06161407030c 68
    0x40d610350001d820800d4404107180715020074003200106c10301641002182d103006842d110f080203c0c101e1081c14002e1054801c8100711141809004c40e180032444d4451195080301e0802d98a0010036110a441403107944001e01c0783c5005a01000740300641b0307906540000180e40e00034200c51740c902580154131410304002201c80006c00344e4903240001e104030382460440c0f004008800820581c07603c0703254210a80c185002d40d40c00f6108078000103015a2140c041c4580f0316610100c01d00c0800c1d0f42d0f42c005003e412115a084006c94143e40301c00300a24800d104064020700a91f60b003d41d03c40e05d81c0c5843c44840152030b0750740d0420041c1c103800706a1844525456001e02211030f00004c030036285040072200380280c0c06091004a20400501440c0c42c2c0c0000c0c01074005400c0c04600140c041d0f020009000c040303183d0311600c10908000e04100501c0701d0b100b1281200c50180099840c000c01c0703441040350074403480035a58040f0300040d040f000415104100d02c80306418075800c03034101301d440e600d407060f040d260b81c1d000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 616891618 1250 616890368 616890401
    0x903080a110d020708100207060603140c130209010206190e010204060216060908100509010204170105070e010e060f0c010b062a0c010c0f0221070e0f16081009 70
    0x2404050402002421441c098503c00b07807651030309002c20f05444200300222004460b4000c01c4203000d122a40e0700000046611402c07a4000c2d0b40e000c00a43e0f1509001d0310103034813500060007042005203d50003181d40550050340900120740c1c642c140d40e0883c6006403d0304034542c1d5160a10095082d0900c0184094800c640007401003000c4840003241e06d00f400e420500400c019003804004944c400038510380c0a140d005804515660351204281c02030049034065401009070001c5281000010741c00340c1d01844c1c40b076031814514140a4019134110824020050700302004224066000880300702512811491400214040d2203010000d6503540100d003402112080a090541160424005945141e054030001c0d0a81e41c0b48480068071901c14400b01034450412080c480c801c6588512400c008400090040d4111034442c4c0d041aaa440f010300451034028a102c0200c1c5500c290480c10354414407803050421107911031b4000840313100d20b0251403105840784e206000300740540f40b8040c11908002000c107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 616892868 1250 616891618 616891637
    0x21215131b0f0b0f0c010906020a08060a0605030a1a030109051c0305060904030516020301111b070302150705070b03040503031501260c0d0e0c040e030a0f0804030903080a 75
    0x6004403031442a00032001000d034000410082c640141400c0000c450b104034070580c881c01c0301201c0341c00910032404036043c0c40d440c0a036220b0030007419601806a2440ea43d8030b400c41130352168140040d95425010700004504240700044804815030441c815000300808149180103490f00400d0950b40790010864040d0407650781d00c440b1022103404e041800e00140b506105500300500440c000c400c1c090806001c00c50b0000c2c4030b0008170701e1003041014145e400781c000c202681e150080010f10360000050660300c40821486680c071000c000902000340c03a0000c0081ca03580340c030348003030090581c04604110f40300c2c0960080051944002e1001d948101e0040c4055580c0c1e1030b04031468041c0b0b0454001c200d0502400c9070303c4c40c00080b03440c0b80001d5600b400004a07102521071000720340d61805140c440020345424408800c0021201049151091030107407000e0104070402c0c9101502c0303004000c2090005503408809044142c852202160024080d00f090209592243c0f03840c045540b0010803003001c1900ba90 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 616894118 1250 616892868 616892873
    0x711100c021917030c0c0d090f0524030a060e09010e0705120c010c110415050a091e050a0908070b0403081b181f0809010c08011202121513 61
    0x8502005280b2818032110540d04a41e90103202d03d14214050040041c08000190000502c000b101c02030881103086a03004400344400416010150084000c9000505000519400d02c8100c48851644c04011058100c503d4540c20812790402030101d88461745912001450700c001c603122034025005c6800100d0941d503200b000901d4030705540d1119001d000d40c1414000c81a02c003040c00c041c000000d01c0c1461660700d46040c0721a590b00f640a00c184c0c0170386480750800031032016504c03200c1142c4041d9103c540307031552280d007001122101c0c0450101d0701c50003404550301c18440e0348941e9101e140d40d100082c600c1a2030321846c003144c100c5502101c48684034028442810f410040c0720341c1c090306606080803014602000030009014462104654501045028403c3e51f00d054002c8400c840900900c107150014600c000e2010000381d5803c6c000303518010507160120f101341c060078143c40090f2040c98500080e0b42c00d10140720042502c0e40900d00848000d40315618002003618040c031864180c0d429100704c5030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 616895368 1250 616894118 616894123
    0x1a031e070c0c08060f01050d1506060c03091d0c0a020109080324030606031c0306050603090a2f12010b040e01050603281205120106031406010e03150711100c02 70
    0xe4005800310790200c420842240007900050b1b0542e082900d02581705e50340b910748589801940c04525800c1e500340f500104e01130340d2050070f980125010342d45030f600003590780351032540903140303040003000d121401c900007815402c01200a0224003014400010004040d4030303540002c1c4c10544d400c541880b0b1002c0e0a607040c00c04816203011401c0d04a0184c0441e003806070009507600c4401e855252040b800c450b000301d03211302951014004000c05018540c0c1c074504907400c2c5031114400d41c002c541c1855840c6c2440c200c40300e8522111094078a030140204099a050704201342d400007850681f80ca5901c40d050450b582e152401814142d02400700041924200902014140380d048249024282901d038a54620381103410400e40e040ea8200e003c41107400b14000d401c6407588106e0781c0280031840780b4800010510b906500c402c5903c036418a1000c820b0300c40100456140100030300d603544c50340c000808001c14092200640390000090704002a940550114850800710304400e108926035494480d0b2070040d130103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 616896618 1250 616895368 616895393
    0x20a1505090601091a0603040609030f0c03050703140415030e1009030c021314040506091605030618010209030a1406070e0a0b1c0f0c181a031e070c 65
    0x465205000da0714160800540d1204144550102a520750600c0c5185030010742e0054242840684000e80d04c0c50282004005041074100440c0000c000495500c8894810390b03000070610352540d516487c0442c036480071110403215000d04c9000ca80c08220000d405d42055031402c400b062151008114100380050450412040e443c900b01500d08040c028400031394004481703049a036044030700044c854500c0c010700000b000c148a44c912411308141c1808140310001034010b04c582c00c1803040b2203420403d90a040c01d02007080c8181a0568850004601589400000e010a40898600050408640e9070009190500e0030005031904143c000e5a07032a0000207201943d403005c100e082900f0f841c150080810380900712445211946440030440c2804000b014084c0e1024402100d0240000034030415541d004000603c500008503020b034140c960400345441280382190344901c0c4856144c04c036a00380f1a850f502c0102001420507404080c403800340c208046942c05140c9995075088280081d00d02111101c55 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 616897868 1250 616896618 616896653
    0x312050c0a020304170304030b0106122d0c03090510090c0509100b070c0b03010f050f0d0b220203010905060105031207020d0312091a19051b0901110d020a 68
    0x420a0301e12a54000084600b1207008400507a4040c44001d10b0a0450095070801050846107100000e0003a038000400c82c00c2110445040140c03110200d034480e0030301c0700748500031082441c150000b078070305915510a0400f87c849080204140c0f00703a94030b072410b156810741c4031201c1550380d400810074000b012054101401080d500c510590400b00100840038600e4802e580d02c120001402e00200034200c14040c00030706443c3c0c0b19540342e50319039605804101e01ca00441d8002c0e181d003c12405d05140590040d41f11603048200281d0f02d86903c21b9400c12034040c0c800d040e10341c035903020100300142c6092040010140c001d031301400c100d50401e02014103200e042e0b4541c0009280c14440800985c2c3d4030120f4440b03143c3d160410351061491141ea401c040c15514202920004000c042c035000992402030301d43c40f40d1075400c0100307648007444504608988040d9030010203680c51f4003e25580410240041c40303a820141000400000e90744419442d001d0303101102001a040f503424902000841c0200c080c0360300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 616899118 1250 616897868 616897891
    0x90605031e1e06070908010501211403190e2403131a161403070302090a03150c14120105150906030a200a0e0907110d0207170708070303110102120103031205 69
    0x14503054800c1001024031000ac980d905111180d40b007000140301c441c041e10f88009003582c0c4c1f10b02d880c4130428080b0300c0c1ca400320350100d0182d015216031850a20065402440800001d4142c64503148001c4025000184002542c51b03150b1641c40c0843c09411050b056204c440d142c1d400c0e2490459241603140b959540b48200340819a20302d001c02c88a801e05580e4850700300d240040c2c075000c41000240d41a226540060207050050341c64808503c1345030031100c601442510f4091030340f15090759141c840e00c5104d00b030501040c0c5140041c0030358900038003102810419004003c2c189200b41c400100161310640b004640d07150349c0d00b00340244002d1120030043d4441c4915101381004100b110182c681d810310029244a0002c800c0060071150107504400210110b1340219104620901700281d50344500380540782008041082400040720006549000c3d1000c400141084510356981030f01c000c4900f500c1c0315180d540901a20300e48105980c00c4a0080d80a80c1e90300703948401040000d021204090700b0010044c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616900368 1250 616899118 616899121
    0x1050703080a09031b03121508032b020c2808181f030c1101060f0605030403030e100911090105031b030106080304090c0207090605031e1e060709080105 67
    0x81d07000701100354805805000401e4440c550300d4100e40402c00c07422409125401d140702607080c035900450403800403803005403c1128800e0040003103074040103845800744075802000a010300c4015000c0d4440b00c00c1c41d405031034412910700348480040c0d030000c3c8403540380caa00c101c0c214896010001c00c0400b000f202254000000b02050301e854803184a03c0055500c1404400390031801e0f0384412402542040c040d41e20100076181d03c80780100a0711280c05182d000401e5074032400741c09c0c601031240c0401c50300c1d046560380303001d8a400c006a419400040041d005e00d03544541d60855014140221b01010031129030010340242140b07880d03d103880d8280b0744c2e68010b02c1c1c00c0b0014041500c1c001801500d03a03422000c070001ca0029a00000d024103043c0d0440d080c58000418002003c400c1d40e040302550304000e40a0701c560300c2d250300210b070444da000d104107070b4103500540303680440122024100014500d00400e03609a143d00c1c2da41d00304e541c00102c0001c607607a0f1000003006070b441d82c00401c1c04083d02140d4001d0046 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616901618 1250 616900368 616900373
    0x2070605040b0f0903100f0f0b01090f0603050907150e0901060c05060406020306041509051b030702210904140406050903070c03060c020c1e0301060e06010507060e010e0109080414010507 82
    0x60340140085a100d601e00011340d81d010b0390f4200144a0304024400742030180072041c0344040082c0040080b080241d070305029030031700c6640c0a01c0c0c110060350301000c072420340a03182102c2100a0300b0050003060040c0203081b0301040b50401a5080024a01c541d12424003400078141800802603051707020604009002480c0c0c0d00045002c01d2154100e43c02140c05602d940f255000034008003207a12510803030350705426001030b14010b907030010303032244040c543c0d140d000c0c10004d01e80d0302d498030040b41d603003005820141c0900e0035081800c040c18040c44c080e092003403c11586001003400c03035464101e0180102091010041003189602403d544400c3c10030196050516540c0c1c0d40c02c1ca40d40c18000100700c3d5423108501c1e88281d108006400440000130180d401441c0c02184990041d4003010301c1c0c3e400382d400e1031000305e483d0340000b0300640241010380d212454400e1686030840104668914a6495501c031000c603210700703400740180b80070355000e5040c03140da480ca000b01a80d48120f2000f4490306000041c003a0002 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616902868 1250 616901618 616901639
    0x1e0a0203041e03021002160501050633070c091d0106080c1c0f03051c0515012001020d0f0b0a06020c1201060308030109141f06030e0111190207060504 66
    0x1d0b51400400e281c00d076088030789800e0b8107164800c288242194400b007801c0c0719000d542e0070781c0f03c0e881d4007850080095443e204203001507000c110300070380340038854440f260300b401d2564400c0c01c15103013903110910308020880e6076a49684480d54007040b01140c903000001e010342c5602d400c1441c40c1400034020081c191a1801d110744908060b85064803603a4034040701801010303e4110550860b50000a110703503850a031a014100740c2103090701d0314800e0170300c540c2400703805c0c071512956002e0180f454602e003031132410328011034450501c00000c40d80d080700e200d008a082c0b00c00340098608035900c0b072000700e030400c54851804200c41149502c0c52241c03011725802c019250f004181e6002000050790f00710524242c071010700c1c1c003500069000408011001000117030b881c00317640c407000d1481d2603803034415800c0c1c50380d20b03c000440400c00c1c0c41e52404080200200710180c040d9100c81550305e042d40c000b0915890300106000300b034110020a03803001418602c40203201e03905000c1c101c0074080740d051071030503c0c1c28229040c0b03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616904118 1250 616902868 616902893
    0x12050717090706120c02070306060308030115050408030915192a0c05010302030603071a0a08061f03020912011b1707020d0e13020d06090605011b1b030b1e0a020304 72
    0x10750207544405d4594a0740c82170100c0070140d60400d206000d0b0039030303a20744002c0c1035109108443d00c043d10900e58081c141c4c0700ea0129811180700754003e50900400100300030702c2c1488258075100404003000b000008120303030560f4440510303094440d0391164100803150a0011030350b81c1d101241300b10b44500300000601d00101842610303030a180051710380d550f041c082440d11340150071a01481d180c1480d00a0701e01d651034010325071010103540d0451030361200720034441344903c40242c00b80d100480e524040c410398440e80c0a01243c40008240380b000015150304a030850b541c1d20b890588460b02115088200c070b4125510030078440701d46d140017013640707041d08000391102c41d407028203010000070070031200040d0b0310850020717030320101074400310b5585200d80100c2000b0507161103a05c01c1e103400c20400054660042e20000041c3d22072002c603841c501c2c01035468170502140090002000e0b031107410040041440c42c0c12062188046030381c000d038a0b05a10003484416000180323510f9000340100201302c001a001801c44 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616905368 1250 616904118 616904147
    0x606091517030714030405010f0c020f0d03090906061101050610080705030424050403020c0303090d1106071703070225032603100e011d0c0a12050717090706 69
    0xd12484400d08040d800c52080420141c255035036184c038000c0c1c003240400100304852098079180c0400c0350140043e038a51200c103001940c01600105545100c0c2844d50001e10014402c2c5042c20b81a52112064400c581c199000180042c40210495148201c24828a900210115021110410480f00050021000500e0b09080100100201d4104100b2515600003000c0794000c522104940803002c40003090110340503070043c4100000200d5505011003100c11450300030f04884030100c0242c0710480f00411a12260790040030801100c004510080c1c80e0408614a13030641d503990b410722940c000d103000d5141271031010907090b02c140641c5159a01c001e40c1d045940c05503400300c5039807680d11180680001040c0a0419260020801607a02c60455006c000c1d140700c2c00c1c01403100e9032182002c0d4200c2071a0f42e01c14150010f0680400e40322504640906040700040c0f404c000500302d0150301300f01b582c009070340c50800308000000d1001d01010407042c10b50f1002e8072800803e401d52809000408070880610f1342d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616906474 1106 616905368 616905389
    0x31a07090b03180a0f0b04021315140105090a0f05031e121c15170a03020606060307020111070c030c060807020309010e0f040509060406060915 63
    0x6609990121000364115926041074584951030f0694022480c031a004182c000210081c40c20744039070344600c4c1c1ca00d50074107081c07050101040402d0503460b54582000030301041d0352100d4211100300e0b0101e55805104400810050380d07070703200d207001c0143c101800c1a008a44588000404003ca80c0d09404131107070808072440300f03980286000c0a0f03d02135045542c400a190f1a8017000e80000d0b134803441420f45090103400c2c00000c4405844401c0070300c440440d0204412140c94030901d9984400202611400c0e110343da00a4071000000c20040c4501404030129118034401d62200b035040200800895403101d0500704a0802e540c284000c40305001c2502d008101503100d2400c460003201c0c030390001c5003031861001c01518260306503007066800c15400584203095507030f1801200d010f215044c000c0c00e498140b6007454801c1d50010381100d00014201609002c0c01d50910710340307208850311700c0b04 = true := by decide +kernel

theorem cover : BRFrame.Cov 616726618 616906474 := by
  have h0 := BRFrame.cov_init 616726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 616726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 616726618 ≤ n) (h2 : n < 616906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
