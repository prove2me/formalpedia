-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0100
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:50:46.716+00:00
-- url     : https://prove2.me/submissions/4128e52c-0c88-4f31-b7ed-bb9dab0a1e91

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17805761 ≤ n < 17985618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17807011 1250 17805761 17805773
    0xf0901050a090306022b0908040e070903050601030b090d0314040605070315080c040b0402040806070507060204031208070e060307020307030305040219080a0b0105090c030103061d030408070906080604020d021309 93
    0x80c2607100f41650f001b50011460b40303420725400700081030340001405185020360381c40640703002d0383c00703101c00c0c2a0f0b11100103171603203204c3c491303000c020346d0010100c403e156501d0820900354582641c0e0010303140583c20381c11100a00030b01498020181c901c240304202d90303480d2940c000070640584800205034072509145441d2140041d01340103807100401509803600300504110803030300c4004041c1d00481c010700c800c002c1003c0118525900c0300190400590b60740076450b10741d0003441603410080290707030804015500c1903441204d181c49003405407100d09003d04c3d2002080380d11b02040321003400581c400c11549002074400c0c0c22198000e407010340780c07501044240040c1281310b0440c1d004007400c1c0d405003524105003d12030000c14014901611044184c0c108203030a0306062105003c0a400151a52400140b2502c06802c0f05401854181035a4599444040c69502d07600203115111406042c6a00401c080d4400b2030b989000310343c000c0029085031826824000d4800d0f02c00c03001c400c2290364190b00c1d400305035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17808261 1250 17807011 17807017
    0xa0c02040c120f0501050904080304030c061802121c0f020a020405040302010506130908120c070209010e060102100b090103031b0605100f08060402130203090c031005041101050f0901050a09030602 86
    0x1c55844010034030409070940310031514800301c1d41c000907042c0001044951540c40361a1380054001d4080c2e17a0301d940d58101903603510410750005204502d4100301c500b207018101508440d05c0d1003110598440035065074940d030380703440ca00820102001001542250240078042603c0400a2401138401000154000904441300ac460640c0541d440d8020400a071034203400d15280d84040034003c01600c0d0b2951142286405910360b407484440040010503085459030b419070f00080c0d4000c203100c1c4250307100c0312000c1a00e90709560300d42c054400c16689808410407030003807254105001d480030312140c0c81d40e2000c4941e5284004004e00c1c190142845101155560007036500c030b000b488101090300c505e070854030a00d03d003199000c903d060308240d09110040e81c88490b142c225440d684009a1242c403640342d41401c00a243d0308203685403203030a901502041e010b0300b11500c05c50046590304071500b0b0301001500c0e240328a6008044000d010007280c3e03507940c055405000c0490907440e20071503140d1a40e1b01e10040368 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17809511 1250 17808261 17808281
    0x8010203090c060f090d02010302040503011a120102070b060d060e0708070311011704030c020301150306090b010602010b0108011814040303090b0702070501120221070c03030608210a0c0204 83
    0x19400104100100c0400c02541480c25000c0c1c407250318081e0740180e01c1c6010b0040802180c410340681c0c0504040d0b80c42601664042c00004000b0011191962504d40007442d07103040043c082c5903d20410001c000c018802d88038416007007055602155030701e50400030300754087c110417910359586005240301000200140406089018020900380303046040022001203603a61007410010700c0c0712020ba21002c0540290f8000b40e25040c42540b800e81840000e0251500f0401407640303030855040081032104c5500170640300d600844a030361081c3d89624003242a100c400801c5800304410303100400408002103441440075800315000602d0f40e0380b600101c0500702050320246c0c006926510641c090004850b003241d04150303503000030300c4200e15000c00070f001c0e41d0040340c0f04c86006038081844d800015603c42c07a111014000c1261805525002c0400f400141e00100d064000900d45000401c048100198500c91a0504103800ca040d80d140400345100e40e00854450f004c000c5203001180040c1c4450040310481 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17810761 1250 17809511 17809513
    0x30703080f0a2304170a030b151305010c0f0c031101020609060f011e030605010e0117060402030316051504030206010603141306020304020604031b0f090506010f030b01020c0a08 78
    0x141c240450041c04403500901100309503072801d403d5908041200000b100241483c5001042d04c0c0d4990600079414403104061100c00072000900c0180c965050303000d000c1c80c03202142c043c40040303414100c1e680a801008905190700050b05014449507028070030360543c052142c80c00c000964504e44e9040c0c1c1920f0316503c1203602400420080c41c1c15a0103002107540422650700518041c542902c0075903200c041072041c0040e00c0c00465442c10322480c080c9a5201458014000740080c0d6902d03078044015035030911515680d04d8030080585042ca8012602500440d0001d00550410040014400c20068288812601131050555400060411600c1c0510481c002d401502c540d6140400250548101d200d01c1d2400001d501d0400400d40303489000444202e402450050320f941d10740c404101103204640000d000c00d1010134101c803240f85c4051488003a1196949140902d03552192071109981050300d1081c0418580041d49100501ca40d0002e05180414411101218030f044041035500025030401005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17812011 1250 17810761 17810777
    0x2009191203120b030d171807080a0501060b0316051c0c0206040506090a030203030109020c0c1201020408010b0616020f0301060911030a150501080103030e130e010e0c04050108071404020705030703 86
    0x3100e1621070031010f840c1c01c0e0060003100c00400001800c00134000c81502000e90288042852043d0000701c5e84440c4840340101d915071340d1107081c0e6582c0c2d40c2a254089800303600b00036011070259028010f83e405000b042001c5400602c071100152102d801c04030305110700900c48820000602c046010301301320a00300747c0142c00942003c1c20584d0614000514a611503403202203001d0009a0006c100d904680b4081d40042e200c0c0398185c14641000c217035052180c1d10441000f580c1d00c0040c410750044c400c903030b5544000c11100b0154000e2110b90301039802034108100c04141000d0250404100100405200800000300c26840d4660202103c007030110041180d04080100302a1032658894025502141040c4c10300c000d20b4080028501d400c1408000c1c02c0080704c130340845443d1075002114a0210052005001c00904c0048607070082054003400c00c40f83c0304454040c00b003800c1c01d01c100381c140c2c2d403110080e010031428250302d150340c00c0400100c02d070000d80c200402000300f0300c02e10140140600c42e030344000c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17813261 1250 17812011 17812037
    0x70e071119020402071e1709060d0b12120307020607080112060e070b03130203071d041e0b04030309030f03061802160b0a050108061506070303110705010f020309012009191203 77
    0x203031051741041031000c42408c1140556030354601041c2d4030f02030b01c100004030f13a8084440100d02035011035160f5271954450802000c0703192403040e002d944151081c0e402c4175010355500e2421540090280700354180081c0a6103840c001c03884903080144000900001c80b030000b40e445016000340d50003192146540e5011341303c5c010861a0034004880103007009603042c01d07000d01419820b40034540107400140050700b41000c0f032001d19800e131100d07019581c005005a200b0319113030170050080d2800d031004500103440c0e40d41c0f072802d00e802407040e081643d540f00c4510b205044240c218400a40c0210541205200410200c00004c0d2031b806859110342d051101c003044c1545010801c038070b000c0003d01030741040d02119421800c0340c0c40b110280d800c400d40519000c9030070748508600e1120781c890310001501550800c044098080c6c2650000c43c0146240b4000b00300d80441c0c00c00b45582d803a400c2c0c2c0c100c060b01104219044081c80c1100780840f02b02000b10b4181c292544e9284195010500c1160840c0822072101d00d0223 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17814511 1250 17813261 17813273
    0x40e071701030b1807140f0d0b07030e0703060507080a050117070303030509030417031b030301141905040515010905030a050303010b0d0b06040603051006031a010804051905070e071119020402071e 86
    0x88547c0320182c81544403143c1035512000b02d990010108410075a40d800780e07424032982005920000c503002201000f41c0d0401000c0245002c00456540722070078201400090700c0d000d010030b240c8002140340081c26a042c1141d408a000d400040d1400d100e5100903c00131603c038030080041c1d240c1502c44030003180d40d0a5440c60507641550b11204015136504207000400c51405e0003421130006c0f0004032468000880e050f141d0152050940d003006400070301e010100144000345c0d091300b4405402c2600c800c0380544c0d41e4020169100b03a0807000a04982080c001040915036000c064410b00c6001030000c1030b0303508080041255500598440b01c000f944840902402d00418100d1601074038050dd001e10005000550b00c0038981120a070355410054004001401e0150a12a400303845103200d0382d000c44551181055a45c80215004140f1041c140802186003980600d80d1103a0454120b0043c0c1480030510700d0301d124182d0744c00da00b41d810076020400003000585050015014803400c0000d02c003c034100341000c4d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17815761 1250 17814511 17814529
    0x9060e06031005160f1403040b09010506030601050d02011101110f03010f0509130305071b0807030302010b03010c08010608190c0302040e0709030203280605010803040e071701030b180714 82
    0x5020341c01e103820b090042d0f000c20002068101109810504400603c2c010b00321003001c00306e8400c10003540c011050104110443e10298021a04840240800d4450400f0540c890102f1b1241903401411007001000550180c090f01c0c0658848400014080030071107800c4490f0750041159200c80c98001005200d0301c0c155490b244082d18058070480a94500500d6403040c46400f1103015040c420b011581104000382c5000b2510751041c00401003020682d9003203c155503400d140402c902650818030b0b01007003400c0510840e444180c3c40e40d01c44001340d00e05001508c000e03078094003000c1c0b40b401d21500e0310514260743c05428240708680d98010327504c91030108002248000071b03140d0400c1044251003000981d50000f41c92190000d6412040401701641d103090707030000220383d00240207074100000000d140340048040c1c0112181c0d040c404000b80e070740748401c4a1000794116034000304110400140b000c90341411034140c0c858a40700010078129460001180341000e568031114402c201c00d00c4402960034041c40e2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17817011 1250 17815761 17815783
    0x50d020d120b03030904020c190804051302070206190c051c030e0309010c120509030f03070201080106090b03040b04031205130c0611030f0c07150905041103040809100909060e0603 79
    0x4010642c0740b40e00103500c1e41300d10202680300e5500402c1c1c50162020034030a8624800e4603094489a02101d86804003c41d0082e124a034452101c800015002401c6402201c5071a0703801025186032602601031140d000c042d14187c5400c11809807418000103a0030065400b50000b1812400340c800321134180181552281c01e001c0c412604140300d118900c0e6001003001e55401e40c00f00e284407800d2070381c01d0b0894450182c030580990620803400603450401002c0000c0410b24000e80e07034000300c2c0e84c850109032450001d5104100700b128003000080c000c200702c03c1d0344a4000c0d10a14080038032006007407070081580c0054030194402ca0300c000c0c0384001c0210001010000300001d0a003203c2c0d1020302d1005e2a2680200c0440e003004c0c11b0000b8900f66000400d00159001e0040d10307400d407442044101c0000c200d0010790180324020780c46c00d1200d4014021400c103981c4500da00c14071180c5045e0440d014003007003140e03e07043e080c02e1041030320000c80c01b0f500c0c60084c80e01600703400c006036010746007071000c06241c6034035410 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17818261 1250 17817011 17817047
    0x61a0d0c111b0111161403060106020a0303020f09060f0d0c030c0e01032a0f0906020313050d03210e0c06040602060115120501060c0201020c0103060501050a0c05010603050d020d 78
    0x504008180c00c0401d0341c2c8280c03064552a1504a002c560041c0e6403980310140d01c1106024040501504d203da80002c0700a4401142011002d1440c0d00d0505a440c08280280c002583c40038540c100042d22940007400e06511403640d00c0c5c20700b403509020644c550460226034043da40c0206800e011100e051040c604100322503c0e003400540c0e903500b4040e081001d0018024105170b101c034081c00035004003a845013980131b100c02c80d803d86c50b00c04910040ca10440741c640c1d40000307403106030001a410301c00426200c406003c17844260f01185001c042000815a0003812801d001c5002030381030078000c8028509450b242040000f207030703100036540321b607090800c1420450700ca00000d010520440c1d900140960648440502407085815400020340b01c6005103080b01c009542000000301e40d00b5070200302412114803e800312202c2d81801401502079075040e014a5000a10500c0540600c9200b00c03129494280580b00000301d154594403201d00f46000900c000c00542e020b0468083d405510000303981158610031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17819511 1250 17818261 17818277
    0x70e0102010b1905060d020702060708030f01170d050c0c0a0b0a020d08011d19050403030b0a090504030806060f0c0a0503090901050306010602060609070504080f0c0405071809090501061a0d0c 84
    0x5001d0f26076000345400768074062a0003180d000b840c402c4981c1240c2680d41c00074119070701c0b9500d514052040e0744c011910904501128800000c103441c080d1a401c0050018801600001001001c1150980c0221018038054030505c0c01c5500340d526001a0180a020b00794012581ca4401c18800f1346071039034495100c030400401e54010054070b00d40b1001410005407500b00c4a030715031a2220100d18511184900034052860801840100354059020729491034050701c003201403556400048089802c1210054085a0580c000859902d000c200914198600c85402401e001e01420502e180c10148070f030485180d0320020740410342e440c1010526005207000c400801840d07050400003516240003611180c003039034010001c60480c500807015280640310705012240e0740c20884107420b5444d000880d18500652400c1c0c003285070540301b000080308640d00c250b540d0102c64a01001d410050850000603901135503600c40100b005211041d2143d202e050000613107440f400c240901e58121000f201580c0248071000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 17820761 1250 17819511 17819539
    0x90501090506120a0207020a0e1504020304081902030c0304080c0a090603050d030903051c1d060130140f010b09040b0708040606050907020a060b0406051503100e070e0102010b 77
    0x4101c1c0e41c10806036480c882c0301d8131000a40c1c0064003406038000d40c4480003c00c00704003035030403444030f034802d200008018542c0c07800e610030700c8100e100035280945100da08000041e04010041c80500210302d403441220320382402029404d080d074000e50011000364020041003503040c03400c002403801400802c4401c000c6280355503a10303030381c440401001d901855180d065001c149402034040e20812681c041c0b00554030b4904801000090580c003038604610020072028241410300028468141e42c4070490b080b001000114640078410300c0108065007407582c680d40000060301800301000715803200c400400c10840010400f500351900d961507a0700844d4004201303c00302e400c620700d894116200b420300c4071084d180c43c20588007406894011070b03041214401440455940043c41d042000e011b500d00300100140b0004000656a2501c2042c2e40304000c21404200300084500440e003004041c0300040401c0c0c0d232060100d00850040700d490000c1148440c00c2483d958084c0101262812304031411a084000c0e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 17822011 1250 17820761 17820769
    0x9010e0f0306180102040b070b01050102011a0915130f050702190503030f060118030503040f0911030106030b0d1403030709060503062209020d11030f03030702060a0506040b0904030207060905010905 87
    0xe0035042880000c07400c00f80c003a94294101c0340545000654203550b114141044a4842c07020301c40c69005611706141c100b8003550080e4400100306004100742c800703444000c1d041c40a1050400a96030092101c1240c2003800c00c0c0307210384043c059a43c1400320b01032521081c06414001c00203001c256002040030018000303007000c01242d90000e002c100c56039640d00d0f00f1004a802403403c00200608421708100031081c820000050400c40b140070400d0360213691101b6107002a105c980c10f160340070050a03c014040035000b50800c4a10b000c001e030052241c12080e86501140351100c81d80f40032290400014046207592001c0c0420240002c1e0401524608000010588000d139900c5820701e14600d80c010300c2204040d903000004401c1c1c00500044c46403090b414080980903d48150a100344242e120252584c640841035a20517191900500441e40d078401303501c0041d00c1700524a503070040d80c1742c0140c941aa02d0b0060140924083c0d8002c1c0492800e240340941902d12980289050003102030080140c4e0b0340d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 17823261 1250 17822011 17822023
    0x6081b120a03080705071b09060602010c0203090906150a030c0311030112030809010f060602100b010c0302150606070804090b1801050a06030f020409020f0a0909090309030f03090503010509010209010e0f03 90
    0x15051030140c0c3d441e5100301d07080310b09003d9540024108110400034a08520480044c00180d8090072001c2007403c3c0d480703600740e003251881c014440161f0014000040d00786011000507602c0b40c8040c000d0040ea0170202d290094980c00321400344003195031031169088065052082d6120850866102860740d418032048501c0e010103940e00804200d10417002490301542900200300545181c1d006103c450f444682c0a900c6818622200c040e244c5841c14a01c0150f2051890b80186600740c0c000e0201c544107100181d900c4400100001d4004a04200130350008880e00000c1c0000e000c0410300082d4504501c0801454180ba41e183d120314880b9440148120f03030b40c656241089502c2c1d07050000b5410f10700561103019001d1603024021581c8042161020001c10b01d00401d035003080355458408594540c1075510444030503501c0580014113071007003400000c4008242c60a2a802410502c4029640c1c0700081d003980e034210b40c41c2000d070b5000700302c0340500c1d40c129a481540b1001125998280501c0a0100303070b40720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 17824511 1250 17823261 17823263
    0x1030c0504050a0e03030106090503150f01050108090708030f040e06040504050c01030207050a0b0405030702090c0c031c0e010c05130803090303073306060f0302160b0603010f06081b120a 82
    0x1a070344030045803280d10325900504c4820805001d407038030b80d070750380d00040c102c520305100f918000e0140c080389180d81e40d554079000e486221012818a5142d003044011166060010007000c1c02c0e1085804c0402c52100400281000590001d402d5540300d040103030b407400d000c10242c0101d00030b600340000d000002d02c0201e5206141d107000e00e0016100c42c128201070385041e07101800078040821010500003400f4000c0000d114440c02079903000d0180e2164007c0c0d102078420500c010600c5d8005020f18450308011841460620703514007404244240d0005503a82101c502c180400041680055103441c22209121000010003241010754200401710009c6500d91046071001401e06514020300d92003551054010342d08003144c0c201ea840350141e03451101c0c0042c8401e00407980860000c00d481d00d10740380701c2d0007220b00014020010700b00803410795442060041010b0249541552240c0000c0e014019500c20705000b03048035402400b607410003e422040415500d42d00f039009041209600444a0700020240300b15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 17825761 1250 17824511 17824519
    0x2006010306021602040608011b090f03110409060f050603120703020601211a04020a050d230304090c030902180f011202060403150e070e0105032d07030302150a0501030c05 75
    0x10390b20740f4140c51a6400c43c00c0000d500c28074041c40881c50100c15404507400c80d01c69600e4a0075062260720a4034901103c0c4101c4541e030a1019081c400150040109911060040c101003441546661500151584455204030b074a40d500200f00ea9072904002d1031561110030040d8070315141281d20000d48440c0305010300d61241415480624445c14642c0302d040c44650051840700d0b01c1105208441186542520180e00c03034840381c0408180c81c03502e890380844559200300101351148075500c6141d1780a0405c0c541c0f1b80d8500040c070000880701014000e030164014156170026031508244100701706000c0001415001e140100b0421041c0b020030031000d0b054031040c1d000301d00d20070440c4c4009412441141c2004010076081c0706080c1d047d801641141c4a0111480251400c29488070518801000244580c5078154000d154420b50b150030038002210b800b07056401c034601e8801c9244024588100c40c0d00860050f403140d00006d80f40725000d00b01c1d640010070301d2001e02265146071103102000000340281131103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 17827011 1250 17825761 17825767
    0x6150c020f03010507050a03050a0204123207030b01090510230a0b031503011e0b010314040309080f07050102101109091504140c03011401050f040305010507200601030602 75
    0x150754a03400e803001c00d090020000d121610707000d00c0c0188140c10420b90f15000c04e08107000320788404458000d0b03600340d4841c0c142c1504410b087d0340b14000d2400c41500c00040709030101d590301e4004459901a0440328070a2801000c90f40d2541c03806c039031105070507031205040c0d6141030140203e035002c0b074070240c0c200c4912810b96082c140c2d00c0c4440c030f2400300c15182025401103840f280000c8681e001800345200c6d807554418040069600c03018542a038000c2241c80c12003494069840b07001e9030b20b42d40311080c2a601890000f03061912600495020703201036a09501003510000208149102040701e214540b5a02d00075007a0360f40703014000703981d0b201d6850036907400da62225900c07604031030410b0513552030f080000d140d500b06091810002c1058181d20495500442c00e010102000e0b8244444544c0100c1343c610b102482c503860301c1844c07882e180303045111034108003081040d4804013900602910242d1b01900000499007440c10b0041c083c4601c081c044501c00f004400e4460003100082030850440341c000384096a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 17828261 1250 17827011 17827013
    0x3100506031b0a0b0c0c010f02010b130f020708070f0c05010908060106050307120203041a060a03080906030a06030807200117180f01060801061508060303041710050702010c1206150c 80
    0x25000c032a81c0064584d5900461100360f4a103000070706098800302a25010703001071510000301d0903140d030000840d0300058086250920b05140d5804002e4070000400c0040c10030705c0070350324562198040c000503101a40302628400c1807004012400e0010042400c020400718a8200001c3c1ca81d14141b003181b01348200400051015030190a1500c180703112860215900e03d41131078499003420703c42945c02507600c0054001600f6050000d41c81c002d99420148035410000e000e010804198001030000c14551f4440e500000000ca0003001f82c200c0900c80c448959a00b07040d203900d4030001c1c0c5e0021f416410009100b030100c90040d262224160021000c42d80c43d0b0000d100303500d00500e044034000e40d91400c0d610f031220014840d04194024401d481802c0c0d50f80c45504c450803401c881c88842601c0b12985500f00300420000018052501e200307882ca84030aa030302340d50f40300405800301e0728111366640141c0d4544805039007699104c1c0205400c00507031003041018505190301c81d48503003002c80c3c0030414003140503100b074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 17829511 1250 17828261 17828269
    0xf150306030212061b0406050906070c0e070c060b03030403030c02040b0411040f0e0c070203030f031e010308120603120301090903050708040815100b0904020f12010308030603100506031b 82
    0x2405140c0203843e0b500300d002d0315802c40c1c0d40c0d2503046450742001214042d80340860a1810704440885205580b0981412002c03000c0022075030004d50304907400216400002000002000514031407a640c1d110441541014144001500d49d149810703842500200700a2000a4225100c20440d0b03170183c41c009481c3d004440801d0003440150000f0036000c0b0046000200100c55102d0101500c1c0107000320703505274462044401c164018401e009600d60410f0110356080a21300340503541c00302c8000c408001081c880c0142d014074030ac0c203030402e85221500088545080c4902c82819800c010f0540040c04070048140058110f40018059500f030942c40d80307004014548914151b803020743e0407114a9a035540d448100550715030b040c112500081c1c100f000003031b01070400441804201d500358019185459000c2d030801c070082d44060802200c48200303004c250310380c4100d0581c050103940f083d40010b40c5d0b0b0402500700352500c3c82615030070420900702420010603883c042584246000c8102006420f040074600203 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 17830761 1250 17829511 17829521
    0x5100306090515090303090c0405100902070516030303060e0601080601090902030c0906030f010608130309030303110c0a0f020108010b07020f040b03030c100603030e010f2309030102040806180105010f1503 90
    0x50003c070328028140302c4c031400080b0046020314400421a000c450b02107040c04143d510841d155806404541c10801c80001950002c010251040043e07440c60090f81c0320441c84002240c10560000350340350000d01048111035125a00b110003421310120f40d141920008120a01c10300aa0b2030082c0c0210200380f031380101200307030f130f084000003010207480e886c1241c00c60f6030700c0e42c0034401d9200051220002c90b8020b401c0081049070190581d441c48280741c110b45040d005040003030360110b141c1804009508549001f842200a5a80304030201090f245450000600c01c52068014105145003002414010b036260031060390140010f4401040a1016038000380c10b41c003c401c2e09040d1801200300d2003000381c0d4690f0007030040d44d2081d190351038a80d04013401151051a030007948404104046014141911841440f408205440d81400d01c1c102c440c0022070f007641c201e40d01c1006154040c1c01441074259000b104000c030000381c50000c200ca589408041b41c00d80305039104d90720380c201c0302e402c007031318400d11903002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 17832011 1250 17830761 17830783
    0xe04030c110a0303050c0d0305010b0a050a020703020907170105060f1210090207051c030903050d0911120325050604030f0c08040e041202060708060609180a0608070603051003060905 80
    0x394002c2543ca040107080c903400148400000d000d0b420101c0070720703806445404c2c180c681d5403003510b00709040d0030004c0c0c405911510408003540b080d9040003005a50b00c0da20320b4407490003642c03004245080c4446404845106030820341c89405c05200e0010450001c0c0f095070301201c80c13011b14901340c2e00d6a40c80d11003400620f80208402c1800014800240035002901000b074181070902d000680c28400d2084044441c1d14400900044040042c0302d04144540c00c02da5601d4020710144e540c0600c03020003d9a1000720300c010f142a600702240280004c0310038007150700c03d082841e404003c0344800344e46d2292508401803001f014001c1d400d0304115203521540780804095031106040b65a0340d22035103c441d9900044600700da0404510007140300755440418058010307601d648074040a0303242c090412040f0703085820300c240c0029410803000d01c0c0c48400280c0e1030281c03211401c0000c00c079051145581c140b00c0c00350005802c0c9810502400100c042c0c10316013100b181d40003000095003104030714056052503040300e0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 17833261 1250 17832011 17832019
    0x3010603030f1403010b07080c100903020c0a0501080405030409110d0e010f1d0a03110118060c080105030f0607121d06060109080a1502070206070c0806040b070305010e04030c11 78
    0x403081507049080034140c0c0712662601c00030015002082d00341032109000d60b40d0700500c1404404005481d41c0c0160024619203001d031032603100100b20310811105011401d40c010b038803209150085007044919600688400c0c80c02c84a2494640c48450796849540300b0700ca030055485c04030510900720030b001c1d5a486983c4400600c04c600c621036015000e8200140d00340ca20b503180c0003d841001a101c140294007481081c054550712007162002c0c3c0f1252075a60100d59255252900704114144150500c81c1c041d2080c0d60010341c0c6d0400c510020b040c4401600300c1c2d4001d40c002401ca0159840000e50194000300c40d1030956002401e8440502c0600b840c589410341d40b1203030b03c100710a202d8012900a10480080c0e0f5030903030711a543c11100ea5201c054801c060130440d00841c00e06409031080c2c00034111070f4005405c1a207012043e81e90404000300c198811042d0340c0011003400108054480442d40042451074144425410142c02c84420840580005c0a04c070710391020800704084400d01480d0610010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 17834511 1250 17833261 17833271
    0xe060c0c060c03030714040303020c0906130213030b0702010e06041205070c090218061e090a0806070f021b090106050717040b0702150a0207050909030409050c0d0c0903030f03020a030b0301 83
    0x18550380c3e40d0740c2058601c8000700b81300d00c211080502d840d40030f46040b2501130b03009003030051214082c012014000b403c615008030f6040c4c03404100c801c00d40020050a00d100c00984000d600e18285130006480c080c21140469042000307113004100c000a03010782090f0403110002c0d501480e10b205861ba031041c40001000c03000284400030354000250b018001600880d2003041e40000310710100b024074440e03c0c1170b6006d90662540341c2c40341700044402401c9030300b0019203207542180d100d403c0c1b41d103480012501da4000500903c03941d06495414424400200c0400c1080001c2940d114000307180c0c1c0300c05024900c200000031444006100d0619800001c800d04608916a12a00d036040c05080e640890002d9000e465a07901c40f4041901050440701c82d10388560280140170b050604210340c3c1d00014001c0c1d209403005200200d440e141ca40310306800f03400d80702e1810f48d1b40d100d01d903144029601641c4c0030780107000c001c02c1d042000c02c0e04801d20030382d41222840d006a40b0107801c80b00382c008002c041e581b10307007640ca02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 17835761 1250 17834511 17834527
    0x10207020310090501050711070b0d06050604080606011b02030309010807020a020a060305090f210f1309050402010314060906010318050f060906010b0c0d030f0f0510030b010609060e060c0c06 84
    0x1903015040d684c0c0282c00030300490340c4015003038030040d0190300c18a040e40d100200400000c8001409880045022072000c03400030360b82e81c009495600030f81c0110110f0380000e010302c003641da04110072060b02a084011407114905a400098613030041d0039001e418018604001503e01c2c0c400e0001c600b50b15401807030020001d8699000400170f09046a410180e072040140c00b0a03041c600250329200001105c0880c102c258951100c0d40d519001301d000303002c09030800d20a02c1c4100703001040701009420b5000340002c01c0c7c9404c0c0001800c0d10309605503800304c031107000203011064803240c04055020b0000c0c00c01060118420388881744074603104074054824058421040c901c1d44012031481c0c0201c107801c00b100c2d00c50340c0729603210b039443c4100c90b04032301950302c450812165540a40c110400782e50350244000755090056070010142c03407049070441040001170000f88100602e10b6a4180034060300d18040b42000e00f4241c014009844c0b0501892107204042441c1010380c104001540d8a80030140c0342603162004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 17837011 1250 17835761 17835793
    0xa060504050d0606090f050402030609030c060402041d06041104050a0603080a0e060c010c08010e4c0905040201030c08010f0501050d020d0c17010909080d1e050106050a090504051b0a020102070203 86
    0x7c1514101d100e80a284003207a402140002600d54640c00400508490b4440b9420800144450381d64540c590588040503203806000348a0240f01d9800342490f000c02c02d898104000407648001d011011a41c41c00b441030001c2800d0a068030702d01c03c458104103004400e103100003203040c0030390381d40e1001541c207100d042041241e116002a048400c40c1d0b041c4d1600303881301191610713203c0200d01143c10362f039060126240c0140c1c00b9102d8410706000041054010000000c11428010071900104050350700e0304144411564148030f40c024845a918114246505142200e01e0340d0005114443c100300020a1241c00c8119a40c111506140040e804002c0c820031060080d00590400e052003402248440000402448500560540030740c00303801c507807038101c11811520003860591444d031040070001c0d42c040a0300c0600e2060b503028092940b42c060710b0b880f5821000303000722a6078201a0069042006000c0c07a02d42070508101c03a0303100c400c14551541d880349d004074024080c0da00003a5140c4291032400e0340000c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 17838261 1250 17837011 17837021
    0x120102130501030f0501050303070f0305090405010f0305061b16050c0d060507080f0408031b091216060302120c070515100f060203070201080604020a0905090c13050a060504050d0606090f 82
    0x240a0f2000e0000c81c550140c00c0040310000d1040329099002006248006103104510300100344c40703802e1050400340400041022104260406a26030385002010700c217002c41081907541c00080072152101c0500001c05440040c0500c609800fa008040441c11007080030510032040360000250820140c807607203090103805010241c0392280414142170214034002a5405264815600300040c030f4a9500c1c2c881c1419201c0011401c1c20b00d120700180300802060781da0803430600c41c16070050021f105151040b07041541c05100da40c003d1003407620401940386510603019402b944121010300c4503803290000d04020b820206610b400300c1c4c14203482c40400494542c403d40d01c00c1134814a01c840d800c01621404140e07a24864402c020380030a0701e19001500078507068006024180300392030310b60740c0e550baa00c000c038401c84402e6a4517080da03a80825503c40130401c114100d0300030a03088a505500504c0d06001038070602c00c5000c3c090040360070341039082c00c2c440c15800840003411164000c2001c3c483d40c3c100c0b400100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 17839511 1250 17838261 17838269
    0x1203040305011a09061005120414030307020a060b0d200604030507060f0201060608070c021905100e0f09010302150307200319020102030606040b0304050a02150c010608070e0406020912010213 84
    0x4010307400468614104a00b001b40701e980356485051609400c5420f002110100406c2162503054000808442510078000b07180142801d400802400115180c0700b002e507900c3e0540c5d1809043c1090440c404100f8400c104c0344d186205c88101600f005940f00480e10511480c1c1002c0e000e07100e4894001842503200354042c07a156902e80c020880b01d5244c01044400020a079031400002d08004009400b41c601185020060604151030200700d965078000300b000b4801e0311509402151005000309042d041c50f202142078000d04030f45404056065070b00040801154100050403c14088000f07820240612141e00303100d1410100c03501c42c4010133440f140d8a80c0305030f5403118200c003044c000c0c00341180140247e03801620000e01060a00d810842050b00f10f0300001c00c01c0d1403d01c250f0f1801c40c00768441103000ba049003003001800d0f540301c109010090035150154400b0900d81d1280c0c1d0100883e0315140c034543d03002a80400c025981d00414030014124840a0803019900d51000840810140850350b23110111 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 17840761 1250 17839511 17839519
    0x60501170c0a03150509010b040f02071b1d070302250203010e0705060f181005090913050d050306180108061b2104020604031a0103060e0102181203040305011a 70
    0x41c45018040c1142c01c03444010110080b0030380c00e03401e01d55141c0002c0c2d400781041000044100440d00020182e41c1c0b01d0152101c807035130001e41842808060100500c202c1c042440e816186407078070001d5403140d03c85000003000e500612011840b014402e404403a880c41007000c4190521018420900c22107840c141d003203100f90f10b0f001d50745030001c00101303180b011910010f061030704003040b1500055041c2d10014108400c3c0350502d04040140d0b49072081d07102d07418142c1c0d0b50355803980e07010802e10014040240c50090a410002611070011798002500d4415003810301e030264494450034041000e405500e0422140c8004440010030401c000190305840b5113005034480801010303e0310700d40301611034500d0062145c42c2c8400c08000c0486001c1925800600c058081842c0030b659499210f0307400e281d4084042c0391443c400040060203890b0040e40d2002e500313074008600d40b1188586814000061400309401f0f40c410303150b1003041510500039240103540001c0244541c1d4400c6001d00d01450142040c81c0c8a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 17842011 1250 17840761 17840773
    0x91103010504050a05040b0c0a050f030108010f06050303070c09021b0319030609151205030405120307050601050a14041d0d0302070506010605270409080703020f070e0903160204020706050117 84
    0x10301001800382c5c0c1d00464000e0a0640951100205c0001c25840b242603170f814008200a01180c51060000550003081084000100f51114503001e0040d50820351115110b03500c184100c00204101d010107400300c410314100140d0390703000b082c05003100d054016543d56950202285c440f140c0c03102c012101015007907580c2c0403c40f01e901c5429000481d001d680c0c01c00c80d03024440a05012510300681c8110405000f882100d0826540d88009020495013401400298002044240402030100305650141034221400c9002501b00342858603461808441030344510740b1800c13140e550001803000b2074007210048043d60b002c503c030890050080d52200800303c406100303050001607042d1260003614560344ca0240c2e415907081c40006810070b01c0321302500d0981d03c10b80d41c0e0925000144640c004024980c8260040d013174561140c101e203810509291f1040000800301340c20000948004000c4840364402c0d842c000c10410b030355002003030003401200700050600707186c0400880c8440d030301c1030614498501796048800c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 17843261 1250 17842011 17842021
    0x302090403200f03091c0501050103050f0706030c1e030905060a020403050c040902010e09090f030a110d02070f170703020a03081b0a0c0e040f02190602010c02010204050901061809110301050405 85
    0x1d903d00306100394041507001406440000e00d00480600c004009100c8503a503000c2003516464216030080e40221000e911174045c80d9071011003840b040008010906042008200c01c4a01500c400025207035100c40007009154210181d02039440340071a160040110f58561600c01036100003541306010a44051013a40b8500b070070b516003405148401a810382d2001c0c125174104090001062029086034001c0c010105403240c0c03c1d00030005086000226540c1c0340c0c4032004c6d078a2160620144103400411500814014000361407110b000504541c03804121400380c8100c620194185501c3c2e40009500c4100510000240326144000c1c1c124031a038081c3c5400030740001c1c205c07541d40b072500c09001444481064802c00c4004d4201d0f00c03540d405402206048148030b425400502e4941103900400e0304a480c6860500200e9424441d1b0040007425000851901c1c1c2010300044003090705100303100801c185210700d9008141041d2402009048100042c41000041c8442c049990000d024a6000314607050001d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 17844511 1250 17843261 17843263
    0x606040e010e0a020103320703060608060f100306090509030c060105010207030f060203150402030703060e060d080403080d1b050702030118080702040e19050109110102010203010b0a0e0a030209040320 88
    0x90b9854100030000c050102d040c0d401503018000f0f0008480742000c60f034105a010f00031903180381c48020100d0701800c0d100d1410980180845a03190481c008018620003004100d40783c0d225030300d804e444212051000e100c0341e134508402800c1d65400125140e41040305200d0740300e00c004080c007c0650703c3c0d0160b503217071307a00c4400490307450f4024031028220a036825246404240c04d40d000b03541040030504110707140081000450309030780c01901d0103070010b5035644041110094070040e40c0d401140890f0000046002034440321424021400054846500010171929401d0113030b00c18038242110310040c0581002050001e450b03604031401c2603000b0750800d1107c56640b010148421180d5034807985072410300390103400740b1000b0054182d070a080c521841e0403946040290030150f001240c40b580002c10340851620304100e609000e40741c00343c15603005000500907010130742e0075100c001c1ca261511442034002c02c800a1011107181e400650401040e00034881031590000001c200100c80f03d51200300036922091709 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 17845761 1250 17844511 17844521
    0x6060e150c10020d02040306061404050906090c090a0b1f0306080703030906050a02010906111e071101230304080a08061f05090d0203060c041502060601020d141b0606040e01 76
    0x81d650382103001c41c02c403807050030742c0504840140d8a100506044c0c42c1c0c1e80385400c95130550003c12807500125002142d503d0302d40549603118030540040d001c0d03428020095035846042a06951261008134000f034044003082e0320000710301e00b0040c11a000c0d44030b0400401070251410344000d002034107201c0042955040012150100da41c5a0b5682140510303103002120300b90440300245045540780d21807000410703018000c0ca0702c2e85000141480e500d480302c03140980e000030340c050610f04003d020300008022a42840442c50310010038202008001080091201ca01e00600031003170100f0404400d100910003018003074070b207281050b226028551030304c100300100030741e06059444900c44c0030420708622500c81c0c1d010700b09031140135050001c0b183c07040e40028240501140c0c0342c4600d400c04142000046141e0300090030745d0b011800549001d00308a00000c1d150090861182e06010b00840d818041c060150700302d41609440840c540c44400b0b0340b003441520741c10180d032007511450034540d680b1220001840780c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 17847011 1250 17845761 17845777
    0x102160605030105090406140a06081605090604050601050c01140f01080f06181e010b0315010e041707050a1b060921020d0507090c080f0105060702040b04060906060e15 74
    0x92103066a2030101004140d1000030007c69940740c4800320980d10340c0007080384601500a048010402c541020748840c6040004900202c0030114424100001d4413010301c00e5402c0b60064801051613620600180c1c2d080c45041d4a52101e03603c1c02d140d40443c10250100300d4001c00c0c903070740103a00300c3c2d0b43e03800f1541d552100780300c035014582c00072800300300b107901019072101e2603c03444400d0b1080c245411605503030491000c030301d140e007030703515140701c502140b9044c89810114242903151207410350400d6440c3c0d51a00e0001c0000307194018050800004030b60400070345200c0b95103d0b003182d00b00303015468003048841e0040c0002c44d040b80d03a000b02240c1c00380a4100002070764101081c640001201919081c2d060361560001d0b070708060380030881408900c0500425000d40750360f450100d210180100010f158a0780244500d882c00390540c010710250b0340d00d030f04480c69235804540100b147d070500e00004000707041c1d50344043c240314545103000405030340000c0c1030b031001403045805501120102080401034407401c22 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 17848261 1250 17847011 17847017
    0xe0f0103060e0a0e120c0109050c0306040305071203090f08070b0601020303150f060c010204031b0f05010f03020d15080a03030e07050a050603070201090804060306090c020a05031605030903060c03040201021606 92
    0x400110001c0355544064200902803049401150040d8100d0317625611511031800a139440d62490000d03c8030030045091007540640082c4024605520010158010030100402407491001c1c2103c0e8907119401450200d5004440c984548041d45000c608a50000e5400c03600040900c0c0002c0b11036001000703132845001503030390b03070b80681c0145010010a00711800100ba40250240701108600c0030903c003400240d80b1904420820020b901c40072020b102047e406108203401c0841c0c24030190340e0105042d03050411a0a0141e00c0301c0c201420f400c06044036401410011a40d80700000f0684000207040484600949080200401d0194050307100c42d490300880d50404058a010020340c14581c0085030b02805501c00040d902420f90f542c120030750b2060740b09c0300001e03403101001c1c00148030a120302154403c4500003801c1c04189a541e0720348030702440c40d2803280881503c103c081030040500c100c2d10185801020307074085141c55045078229800c1079030141e00500c03800c4503884034007154000c60308c29100103403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 17849511 1250 17848261 17848289
    0xe030f09010f0e0609040b0d060207060b0307080d2a06110307090608061f02161d070201020315040b0406030204020301091a0901030809130902190312170109150b03070e0f010306 78
    0x3806100190000381252070b084055070b40d04c4030200d411840549000d0384510b20104140c01c00404252601f40103400150302c5410030607840c01891723000804071201d8101e02c3c12080e034b011018002190320107c2084040c00d03441c100b440070030b80140d229006501c181e241c3c0c0c4400c1c0d4810745503d030884001c031044804c2904150039041c0050740d01c25400c04002200940d1045510380848280d80c0050001702c0d60000040c02c0710780c0400113000800890b401e0380301250344021811858409151610041c0c07852400b030140350f4880380f803101e98417560007150141d81c0180045d903036540d4803c861301c014814022a01c00101048100000300c0c580000c10074100e9030019081410112010100129540140f800e126150b030340300410001a00c6100c0d412207441031107200c0e00326031842c50074040c100304103150381d040c10001da403c031030012003102440c07035030540c1c41c1e000001801e0398405482411210346900b03c000a50340c04403c005c0800d03482540d14031155030541d1300503a1003c8280c01502030b14068010741004042078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 17850761 1250 17849511 17849527
    0x50c0603130f0f1a0405030706050402060f04170105070203070f08030c040f03030c030e0118060507080d02160516050d06090204110c0309010206011401020d0c060e030f09010f0e06 79
    0x110010310307040452504034106441c2a03076240aa0208800b0b41180c080c0704002c6a103083c0928165141000000d00b8581c101d14602541d8140d103e12801d4402000155600081005c0d900c50710305942c0c400c110f8070185035807582c03280005003000755009061200d42d800c1c00c0c0014640303231001c029520744962101c100301007140c0b181d40da52219000209003103400c140c18880002c7d10341d1007480800c002e600a480b2480c4407449420001e00030403240d8540783c140b103501d00d6511246c8030001c450b0740444403249011512141e1a107400c5601d03100f0000788141150000c1100582681d0804d880c0500300d1041f0f04540c04022110815046a4203078440c0c0c69000e1841d0504201041c1c45400c0100114801000050f0510f840d03204034015404c0184084401d0b40301244030411960100081400b40000c81c4181c030120300d00f040001d58031540808002c0c100704080444c0010014243c10080840000c01c00742c1e9156561481028901e42002c80c8083c001800040c1044105003d443c00380d41c1c55002426031482c01d503107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 17852011 1250 17850761 17850769
    0x60a0b0f032a0403110a0807060c0602090603071812030f0f0c05070609051306080d0e010207080a0305070b150307030201030209011101090605040c0f0e0a0504060e031b01060f03050c 80
    0x90042410450ba180d500074110b5148034040e448410b60320485032103a0460400245c03e41c03446044a00404504005112000d400140c0c1000c846880c036000f900c100162030203d01902556403e1a0080d0000c400d01641d0368020390510040798401400240d00c135582c4044540c190580040070380401d46011a41c0807407881850340440f00d1086007045880380e2501c0e641d16207800010350000c00018121780b0103000c0c5140542280c01c04001d404000e01c0300038100006075454004618500041c0862079500d86010f034003d110003002002c60100f61040c0c2201c07810080c10f1a40700807411110b064400380081d010142e4030551500e240300c040c0c010100c1c0c0b81194019002540300c503071b0041c144a01b03d40f81e505096400d0042c42000f034840c0c0d101142c181880d103403075010544180c004d100303050031121041c0804203054060b1175005c124500040f80f80e842d1814400000c01039107a010361240000583e40c81c508020140a400581c8a40001c1011036503ca03d910005038071804001c01c2a0048080030f031381c902d4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 17853261 1250 17852011 17852017
    0x70c030c1505060901050d0206180a081207020f090106170c040b040b090406060503010b0706050c0d0e01050609010503010b030d11012a020706020a08030604090c170109050105060a0b0f 81
    0x8800d003840150600640c94401c62480500741d038a001c0d503252410070205082146403d801400e09a410240c01541c1e0750014540f8094040200c0d003051a002000c0010b80d910070140c001404000c044c0c83d47c2ca040c1c8445948641d2098030240d004031210714100540341000d403200c0c0e048824550703448901407030092541e9107903070300506800d007038030300c240404200d030120b001c004c0004201d4010183c0c2d8441c1d50390280402d0320300381d46c426802e0040a000401519904a049a107100e44c04000010542c3d034104039a01180100032504410518115918000010560180c7e0040c2011110480b0580e41c6000301420394199a0503940c0540040d02030100c501e004407008500307129140004103100058840110f55042c2c0c0c512607100a01010344000013881d018000100034140610180500501d19121a200c40c40081c1070180625511310010082c000300007031a0700a040c850045607407600302d01034224041e1a040340155150b5103002c0c040351482c90024180300c00c56005000d07030f5042035407980c49004150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 17854511 1250 17853261 17853263
    0x6060f09030f07060905011e0206010b0310030c06030c20070b09060d0504030903030801080102090109052106010e10090e0a020103021e030a020409051f031401090611040905160503070c 81
    0x102c1100100821000c0900100c4041d1800b9500c49420501d480001080d001c04920080021482c10007841d014960228481c0d0644800e48229980c07501e88009140441105d90b2001c1c6c02d40384160f4021480715856001010303d54026074406944110b0b0004100d804400600305c0d003a140e000010801050383c1007400383c0204240200458100040c01e0403000584500311000c500044400c0c000f4401c00d500324881e6800340c00040021410050f503500040c0002450b130003958403817140c81d80070001e0401c8000403641007100d0841601c07a10b594444205102038825a522040c0000030b04020400b05064070410001186c0d83c0e008004440f00341e00150000d6000f1440044c09070103140030041040c00310741c021405048030220050f9941e2511500b00101c800190a6590780910700c050b007140f910b1000503401c00c0d644c21200c0c11300c0300c0407040103040c01011007220091040741401c88072489090080c1c00341044400e051024400381d0303100000014054645170400e80814010700114170ba00c1d12401094081c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 17855761 1250 17854511 17854513
    0x8090d1d011710090507020601030f080f04031e0201031a010804060e01060b1209010b0907020c090a06081902041a130507030b090906061008190e03070807050a06050f06060f0903 78
    0x1001c0040011400c10400c036415585003440303803c200712004d1580f01d9030340d000030b15102070485941541d40c0c48210a0320244003a200c038001040c61000c41c240c01080714025907000c501c001c1d0344c001403108d03411080f40c41c00c416408686412071011a040060400b0b05a030790050b9103411103552070b81c2da08070040c03445041c801842d40da40c5102007070300d15440004003da0a0700c0c044010040c94250310302400c0d5103801c0701c65802441000244a00c2c40c1e000210000c1c0040100c8101811781d40d4035100b0b00050405078003145440c8207050308241ca240d0300d40700d401d1105000b035a003401502e000110344200c40d0700318014590003076016400001003004560180b9000140c0d0b203000f0815500104c001900101c00b13980e6008540c21103020b101d04e910f00214005803000c1d00c2d08003210589068090402841d5000f89079488168462050031000700707003031040b6180d00d940008919100e10721402c240d590f4007540c0c0c034110782251600e0045240b00054000d0b07503101d03210003030010345000751081209000c1d0708640010340e01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 17857011 1250 17855761 17855777
    0x50109060905070f14060901050304060b030d0c0303140702030301050d06090503070309050f030109170d090206040e01030302190203030a030f200307031a0303070f0201020a0804060f08090d1d01 85
    0xc03180d0085010090294006040e014103103032205090a14550181c80d04003248416442c00d40c8800c0b050700d00c1c4180c01d0034015103940c1c40c0c2c00c10f0809001c0078400742d40d050080c2910001080c1d0007103100e003a005d000e9502001002c0c0114000b01101c035040d00c0140150f8814401000340d0b00d00f9000f8107601c3c502c151004603005031503a56103461504034000407004108100420300581c101440490342c140400c500901074011030ba120800da032001c1d03440e030300a1510005408401c201c0207812842280d50b005d00302d03a50740ca603980800c20711240300b8001100107016032103503090a089034900780306a80350002c01651070080d030460700317900401c1350200380d2081e541c90b0300821503070074014208051041c1030f2440c0c00b07581c0e103081d0307800504584000003946061090303024101c07110340340013094850030350384000e1503810700040d4001030f490440710100080c05451b0004001c03c08aa22117500c40404105443d60354081e2195002c0701c0d203030314813001c0c01c00000b00000ca00b141d040229001c82d12144030181403081c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 17858261 1250 17857011 17857013
    0x3010807210c090507110a030903060b0a08030c0105060f1008070f111903020f0d0c080f090907031b050a0c060f180602030103020906040603080412020418141522050109 74
    0x100b01215400707228025030324000c1011154010900c000103c0b80d010142a0303c2401341c4d0007811429207404080e1000b136a6101208464891125a0014000c40004c0b26250101f03040382d513018100840b8064010fa880e807690301e030035081c00350b83c201d1901d005882d14051075a03109400c41d04020700c0503014080010361038103804e060342300703110601e0031410816003141402968140a4500101c00070705054540c0300050f001ea106511440741c5001a0703000501c6036882d000c601d51b84050340244e5410030360014904043c042d02d5501036210391800b07500401d030100c0328450034000f1346217402040c0070100803c2003021003c2c000b5020b0740c0309004407601e0000005000c010403500010030344003030b10121082c5134000014015490030045a0f035114070110b405115060035942d80503668003441c42007460700b410043c541421503485030003146407021000304401013141039003030101c4480102d691600f5980658a502c180f51504080c00758030070f244a4118018480d80713450b103080c1607e041c000036980c0d5540c82e00c4041c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 17859511 1250 17858261 17858273
    0x1205070204050106120c020309010c0f06110307050c0d08010e06040506030703080a030905070504150b180d0c05040c030506030606010c08040806040c0609060f0207050904031209060501080c060301080721 89
    0x280600005da0314155010390100ba40c008440d0340010b0041554020f1143c0702d4542c1e0700c41b0030b200d0040d070301503605401c90303e1510f00f80c2d000d0f0000f03907801c12040001004101401e54000e001d051404440012182d0115108900f500c808400303004000b4a0807041c00010303980e0804d90000b6400c02c00c0502107480b0039a07691035401d21390b00300c02283d0b000280c880300c0702024000c0c10031021019010840d01004103048001d04004030780b030345128014408001084029030180103055101c180040900720300c0031030f00301c0c0c50182c04034035140c001d00344101e2818006e80707200c0e4801e104d03261249d08050000d20b4075488203030041d80c01c1402d0203c02c071140c2d101044041002c3d8001e010490065209140d400d80003401c0400c081d050401a811120401041e8012502411f80c00246101190310a584a43c801d886900317044410040c61040c16641504081001040052a5003c581210301d080203441c0d203920303483c0404c07040784420721500c0715540c4841c0040c40032040f840800b002c0907a900d87d280c1c10702d4080e07aa80d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 17860761 1250 17859511 17859521
    0x3030c07030302100c0e0906010c14010501090b0405010608040218090c030a0602070b01080303090307060c0908011401030618020f06030c13080703020901090504080313080903030c160506030c071205070204 90
    0x100d005070045031204c07001819038040d6200035102810140070406210020078051100144140e042140084205041c048600c10040090007180300074425913866404c00c20245c01c032041d000740a02d01d1300f800050766910854905000d69401048003560280391081a06401c10240901c0564015201b0744007041c0d4042003890710091040c90003680f40c00e91400e100010140503401b03071150713410030010040d45440101c03c0302c0c5c0c0644e21a40010f00d00e03684d00c10881d004007450b00b14001642c87c002d01c00c010002c850400c58100e901c00d0390b0504c80e006d00364848000500800100a4200080d180380c4161458002c01071030380226443c10103420700418950b48a030803105940105040d4005001c24400e50500200300e5014000700207080c00701c2d051564691140744002881070422091612002042004600454003030360801021030b620340b100c8800745611141502440c006000e07414200050b5400c001003a41c1c402d07058070000c281403540340e40380c2c0040c540f0721488003001c100d4100204001030360340d4495 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 17862011 1250 17860761 17860763
    0x503030a0804020a080c0d080a0e060a0201140a020f0a08131b091404030504120f05060a060503061005031f060302040908030601030e0703020a050f03010207050f01020304030f0c1e0203030c0703 85
    0x2078980c00b41050700501480c070100e90081e4146070080c5d003064100352909000d40d41c02540c04900c2656a414420040302c00003034074030300301e0790104000030040720181d81508200032341e11007a07002c0c0c946920f61103142d034220301c04d40700800c0402d90103205c0109000e0113029481c0e070086901c5859006800940da608044111169100c890082004824003014810b88a01c00302011203440310030050800c0c0d14080c242d0b001d548a4807080c1e4130f051490320100302076900e004030311692000071101070742818886131002c0e100d030303004160191190100141120206a08010840d8006006400d44600864411007911038410095942a841d40800001078446118118015015011558503030038004001415111014109881540180400c1c0007680d1071161150807134600b00c0d0004801d06c8038001181c064011200e01074500e014080007009100c02c19001944514802e070b542c4002003a40c03403000c0c1c40404a902002d021710540440305040501c40805050384540010110ba0500e0100c80300c2519000c1d00b07401c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 17863261 1250 17862011 17862017
    0xf0906070501140c03010e01090207020102010e010509010509010b1504091d0307110a05010302180405070c080301030f0203070803030c161106130509150904060c030207050601060509030706030605061e040503030a 93
    0x80c00d40c001d400700c0021a130401c01d00c00d611851945040c202800303000060240e013a0180d8009003540440e0b000354082119421948002d1125280c140b8405009080869900099500f001e030240300c1c41c500500307a58001550000828101410300200310001d29203d20b015125002c0740708109a00c58040000c0c2c00e2040c880c108a5804098550501190b40080c2d80940d06141c0140040c0c82d00d1030604841d5031841e1401d03240091340350f0790450f0850724ad40310321402502c200c00000012013841120f80144c62214025421110710643e11503a03d5901d12084908501088050000f0301c181d45561b005951500d00503002ca40c03801e00e501e00001c4950303201e20000010107000b0201000b950820402040c0d02480103080d06000300b1001002c40c925203001000240b62a0350380107507540340b0380240d05480580740c0042c01c940c469a112000504694024900140320348552039000422038468015481603a901511ba10f051500601d040789108402c01200554250300b8000851540c904001618008c0c00c10780d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 17864511 1250 17863261 17863271
    0x602070c0603050402100f0207050d050106050406060516030e18010b0309060a110a0806190e0901150614030a0905100f06050402090a0513021312021e010807050f0906070501 76
    0x210385081049600d41c00903040c10f040c50108005030366402d441e1804c80e005030a21182000880c14101e04103880e40c1c010036884408010541e0900105600400503a1400d45082002c9621110191124014180e0b942058100502200b0001e4480c00c01c1d9160104050403a0300300d209a9550001525402d80291110000200412030310714001c000711608207500c0b0302c04001c1c0211785400d00020f440b075200341409111a10020407540d48920640700218107825500701c001c0358481d40410401c06080e242d41d00150b007070421084000240c2c0d440031045030859155510b01c14001d079888143c0d074000811280b25a5501c04007580454002c0c84a02080c1e6001e140000e40061001c0104040f100c842e00064001c520503c60342130151038049410007034840444207410045004050400079120344010747e40d0b00c0110801c005402c0c419a81d426004510881c0c180821024042001190302603440c49180010301c40d60108800d40e014400404056034180c00303c900d8a002880468026400340350f00329080c0e9512 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 17865761 1250 17864511 17864513
    0x100c0302010c080709060311040b0c030403050607170403030b120f010501060207081203070806030a0f0605040b0105030d08060603070504050316030201081605030105150d050a0603020306060102030f030f07020a05030403060207 99
    0x81c46010781810b91802c08111900b800c0c90010001204c0f4040c14081c07503a241c0c880c02c082c031041000d5800030041001030036500c80300c100c241c0c0e490b50802d100c211154810080423a04490003000c490001e0116240e54200c3d55546403011005407881181d0313944c220010135040c2c2da4880c424004080f04883c03240000c1825450410028689145d5920200c03007a0010341400450034094803c6a41220152510403c5900d032000040c2c2004c0c0c40324002422041341c00075050030060941c00c0584a113002d44100ca140b42c1e80c4200345900c955446105100041444000690301c2c50711001654121010741b2301a8240f40d01c44010030318012803d01c0107148400d0303c4000f0070440d070f4482255680410380341c1805006440001001e0240d00040c0101032081040c00322010090740804199054884900c606220703d04010700c004c070040182d404264041d0140c1c400186080d40000211240300d001070b402c26180d0750b5520035040304240040c1c42c11045000e114080c40125804102820146004010050341d521b6a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 17867011 1250 17865761 17865763
    0x402130303020d030e060a0903020f030c0615150a0c08040b04060801030506070207031a04060207060c050309010c0e0f060c010b0402031e0a181b05101205010b07020603010b0d0605100c0302 83
    0x340f6074003034040600302030048403004000706101d42c001ca0041da000c00c101c2690b1400764142800181d031800070313110200b40340341154000600f06004100223003040f08100d42c2142400070100000c1c0c601032000300100103091441c1e01c0384030b0100c00c1c00d000360085421725844007885149640141d0110000602286c014800e0050602006030042038900080c0b07102031455454101c02c1040c00780446a600c1510000707028003406404030384920343c0c4407000b00200c03480000d0240041d00300b03540c0c8088542c6815a82c0404500820740d45014200007003030441c0507001030b01000034681c080c1d40100942d540740e9542e8111901c403800a1030150500241d82c80c00c002100c40c1072040e6101c014074802000e03040c5100c060b010100d012148000c20781008201d81800c56820010035104204c0d400240c209110030002e040166114082d048140c030030740340078003050b680c2d46207560050040b0f490280d4852000c100400a030b406417001800140000400890741c540d54400145400d031111641c540440c415034411020168 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 17868261 1250 17867011 17867023
    0xa0308040b0d062103080c040e0403050a03090804060309120c03080c0c070308070501051b0304030c080c0a0b0f01090608060606090609010228060b10140315030303010b0c0c010c03020309060304030509040213030302 94
    0x1f0401102e07a050500d04803140c240f84a000d03002078140703c070006000e505180301c6e0300800000345d0801d00280c0e0312592900010007d006403103065131b210710b882400b800f500f4400c0c0715901e8402d4040d501c5d1129a04c07101851b03103d560041c1b1f4030040f24814410000002807102014083c2035004400014080c42d15003000d05000d0070000c4040f02c1202c00300200000a600800014103098102c950141c580150110386450111100c1016003270102c0389040005012200807582d0589290000c00d001c001d03034912601d541d80c038003030300c940740c1c030000c01d100342d21440c200200135020501c0144115004503a009030603c0c0d29140200344180d40481c018507107024490140100740800a0603640c0d03114140354400001c000e00211142c2030138028000000c5010700d040c2400543c0d0301d070401010b41e03580c2c0d6540c20300311015601040d10302025004203007020703003558000c100078820186c068029528000701081004140da100400480a010040c0b0001d0520b444901c0030704540c080c148114407102d81036041c0030b03192031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 17869511 1250 17868261 17868271
    0x5010e0106020d1b02061611011101020703021b0105040e010b03060411030103020d060f0b040c0c020a05090606030106081b0c0c01030f0606050412051005091b0a0308040b0d06210308 80
    0x142c0031640e01007107580d1001e106610b1102c1c0540304103900013944006003d40c440d84c0400506440854013210038882c0e04903180c0413281090f01c401080305481d5141d43d00f43d024402c0d004e009a0000c2030180580403481616500903101454010324150301da07200d00040350703800e0f00306040c10310010040000d1810301d413089080e800c0741c0d44505400c1d9031466001445800e1515001030503280c45031a03480c44051146c02c5111014401041840108802c000081000310b40c094280d00c110300307110f800213213401c100203503900852026003039503d90b07030a0503001c0e10f483c04094107040c01142d10a00c0841c402d400c0c074014018084091014016407a0322000040982e4800008801001d140034010402140c12804842c01c865040c4404400340c10181015410862081400d10700030703080c02c0801c80c035904041600d2560030302e0000c4014220316103c041c800c212240e0302004240080c10401480f11006001c0035017142155444040340540c0c45003003404885a0012001d90844681500c542c10035800c10080c9601c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 17870761 1250 17869511 17869513
    0x90d0e06040b030105010c060e070803090405010b04030305070209040c03052b0801050a120606030210031b080103050d0e0f030d021018050a1103031b0d08150333010905010e010602 79
    0x160400b100c6003042c0c4410b204550622a1000710300c000c1112540001c242000440240c8444580e103072030711522036100d00300d070341d01c12480c02c0c0000c520851850305490603250580d50b8241414010307804d0201040b0090026071340101120710000001718100003180c00e040080381d00c0c225881c001ca5034180060f8a00d8540428041040c1c0188115216504040c0854000d01095042000700f41400001010075400180d085220100c09150042e00354200c4000880c06805036140221200e5007250542c40a0100400c2034000050b0003200c94490005000045001860070841204040000e4034008814880c200585c00901150000381014421807407441c194004000950300180da82039181e00b03200c0c10007032a0003400d80d00043e41ea2010019900340c03180d00001900b80c0c01e0400c00a1350344280c102c00481c0020820f80002d40d001c0030480503d005500c0280060020303450b6002c1c0c0c01728121280e0244490610282d948200a641d001c10301402000541c900103403550408032007544101050f0404025 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 17872011 1250 17870761 17870767
    0x40b030c012f0304060212070f030806060d020307020c130605030a02040c050f04031518150c050d090317091c1107030204090506060a0e0105030316140105090d0e06 72
    0x1a20041030219103890309180c4041c0401c50300c8094024421140d4900c0705030268954041440500000100265012602210485296426031601c40d2160722230081c400303214090501c00007402184580c0c0c11620042c00305050240304d07250344080360030031264030703006074000404504281030044003005c1e011652034041c06158100070120781c1d00d8215820090245a4900741404100d201d0030544d034244070590f641c03558480c1d49041440349011707445031003030080c0d1409145001c8d1103e60000d00f03000a501018200300311589c9108a8000c1c03600140030800d102c0e04100320315031008a0720404904611903128602510080340219030441c40c0244170f550142c0c02200c007085c1b074450704035178012418403038234050110d1034000340818102416a4002034000e420035640c4000c1150101c0c10724451b10f001d0b10507982180e03503904000c800c0d810a1107500d8054004021440e25800701c6880c0d80d460714001d8500030540e511b41042c0c03d08666040b561401540c00c08000705c00403076071081c090301082104964030740c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 17873261 1250 17872011 17872031
    0x1e0a02090a1403011404031e02061302010e04060503060106031a0303090d0807050f0303040305120609190b0402070804080705010801080303160c030c0f0501050603010c0207030b0606030601091a09010e04 89
    0x800031a8038010902c8501c000040e80140d80d409401401030503840c42441ca0b42410f043c5405818080040100390301c100c2c00d14841e5800c0c91001805034411030400704c9210705a0801e4005542e1032000c1d500290704961500400b140031780f0208091030007001303e40d030001120240300485000317010983c1f410034802d4200300070224003030b0b9645001800ca1604104a10355402c69482c08516051100c8058413281c0404004c00c020315800002502000b04185c003109103a5952208100003003404441ca00c200340c0061042030400810303507102050130000540018070740310881e01c03442510740080c3e00a01c036590bc81c0100741700959010070200c0c010111003008600b141040c0504140c4819021400ca040245d0007940006152048041543c826040a400005c040c900d04046020f40400c0316814000d6080c4101140481e10029401341100d800c1410a20740c0d454820070030205500c0540441d0402c10f440c07101042d42884200f22200b03c07a4000d124640e20b1030382e50b0001d0020800ca1032814481c900d00803901c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 17874511 1250 17873261 17873269
    0x1404050d02210703030807030605030f060c031005040203040f050c061611011b050a1e05100209030f0304060801060305070509030c0409080d0212040b0901020f0f130902031e0a0209 79
    0x2030186a8116285036000c4421103400b4910401c40a4040c1e4510803801d001040c5900419490301940e03185d50103000050710b8405141e0b80e050032500c446000d500c1100010a034484010240d0340141618030380440459460000506030307002a20151080a52140040208101005070307050200c01511141c1c00e0042d41b40803035207a036186000203042d540c402c0d00b002d45a0b0707209940705c1c10a200030007080d10102a5074105035a0f601e600c1e400445818a000c0a001c110a05005480452680c00002405860385550581c1c000c2c0d00103010541c2c00d840380002d4034040d03001c144081d002501495451391010b41c035040009061344c4010b82814180001006401e02070344000c90701c0d8610440581e00801c0110b120b24080c80c3c5886074140f4440e16500c045026003004180c0780c41d00303014500035011021030ba21400390141c00c0340710b85804049115020409151184d070381401410810302c0052504806556891607a402e9038400c45d8506a620b80100303040b80e000c9140e0170000d400c00d40401301141002d103888085 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 17875761 1250 17874511 17874529
    0x6090608030301030f050a060f0209090603010203010513020921060403080a0207030f03020a1206081501080c010206041209030f030e040c0f0203090103020d0b040c0201061d06090c071b080607140405 87
    0x18005a006000c001705200d81080540b49156002c2c408200211142c00040003d401c161010f070b200f040e81c41d01240c0d4618050003960306132a002081d000301c0e0440c0c81313030307080003940b0680065070896403682d00c40d080510804246c8840e072070540701600d0680742c2442c00802807000140540f0f02d0601c1400400003207640602c03a014284024140183e8070354603481c007645c0d900c02c80c4a4200c001418801c010500700ca02041000038646411650b080590701c403954182c942144031140390050344080002000b050800114410140c2a4142031141903102c0c0c40f050354038003605801b074020458465038941c0da0b003060301c150f160100c100d01c2c20b1044040410700c025102e2180c0c1032400d040580124121515041c641d1144944441c014030400c01c0171181075001c3d01a01c528428480300d034560b075501c0840500100300503441100014040382d0281d80352112115035400c800401d5031103c80801c0d80d10b01d4500c140060402a0004500801d510316086030003c00512054a440e011458140001c1102c0c0c1c07641025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 17877011 1250 17875761 17875763
    0x30601060315060809100c031b080f040b1305030d0c0912030c110102010b04020d060509060108150d14060f0105090709030b010e04061104060503060414190506040209040e0f010609060803030103 85
    0x80f4040c0ca03400800c601d80100c1c10b0111040300d06e003013070051f42c3c1d83e01540891540c481e207011201c42e1030a01c900c01d0ba0090070813207420301c0821a850024001892560210340d001c036440402508030a0745884041c40c540004c44480c1096584405004c11940c000b000c0e8001002c2d010f824081c000e1299600900c0e464204600401c1c0d291860800c007940c1e0f0007034110032070340c0101401c211b4980280400300c1019014910606003e003100802041c441d510580c812441544000b1021400e00407440034040c100c805408240e03240d420000290007030000502005001d039680b815081429410a800c01c40001d0014000341c0c14400c9202d420000151103482d4141183d04150700715815a0308c908210010340f4080e408502440c10008000c200c20381c11401540c010502030b10100005001803145610082d01503440d0030418408400071003030440c49400c0542d10803000b620240c06d1842d010042030588100701001c607036035003012520800e650070900c94500100001e0b002480300c2031414114580364881800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 17878261 1250 17877011 17877017
    0x5150316081b070f0c060905010516031403010b0c070905070207051203120c03010608090a0b040b0a0905010203010b070201030509010b0d14070b03180c0a0308090409051905010b03060106031506 85
    0x5540b265040c1e15981c282c5152040066841d580c070300d0702c040490715411048031000280e05012480b2845100b028056403010b84455207005c4001e903004449139002c600c1242044100046101f280100030301450003843c1a010b0144c075228170900140c188009034004125580c648810070600950000304030017150011f072803140c41c00030800710290451181100c10905035000c01c042c484149084030045040716110707038407aa901c1c0c441000003912010014406003001074414007040104041600e00ea070003d916810000d15054107a4880f420790f0001d0380a14040300c40496100d05551705400786682c000c6140c1c00820180c11808000361150310703030943c082e203000c0c0035510501506c1030410580c0b01420249400c15140c0c80c2c0700a064421428920307140129002d0944440c00508280c900030301520b60003042039003800d5212091100a111030101070b00c0c1803050b004080f80540d07100040e4290240a00c0000c03c96803840d106040c608841a8820001c051600e502481c00c2d543c038500503015209285 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 17879511 1250 17878261 17878277
    0x1d060609120106051009030308090703050304030b07020f01060303050307260408070203030f030a0c0905041e0b04060b0c010903091e06030203070507051501180c02070302130207080708030105150316 87
    0xa40418010b08030f5400c1590851030744051008110307040b11556081741d120782e42e441e100e03607a51500c0c141c5804e101e1000800a51090005000160006101c0380e444503544c81255034008885c8107190a403030082d8026004114008144095264042c3c1141184c1041440583c521005030241446030b031001400500742c00703400300d044030440d58280100c0d0000c0902050450301c07030800009002c014100e10403044041040c0140004480c1031500550b40d04144404010340b20b0019110110060503044941c5540a603403a000845c0c1c400380c0e20003400c201e0006030000a03d1000c149030207040c007240e94000c0c0104041640052030b6695419101c903080d10300a16000d40c4035207805009a80900a4007402449400f42108011070004a13842d0103041702c60030041c510070303107800002140417280c98a42c0f03040180c00001003031004d41450480024440401a001842c2c402d46844080c07260300540021540e10000100400030341c540400c0000b40c0300104c000f6207256003008050039016041c0c05c8241c0c1d080c402c001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 17880761 1250 17879511 17879539
    0x1410020a021203091e01030605040513020108090c060c07090c02010605030604030309030e0a0305150703150302061309020f0703030c020c280b04090c0314040b0c0f0d020f041d060609 80
    0x303000303a80706010040d0005e0310b041092030214203c0d07400d1000c90341c002454140300062391f1070140991707070244528860034540203405800441381b1501c000c1c1100704078800e1804094098a130440203181a0641c0005001c00d40d003451041000d407032107404071404680c10420107102c0c2d65808507102d41c106905040c00140300b140341c074040d1000701c500d0240d6640140d0f117a80c00400d100000c910b907030040d141e9049407122036590341d10540c01c4030111016150058090407043c001410600d00801c07490030203041c0c0161565803640894242e900032600030068180105482c01007640602078513141d83c845001806507a41c112010442050030702207459a440341441e150001006440300c0c2002030012481200c0d0740d00d40b180c0c180030262241280002c002482d0a201e454200083c0b205240100d9003c0501500340d01c07046007504454020038090b1042400406c08004000c6541c0700504100404982c003d03140c4c1e1505a000c1e0003a030820310b0411241c03440004101a0780c4c0d548085580f944400c885d100110401 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 17882011 1250 17880761 17880763
    0x30504061d04020403080d0f05040809060901020c0306040317010b031b030c090907031509110f03040c08010501080705040e0f060a0e0304050411031b040e0a020a030e06101410020a0212 81
    0x7500401a42161001034007206005001004150801c0e400c4400d0040b4500c00084508403102120007401c0c105040c0546511403401c1401400f280c1c40510445180d41001400a424440c09850440204980c42c4245401c1f54a10010314010200001410f0462a00d4542008824886840c5c45100c580000001e2880500041030f612400c101800102591a0009000d001042c41500d84a0768043e0000005908034088c010368130042e80c0c02841074200342c1083c400b6000c03600b014004079106800d00c100468840d200744140c0303008200c5000100001ca1a050610046804203003040860390802224058400d030000341e000e0300064a048001511032002440c64154000c58010a9015003031001303003031903120760f100070b5401001c1c04103c12903a110382e0081c0c20301c0d1348554816401c06141c01c00020b40c034140701e80c2c080c00d6441c801707040100328405041e1450341040303000c823002c0d44480c103a00700602c002c4294402c8450308801c00d44441d841040e0300c8801a60740e09001d20001d114440b042844401580 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 17883261 1250 17882011 17882057
    0x60a09060c0816050706020111070c030b060604080a050304150f0f0804022701080c040c0215060a0308040303050c0106061b020415080703051c080114040911150d110703050406 77
    0x32420f00b515a440418a8003540b00c07110b5218401c010340c20300084503602c0a20208440c2c40c03d61001f55007241c146190f8994004200060203941e014500f800001521071091144600e581d10038006195a1410131100341c100741c103106000320402080320791b110103103a040440c1c1588000c0e1800c0403101c076074036880099071004802c0c001c900500010079030044c43c0c00455518506030b4490701d060354010080c641c01c0c80111050400000700507804008c41003c800b0700320a240b070700040c02519200350310b6100c4e21503484c1544240c0c401c500068002482d82003d00b428480e01020744003528011540e0800b100c80e1440c1c02c41000b00213841b641c0d13205541d044046d600100740c8001e080a00660b003090307079241003041d1101100c0d41c1d1034404500000f2030280b1030f48a0140c0750b0580d103c90300c0003440c0d550150f091200615841008031440503c4a60324034040e6107455180c2021211089069540ea44180b6100c041c2c410003110004105003d2100e4030000e900001620103445040ca402d00001103811140c1c1e007020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 17884511 1250 17883261 17883277
    0x8070317030c071119090903090b21070302040320010e0405040c090e1501080a0c06020609030304030f030902130f0605040e15060307150c110102030a0906081009021603020606060a09060c08 83
    0xc1c0403545d00003a002e00325080b4485141c003c1e00e0b0a03440c20380d90003010b00b0500c80c0208401400c0c1410030f0070040000d09111141d000310451400605217a00d9966a210201410000032140d40c0c018440403042e40e0320a185106082c01507606200314103060351009520312140c080c123401c4648601b468900590300b00040d0b0340d800b00194155900d035035107051031506c84441c1e030025120407941c4034002c00c4c603078000281035002c2d81c0765038019440e507980c03a00d045895129100d55042050b48440d00314015986030b600f988150300300307040c00180d4152800c01460844001781d12039401281081c0200314009404142880040312800c50354901c2d82d180c400080c1410b0b200c1c0c1140300024030107030850050740d03800180d40d05554410300c1000f0121910500590b9207000f05644540065107001c8e05210907442030a0b03d41e0025a21815590030359260200c000036600190450512407515603000014540e04124a681080094030074514140c0d890000505841e420b01590083c4000061100c3c1000b440e04c08840c030319 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 17885761 1250 17884511 17884549
    0x3020f04020c01020d0209041103090c06070f05060a061e0602070b1803030301080607080106091410051c020d0606080717041505070804020102070b030603210c01020408070317030c0711 81
    0x21781104c01e6443e009421489209025a14200382c0c25030081c401812070740103000c0c140051810010f20401c1111a5100417001c88800c241601c8020000320708014aa002e14040c070808282c15080c2103020b41c40681d550304050709080d03140400c001c12500800e480050311100d50745542d0318a072000701070082c95041910150188800400000c241001050a5009058a9075901e4017a680d400080701d084d1054003810010811080c8259090700d8803081e0302103610309900301303e402d000c0c034601c224001c2c8400e1040c8014007600001e8241010619100d800301410480c101241c40742001a0000c00050f80d0007500c050140b0003002082c2405001104100b000c10310000a0001303260034840140056030540e01240584584480803c004014034180c1e48500c1018005045000340340810444802e2000034030000e40d9020081c4078880710080c0000c00203002aa4010b100ca0b91452a00030541400e07441c44240c0d80d8401d00501090614000448080542205d07204114080010008000010b819000000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 17887011 1250 17885761 17885767
    0xf03070815040326060f04090204110703030f060b0403030c0305040306090309090b2d010c0c0303030e0f03090307060c02030c0d1104110c03030708180105070e0f040b030703020f04020c0102 83
    0x10086558102d1059119603030300700002c00360503040100d107264402c04c2c1051581d0907001030700f541070906800900e560f00801c08104811550081421150004040908108006900801c1c1030301401544100d0945002c00c01a0707918001404c100741c083da002c02400c200c0022201000d0500c62416100510307080301c002c0100044501e000f90442c0ea40b8407a000496007442c0310b56030b103882c0c0000c0c100390404e500286014088411801451098114807000c0d044c45078420140022803e04040e00000d141309881c0050482451f00b40545881c41d040a003c0640e8400c0182d100682c4000c11180122011810054211421440001d0138107004100403a00300d121480300340140b01000040c070b841424203403010891051000302c005201d01c00c180c071503041d039071040001c907001500c9a54016400403120203440c40d010f019000782030941c1c00680d03550000955a1048030340700d20f0000115400c0000842d0108a0000c0480102e600c039511071101034450b80560669101544407601200e440126900007159 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 17888261 1250 17887011 17887033
    0x160201050c0a05030d050117010e070504021c05090102120f0106170a06050d06140a0603080301050d0323040905100501020a11031c02010e0606010c0206041203050d0504060c0e010503150f030708 85
    0x281b009103e540220448c0d0540317151903810612900c0034442040029003140fa05007410310000c1c0d0311045155035120060704a07100f01032a1445014014036003000056920f04014040200c0783e1400703020884098070303542c010002c65070804105a00e81300c02c4103070030719240d841d80760110040405034040c4c1c4d048102c40c070003082048038036030000240c10740c2401c2d20600c940b20781e40f0b8001241c0da1400014010401080140802e1500d012610140c92083c5000003442d4950350254404003252410760302040d40105040c4402c618074014984d000011003211225913107001c00003503651a4140c4094494019800099030f00d0b202800000568480100c08043c2e005040400a000f000310560380c9409004650200b000381d882003c002007499002401181031904000801107115583c00c0300300c2c1813200030004e5103640e00090103094070603401400001028aa200c5025000c0d12802c40c2880c1085010010400d482e107078140f1071940540e00b43c1d00c5011405054001c030b494503540d60409903070780c803681d140d0700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 17889511 1250 17888261 17888287
    0x15010912030e102307060603060212040b01060c110d0507080708031210060c030f030b1f021902010207141801140102070b0903070e04030507020a060504090b0105160201050c0a0503 79
    0x901804140c034420083c0300351980854015041e4808150900032070890115880e1050001d8003107103000700700c00101c00380ea0baa22101240c0c05548a460360555000c10881030185818070580181080d00380030261500300d690b0020500c50103490980300d010705446120034080204200700c040c14084088815440e142c035681d503030300c1c0c00060b03950320801c01d0f40700011041c0c4280130f1418116103050316401c5a0310a02c1c0c1c1c09440f001c145014440415a031f82003180c046940da001c0301a00d0401101070741c105039003203400007801c01c0401c420702c140c0c11020a62100050b640090900d084541d4903103288503051200c000668a554810003264000100f1030000c5020617160081004041c1c1c00d0b0200c0741081c0d40d6a80c6060680501807049900d6004580100003044104021a602c01d10a1504a00d030141c0e542c0021080860741d00b001c00041c8010500b40f19608251040d40c48644090030440c1c24400e14003084c0704620981880207042240206075004298001c000c15178046511a003079940700c5c09000c0e103407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 17890761 1250 17889511 17889527
    0x306010b03090c041a030d0c020604030303020c1005010f05010e01080402010905060c0102090d1101080f0115050d020f0d09060b0627031903210204030506061e0d050102070b0c0a05031501091203 85
    0xb0317900c0790250b251210451401403001118442e4090000c5082c149140c8050300250051080300c60300e80900c400504a80c0543d1140030f010309481000100d0140c1003000041c00395000228031030500c60480203100161ba0060b282d1012034604507100b581e901c013507542c031601a0068400007900140030807520000c100c6030f0030031074000700d40c2070341d0300421070b669401d089404d43d03800c0c0309030501e9498441101071080d10a0380140b81c0e90860600240c07506581c207e240105078131003001c422800d070769014090104102d074020640e11003c200d40580c01d0280206440a40c012940541800945417400011040d01c007030100244203c101c06050014600c24100500b404c00301c00107400b0f48a07000324092410f1501031081e80e06480e0080300502c1542d48040600c000b00f600b0001c1e0710344a00c0e40b5980707a516070392400c1e00d1000c0c5910403400503850300018034200f070000c0c7c800380032440b00d8103060041d803001951010641e0303070082030003d4107845c4150312130069400340f606800c02c001e02c1ca0010014404c0c940c003c140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 17892011 1250 17890761 17890811
    0x408030f04080606030109030507060207030c08070f03140322020f06031305010c03110901030c0e060c07050301151409040602070807210806032d070905091002090306010b03090c04 79
    0x80c3e86107590744104060880740c0320031005010480500c10500492056409000642c4c82030500081121482d00c0f0303041a038010742c0c1e044070030140001c8203404050707200c80c03407801c0943c030100d040f81103003044080400811080514000c003656054030f260250755441381c400d100c3e40b00182480d039032420b00300d291090600c030024040e07600d0760038143e4600c2454801d00c1204600d46d007511102d418541c0c103034011406402004401c4080064070f40d02100955101c00081000b51640da00515581e46050145800c0d070303078402101c0c40d40c02d004120400c0945240101c601c8603444c211141c204030703522454803500a0283c210040c0c9008404500d0b0000c001c2c05140c540201301300300b5202030f10018046821503e800741240c84540540012083c0c0000c103000ca080c000600b05140000c080c10b1000000716490140191301600000751550107200340c6038000e0200c150040c01c1c07a0019450311100d24046940d0f2407040c4640c403106000000000c10043d0141700c1d014031140014000c2c0901c080d01464005100e0203000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 17893261 1250 17892011 17892013
    0x50c0309130902030d021b04020f0c0114090c0d0803070503060303040b07030207030b01050619050f070204050406060f0b04060203040e06010309060507021501080c01170703060e09030c01060b030f16050408030f0408 94
    0x4104181c14000910401c68008003887c446090020b0001c2c40007a400ca01da440244480610400c218a0313001e0145500e12041d1603c01c5c034141c0f8018101ea0310703203080c408155004a00c02114540031400c0c09085a6000140342000d5560f5251751000c41d10310f101342e50142070407840201c5c00004055010030040e08070380c081c201190603a6203810803c1103e2113542050307512401603143c85045103000d41c0290100c408261010b9060009a80105040d10700c210b4007209c20603950b040506c0001074140703556020f0516005840e040a0a225019540344a03500411000c94a01d10000d031040e1320076040745408030340c003100070701c41414440c80103555041080c0700343c03c00d60341c003a00104464600007040142580140d4a49081e5040f010b501034195001400f820201525200045000042c40070058003d400c07200096660f47d00c000c6409003142c010740c11451035413000300244090016251289a0081c3c1010507440401540481c01d480d03030320860780044124080810300a8508905801410407500142c0c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 17894511 1250 17893261 17893273
    0xc0a060e0a05031c0b0114090405060307180605030607030c09030308040206090d030e01030b100c0303020f07050105010e07030b030a030f2f07081002070803010b03130506040b07030c0905030706050c030913090203 93
    0x90019174103000c210001c7c504200301030000811a2510b60001c58000202030196680c6988841c0200c0141d9100a07610390533680f13818040000703040c00c000741c682c001101d1500f0400342907004c0e402030500070503110103800c01501d1804607096640700012184010310040c115500810303546006000d0140245e0384a010900d070a20484050501001c501000d65036030b0703581068251182e805034025007140d8140c51408005100190003e0b90034850f56001c1d00e6900c0000c0e00a00d44480020207a0390061078040c0240c00090075140003c0c0c002c900b44042c525a03041060410010000c1000000c03000c0c04040c0d5000340858080350000300204442c4140d900305003e83d075154001d404250b05a12460000914100003000100a200600300117550441d0000c48000e000d5141c503281c03185020001e03641a502c8454a074240040c0c1380d054032618a4100c118107100c2c82d1689001c000030f032a012288a0f59060000c0005c00308051764090084130070340a00200302d01800b005000c4508000c0685400413802803180b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 17895761 1250 17894511 17894531
    0x5010e090106020706120204030c0602072117030a0f0614130e030301120201050c010203010602070e06030d0207030b090a061a0301110c03030105040b0409060f0e01110c0a060e0a05031c 81
    0x221030914160360301030b0018a13089140c540100c0f055a030410042c0d490303660900000c00041c5800c0300c0000200a503500800c109410300b0360260400c05031001c100b640b0900d101d40c8038009414080d4403107010660354021030301c0c0c1e6138014078500a8191441c0e4001d00034606580840c5000f1404018581e1220568800c803001381c14488010450b074400000d90084d60040c0b00402490310315150000e0b0192040c03602c0d0382030801c21130843e0b0a83e0001e0b04004096000020b00b84004c4001580050348264200d001340040406404080d441d180f50f0301024003241c0042c00014220300302004072000a650268041000001403a05003941003a1042200d22035420728035004422400780c0256014010100c01a40c075507440d240030030005200c00c0309455001915442a02d0101e41e19200b034080640c0c00340c202140c8042001055421106a000030310359460f024040103080390760001d003044410394880b2002840350800310186192804401c00100a40300000b00e030340048075100d2104440d0b40c05880103020140d90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 17897011 1250 17895761 17895769
    0xd1e03030b040903080604090507170309010f03020f3405010212090703050d121118040c080c04030b04080702060304030f0807020a0b04080d0b03061503060609041e060f02030f0105010e 81
    0x4102004e80056041408102c0b5490a5484414240d108408507401071b0f0b510a66455603017400c0003055095000401c1c9175809517001183c0000c3d001003403504500c2c1909104407280e80d07008060550700c00038408001c0c0440301420310305000030b079401c04150102200c01880d0540c041c2d0300800031000800e6698001c280c01d2400001c00741d0036254030102a01444080312002c40c0e5110f103122200500940f40c1e060440400c4110740100b9004030413581d843e0748103840c0307400c0c0403d88202c1c00c280300804c6003100c10003010300304ea80c0c02d03101a203520000d2006a43c42e6400c015945005e55000603500c408000103100070190080e0f485948000103450b100c804e603403921800c0c0c0c1c58001d11440030f820310400c1c10005001500501c000e103184c0305541d00c0000d070034607182c1c08245010344c2203404899443d88030240c0c2003180340030408598080400ca5840d041c51820b50340c0c6010400e41040c5d25030030041f00b030b89008100000c5401450510201d120110748903d4070380302a02d5050020712405000c0740c0c06110407146414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 17898261 1250 17897011 17897021
    0x204060e040510031205090d0c080c0d0510020a090b0f1b0606010c03050c0f0a0302030408011415010507140109082502090402010e010e060d0c0e2704020d1e03030b04 73
    0x9512242d22040c686540c89018000c5c918140f20020094108001e00b080c0c0c1d22100000c2d2220f0092168111450801e18080d282c400c035009107510403100040d10500248000940c07640c1c1c10003141c405030300c0744c055a40a0b10120b0240e000006102c07404100c00c5105140c00020303090203610000f010b400c00d02403000117a01e49205603940360000b1031030b24034000400d00441c001c4c000312140030119980800580e405a041892042c4220f0040c0c100040c100440320090180211030300341c141e03881481d8181a044080114850300d03010307060080105980040c0a1131101700521080000000d000f01d801c940780c40c0c96076500807a02807480c24104400c040e00c0c422803040e1560780c1c03a40035000410b81d0312203030015501e828540211604010200c400b80e041c6882da10040d1440402014001c140244154400340240c001404490700035001558544c0c0c00300d00b030110a002c0020364024904403a112400850700c007605d81540601403011110000c0c03c4002010355035298140170b0303902002402840301c00c00c02551 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 17899511 1250 17898261 17898271
    0x10e060414030c120705060307090503010903020a1202010e0718060b1b0712050a0215130902030a0f0e03030406020705011b02030c15070504090f14070c061503080d050a090203030d0204060e0405 85
    0x140c0215030034401400c0080003540c004092b03007401140079030b480001030b00391465000200c3c010781000c0100c0c02004205168055440190b00003440b120955405543d40d6000501c101e00703800100081c407019841c0c440c0d111001511300c010400c0d948104070301508440420100e00c84480d0310815000180c01040c03451204100742d8030401604420741e140d001c00c108240080b491b43c20010042000011001483c0607034002410400300250710f0340b43c0040d03128102d401c0e20507408192820994047c4020344040104c991099015800589504140c1440b070f005207003440070010301200049a0b10b041c203400201500090040500705c039484645522081d0108000340c0304480415400c0c4030500080b10030380c024000c0d00043c0d00b40040c102ea120801c1440d13450064442d02c01090f18041a8428491640525418061030400c200612481c682d191000362050010200e2016614008a1402c41d0190440700480d5002000c036616081908000c00c000e501501c20000800c00328602e0802c00e003464080c8600c03070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 17900761 1250 17899511 17899513
    0x1090b0301090203090708010c0909050f01030b180123060405150303040603020a02010212100806090604050d0c03030902030d0315050103060302030a020108060105040b03010801020405090903120411010e060414030c12 95
    0x580d180a000b500030b0742010309140d4007070080c40e0300440e5200091140d401400d9940d5103007441d4510308844141140d03400b511031144841003400510114450b032035919089060311900d03d0707a003001a1444c40c014000041500307214a400141031001030b01c1c0c2c200c118054281210100940d0b00d030416408007520800c0c01803034040d00b040c0410481d80f03003ea03000c2c0945501c176000262030700d5107490940c28518400c031110b03144001414001d1100d01c3c01004000c0c0d0001d561001000f16080a8449550f12031a882000d81003100000e41c1030101482a04207448c0c40da03000d0100c508803107503040041c2c09002c00007608461151141c400180941c802d00030401280e07005005000b103406150011200000001d0010781400381c20400001c02d00350b140000c500078050074000603103690070201004144d040280c09408950700034407020342c106062401c456005a4051401d605040c0c24000580e450b001840046a200c00085000a021100821b20b41004c06088003a0717882916801c0400800c0b154080008000b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 17902011 1250 17900761 17900767
    0x40c0317210705040b0415020c060a0206010909020406080a05010516020c060702040207080f0d0b010212270f041401030605090d1205070c060f090201120b0d060203060d050a030809070501090b 84
    0x1101c60640a03881c1c1245840c6019454181c988101810303a510980c000c00c0340341548101c1a90030380c0d040c008410001400c6031140c3c80c1c400303044402584c48106010b81c0e00095032f81e6441100315546c9600000040c80c01c10142d1301418100e0a100d0300900088411110040c0301101d0060203d2002c40d60101900c00100002c0c1030004030b40900c0025000107004544080c3c04200c80e141c7c1090610151104d1800380a010032803107240e500090074080c20224401c51108241720f02c1003001014400c4c00380b52140e00b084d2800010104001594101d101c040050f0400e181c988400780701040e520070603040c0e82c06201c1c00d10013501d4407181d06030341d0501d01e4203400000c3e09130815040c05c580309400072070300084c07189450301318511035464420444140d1088210700e00d507283c030800c0031940c2000700b550081040d201d0400c644082c080100f4402e5042d048000d0403103500100080640c0c3e20454102aa942c0080840c4d0b030741c1d00e091038040e0641000307803201d5030380d4410b0a000161541c031400d1040305030340d20b000044d41 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 17903261 1250 17902011 17902057
    0x61905090d0c020301060801050906090d0203131217040603060302030c0f0906011805060f0304030e010801050f120307061b080a0506011209020105070210030c090504020405031b060d05040c0317 85
    0x514062502e104076450354130b41c14005440381e0240144c9005400c45000360a20381480d103034991030442c4d4400c3c40403e40d00240701e42030380c1c403180100510484950507040c4200322418034005080b01452086104c04601c041404906158941c0c4900705880c4241c0894150100c130b03108002041d400e2003a40c690001c408000a00103520400c2c250020342c01e01a0340e440c4461721200000c08981200c2c43e003103000e400c0403041105166015200980390301c2c2c2800d012440394100404a0494045550150b0140007201002c0700c5886003042100c10b103e8016400b007041c0c10a045481180800c0b41c0541c00002d4016008500664440d12543c3c4c01614143c541194038071400265a0142c1340c0444e090b414004184214405a11802d030204142000c6540000d0111041c44000d000d44090781c1003c0e00a1b481484184001d80f40003500c524021480c00d811103c41c454140010414400d01003407110085c01c002c1800704200c40000325030184e1303219000d070304140750008003020030a020b03240c1204442017040802d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 17904511 1250 17903261 17903267
    0x1c02010e03030c03070813050904030e04110c0a080a0201140c070b0c0f0a0c03030510050303030c030a11070803040201020c150a0f020c0d1a01060306080d030e010914061905090d 78
    0x19038002009410399003818102d0102904503003040006540003a000145040c0b0300c403019090001400702200c00003600d08103528000c091087c1c0d504614007d0b81e40c1c2c81050f0184003000f05640140c5140b83c1101c0506c40d40307141c42d8885d0303040502c1c40c41c00f560030841000c2420311210b031914410301c0045001e6080200c180c80b0610311600c040d0088807000c004101d9003400c119030400a10240350181c984100b211a640303001400c5800042c030301c01082d00182c10034021642c000c030881741c00c10345106c50b494072a240c178031608005201040d0302c0d1030205000944101040101005144a40d000340c003516207405100042c0440000260741469140c05d040000c1d250440c05041444075209861046441c12203004000c40c071508800c0605865039400c2e02d410700224000d944143c0c0c050104bd02c0c081c0b0415207400e00040d90b420101c0045000d040d150449150384d11000d40c018020190442e441444140810032095281c3c0c000b0340d1118208410041d15003450745050051500480100d00280f0111008250032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 17905761 1250 17904511 17904527
    0x1060b090d15020909070302030f010506180d061d0d020106060305061c0302010b0a12140d080105220507050d050a15060f030b040501030c230109030f0f120216051c0201 74
    0x16a4683c240300140050316222401403082c0d0658078016501c3c00c00d681c520400c10340581c0310314410740d030070801c150305c1d481c07828902d0402c000159605641c1e4400d901e09007003c1c050324851342044100446884000303550001d0070700042003a6400812081d611110100c041e150229200c40e0030403000b1001a10000c400f056000d1094000e05c000207038400e16100195001199501c030580c55184031a1903070520015418260b6904003100c0100704040c0c05c490080c01c042c205110700707071240b0580d00b9450003071485903050400c40755480c041007241d441e0088000d81150411030069601d6443d103000101c05034828400c8104ca43c0200c1d00c40841d0a1508404031148040120850201601c80c1c3c41c51400d074030351780a5103010b58850400000194240f0100440b05241c0d105448403403004183d00c124180d8004075000d06907078000b800d03240007080b40d0410602100340c06d1001440851020000ea80c56030b800f281440d02c4031160980c0103181a5128200546503110070542e644c2602031403902001980a0719034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 17907011 1250 17905761 17905793
    0x403052413020109180e0607050903010c020c0a030f03090803030901051005010f080114060705071202010e010503010e06061602101106060102030a080f040507030b1009110a02100c0908120c01060b090d 88
    0x201182d009a00111b0505003103042d514180840d8011940700c10a00e821b018105a010052005100f9072114400150040daa548005480080f01840c0102410321a00018020f058202d00301c075940d00300260a1802080101c80c004822154402c01050941c420a0501c5000c400c03130ba01d00d80d00ea42032400051105110300c020704da1000d010089070001660030b1141000a01040c864030351100711500015103440a240d85c01810004d04100500c01407191000701900204140c90076034454406035a124181031403200c0c0650310216003100703408615407050030000c5905510040d2401a20340c6001a43d480c000c141700b96001c02e00c10130000d620482d5418101d81c0c480d0058003143c00481e80c984803840700c00340c04d8814803501042c0131401d1050061a004d0218050310000034035117081d0600390025100e030801142989019100c0d202044064410369650700900480380586180d03110400c10004194000c407001040e0394284480050980c0302d19042d240c02d00740140254400d101c1c41c3c1c0d0788840c01004c03545 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 17908261 1250 17907011 17907059
    0x60a0f080a0b100908010b04062103140c01050402010e01020d02030a030b030304090606110609030703090e04020d080c0a0b09010e0c10090b0a080403110601030206090409080403052413020109 84
    0x540c2005690f090b4030516050310580300d04401d2030500003100e080d60003000b0f00794011800c0900c20005103111003048072840d03524100d40c60865040b490b08a40d03240031030307100104a0708085030b0a045041d043d440f450003036100f62650b021014051006980341c41e0303646050703805a0000d0061070b1890b4040e40001d002c0d500000e040c0e9241c280c640c80b80800711a80c0e900004005919014441140304040080a4100105000035402c1024030f540c0280a100c8600412010908010100301107445001610344900d07440420b45444581001401d641d902d8801c10950320100c3c0c86002c1401400103129000102900c5009400c0902811701405040d00d0a20035804c00c200c2c031484002520403501c80508107107070507a071340d5240905042c14014080d00301800c07410740c02e030048001000103030340719021505100d60558021410b04041d050000300c2c1d0085501c09042c60048403820b038040d40b0b80302e40f403c030a0002c44106240540b10b070305580c90742c00c2800780c00901080305080280005450f03186d011104080b220 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 17909511 1250 17908261 17908271
    0x180c050d0f1b020d08130807030e031f0b01031107020f06030402010c050106060e0a091506030b04060b070507060912150b0402070f1103010c030209241306050d0506060a0f080a 77
    0x450203801c003090032a500302c016040b0710080e4554503800400c1d0f603041602c100c40070041101c90740711140e591056400080622404130342d1442c144c0c0b01030201c2000c070000f4031408104105454201009000c0c1a182d5500207441c01002c4c4018444c0130080d686441d03005400503444202903c10701003264400b0300300f039040c48003950b0380c400001e4090048402030f0800b6076a151011015109101c001d0b00e003500102c02c1b1070b050a142c01c0b13400000c511000700700c5985280c04a00c0104c1e020105000784030603044481003490010b03100007030050000703107401280c0702c50391707000b0041b986c40203200050361414030300500c1c00c0d80d5005112502030700c031b810845d84007400400052074240c05688002c40305c0b00d125003c131440344040c0344180440c5001c0c4502c060140582c10290b01e80300f15500043c200a100074103018900410324000c00041e20100c041da402c03140481040b801e2152034420242c80c58200010883d0805c2c2031100142d145c0c280078040d22400f55454585010003005201c084d1b41800005202c0b030310595a070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 17910761 1250 17909511 17909531
    0x405040512030405010b030c01030c0807080c04090212180102090102071518030b090f01050702070b160803070c150c05030106050c0a02030d0e120f0d0c060b03070b04180c050d0f 78
    0x800e000b540210312543c00000d155004105042c14940c160f4034450500d440e201c1d02801964004c4c0c41c0c1948034666182c5188256a1708640d03103928051a04507a03c01c0348040303002d0400a6400701c07228050200d80319052071a00e59040840e00b41d01c10440728500507085280e08200d408101012050040e0040c102840c01c901e0f092840031441423190300c1034800380560130500580f244240103240c000b8800c280288028a04000301035640d0a480c07040455480d40001d821408998104442040c0e5901129040d03403400c221030001c1a907042010295811091035000e02040c040c24416040c00b01000e8035814110780c42c2490554880d0080c00707090320345006803048140140d80601078035610940a44403480000440801c0c0b11009400c5d010004043c1d2028a5a51100000241d0f4202034041850100c2c0300100398a0501c0140107801505a018403400b103010884800d0140644243e407041000c2c8208a640c00b280c01d01640c422310315140106000704904000a035003900040240c0c3d02e0120040b07240f00c0c507 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 17912011 1250 17910761 17910793
    0x60f0a06050307120c0f0314040b07050702061306030b03070f0303080610030f0f050a060503010207080f0a1812060c021501030219030f0c0306051003050309060307140d05180d050904050405 83
    0x8a81c1d0b6181c001b032038801d0098042d5806104045009600e03445031406440c180c1d461b4401200041c001606000e408140801155a00d000300c0d00d84915884031800d00b42d56840700035000e0805103000c580309004502021450f0b56054001404582c0c0681d900301d40d076141d0038140200500220080710403d511070130a040c6080075030180c9090883d2034480000c16103003500c02c0404440302c5810041c8641d00410184010842020640f0504245c41401c2941ca640c40b25051b030b8040200c1c82010b0040c480750b10002807400314003104d0001280554428409803030050000ca881d03404400c8000e0f498440000180007505188006003280e901100381c002d1741c5038580d16480c1004030259812140c2da59514410700400000740a010741103010550a80c10340c03405c56407956164000c040046005081c00b100140f1518416400d000301c5405080300143d4915500242c00080e0108a48112592000c0030500345110741c0000c0391205070f141582c8642c01c10b0b02103170801015101c043c006440301d200c3d4403100d0100e400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 17913261 1250 17912011 17912021
    0x40804080328170606090103060302030d0206150d030c03080613020d0203010f0504020708070305030a090209091005070f021504061103010f030c05031609090303140a09020108060f0a0605030712 85
    0x1810341a02e80031005601c2c0301500c07840380c0005902c1000f00030841c000300110b415100c1c98103d80704594154452000d000100c004000340d51000c2d500d445080081c512064004c5240c60251140d070710800c80c0d03e00c001c811b004245002c010002c001551403059280803d120f14480c2d41c0010340104102d01c2805030340d03c4182a40c100a19040500d07a000004020341c65803400c14500804064400f5402e1aa25072a404003078011040007405000d8004002540d0801a80c0300107480c0e613000f440c500440c00c11085007a85c440900c40070846040ca0a070104660901030071040c0070b01c41c1198010300409880c100c441c6c0c0ca80e10041d008951003500c0328050740c2c2d1402e101016602801c03207140d11030107036407035801d00983e901580c1c1c1c08580250055120883c24a11400c02c900a94103403600c0498035441501d405c8000300003140300c540c44030903142e0034092011881c3d0808500e01e8000d0346c1e9924251541009c00a4581d1149031050307001c040081d0800c1940c0c0280069a4041c0850503c1e00c040c0740041c090405640c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 17914511 1250 17913261 17913277
    0x1060b0f0406030209030109080a020f1006030b01150201060305010f05010521060c0705010b03070308131a1602180103060b0f09060f10140c0304170102070c0618090905030406030627050408040803 86
    0x82c01c501c65803840e04004002150de8484546c8042c01400d146440320b8401c0c090600800c440b114840300801d061074000d4012030010b640c00802046407201e0911308034018903080c02070f9845516403440100c0d5444e00c10b4461026000b2400141c20551100ca030440550391202c80111120754903042d48070394569050180340001d5004100440c0d031500030502710f1640503441c0d000520343c0700c00b0001038030910220303c064440f40c40003000340394074940301400003500c007101c490804840300034144008002c01103281c02100341301ca000e07a01120340803910020001a0001180e081e90000e200c3c1414415038900309044402d00002d074146880750301500c1009070319550010010345441e90001408100801c2111060741920f0741420086090444a075151081c495a62240b401004600d01c413404110041c81d00c0400141818070080010684034030740380d80c8941141c840d03c00883c1c40d10000040400058003c800c0090701490b905060090207038501c4014a805841914000400c0c080856440710400c0204804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 17915761 1250 17914511 17914513
    0x30408070317040f0b060414131419150b0a0e04030e1806040e07090606021506090712110403171801020313030b0a09020d03090801060b0f0406030209030109080a02 72
    0x38000a0902030004501c0a400b468104150780070480410010707a4880d0324694001c1c03005450707031111000280139003280c0249052000c00300c802d001c40196500a50300c50b181c4205091180c50485180d00d07501e840c500034000c5000350480742503200007200c0c4410728100070f5200da400070f200458200410034a103015008100c40d141e08105100071b043c1c1000410340c5d840401c03a403030700107540001c09a41d418170000c0c2c120b9000c2c030f8407411080c0c42040d0502420000c1d0040010070002c0070ba4810000b980c8404a83d1302c4e82d004d4080c240030654a0405412562150b841c47c3c4812010103401e00c2c1440040406a0b001415201c1c240004000900c80b6110100c9052561403020385400b036081001584011004920381950300c20840f041414120280c0e5404580d00021031144a5403503103910710180c00303101d0b0300035030180c1d414045100f003540001d1b00710150f03010728000700986522004400001d120f00b021044000c2c2e402c1c0000c000842c480d80003480f20007405400800c1c4401b03142c0c2c071442c80390080103c00000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 17917011 1250 17915761 17915767
    0xe010b18030d05090409020103201209070b0306060c0705040c03060305010507020106030308060f180403090f060207050604090c0216030507090c080c03010e060d05030a030f05060d020f10030908030408 88
    0xc484000c111014094114054440700c0074220b4040e1240c803440101502441d00c51403201706680c041c0c0d02c080f00e4052030b1185290014004403052a2581c020410546100800000300d05005000a1181c00f51000c3c005814655120103040104030f0304501c803440520710548401041548440c0151901c180c0161804036120b419403a0007030a460b401042c22045a01d404801c101003a8002d035401d401c00e170252119444c800400c004602c03d50304058150810100784400c0c4810581c0c0012904111445442c440070101e0322034a00300c0c0c0b11a06071080c070382e000009003c00d00584c0981d900800c540341d82801115142840c81401015000c0240e2054883e6000030304100800c40c142d00032444040071904e0700c0d403410324082c00080914081070048031070b20b009681c0002c00f162980051741030703029040b600300c0e03888030044900240a090800405003072142804c0101d00581002e4000020580d8010050100c080c030b10014800c003094804110010103440d101c2483c08202400019030086004109a80d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 17918261 1250 17917011 17917027
    0x80403200f010c0201020d0302030a0f110c190506070315081006050301050c070b0a1104050306040c05100f05030f1012050c040c0c0b04080717040e0610030608030906130e010b 77
    0x48494545800c0d02c0c140301d0b0126424005071384c08a01c8548003400c50030010388940b50211850020004440521000c0b450400559507113940c42c409800001d10182c222820780410202c4030300007a0f003030300c402082c680c89400803543c036600907080060552a4810016801c6942d000f08514007400305041c80c900613510002800340b82028080d15501100c0c540c50302d4601005660740ea00c01500060441d0042d5030356000248505000317408036002003500504540a0382001d0070300480703503400c81c803030b1500c64042c45002c0840c0d10f00035101c04203940c24940340d1605641e42c00310580301c102001441c0d5041480225008034050400104112a131b40c0600c00a000148070881403008840d00d04034120b05120081d80203400188480086581c0213034001401c5458200d01e00e03100414030030000d82c0c451012030110300401c81a0705910b00611171001140c0215010080c00780a8003240d42500990005030020050100c1070704201005018403418502e18040ca0303565001080d034110000e800c101c00160b40001c7c441c0e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 17919511 1250 17918261 17918269
    0x207171c0c050d020c01090302010e040b040213090c09030f03030b01030b090108030705150405070b0a02010902090a090510050c090409020109080319020607050f0a080613050c0405030d030501050d08030408040320 93
    0x1a0f040310450000346003014001001074102d07111444020304102d030561503400e0f5519248c0182c118480301030070654482800306c4481c00c2121140c080c441001d0300e840c1d08040d001e40305004110440c1e8001130724400030006500c049002c0c001fa22200c505050322011030b0714040d1100b10541c0d00070140d01020f543c47d02c141d841c259091800c01c00c4602400c11203041030001099000c42c40c44111340c034540350070399224039044041c0d001d45211880690700c10404001c01000d210715030441c0f0b1440d031080301644d0a8055000070442142c10076100c1c90408901030019503070500341980050081401410500080d5588181315843c40d8440c121480006c910b41d1907110510f40c0401c01c294010234142403031f03804d00704880600c203c0c030b004403250713001048001008a455601c1d0148084510b140c540d401b40280d2804504807101503015100c0d02c0e00900c10003a0005509102c1c2c46014140c540041c02032101c0031301900c4d0132045400c003a00545101008100000003d034180c0000400d64400903a00041045920108 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 17920761 1250 17919511 17919523
    0x50a090608010b090d0510020316080a020a2a02090901090201080105010207030b19020418050417040803070b0915070f0206010e011805040804050a0807030b0a0204060207171c0c05 79
    0x65428049400c00521848405401392034060900751030722540c040c1c0604045103060001520609518400010f00056000710343e01880b01401d180c0b5031001c0f54840f5483c1104078400d0028941c00038015403d12202000c0004040126010390000f01100e0202500000d8507404165070000040e951840c40a0840d43c000103440c0c010030090006d047c00515588960b01d400c0e00c028400841600d80d440d005402600740c0e03054402501d08261320601000c02040f850004050994080d40c90303c0e0010341782d11540c04d903e000c44040c1c0c0c0e05c41003c2e500b84481d0b43d9840303041c003c01925100c458050a0003070760340404181ca400c1c0c0700b0401513607030140b1b031440f019000e810004181c003c0321180001d80014450128600400305c4104000800001c0d1070b901c2c1d0401c021107004a40005034003803024800003544c3c090000e489002d40e40212401d501d240c13500e0103440304a104512074135001d600406000c11099040d031030309956446034442645d51a00859a26028800300100340001182c0d0503050442442400c2200c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 17922011 1250 17920761 17920769
    0x906090b041406010c0609051507020604030206010812040314070b0f1803010b010507020904170406180b0702100c060b03030d0c02010f1a100309060e01090201022a04050604150303050a09 82
    0x4200043d00b04800000c00310020700101502054540c000e00042000802000700280300510301e00707840d0f0034640002500c8510550b070550041c800d000000c140703e00040741c0e0314001118140c0303480c900351a55460002402e1100402c9140c0d01a2900004010b02242e0007801600045000560384080300194070321290706452415002c0d0b03141c030140e0021390f600513044440042d011255100709035149e181c440c801ea501c1854400c00c0400102c0c0000703820703811101c0c0402c0080400c20003480b003511403a0109150080c890060361043d215041c0801d03081c00741511841d1240102d40200304140c0900100b46141c0c0043c140d40080c81d510980035100a038280300d04110945103000902012114010b820016016400e11521422100408d407011038007a6100d61362081c0d00140503c050b444260b0400e000300010001130740580203003015880541d10350040700b80c00d20900d00040c11407610500034040101401080039402c96903d9110380c0701c0c20801c2801c0c00080d88203544286c0d9980c0e081100800c0a181548 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 17923261 1250 17922011 17922041
    0xf031403010e04060f0b030f06070f05030f0403050a110d05030a0c05090d03030b010e0d0b0403090b0301030507060305041a0f01180603030e0907020304031b050114030108100903090906090b04 84
    0x10041c00907078002c49034150819004500494a590b000922070010310b2061101039040c403e4101c030f10260100890150311800c0350ba00c0c0d8105506011700700359621b00c4100e4003c43c0070529a00002d00007401040a00703030700c03c103d1405004c03081912004070700e002e841c1d02c1c2c91f40103c0d001008000280e100e500607580f14030000d252650901d030400000c03c841a040b00001404c6c035803540c03244c0c61203901c11410310340c00400c000c160501020f82820114282101a60103400284000070701140002100084134100c2e64000c004040c06441d001c012401000007410882c3c0102c1c0d900380651422580d004c0d11406400b80c024200069450104640e0f943d1007412001220b00c0d08000080001c40d800c080e04003c20581519901429a40c000c022400d610582e0801800c010ba4500001108903030103051809072102a240c040961006102000035404240728810040d48a0484195072520315086a00c40620030f041003c08152204140c42c01c0c2c40d1990400c03101c140d910707402c590451406000b9990a580500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 17924511 1250 17923261 17923267
    0x106060c02130506131802040b0103090309060815090411031e0a0f020d050304151214191103090d090b03010602071205030405060a0305040605090106050a061103040b04030f0314 78
    0x64046282c24100344003000d04590f0301c2000407070300c1d1920700c0e0042d50010180400c2050300746001003442600d03c2444c06038055890804656201d500034840e0f000059010f46615201902c1c3c041c0c2110b01100080040104040c10701c2400c800f0b40320a074079a03000324403070b0a10008440785181410720f49040c0d04040401200100780c40c0b60b0010005c128400c400381c1004c09049040c2140c0045560440300394070007845480006400141c005540c10700902d511075a607520303007920310080d603080140c034400c0d000a40c4104030400406e4104801144601420320910000701d1420309100035041c20745c108503840b260503002200b40d40c018039804560b610203040f40d94111415541050002035441c5070b6802107500c0c10161040b03910910a0400542d0020240141555520300e050f11005002d030406540440b24941042d01007020310206002d103034152000508141c83c82c0c1d103400e10464010f1031a02030706426010801c004100c07080072500070005540920310700d00c030b214003903d0014807090302d80c000321120301028 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 17925761 1250 17924511 17924513
    0x60501050118030b0c0c070513060e070809030a0518040603030305011e08060109020a0c050a06060509090a0201080f1305070b130f1401030b0f060a031e02040605030c030a09020303040b07050106060c 87
    0x4000b81d80d40112851005c641c80c1d8440040d20f078a00f00281d00700c3c1351701071094941c1da481c0c418641c01c00015500c1400300401cac941c8400360251041c0f40140c804c511550400c5c060302c0c43c150301c160040c003452403025480c00d0000840034049421035580f85c109a0000742c440340180851019520000514000f400d08589994a402c43d2151545410300460703030380e244c00103a09280c1d9845515042c0e107050f000000c1d1050403090b07140c80401000c40b881002d0040700000001485600003007281480c003901030715021720075a0740d14104c40310001c00511205800780e280c2c0300540859420404036003d000300040b16507483c04519001d0054204560207400c1311070513103c09200310f0b00b1420f118154110b00f802c01185540e0b00c0d034002030030301c003403110255004000400e00001d1b841d4540c00609410354145000349560b0b070400842c0059210f28040d02d40407800410118001c1a0800003c56021001c0c40d0001400d0396907500203420f545c0140c3c000d024410700422090705005081c4501c0000b00340c0c50420744541801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 17927011 1250 17925761 17925773
    0x4020c15180601051c0c290901120906180309080111030702120a020a06020a050a2a02060c01020906040e0f0601020604020d030c06140705071401050106080c0c03040302040906050105011803 83
    0x10501130390307018441000e102c0241d1040c002d42c440580e03500c40e0400b80c246890b07142400c03040503440809003030342ea00040c0710200385203036004031582078070706170b5416003c1b5640c050580003a0103030000c212100c80d500c0e042260411074146030034040b10b2090343c0d02d486c803901c1c3c03901403401c1d02c490201e6901e000d0360400900420780d40005400310342d41c400c2682182c449055a0099080c0760713964502508007030000400015055100f0028071296007542c5820002c40da241d103013030000881f214551011031a42078510380240c507010703000e008601c24075400589080703450004101c05030000c5e407001130900500b0040c00030b00b803004069154452002e100400c41e5162580001c2c0002e1940f85014060080811003042400050342000c1d45410040442090500301000002d00310740c001d2006807068605000784555101c410f004050403911240d4a03144951120303807450380e00b82d0110752800482d00c8100720010050b152402441035442c0101c60014081d03242100142180c3c1e81100301d1003068028040c00d0000880d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 17928261 1250 17927011 17927023
    0x20a12150510020109080403060e16080c040b040204050301060e04020a120302190303021905040f0b03012303030d050408030609060105070210050d0905030c0607110604031b020402040504020c1518 86
    0xc0704075071424a4066641c03080e030051981c01030103010a50700007804014066150008a80d0000c8002100c540f43c4c2c501070310201055050140203011342180004d080310389096005100c8104008000520f80f6940764006400c5078855400f8208800c40b401c2000150300d000c828800050540342030074000302d4190f99000b9150302d000c142c05110740840c0080002894403940c10340d100103d01882d213170001c581544003c0c1182e0002d12800103201c103400004940481ca03e82039904848011030030440e00040d00c612072450321104d0140f00c2d09444140014942403c0c1130103414000c900603031085903030f41001428001103030b03c0205090b0500500b04200401a241e0861480d4040001d2800c40c0d1514000040c000c0603248800d0090054030022840c50440040403804600503400c1c1e0b2548800d0320f242801d826100c060842c2c01501140c060800460100311108040245501c010300041ca06a00c03080003d04036000440c200310143c0c8030200300003107178a102c9038040e00004251903801c0194a80e6090950303501c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 17929511 1250 17928261 17928269
    0xc0509090307120c0f02060a17070203070b060d1b15020c01110c0d0204020910020102190309080a050307050f030106020f0c0a050604090b0a0e070c05010501060c08070b070210020c01020a1215 84
    0x8540d1345100c806100c9040311914919034000d0085545030285100248a20300189000c05058200701c08035900310300001c1100c2400b035000c115800180d0b00e240400c08840c401c00d03070545040d50104080b200101244401300040e06031007841c00905901840020b18000740a800700d8144181004401c80e16280000d804122400880d03071100c10030b65910104010340901100c06030428103018003080e81c542c06402819a8042c04c0e0001d40041c208510110241d9040c00c0d03010704551420400402041e201c0d01c001e540c408074504007146021200800708070150b2003640843c006804c500c03000c604010b406d204680702c0c850b04607038441c4e04604080026510f44114070540d040c1c0703982c64414840680341c00e18058024840305440706030510380020702401102694404a17469460700b000420703080d004400003810301d9002075025042ca0032a0b03450090010010b0450800d41c41000140502e01307107240001e02042140400140e00c5920703006000c3c1038030003104440e1803014180a82140c0d4010000b81000c22a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 17930761 1250 17929511 17929517
    0x709050d030c0203030c07030201030f0504020603011517070e01020d020c03060c0a03060503031308070801020313060504030c0c03060204090b030604050307080f160b010f05030a0309060f0210090c050909030712 92
    0x4092034901580c2c01c0c05124002505408041422090010041b60741c200702c038000c3c0c80c18403180d0181d01d24a0203c070300c00c450080d40107074103000500c0740e140284074460144050742810200001207146044400c2ca0072910140040c4010329001c025581c1032001c81f0340c03840390340000e203c0c25400100180d11284c00400e0840b24020100355090254442c0e04408010040034080d2552690710b050f548075144020302500e40d080c0320344480058003000c140b003140d20458861403981408030303440d5201c0001e058003420aa0801c4500014030010520300ea01d1803006500c0b800c001603889141401c44801d442e1840300c603074401d030041000c01001c20800b20494002c41d91050b1180d45c2e801144503d003a10b4040c030f00001000a1207a01282d0030021850403590580c1c0c41500e443d10003540d1402019503032038103004010700003408424100000c40c0a40301c5800343d080c05006640c0c0503101900c504084885110050720300b4030310130504101c5030603c0b6060a81186c4464040d41c940541070310340882000d5100030500030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 17932011 1250 17930761 17930779
    0x415031a1002030d0f0f0606090819150c0e04240506030403050c07030c030501060509010b09130605060a020c0f06030103080307050d1e05040b0f010f1404090606121a070905 76
    0x140a01c03d00840b0454448601d08000810700c01005000510b945010140154640f04002c11030340c2c06203040c80100d80c1d4160040c218050804015030340b01c00c072603500310b40f0b14580e918460444c100745d0250211410403a900c5240800e110303400c0200b59004c1c92441d008100030a000d40403012902c5805c0401c0d60800d40e1150b80c0c83d06c0300d01d022101c1e44591042c440f164010403201100300002c42c0d21400031280600e0080c000261150100501d4003000c0c406c444050004002c0c0f444a0308005181c1d10300c1c40d0103424005090b5a40d1030203d4a2980002d4855006802c210704c96034092a1081030b6024a0005850190441d811a6a1107950f8031018040c2e100340000401c0c58900c1105503045640170840d40030304400306c20580032240000d001c05580031180c0382d801c40001081d640d17034003154134102c0b0340586000741d04624000e0808828554510000d8105840f250420085a400d014910040503101080b61179010369040001c4000c200e13070861081c0341072302424003082d0f50340207400e1802e44e041241c1a00d4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 17933261 1250 17932011 17932039
    0x206071e0903380a050a0b010905040b010c0507060e090a0606081807030203160e07020f12090301150f0302030d05070209041112060901020324060304120512010305030415031a 77
    0x1ea07150910054088403103d1000d80c80c0c000791071800e82030181d22540d9041c0090f80303c40b908482940c03a05040c20740044c0c0b072144100821724060700088003480040c14901d0242206444150910705035402200104013401e804035001c1c24020300ba15030100d01e00070104a22401d0071001025120042c00c5000381c0c05a040750300200403810300041c0c0040d507004041f14200000b9415605200402d481600345011408001506680c00443c14114210070203026241c1e0f200400c000c0c0e19580c001450040e01596199003402500d90311456050140c400f006001c0041840c1d4810140341103030461800301045824002c400050b210b861280e1b401c01ea00480480d240307091900801c910413603800421002c1c0c0305e0300007840740082d810750081d8000e81741e10940a4800c4d08403400d600e0060041c240d00e070f422030300c1000040c0101c2c8000d000d03d402c8001703c1c9072061402c480c802102c00c0d482800e82003900c2e2600001010000410300c504204c03603d605c84d050601c0800000300d41d9058065000074143d000e4000d02407485 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 17934511 1250 17933261 17933303
    0x3100509010803030a1e050f0a0605031504021002100f020d050606070c030605040212011d0705010e06030a0209061b060618130221030703030504020a0e0c040b0703030b100206071e0903 81
    0x11345440c544146c200f00740d146c41003c072401550191200c0c2281c525050012482e400c0c04244c08448000322042030000e500c540c4d09104084d8003510345902140200c4401c07408035883c500070074403060206180540c855140103e0101120b0b03000e8070940c4103140030081000029180c4040b0f42c112604400000741c41e950f640003003001114440200c0b0015440c000e07001e040182c9580c031219105112500320b802e096207900054500600c00810035070303c41814000544641d815400610300350002600c000c2c1002d060707603050102403203060120070381070700900200401410004941050408035154540395400c048610050342c003204100a400b5108400c25942d180211103446200720051208603547c4480900f402001800c00740c1e4103e1207443d030503c000030310342c0701100603d0013690b02d51581e62406291200b0540c581c0c2c40300600314149510340d210b0700030035a80e2807001030b00420950064441d034903080c080200030074800305a941283c16152804258140d101000206880e48651440e503111000c007444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 17935761 1250 17934511 17934551
    0x613020f04020706050405070e01060507110a05060307020609010c0305011410030b0a0909060b030102070206031f05030604080c1e06010603020706020f0a0207031505010e04020d02131103100509010803030a 90
    0x100e41042c00000c208003080103540c00144200e01074010350b00c049446091021304c403030742071061a0000700705002c43c10110301c019030962815400100080c924503500c102040c4207030412030b84000560010340030014034039004c0c061a844042c0c1c500c2c00304010340c1408500c3c100144240c4400780540d441200400b8a14040d511a841902005000f40380b4070b070751420b04102a2100f441e00316615820480f252100e17003014020307107000079070013440142166512081c0c801000110160302c40c8400900d0303000120382e02c050080c1c5000700c0c058883d940c0d0340c1408100c42850000c034030703d852015040e5403810b0382074200007094045c196549444c0160351080581060806405062500b0560581c00203018140c1c40c0c001441c4e2084034404c07101b21205501410401088540c24418a034141c04810006001450000b91050b001c0e440200240d440f21042c1500d00211501e21801e01d0345001c00105001000c14204000783c010402258810366641c142224140c5900020b006884031540382c0f000000b15078020020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 17937011 1250 17935761 17935789
    0xf0f110f010e0d02010b06030112020f0303120405070303170601170a0b031b01020601050909070603050712090501050403120c090b030a060302060d0203010f0b0c03030612010219020604140c03061302 87
    0x24024000340c0e910ba035454a20940c0e10b8009586052011055400c0c02000c0d24101d920070300d01441d5041240e003d0003046480300f456558035000c20443c0944140071503c3d40c600841c0601d0050031518114503020380140d185410340c1200100080030000c483c2e1307000401804450158501c4003070b1313846004c4800050301e003040c1e400307034540a141c1d15440c03103910724034842801c0c03102607086612591340c0e0803e0044000303007520740c02e8031904103042c18803041e80170f500441d8000c1458a015040d041400210320122482d4071800c03030351139448600f40710500d94000c0070f05030701000394442000545c00810703010303210070f13441c2c4a000342c004408000226007062aa20000003540c000d0606582c0f0807040355a1402940b003402082c00314280441d002c5480100e100580b000c7c142d60800039841e5464040800200e10944042e0b02d60964003002200701c3c20312404042410b0f05041c0d002800203040a10340f0307281004507110f8180c11035001650040455400065140e08940d81e0342d0b600b0001c11440c00456089071502078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 17938261 1250 17937011 17937013
    0x180a08100515010507020114070201020c0a0902070506010b13060305041403030403050c060916030818040c0e03010506040b010f0807030e0303010e0a0e0c01080105010e0303120103110306070f0f110f 87
    0x1031450201103054020390300ca005402c00c95149041400c0040d02c0714010910064000350b40c044081c0d802d480c410340140314050050040314032010280c800641c2d0440340360030420107503401141500400034104031a070701601c04050341070700b049212021440d1554a52184404041d2644046400d001010102507104a8094181c030381d01d1405007400741150384580d04140a51082c10000794550a011524541c544039001d01c0390310079403841d2a00701c0f40303030403941000e61603209d54020408190ba03640f14400c58002c40d5110100d529141d00d003050b08450004003075a00542c2401d840b60001e07a40b00318800440b60550401c0981034540390011001082c44410700c500c0351000000108001c40034204a902c2050021000d10000091841c42ca4550208003440b6021a075204c005010640c000d88168146140140889040c10300e20070703103051450740a0380113556080380380c603a08510f07040611941e54800c0c00ba007010200900f010303500900d00020805000f0400c0f200301c10b01204503c083c40400b00d4400154 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 17939511 1250 17938261 17938273
    0x3080c09012001020c0601060e0d061d07030c05040c05090307050103020307020a0515160c0308011401021011030a060f060504180e010c1107090605061603030204030503030c0c010c0302030c180a08 86
    0x40020350017076010010f810140d205c1d07400009074942c80354504007103c6c1d0f40546003514001442d5255400740c120004000e0a0f2901c0100300038502d80104071000095001e8050001c5091511081c041240c0003042c43c8001c02804110030b84c171b552000100c0d03100704c034000e00e07005035a565014030490500c1e100d0f070001001c50040340c090440c40b104e05060319004503a024400c81c0e5403680c190003035a10660010006010882801c010009030340c0c00c80c8031101c103500600590307418a4045290404444940c0c4403c1900203010090055101851044001038040e41c02c00000003800c004014065028510640007403101c0001c4849859016401c101d80c52000e0400034005401d00392000b9040d0038100a0101c0e2130310440310300050f0103000d8042e4904880c0d001c1c1089180c2051301100c200d00c8030780001c0907801d040d020000000001e808000551040201e401a1030300d13508021100d034250340c8011801e80800d8010702c284090000c0c0c080c121510000c42c0d06400c403040440c0b6000c42e202d1340041d40107c6680c0505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 17940761 1250 17939511 17939567
    0x3040302090c04030c06080601020a06111303061a01050406020a0b0606070204061503110306010912050f0304080a0318150302090d150902010305090a0b06010809011e060501020c010c03080c0901 85
    0x42d01a0083d41c5c428030011103c0e07916108102c5a401e01121031900580c043c141d040080703203040c0e0204041400e040401071400851841c5042007500c80e91040b80c60590311401601100200c046050090740c0034038280303103018503040c3e0007540c441c0302c0300024140702958004641256504401c40d00034560280051003c1551000900a0311017100180c002090038481108288021901180d110f420141c481800b11801d0044141a198000c1d4046807144607840c030714650120100082e2000f000118010012107010b07190044c000300e11054180e0030003170404014064800c41450b0740045444510300161150030140008011030040713900901031090010612a4018454011008036030003a200fe010ba6240c164860755286c541c580064106460300707021845940c0300f4409250030018800010500c4c0142800c0300000b0045000c0c08581640d541d5410881960140b1150348440b00c2424406014001c584016101d0000204145080c0c440001c1a0b49560f024890703202c2800166010340d0050307484 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 17942011 1250 17940761 17940781
    0x50312031906150f020f0303010305011e11030106050c01150f090b1206010e070507050d020703061a0307090f0e010501090b03010b060a021506010e030f0a0308071b020904050304030209 81
    0x640d855090314a201e0740a070303003060407406450100c07410003080101d0684114811030b0400b000e5003840c000c6004103955141d0a4604001841c0654020400001c18281151143c0e80c4024410180141542440402504c0c0c55103036059904490886c00c1550750703854020b000a005003080d03580a1070b05422200c0200709a5807501420701550a601c2e41004000600400c0004000000300b041b026030f4848030040c801030984954a0b44c2003005030409a051441d00d58809040c80040e40a050040c2d01181c0700b007060081e2801035103107c54409041e4a00189044082030f1500000d00032900d656803110410a003552b0241c1c000e0140c408140001c00641d41c56480300b60107002840c00d018032960078125070111901d019401c5500210f0740350001c2884001007051506407090080c8941d042c00b00041140c2e4450314148100410802d01c1d0020b030400400502d000381a180f0060442da082007501e034220300c03040741c856580486060301240e2060360755481e468070500d14451608004e40001301101841a9192 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 17943261 1250 17942011 17942017
    0x3020606100201020c100f061a0304050606090105010206060f0102030f0406020a0203070b0a020d110c0907030c030501091109061b0a050d020c030a0b040602070c09020a05040603060b03100e0907050312 88
    0xd0441c0c401c007041d101c401c0224281e0185039489001500101a0320700c0c0300800c1d500584144850000c0400e51581e80c0624000a0aa48200712030b0890000704110410400340a81e0307078400001c81310303201a94100300000355500c0008140e1ba02424100400000360b0380200107603880d841c500c10401c5e82e03035512550021344032001050304074085d119400000c15010540002d039101c0640c580d004007045040010102c1310b00c00c01069100c4240950164190341d902c900150a05c00c501a84003c14207982e210001012114140d0240560300d250200ca41c2c0c19140c00300803101200301c22203503183c4400c203c20340660302e2801c0c84140b0900f4400d554600341007040c0407400c200000465026901544051014141c41e803902480003445180d000001400103000c66001d0030086000e018507400598542098804036808800c440d000300f10041010040950b03d030040d1409030004281190030750420820442c03540070107000d403888000001e4005042c944040007a003008003030081c125011480c1c90108418268 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 17944511 1250 17943261 17943271
    0x30813120c0b0a02030906131401020d09030e0904080406053402030d020f1f0b040c0905030c0f09060f031204030f0b0a1a1c0b01090204050f030a08121005040207030206 74
    0x46040000030303803103c10510030b60384907080140c0500710302c0d0384480c1103588148015904076000c030414123200c8161102407018122208000400042202d01418064100116540258802d440c041700300800600d50740e05075400c0300c4a03400c0c42034658501c0000300b000c1d1000010005d08003c5031017001f009200441e40f0f1505c80d0f03402602070b1031090316030000890b21103011422804072039210000240132110440f2001800500c2d1150002d8016840d50000d401d5501d43c0204400140c12410103002525007801000c1c1e0f80401243c03046202c410480c0840c1c030101d4000c0680b441180f0300d078540341c52501c1c140240282601c00a0920f0359458a91600684070007480c0ea05450781454000021400e080070301c5491110601d40c0ea02c0e4050b04243c000308007000c0d5010300381c4008040014040d100040381d0100c414041d20440c440580c40714141414816944030281402d442948081a950f020440007011a4411901c2c0701c0170034620341c0c80124240340443c05500158204d0310010343d40c0103050b40802c445000d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 17945761 1250 17944511 17944523
    0x60e01050612060106020606060a0504170604020102070b0a0c060216020d050d18050906040c11010204080a0506060a0f140f10050307030c0e0a0603050907050418030807080112030813120c 82
    0x81480c80c40e042e80d549100340500c4000d41d01003070110700246816800740072805810b29216140c1622038a441700203803030801d403e039415070041e01448115038040c44500701034a200f462403403d0418441004000d40c0c032401001d8040c0c0e5000619801e85812003401c034030074039000f40420b0040000e52034600c0e503554082c002c44000427041101034001c00b040120890480c0e400500348045904c42c0c070b04003c01009044140c0c0c040c003e081002601440c0c080c000760004000b480c000d402950100d0400c42d040001c0180b541d44202145e400505c82c03400411014016104481c3c0100c0100306168003140c841d0015030346007a44008005203440b0041c4c1d0140045105002c2c1c0e94040c8460348040c0016a03007d80c1c18a07a040e803010f2588001e06c0180e110741c0c85980c0c0905001c00f25000141c4d03032000b0800702c881e0056441e0300c0c55011f0000308103064002050f507412940c9450f1a807129131402d07080d01d02c20701404c10001d0030001048082038041c00c14414400780c95822561040c1100700d0385c0c4000d8107015244200300c8403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 17947011 1250 17945761 17945779
    0x7030302030304061415040213031e140706020a14070305060406020715050105010e0f180f0405060705070201050702040207020102010902040e03030711010e0601060e0a120b0a110a0903080f0403060e010506 90
    0x8110340c80000c160040f041b00c1003000e8080d03072941c20000650041d110000b07140c03103c00700010100304807045076003120034400703401c4c406004135061030005003050500310b482c960b1245d0401c1004643c0000e10356001d50300000c03d14200b05c981f050301420640d41d0f0b800030344144140d4041c002804040d0303008100c000e2003140100f1030040d802e901d50058880910881c0d002c104d5501c168542d505000224003059080100004c80c1e42c0707401c8858482096042d1465102e2481c0c6400304000c105d0100310483d00040d8a0411324205511740d03000a2140c0302e82c1c10000e01460b0041041e10442e4001d4001d5150b00d6030051092040f032109010090b0380e0740049408100080301100d1228480006202c0c1c00b80040d441030251110742c1c00d003402550780c0300d14480d00f1031700028106000a01c24440682c8901210b20031401030304541130501c0c00c4010744166034200c119034003080020341d481c0340e00305000b00300f125484984c6a80359000701080005d10b000316800600090b0410411a21100041d4401071061004545c030b240 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 17948261 1250 17947011 17947031
    0x3020a090504051b0c01020f0304060c03060602210d02090306070c020913030509060c03040b030c030103020f090f1620030903070906030210030e031303050f0c06191b050703030203030406 82
    0x1640d00c01d4070a090700d50013080030780c41c90000120051040030301034400907240c400311103401440c07079204480c00d031803181d600d01c0303d0313286a9810302030386e00107144520082440040d900113400d08205000c20306d8032055400500c06da085101c540503200c11a0b8001c00b17a9440d45460b0801410b01c0580c210100d00c603d00c5080003802007145141a002a1070309669403030b003059900c2092110b0341d8400c00c0c1549240c0b000340000154100840300442c0700c2e46000d1102da499501d148180401051002c0c03a540c890200081080040c21440a0703140e4810500c42110044100c51401075444001c400c803451241080651055040b00000008000012081d01103808040e41c0b0b071440320444640303010082d484105104100000c81c400e0300108054100d510940f4030b014000280c0d0302c0640c60681c001c9603542c00c00c00c00d01c03040070b000740902410048241c521525006202a41d0019840d20068190a01c5698080360183c4900300700a6151507a00c40202c2d14250384a040c06960382c3c00440d001c80d020741c10566482 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 17949511 1250 17948261 17948269
    0x11b030f02071e050d0809040501030311160605030705030a0b060408210702010e0d081606090b06030105040b060d0804051008090d09060905040902040f05040305041e03050607080402060c01020a03020a0905 90
    0x2e40d00b82824042c240c3c15900b05410000000500310040d11280c078184075010042e942ca200f110300a5200740c0310403407450f4101d9815402c4c00da0100c081c440c03040100204000c480d80000869a02008503d0301654941c0d0307902c2084010720200c0001c9030020390206000c1075130403000a80703541c40d450302c4006010043c06022054200e1084d80301c02070002e002e0940821803800c0c640c490a44162040700381d10b061007925211b19800440c0084c0c02c0d035445071222002c4061182401002d42c010600380c2c004d2001d49884c4d00c0e40191030b480a0604ca0140c950345503004103000029003500c010382802010114001c006090003814480151032044c11070141d0116144414041c8140c40c0c1118603d803190760b5407500d000d0801c402403c68020503030300325490712451090101e080c03058038440d501c00c6d125142c6803070800f5040e040010783c02d41e03010510004100180041140011a6684006c9034900345200c1e40e0b4920109403103000d10040e403000707036001040164000341c054016229141d110343e41c04040c150780d00200 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 17950761 1250 17949511 17949539
    0xf01050c0703030507021c09061d011d030a060e03090f010207030c0b09010507061b020d0903050604060504110303030a0506030c09010b0307081f030308010906080102090306010b09011b030f0207 85
    0x41180e00200154000a402070b040a41e00c400385006599901d010101d00001c0028000031440000388099003c0c01290f07000541940340790b4401549100d00f0948400180100c107020300320810034549151400340d075540401c482401c81d40c1c0090309125106031208800c0c0e41c3d030403000c4003500c40c205012f121701c5c0039440002c0031400c03a5000903001403124500500d040c0290301c007400e1a8104041007210380041001c030301030048211020020f60310380c17007490040242408402e00314601080920780c1c041010410000da11900319802800000b5603440714035146a80c9070102c0754043d098080442081090703030b40c0780d110b188205d90a406540c1055024810041d00300024001d03d07601d00d2040c40410707c101d1103440201d0b8000c0c1d62082c100c020004090300000c0144480d030003100001c01030b81c014485105107004220091003144000d608120070381000030349850381400b039208030842c081514411607110705000b05800e401c0584027042d40c80d50b82402040701c404640074030b02510414400190082503908a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 17952011 1250 17950761 17950771
    0x405010509190207020a0302120d020c01020d021b0402040509010e0403080703020f1615050c0408010608011503020910050a0608060102060601090e0106050a020307050f06100b0306010906031e09030f020f0105 91
    0x60090b862401010100a400c00f02c8140d0300004042c0c004001a1200c40300c3c00703102c40a8000800680c80142c0c002480d0100312041d090440d0000c0180940380c540000f0f0b04c2c003115408810700c42c81a840b04010030001e000742d500059100242d40c000150300d010b4400620301a031b0281d40c41119968030084c1c00c2e820b078450303980c4031003071103004000030a0701d1880d000f224481a4460355071940c001c014440c1c2401a10001d6401c01558000003e0402004400b44a40e00003408040002d01c0300700050441d2110f20442444041c0c0966070b07502c0000d000040d0300f01010b01500380101280c5c0303041d40710840200001e104481150140c440e040104041e50b000d200d0030021281c00b111101c1040e800c1880403103103078000301da0381340a61200f0700503240069014072550310480c0c008402022180b070145400e80400180c3c1e480f1450380001081071000c1640e1200080003038550500780030510300c4481008551002040c3c0b4107000051416802a0403da07201c02990001141039084074132503a501998a0300701d68003031320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 17953261 1250 17952011 17952031
    0x302060301140102010902120105070e0a03020604141c030309030306140901091805010219080601170604110405030a0c06030509120d0c0e0a0b0403030816020316050102040b180405010509 82
    0x40041a1441542d0342c600d102c1807002090690440d4007040c00140150300104840c1d4540d01000078840d8404002c02c0142800c0382c5842c03816103560081030280c841d601035104890301031124900340e521351f20900102d1100f00c0e1040300300c050440c00c005004280480d42100003d041140000e00d8800844c01c481a060008008c44456480c02525000800f2480341c0e0f40103840b01d4008520100318288064103a010548940310030807003400d1402026101d0050649060190324840c0c48810300500741c1240e44081306131000035100b00b880d100e040060040d03a120a60500c110b108080c20040c00382c00c0c0c001241d030b07551401c0c00192034203c2c401e92111380300d2400d500305140500c010410003010ba002040089828180010b0302d199010204070025410780010011040c0040e08104240d0722180556011150122102c80d407850700c40c0c025124402c0c204d00350009140c018840c0140502941160f004007084d108042e55151981c0850b81001080b0031514400c0c0c0c90701c00005624209456500d00c2444400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 17954511 1250 17953261 17953267
    0x90201050a0309051002040b090f1002030d11040312020309040c0207050f0103051b03010608070806040207030903110112020301060f090504060b0412060213030b060f04090305030109110c0105040614010906030206 93
    0xc0880007010006804e913601d2042607100541c89090744020030150081e98491a5182504418482141c0c20710030500e004445c2580c1c0e200c030f415404030649455408003080072916100310402c0d10303e01e0040d82c05c041c00605407200c040d50b07010780000c010490110300352001d200c3c0060003602640c45207468429260400d0720819046032070740c400d030b01c156413201102d01d03080d031154820700d18841290000d800880105201c0014051100d8020004540c048006c80e01075141066a65008207071240510000340002161080e000c4168001c8d500303000c05c01c0d00013004641365030756100c0c01007481c00003180b8607012032803000d000705050809000b040184c0e1002002280791a14146102c0e1101e1160350782620f03d1075080c04034000d50007680405c1e00046008009001f064104036003001413403101140400d11551806145a0000b50003809590440d800310200060300040211410b4440c8503c40640041f540303400e0400080007015841141084014010f9200d00c0c1e803138000710b030200e03015804040d42c0f1001c24 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 17955761 1250 17954511 17954527
    0x160303080a18150905070b03010f051002010905010e070f050a0f0608060312030a05010612020c07030201030b0303090a1508010e15060d0b09070903050f0304120b060d0203060705040905010909020105 87
    0x1641002e011902042042620780c00d454480365103802421082000490703c41c4116000d00c00d08211802c00707812007604491955242071031310807407202a84103503809034110b5500242c0c82d0307000707500c10021075400400034810f40c40d640700e4068440059020300001081c89400200c0d0a00340500c1440a940071a08d00c0345080c0e0424009440300c01009080c42d905102c2c880f41406407004560296008055200c00441e041d418900040c042c1852903101d02e040604c180442c402d00c401c005070f10000c42e40c080c03d000800031007120110741140303e850b81042d00048004400111484440c0b02c20b50b80c80381550701c0200c3c40e62a41c000890a000c1030718204644180c0c84805802464904c004014242000d00300180390900c0b00b003c6036100070112a130101180c05407004109000c0c06000c6440244515000303103107403904000d410318060440d440003421070501000002c5240d00c0c0c020490302180c0d0002d0407148240f4100c0002055039010b0f004260005083c103000180c00c212502501800c0750307058648900381142 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 17957011 1250 17955761 17955781
    0x30301140d050f061014090628080c030d0201060609140d060507020109110a0501120e0a02150a03060e01061704030e0603010b04090608120f070302030d020f0a0216030308 75
    0x1820300d91080c26407400000146040051030a00340409018000d54908044044940b010b10341c42001c0507884000300c2555503a4110300c0990100d003ca654410041d100080600c46940d100c3c138080c005600c240020840d01c01c001020104168120308035952507880c2c2008a09840c0c09114620206a0400302403107030518140007507805104c090507200751300b070b80e503251103003a1503090714501c0150b596104007030140a41d0030704400c101c2034240e82c2d2540c00ca15000000303040300988a4000d0081c0e60740e04089070328010601810340415001444019032411a9401c10030681c8142c13542c9011900e0305000040340711a030400c180c102e8090f80c03110b0344440c2d0309040030643e55100500490400c40301c950040c0360b9945500266000c0c0c130b0707032411964941d801d20070448101c5959030003c1c09254804c8000002000e06031085800118015204035111b0ac403501e01a8910300505103201e0005002188880e080154503010b00021100d81c1c0c03c61303110b03211010310081040824080503000510340c0000131640d0034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 17958261 1250 17957011 17957039
    0xc1e09040b0c07050a061a100e060711030a060606080108070b030112050a050105040308011d06030601030311070e011e05010c02010804020105160506010806070206160e010e0409020402120108011d030301 89
    0x104040c01c4a24041056403a9405c006a100048030300e51794030711040754091107100b5001c481e01001d40e50f01c8000c11188402600c041100c3c448140325541c000352803010010042c0e100f5050820185c2190342c001b402d49041d0001c0c1143d8040c4500191092000081c0b4050000360f2100321260b01c00e0042c5181d0810480310b0071a01380100c1030b1114455107204600154003481030a100d540642d542d446a541046c0074070301107800b10400d101e48801c04000b807100603039010440d181100d9060030301b2a004103d232090b00382024150350200382500459400020050f920009007500f0344071040c400300c0019107800c010350b5102c5070003201074002100040020b005501a100070810102d141c0300703202040350184d80d540e180a200b6001014250401e0090201954041107107603048032800d0041c005119608100915690079004014104510f4120303c11326522aa4004001c2d5a00a0300c1503548145c0484144000402886400e00b00e43c80d01d0401820b40d140c0d4443da015401c20700c00614174507481c01ca4106d035058 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 17959511 1250 17958261 17958271
    0xa031e0609020306130b070c0201090e18030c0a02031006030b07110f030406031a1005030f0408040b0c0d0e01020102090a0306050a0e0303040308010303080c030105131d0706020c1e09040b 82
    0x6540d841e00c020159400300051441412014818000701c100d5250a0007090005400700c0305105c00350140100507a013091118007590140d15030843c0503902d20070764103040c00c0e01a0900d034103800001810400000e002c90030075100c41c0281c040f100201180c266440486000384009424180c1d0380d40403880e500d101c0c0d0322040d64030004204441101d40c01000d0181550310681c8410046980e4400c14a241000e510380c60b0103102007150003046180480301c001d4072601c8005c0401c15401d8029000170108604503044c1e42c00350a0148000b500e41d00d0b82500a503690490301d546a001c2075850303c49200643c414002c8494070100503282c90511851983c440010300782c0079051019680e100d43c0f1082501d00104044c5100b0b1b0b010740d5841005515508002c7d1072000041c2031070102030420030040c4920b44411220000014000000040c505104409600700701c40721080b40201d4040d40900080c204e9000503051400780781142d0b4030382d008a14141d4a00100500500790340c1060704040000d02040b46058260b031f100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 17960761 1250 17959511 17959523
    0x203040c030503030a02090a0b0301030218130b04120809011512021f0c120516080a030b0306040606080f06060a06050a090308030c0301061b111203040302040f02090405060a031e 78
    0x11589039030342c550864004441c490102070b404917220020307240540c0804001e11022280b41d2955040d0340114060a0f070501c007400c800c0c41c003c00428840417101810009040c1c200c110f82c1310320305181c0791004852610100340c1000850490200d4140001840380110b281a8901190a22442c0500400c0310403900081030340e1010301e9821219a548200b0381c06c0b072003e5015540c0c0300c41805146016911030002c401c080040007424410740d03401010341040f5141e4640c0064500b0388800d28103104401520118242c1d9401d4060380e0140310030006503810030b600741c3d10031400b80c1d4002c140c072031318540d5a4034003183c585a02003084035040005600a0004040040c031524060344029125228500c0c581c0c4203950150703103ca400030042250319404101d941c1c00c155100e0102020801d10745441030a50b5410a80620402d00034440300d040407030801c01c4400440e40500300f4800d201c03040700e60100035081824102e00850500c00020100d1501c0c2e1458004d0300e5100340d4481941407504644041d14001010407114 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 17962011 1250 17960761 17960783
    0x3030c07142403040215070308070305041104140405062206110405030a03020c0f0405070503040b06130e0303040b0c070203060406050c1c0902010e01030b030705120102070c0303020d0206060d0803010504020304 92
    0x80e41c540d01c4029a40b014503804082c0d903d050030b1061109000c2d10341e400d01c102e46030500100000030ba00c8114103410100c0340c48c01044941f01d84c10f00008060010003283d500c98a001c020b451700c64840c40c0e147d4411401501030ba2510755075a50751710102421034001a0800e0a110920301c000740a552260104540b1901c81e1420280c84001191515a45003003e6002d80d005000281031450400180d04186400b40c409101d01d081191001d40f0900014100a0218001000080640d262540c0240782510a014240030018031080165140c0d0702c1950f054400c201a02d0000d880024081c08903403c46a01900401680d83c941d100c9000401010b0710f04085464204200410703100c00307200b05000429101c500103113980c00c904c000342201b0082d920b42c9043c107040900700c1d031241d6004110070301224015a1901030030000c2803402030082c46407100c02032a2a911103c08801d159000a00380c1c0c2c481000d4080700c5107525030700204030780425004c0b0b008202603400c00052106040c03d40285820501c070b083c5410b2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 17963261 1250 17962011 17962039
    0x1a0d110403020306010305060a0c0306060903030f140307050403110609010c20030d030614090606090d050a0204020f07020102070b250201051303050c0a090e0303010902090a0909060b010e03030c0714 87
    0x2084c1003081c0e1054850707920000030f00c0990080da02c1142030300314050800300b00040c6060009803600c9200d100103010b00c2024414104403e003e00c11889500c2d19030035800c0c1e41e80c41c00520250454005010650352800204654200c0381450b2048804420050711034224841041d80e9017440d4000842c2c84103500c190318804c0b08801e4508001d1101a014951000714509003407046101c0c50380382c1070440c0c5124014080501540e40c450108540010f0f00580c0c091549291038140249403004005c0001e400074400207058071611011000b031316003217100b44d00381c51038140d46210420180c040c0e80d48500340014101e03182c05c0e806942510342c607012841030514605001c084941c025001015901c2030716242c00c441d100b15a985450320011024180158040010300c0280000c15568003050081428155001801040d15540c1000440003040d0800040c401c0140d2031400201404148030351130302103038104c440e100c001e10300403041d2080d000005004004a80c41c0100aa03102c1c00101c400030307004140f803010740e4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 17964511 1250 17963261 17963263
    0x403050304050402030c0f0f070b0f0f07030c02010e03040f050f0109060905060d060305060a05100803070b0c1b07060f03051509150103110408010b030708030a0215040302070b040e040b011a0d1104030203 89
    0x1d0f9503400340700d021b9222760040c145400180c0c401065030b184052400308112003240307208407090708030805140008136111420300071b9006001d16101401548000b050004855903201404410764400742d441c2e103c082091401036507811140c6c000c04003c0384c01500184101d0a040340580034541703801e080860800c0e5603417203150400d94255018124652540c0820640802940610700201000802140740000310340350034409a20241c0401c1d181d030400584140744065083e40056565540001d4680c004d60360100038018000c1209800046400d180016005500805c0c4492455801400a40d890313914500074400f81501402d8032818980d9822104d012004c3c550301402c090100c0e0800018240055070406180224940c84940700d030b8401c1000000055010a41858181401c204c011160329a4a41130b402c1c04080d4000000281001c00d00144c2c00c0c1e00100800e01443c0078502c1c581034ad90f02c800e076180200304190300d490080300701008504007103030703031a800510070890000c2c0d00c50070079451f58002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 17965761 1250 17964511 17964517
    0xf03130302071d060306060a080316060605061b010501080309010906050307120f0e0712030c020111070302060f0414030a260706050f09061509010303050706020d0e010204060e060403050304050402030c0f 89
    0x3c00949260010000c0b0350400304a00c540140b021034607a943d00c1e01d0940c180d0b43c3d0784103000c0c104c10100714610020017003106580101010701801030240c1c0e1903440e41101810b0b0b10003c2180490b1560170403000085400c0044100c5040030f0045c1d40c2c07064040e0503d20300703445991000c0d062104105050100b01c031250103d110311282c034402c90340c010510041da1a0851300d0622580c0150821002c20f101600000e41c0209020404a070b081c2051014440e410a03003030305080055001035005040000d04030f0b582040e5000403c15035091315a030080584802d000d141d42c480c01038a00419140030f5030f450740040107095103606002074201075643e140940039991801a5070060341c8421141d007050303080c440c2c0c00342d0510041c1e520803070381d6840c281343d4101440002e0030250113100240c00d1240008144048c06100c1d011a5406882e000c0288504800d82080384c1c000e41c018425240050943c1c07855811034589482100c00301c03a0040c0065040c01e0030102048002c0d0700181c0f002504040400c404110180041c0103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 17967011 1250 17965761 17965799
    0x91505090304090b010914091003080c0109031709070902090d05031207080c030f0a0c120c02060403020706030e03030a0b01030204030c1e050f0108071206051905030d03020f0313030207 81
    0x2940d1124608100a4195001404264140a1b18610501949009681600c2901001c40e2600070039200c5206a2682c2c1104d80c0000d0262500051000d00c64003054001004540c407954072441901050542c0700c1c3c0c003040903560040160481c90041103929400d4000d0a40190004d0114a15552568810307113154003901000c40c0b007056501c20400041e41200150b82c0c46100d00b19141e25500c1c0c00e04e007400384100018100310100b82d0750007032a0180b030300c40d5040c54904403408000b00203036000d0f10b1000e90b44600484e0110010700c00c0c0e44020429610074060710340408241c40c0110309540b11100800d02404a151260b4109682400000041004034000b000108200d902c3c8045001004080280c295000c0c8c01060180b0003003d0204d809903444052a07a004d441d84c68040d204014001c50b45002c0c0140e40d010395444140c000c0b0300d180c5c0840b4032200b2012036104608844295003000030031340903801200d41c1d52040483c203100140380d1503002146007845d20b10900c140ca4929880d55010318014400c006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 17968261 1250 17967011 17967013
    0x111040306090b070203070f0303050903070c08010207050601051203090108180d17070f0806010f030f0203010611240105060a0306270b010206010308090f040f05010602012a020606010309150509 85
    0x2c400e0100c0e181285070070030503c4c4091840d0040381d45a02540c90781c15040101050b56900007e029a6014000d5440140e44004c4913261140d95842c181e0207500b10241c00d4070140509800024149007100351201c10f070780c000010314100300a4100544e40c90b03100401a02406610095101d00c0c420203009809289a4039143c840c1900140054196203020003003c507801d1018403400410b54542101d82d041c1d03c80d9003443c280c100c003600c20384120094a1188241c0d15400c2c0088004a00c00b0380042c28054100c1600048a110903402010007241451800f03a09402184040040c0540e0070000c00038007104e803e0b81004100135560342e81e40b590301104040f80740d094a0300c0d407a0300003c010060148114036902440248160350641d241e83d845440780e9072203144034032414554040151201d4000b50441e8149000c10021580c2d1000064060304080d602c54509224040391141e000d0241a20000c05c03182c5a0700401c0035540e0040103500503d030040c01600c14100444142c00d142030030b0300078244a0b0304440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 17969511 1250 17968261 17968271
    0x60509070923010203071101030b03010609020a021204050a0e180708061005031b10200102130803040303080a0504030905030a03090e011d040f1a0a09021503060906040506030111040306 81
    0x1d4004030b40071200005914030148042100c419a0340082901c01454204041c441c40c2010640140c00801e200c441c0c0b55015400c0060004041000764043d01c4c0080480e0240c80141c10002c841044620580c040c1603440ba40c0340f0300c1803040013602d000303080d401460028440030340b108003500c031072403c802a4400d5030180d100504016078440f12024441c000d00040e0300914840031013144004c0c00340009180319000e0100c00e0310341c0403500e00c1808031a6688030780301c0260b02c2070111405002d0203036100340100b4002c0020150009403003d000012902269050340e141c0f241501c419a000b006410090010340c00c2000071100802c17242e0b030074010304400d00d00c03944039030f03507000c0c03414041c0900410705910041d4094114003d210844482e241081da0055120101e0311448160b0b20b06014060342402d5081010485041001072181c1d0300c2c0c0c001d55601e802103580405090603001c4540032031100301c0c1d52a420045900c041001c5040540107250000d00040002c15200490440b20100d41c125a0081e81e0007a119 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 17970761 1250 17969511 17969519
    0xf0402100e01050a030911120303060f0f090403030203060126040209060405010501021b040e07060908010e0307030f0c02040609050a020a080f04080a14040906060302040602010f050f01090e010605090709 89
    0x900e808424180c100c0c14032022140020300068064040c0c040c1010600d41c69240402c2009207140720f100126500403c2c404030b0a1014202640e29001224000e004008000d102e100300c1c544000101954503000f4809030701e5680d40e0b074045010750009000c0134144035040a450310b40d040c2ca810800281075070b2030170b095803c0c9000d00401c50042e401802d000d000c2c0345071100602941e6404209116011040d1039004040d1480380003040040102c41e030304907000e0042c0800403a04541c401030b103008640c400c0340244240d105a9900580f28070075240002d0100d036500f030503190101e01441d62850789a0000b000083c940350f49100e1107082d80c004491801003250700041800c2c14903009080c41d81c1152906041030404c8c0390903034441c42030384159100d00c41440301c83c0003004955000c800480f000340c03042c403005101007541c0d03a80142c080d4005019220240d4280b844581d03128200b446100e1181b18081c20381c0754180d10f004803c00050001842d02040c55488290200b4503440e00012180500503550b141e0b20a1868 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 17972011 1250 17970761 17970769
    0x50a1209260d030b030303060d050a060e010501150201060b1207020a0c0b090111071508100801090503070c060e030a060b03070b0315030f060405060c21040303050723120a060b030f0402 81
    0x50b00c1814605111000c1c0c80c0c40010560364055070a6403014014074060a10718a403106000c002002a420b01e100310401d1003040d00410304860b040300e103441082500440a0b800c0c1c48041c0600c00c00d40d0414040c000c00502d60010b1140c1102490068400201460f00e50f0004500960420318002c44000703120b08155034001068803035072501c0d03800340034900e00b409040d0044841c200d04074001c0094400120f1160980d240820005100f244001c1081c0c40702d501d00750746c03a50014202500c002e0a4964000380c0c09000c1e580070095000010013038006200300d9a1010010510725000503094400e9400204100200d01d000758060600c0006e20800c0e20a0030040501d0a103440d501c007101d5420000500c40001e40025400350412901c0302020340b602102051180c010700c443c01c40700c2c04940d40c8418042072503095840b003801140c0c29030b41c00400c000c080e000c1c0e10b0080c0604004138202c81c41004400c00610609920b590000d218000c0480d6003507590261104d59041901c140c48a400b40b04180821464 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 17973261 1250 17972011 17972023
    0x10b0114040b040e0402040b0306090705030105060f010f080c1c0203090f0a0c0306020309011509020a0e0a050f011d03250801050105010e040504020409050115170604050a120926 78
    0x80d0303521528501402c1c11006003590040f440303110464600000032600310345e80c1340c00900d000500078044401d28a06081d15607070b80d00031842294029480d00303020403424188107086a06252042e100d4100386c9080c8802290030060042000035003200034400c10300310901c5058000f088950a42e400b588908001030300d207050006214202149620400340724002604001c41c0d1822240c016100685035690703608118050b103644e10191030411841c01001c600101c0940c0540b0101c031f43e42d40c1c0c00c044098444140035903201180140c992005265101d000c440d840780710011152034007201c02101c001c0b1401c0c003092503c2c07449100750f0040303440003452000b84038401044800a00e00c400007403085500d030100185c011030101e100c3c14003803070300c800014003951119000030310b0301a8090000c008104011400d60012084c502030701812440266211a5080c80018000e000d240c201010b08100d40c00ca946405a0b9500c101e40b0000b17100c41d801c03001545450360800400c0c0d03d0610b1411840c20502000030a00f881d03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 17974511 1250 17973261 17973287
    0x102031e0f0403021207060e0604080403060b030f070504020705010b2707020105070806060a110601030b0a0c021f090201020f12070b0a091101030c12051305010e0a05030a0804030e0d05010b01 84
    0x1201207020000840d500042c041c5880e60703404040e07566003005052240192040c1c1ca0000c0070340c070400c01071008109070040240b088a002c0d10b03003005000c011f0000c1640b00c00e6600421a20390f44141d2060143c1d140507401007128601c100c0c000551440d5080114074020740400007205a022810300344002d60b420000f41d02d42c080b0051008000a241900c0e010705003100180490f40500d002140f481d032900d000300030f0034007454030500c112016503940b8501228107010803035007910101e05015400003c9800041d41c90500c07820722407d405010044040c21000b445100016070461241c503840043c0610b083c00000c0303040d242c8012a0f91b8454190070003800308030010b88004811860304008074041140f120018241079000d00e4013090402007441c00300d40e100e070003601e403490042ca04030500018500000300c0d5004184140000d00510f10000d2140f40c98400310240075001d500200281020341e44195011503005102e414181120100500480c01e040d1044a0440d03050307645800300708036581c2040c511072400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 17975761 1250 17974511 17974531
    0x1b0405100e130c171b0402040605070f05070e070201021201060f020319021e0703050c0f09040809040204030803090105090c0906010f08090106080a0302030a090f0f030809040e0102031e 81
    0x1441c00c0311440c030501004020303000024405000324204100d40040c4401046151840c0c21074159500400ea200e0800c001c0f020300b43c00c003081c10b140d02400c050082d90304030740f42520740c1400c10505407070701c0d2402940b14000f1185402141d01c04034581e4220319150780640c40a9000507100c00c003410f002c40b000b14060300244c091000c407072075001501d03900200711a0b0254113401540f89250362046c0030307458488044c4450410400d2070140344a190800900f0004582c0544200e5a141201070b09101c128440006095044203403440000c020070511070007841d290f0409000107182550300d480d02d00d40d981061703640b12401d945903400d11102c01400c0001c4c4036031035030455800e00306d030138108006007141e20058240000d01a4001c00620340305000c1d071000d0028030040081c0c0d2400d03116840c000707449500100050340495008040441c840d5001c8007001c0950704001450031000b401d41d200c00c1341a4102030307801d80d8403988440d2005250182800070313500a05003428014641c4014401e2542c21440c010420300b09 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 17977011 1250 17975761 17975791
    0x303040e0610020703021e1302040605040303050708120703050103050c010807050d230408040e0c070c09240308030105010306061805120a05030f0901030e0102070b0402041107051b0405 81
    0x440c4100a641001044030b8401254000d0181a410000e80754406580484660810403400a450a00400c0001c00300c0e214070781d8044000c007203401c9004500541c40069010b010a10020307000754014013046000d02e44143c107080f05e0686401821800321403000004e910b81c0300420400c50100030710b045c0020309080c00b03511840d210a00a1150240380481c0d4002911200340f4482c4007031589241d080300561201a040305c1c5054104981a5440362040d8240420150000340141c100321054549c042c5c5d02c410240c2c00a8901801500035000002e03140340f0020300e604195941700906103180008510541003d52207601d041c00140848845038840e0040c401501000030b1f407080105103401c180c0303004403030031030440e80540241480d26120390780041c194400051120180c0c1044000747c5810042660140f00c414a050381d414240d01400b9030083c01201203102182c01480d164000c00158209244030500780007143c2c5400d03151082d03104220f82e0104c9001a40451030909005165010a40780036a580d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 17978261 1250 17977011 17977019
    0x1030e03070b04021311040b0901110604050c0d0303060b0706060602010605040903050d02031305190209010512061503010209181501050c071401120c08090706140904090609140307060506030304 85
    0x208110004000a1089031700400512038611a41d00c10000030404a840ca9100c0c0d4440c00c4289540c0d008402160104500c08000201e0700c0000888510882c1c1c880c028007a6101064180022060341a0044081c1a141c2001003248200c1002401c0000c0c000c29021800c1407529002a00310350321504980d000381e0034172602034007082d0002d0403500e000000e50380043c0da03540c4400352022900c0305124010807900031882d501c3c1d40c0c50840145841e0341c90003258100c090b66601d00821a4120000340c210101b60803110000c0c0000240030074503c0d0805000e0005850044c00d00000f035024004801c44442584070300c2c0a00101c03c1070f40f204194403c0003030030500c0c5848058001d640c0d4480007441350000c0d0b00403e00002c0040c2c0d100e64000d000c00260384038140030340d0041e4080036091201c200d402411034810080005001d034803602141c007d820303020a01b6440e01d00d0030420b2001501d162481590015207825241001890f282d11034100c04030720074050f6845001030700d4844c080d203001400c03943c8640c0c4240800c2c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 17979511 1250 17978261 17978273
    0x3050a06060903020618151e04180203150a080703060b030304030314030c040e01030b0f160503150d05030a03020301050112060509010905061c0503030a0b010503090a02010503180708070501030e0307 87
    0x60030f503a011104a6202c3c039801011b0781189001c100c0350354000301c01d01c2c0001086d9111101410002000042d100700300f00301019801e102d40564071408484c0d42c044400001c1c540e8280d0300035600102c1e1000040c109d0f4500401240c2031030b480b54003000305548100020800d0000b184503050755508110302941c901b80c950f031001030001c01c04d12842d4079100310010104101c0d0030b002e81203600900352035482900310340c0e603400d001e04054002c6814120142c00c07000020040c101244019910034201e03100c150031a1181800340c0900c940c4072050a4004554140200201d4001c1000c1d012483e05903802680d258107281c001021071a0394003142064034106182400341e90b407008030725810758034550000282a91143c00040d121684030641c2d606645400400d01300b4090080000c41c81000102c600b840701007100d0700116198441241d28815079044002c0e60b100540c810320003140c0150103034804240f80f400106246040c00b195600143e0310342e101e041c0810081d47c2600039448610003d00140d420301b10a5201c803 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 17980761 1250 17979511 17979527
    0x70e040501050d1b180207020a0b070c031103030d0203040501090515010b0703030c03020714011a120604020d17030f0105240a0806012705040509071503090302010902040507020a0303050a0606 84
    0x41880c840030030540307100c131054591500107000c0101e041c401c6150400405000354000d82d41a07028040d0044042603042c449021600142e6001c100c003c0c0a500d140c4030351000000b4003840b030741e060004000c4004201c0c014006140598020000010045150310300316191102c0301c24a0305004800350700400c81c005040b02601c0c042e9400d4180802c241700c08500403402489001d40050100800521810a4400c158480408108000e80590000c04090108400c500d160300e4590100d501050000d40141840a070201700c0b14894140b80201e1800c202c4555060303001101c0450903040345a00410842c6002010601b0070b01101070400b003a84801801e01040344039203c0f06c04140f0110b20049034869100d40c201820104c2e40482100842c101c00e1000781449040d8401d480c803450034000410341102000c14614101d0303200034446000760340e500c607003500900900002502555039030f414450150312203000b0030b41b00324007079030207480d69080700e1401078212040608154603107071074004140201d64008110b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 17982011 1250 17980761 17980763
    0x1b080406090201030605060708120c030108071403070509010305030703120207020d02040c170702030a02070510020715110303040c090c09060f050f130909020a060c0201020601170f0d08070e040501050d 88
    0x40820422030600040c4c0203000c00c3c3d40300300d0f0020000180700051010340707000b41c800c000710340c0e403c020705445800305c562280c0406c0c040c1d40c00c240c02455040002030611203038a900d0010250940f105140d403100019040c0009900944c1c0c0b90b00005025010103910100034480081c00503130450800000342c010603449186081e0090090740d41702c9217091124091300c42c5130b0404401c006251003516252030000c3d00da4010300b4040b005441180c401103610700e80290340c1d071f84030311540d40281407040c03500800c003012a800340741c0c0320140405d0b01444501081c0034001103128500940001e1202c82c580b0a081003200c2c0702c0c0c400c0c141042110301d011711030682d03c03000d55510300410b8070f44240c9130701248043d48040c2c0701c1c5100300606100d42c0b07280040c5000554000000c030b00e00880e00e050607203699120070b88106820f00320090058000100501800c02901b0601d49480340d0082100c41c02c2a01c4003000340b510300701e203d41601040d004010003c5160740941840780c0d00009075028003140d40f614022800007480715030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 17983261 1250 17982011 17982023
    0xa030c02060901030f050a0e1506150a090b04060201050f070518010f020f0106090603030e10090605030a090206030906100504020405010c08090303130303050405130519090606120c05041b0804 84
    0x100c0c0c2c41103030f110380c110800d8214000820080c40c104090008010180c0c4000003c0c140158401c0c44803038400d41d98607511944000e841e458120324485c407200d100fa400044d01006000104401141840b0204003034405442150000121801d021b481c03c03032801d02c02419201000020001e000e01058020f2060a0b14034082c2415401458080740681c1800c1000d5607071050740d807a0500c009481c64040d0002e2044078000d407140300e081440c542c14007910308008062a0080307029007608110f0244540011980001200000075601c04035a000810039071042d0b400002c640d000c4414440c05481d16000d510041808450444c900b034030b0078002a010751600311002d421460b0100320350f03170b103078809004540205c40c0d4040d000344056120b14014015030020300806001e04002441d200400f89580320b0340d4000d000a40f203070060b00c80c0c5440100c010748802002161490341302c54000034820883d850b402da01c0303449101603820050418040c08115481002c0e0070070b4003118143e42c401c0301780c3c20075482500240c00503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 17984511 1250 17983261 17983267
    0x20c0f0a0b0c010f0b0402090a030f02010203090d05010b0a05010302040f0b07080903070b07030206220f03024e030c070f0c090c02010f0501080304050111070e01090e06090a030c0206 80
    0x900103400881181d000345401407001406442c118410f6001411049030407008000c0c8040200a00c4100d00541c0f914640001001200b4808501821800907036248148101da142521210105101c0d060320b805c1101c00d69160044029589420070140019140a01e02141003d1030140d4403c241c0049201d01185c07604001041402c1c003003038000b107411070100036045540096490182c10101d902601d0143c6c018092000030400c3b1413407080e440301742d528001c2c1171180310045a071075110450390050700407019481012000c050451201d000c82d8507161800140702540c40c0444818044922102042800030810b0300c03016080a0b10041603a40218074105983d80351015407406408504860720042e01521030100000f80f50700c03440d0010382018401d0750007400010940ca4600c0d054401c2809541085d40043c0030600255210700002241491039008a80d141581ea1a4403004881d00f80c02c1045560340300c0032050114103041049039003000c07156005010402058900806003954100002c1c4201c0b000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 17985618 1107 17984511 17984539
    0x12020a050301030215070803070302090f120c034303050708010203061503072102040f0f0501180605030a021305031e0c0a03030804020d02010c0503030a02031504050403020c 76
    0x1f40556042d6103841205038080e41001e000c0c2c80d0403105a400b0030616039229a10306c1101020300c800b820100822100385802d0400c031400301b08a00c249040d007500b00300e02600500285801480d0110307210415404144000d0101c0c0e4406401c0b4465040080340e000700660046028020498011828030148400c44c507403400200c80034404500501d000c410860344100401d80034415a13900140392546410207000100d000d03802042c2d03418000314081c4820350f04200d513540c00500d1035460a10051406100502314030004101040142d001303e00560004a0184c80d8005484000c0c02d4403080703454a0000802400e841c24200038500c2520114011402c08101940540b0b8055a0703108560341c4540a0061200031107204034100214400660086070040c40558001c0c4007110780582d0740d050814400c40b42408031700d0520b10907860041440002a0005101d1940d41c4098070484608410 = true := by decide +kernel

theorem cover : BRFrame.Cov 17805761 17985618 := by
  have h0 := BRFrame.cov_init 17805761
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17805761 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17805761 ≤ n) (h2 : n < 17985618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
