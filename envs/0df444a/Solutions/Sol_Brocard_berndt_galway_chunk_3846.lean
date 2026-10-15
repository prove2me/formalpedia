-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3846
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:51:28.572179+00:00
-- url     : https://prove2.me/submissions/0cea9575-12ed-4d16-b011-89c8ceb89dd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 691546762 ≤ n < 691726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 691548012 1250 691546762 691546771
    0x80319091a0c070302060a1d0a1a1305030706111b090712090803011509120519030509092707080718020d0e15070206070c02100e0411030109060e 64
    0x14118a0701c0808022929074040d00c008181d9010300c1e400400140c0d1500080c08403c0011350715042e00101d00800e81042e0300c4441d00c040d205003034100c010420100000150342607468055146070310340e00f000820a82005468100c194140503031030f40803032125030017885000b04450341400c5501c0d00d05501100755403800c0700a12a40c02a8040c3d0000315080d0050465440c18005002d0004410806803175910140d0030030380009400d52031070f07110180d4a562105501c4090590741220a904240c0369a60b19542c146a00004900800b5810711905050145042e19420f4001034121081c91821400011944101c80030a51a0802c1158028040c16002505106480d800340003024402d0911146003055030042e4401c00159400700140c107a907100c0c0b80140090f02003181c00820f0722041c000c88007031029600410042c1194030410411105682c00541c1c4040640c05950304401c82603000022561400d81c040c49641140c104890a80601e54a00056040740d842d04e104104140e281d0314100764807041601d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 691549262 1250 691548012 691548029
    0x30408120f0c090906010c021237030f020f0708011e0902150d02130905061203131806031b0f06030902030c090603010209090a0b100c260d0608031909 66
    0x100c0c03d81c200710400b590050340504040e803a51600e81c0c0003800300c2140f4040c3c02c1d055000514140050144460032500e10f02c0c1154107c0700b1002e92411094820800020180030094840c0b0391013a4140240403645001400100390b8440716200c1c00000c0c084d042404c0955809903105000600814043c816845a0342d402020400303182d1100c150322880b500300c0350703d04d200079508000c00300178850248c00307800082c10074403c042006c2c9005800c014050715802000322290700200f03d07590b4502d00648240c01540c481d00d040c415a1021900810002c0c00542c1006049940800d11221000d045420f0b18041f600e08040c008440f07900c59604405079440500001d40503440030400210b40d244c0341212070b0740f000010300010b00303000f00b01001500c54001550721760040c80d610803040380907043c001c4402c034030615203084c100e401e400c01c1e5132403003030000c80c4001da180c500410b05405e034129103108084075514614843c080c00415184c0750707030546a900280e4000b500200d0707400704440450140f2603204c203d52045 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 691550512 1250 691549262 691549267
    0x503121b03090a30170105010809121c060617060102010e0712110a030b070318030f0809010f0507090807080705150c1006060302123711030408120f0c 66
    0x540e6480d50045074001c2080d004013120304051034403800707011405103044065981e04041e1401c03648030003103210180c201178100070f0315200f044074011002641420380c036544008143d464241d01540c00e001c000c0e2008440109042c00c3c000034045922802000100082c611940801e841303c00059088440b000030189a942000404001d4580c2000c0c0d030102090240f04d81165080201000848038030154004450801d004001e0040183d4544540310a490b00755080e21001c6804d030300d01070500c102c04480001001400000a900c2e0171082d00254000100c0c2d40c1e041c0000c1c00c224602500d80310060003072403104d2055000000d15031a00003850f00484202410a4888000e400d2000c43e80e6485030050310818410345c0e942401c5c942251241c0030047c1101d035401a1100b201001c1502e4620002d007184514900186243d2100f080c030001904940c0c900030005c481c480d000030551000750a03202d08091428401008000a0000410040603004c5030b407103a048555844a008060f2550140d5145c5080302d0f06 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 691551762 1250 691550512 691550533
    0x6050a0506090a0b010c0212150108190f021311030601020f01090c0308090607050d02070513050424060905090f010b010f122c070609060e0d0807020a030503121b0309 73
    0x15540322504c0d40b40c0614140001030400d0b000310305c64481194205155a00038408d11080c1c02c00424000d0142106034003078030f104c401c0010011403451a0800240c12100c03d40c00c883d046649410810740790480c0410300380040b000001c02c06105400441d2802d015005201158444482c10b224464040f50f204030981c0010782141c54150040e0005000f040c0c00c10410080c010214500b084605055030181c0e009060382824403040c00008880000c040c2d01c064201300611002500345024049108000320758001617442c2031a1481c0540016801110b0726803800c010700c484050003003140c140110b1713148020700600e4000c0c401160b0351340c8110003c50010700c0c40708020a061a640d000790248140e1144000d901e207030310061111400703040500d40685580248001c10110790802c0b4290b00a214501304440e41c05a0200480d614071030780f800c02010941e00080c0e0504564600001401641d000720851b6200d20402c08a601081c40c00d58402c0c10b10258140c0f494404901c900c00c9901c0340b44002d000c2c00c0d05011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 691553012 1250 691551762 691551781
    0xd091d01030b0c13080607090f180c050904060315060e040f062c03090102060708090304090b0a0b0f0d0501050307060e0f03120a200706090b070f0c09060306050a050609 74
    0x801070070114031003208101d03160320011828503c2001c0c20172040a08007a06000a001c1d100000560282d403c0f5002070204203c1c100300315070001c0d02381030b00e00c40110750203040c0c1c002114a032280c6041140c0c070500e04400131007801001901d00218910280b0108441500c58500031144042150300600c0031181c91b2401002800a0700990005030185a6440c80362852000405011060845003801903001190301d10140d0327410088642c001649082c180107904160502c02d4507441035024000341c158440100d20855221000c2100c0145500d102c0c46445002240e408000380d0701a86600c490542081c0010070342e4070740400c07081e045131a42d0300c030f0003081e290400034840079000c00d2407825850f004141100307c4805941d00141001d00195951070254441e041c910030800303004803100c003096800740000384940e03034019030888191828800b029880300401d04c0c0c51303c500110b8240c0200201d0801c0780000300f0215a0f005003065078401ca10501c11031b40c8014004044800441e0b00c542d0010303060b4086004000b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 691554262 1250 691553012 691553033
    0x50c0d0804030606120b070309210c081206031b0d020913050109060f0608011b08091219030f02070b0414070e10050405060312040303140c0109050d091d0103 69
    0x248500212410705a0341e4444104440f200d52100d00305032840c0b0f4402d070801006000c0740b0381c804602d09040281c0da1039500c614400480c0803500c80c040d10b8400400380f240728090009220f030ae5602031251607854184121951038044181d5405000e80324100100c3c51005000401c440c0790080a400c0c2220112160208110900b000d4000c41144212140b41c0e0003092080c024100894000d0002184030701071341e00202c0407a026944440481c2c2d14160841c074003042c01114451040c4075629004440da1034000070340b402e00031007089900030b486000030700c400740104800d16481c212110362020024800004503a500703034403956000030070150509001a0000d6809280c030000e82c03400c1401c40d50119140da440d02240c2200350b0300400e048160703d00400c0700b031074280a0994444002d4016100400c038110061001d801140001000d000c00e84080b0800e00d0f5520055507d9120020000d00500c25036040040d1a47ca13980c0d41240042c0110b5400b01e0b071480318070520348801e03490400500c9107030b03c1c50310307006200f0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 691555512 1250 691554262 691554289
    0xc090108150a1b09030b0612031b0319120524012312090f070b07060f090b040b0a0e0d020c010c050c04050f1503010c08150a05060c07050a12050c 64
    0x1107650341a403514042c100c1243c07140249041d110749606900758101061864402082c95100b4604000c030300410040c04810359440541841e211005075942e54282070a502440d11000b40740c41110000340c0020394480540800c0c0d20305c05104001da615807a50000f00c0248120708070780c55042c40708400005501c1010507811054002504114000f008001c250480d80400e40d1602002074520900815060034095994100c2d88030b0f0041c20018038000c1401100d00481e5401340206076a40001000b501d0150840600b03d03611001c10603443c501403400c40413103030b000d6031440541c0d850303d52111003030040001c0102000010343c0007041407240c0c0000455480743c8801045640d809000a05002500d4034091140540082d0070900024900f03402e65040c0950303204100c9100380c2c14400ba2075250b035084118140c100341c4054441c14002e8141c000711320303050040d510140d0018000101240144400300b481801d841c000c40d100c508180d518030454071800c034064009021500200c40000307440c5032034860f1a694 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 691556762 1250 691555512 691555531
    0x109030f08061201180303060f0f0614091f170c040b07080c0a06061d0c04090b0f0d061d0a0803220c090204150302071703130c14030c09010815 63
    0xc0000d403c080c255048800d1060000c0880e107590030425805015560290003840b008980b0b0900d01002e80350710a0740d611692003070221042d99102d400e4400380842e0348489011300580b540d1188824140c0404004001110000d0600440407030681d04146440340500c00c0c40001c3c0703062500b8500910b0303041d8030400301100c0401c010800510310300418080450703041e000f4040022401c0c40e250140030f00c10741380e00070868180d0a4074208145026a101601d0680f41034042c0010007544050119050400d2040115403084407101c0203001c004003904918121084d4810989100d00c0781e1041c15a0342d04907003402004410144006031044806070750083c0c106802c0c01e80c20108884c1c50715010a1549950007211400c0c5c0c00040a100c10884d000d001d03540c54001d45421071a041e000d40b5580303c5007850003c03a0740600800030200b6203075030f140503007420700d00d41150703005001c155524030500351a509441460f000380074052954103d403500c031850760b04803542d0b64050028540c880440007041d0300000c006449 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 691558012 1250 691556762 691556779
    0x604050c0c010e030d0501060503090601090b1305190b10020303131109040308010e0606030903161b090b040501050f0105040603090c030f1511130302150d09150e0109030f0806 77
    0x141c036209029500040c21850069035683c0c0702148000b00340d40f4160031200600c0390400030700850400002e4582c0c11103541c0a400140517010800040000401d0071806040c0c604150902c11031a000b03580709040e26024a408100d08a40d04007481850740510400c000036030000c0c0000b4107020912841480c1441c880d006d000e611880903400142120015202900080c1055006002034940e0800ba29080401150744030709500d45044c0c81c83c1c0e24810101c60860300d4044076203007000c00c86101c00d6050034807484000c0e4155503031101c01010080030520750840c070507800c1000009681c01d004400000703c1e00103a440c586403d0401c0e85c290081d0008150888034440106000800701e120451200c4e000d61080c080c01559441d0111340400383c903c0b0b00d8031010380d0340c401c104c01c82a803406414214203c1c0c0e410b540314512190300d0002410306000714518240d0b0a400d00c010202004540c0c00d8000d0f406083c00720402c5040c10700d0b8050b0b402c958143c40c000340410301c4040199009402481c0d100e9000d28020107208 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 691559262 1250 691558012 691558027
    0x607050604140c03011b20030d0f0f0b09061203120f0f160f0e030703021008060a090209090609060d02040c020d0e0904050303010902070c031202070f15080604050c 72
    0x185400c2040710103032005244040d0103a49800c0a0000d960300000450081c001e400300f003d014807030243c03a80f0b194000c1c48800080011010081c40e00c400c1e08a040c1000e50381c0b900310303160b415400341c00300595400d0814542800c601507000d1511070070980c024007410003400d507900c00041c0304c2c000040b043c81e9500c520013070083c07400140b6001c0000788203200840b800c4000341450f03000408265406002c5810742c00300104d6081c040341c0e2200b0454000c00451600303034460464540030a00709006a00f010350071405918100034010b8015611600a06058a0400c19075071360b140113104900603014060790225002c0042034180c90f0030000755800c0000141004e0780a641e80d800101120070403564200076800c0b00040b10990ba400402d440e41e01481a10444040d140940e43c240d100d2005015a06001d68041441c02c00d0088172003405020356072000f0b01895403840144060740c0d4151921641da515036000c0d00c003141d0342d55585c05034020a82540c6981c82d0584503c410080908002052814000e600784042d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 691560512 1250 691559262 691559273
    0x504080304060c020a050f0d0204151e060f0503040309050d03140c0a0b0a180209091f021c060b0a081503100203011401080103030c0b04020d0611032703180607 70
    0x4100400325511514400c00340c0b03105001701001c280e808030303215504108a83d0556164951520345180d41120000750071070b1303007400c154801c0c1c082c2c3d0401c0005107180c02d642400340c1e040003c0f220907901e85803035980c80703184101e104403400c0c4800c070740040001b0000f00c010403c41c01c02504d0400203900c46d09002c80d02e00b68002042083e9001500902e26550241142c08140b10b040c60704a038010415080600401507040c003007a1030200d41050090264408100261032000d040c8210748a1404401c10001000b00c141041070203908840d10100090410700300301c40e80541c0920a40f4100c83d09964191300b0060324034402d83d20305000404400c141c103a800c002000c030750303030500070b2000c1c49012400068483d41010035812940048004203414040c2103001070000c01c2e0000c94007034030030350701100480e015690f91001ca201c03100803002c010b00d0b89d03040c04c81e0141020318084c0514440c8001e00c2500103000d110b000c2c4010040f00355065003146030070030040c12641131000312000c12158000f0308810300d040ca803691817 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 691561762 1250 691560512 691560517
    0x3140f061b0304031b031d0f2110180c14010c060b190b04090f092d0209070305010305160b190302070507080d0809070509010e060301150e07030c2d05040803 69
    0x490001d503491095052207c1c5140e42680342c1441078a8090104a140300032800d44040500070000c035190040050382030950420086030840520901804440e0100103441c20b8854152021924005075140c0414000c280042d00d242808050790707001420303020f03611134400500000c07490325000400b540c440f046a2007030086241c000d0054204080d9224070b03143d1a1000c41d104d000c120381c07441c0e0400b4220300c04150b42c0303030544400d0035000086094441c858540180b1407001c1c3c202c001c1d04490804c0030070009030b030550f01845c12203006d24140c651500c019040718030721000c5402441c548a80a100f5194079202c0680058026000b604005103021100d03121030340b62080503840700010b903116104120010b0361080000e40c00c0030750040100310781c5003000005050b0441c14090020346008030710014103a40d0b0709402815684034100d0300740c03403110346901201a080804540c100c1c086402c1160f44000c15104400300d210582e05d8917028001c05090b964441c80310260340d4100c1c420010706000c0400c030600c05000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 691563012 1250 691561762 691561817
    0x6130f091a150307080c0f0d0f0f0c08060601020d14040b0409050105150436050709060305100608010b0a1701170c04021c09020406080703140f061b030403 68
    0x8814082d1030404141e8008500d40100a4003a4110f14001c01c01c01c14001031840501c58100d0703010112903480d0010aa140c1c10188001c0c1480000b40c2d22034042c4041211442c4c03c00c3d004501c82420740340c0b2840825a05c1d03200f42c816070300603400300c402040c1c542e2040301d646c0304200b4059655450b080d568a1800c2c890f03081500030072001541c6100402040c40c0803c1504845140c1d138550758205032902010315510304032080001d407081c40e61640840c14034080268090302005c50341c4100301701d0a100c00c0003002c8405502515001c02c2c580004661044146c18030801220f505e039450000c01d0782071858403000d070340050321940c040c0b0854200c90001c83c0c441b0313003c0074003030600880c0c0d01a2241084030b0f0185003122000d00035006d1403041004501082151340d4038814003082e514041040082c51000c03400500e0a40e002c0c0c0b102e030107480e10100030000d1b00081c0070300c070440030b800b121010241c8000359500c030318042d41c0312907250007185000c13482040e054010315401402400c1003040c110340713040c54684103c411503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 691564262 1250 691563012 691563053
    0xd080c120307050d0f061203020c04061a182409010306090203090c04020705010b0603010821070b0601050c150106050405010e04230c0415050903010509060f010b07020a09090309081506130f09 84
    0x303040c2950740bc082c890305000705252400d02e5070080140c000c001040c8280b01e0b0401640f00ba4170034010844d15201e0710401c620b07842103103100780301d002000c2e100d0041e004180094006400c0c0b0f9800a1021014020342c1d00a40700c480c090000864614100300007548502811600345d501c40000141982c1e41c42d0156008107608800b13000c170702d0614803004480b0b05a4090080035660b0520060340840c0c900c4c1d000641c080020300700941d5070040d00480d54941000403411b030000059400012503415070110103402114000e0b01d90102c540381450800054601394030311190b400c01440c8121a869202809064210919101c02440c15864506840d480082c0c00c8440005c80c1000500c5081410240324055100f104000500402c1c2407800740c0a038103034018810007014141c041a2081956115500c074801407100c44800c10800344149005051a20340b0300c6180141d000e6648207070150303d0700386515032080070700030300001059030b9505d0130000800c82298180701c41603840800d00001104150182c0e0b0003100d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 691565512 1250 691564262 691564273
    0x305070501140c030a0c1a01080304050f0f060306010c02060d0609021b0d02060c0a120216050c0d151503020d14010f0b060708180d080c120307050d0f06120302 70
    0x2500c8402c0901020074004801c1140031040a404400d0728280ca0081c0b030080c0040325142481006c0d0001c0c480007190100460000041460b07001004104a400079210044036032049405c01080d0010b09100640064080002545661145803e807403030601c000c02d02410f0000090809040790a907404c41580642d000812020316600c1001000c0c0c86207015000f40baa650345210b00035150035005e000380081c1500415030042c03860060907072905455200e1030440d154240c01c0c030201501250241c0644890141030454a4581800c241c010b5400b034006294403c2c0b81e030802d0200c002041c00d40030200305015200d402100681e589458000c3c0f0718096880b00c2481b08681d1003136401c6038111050710b0b5405180c0030384100b05483e200c040c0d4840303a400c07408860316451106440b0f42d41c24422040c090f1b0001103c00c802c801c2150500107070813000d003454120341d061407049480d1041d41c8400e032500004174a0510001c00540c7d9550006039031588008000300b042c030761b26201e4402c10704c0d07440c01c00c50168118 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 691566762 1250 691565512 691565519
    0xa0231080105061f0e221a04110315150309030a090f0609030312020d06080604050607050313120212210a0504110105030a061805190b130218040501030507 68
    0x240070b001e8000004a40007032400d2080110840500d00c07010318031050213402d0341c045c41195120641c0c0485419115680703d0f0f440c0f0146200c200500f0703101c0310f01c011445d1080920b10103080070304c94499201c19410041d4a56210030504107400c0104c80c00343c507844a0408030f104001d00c00c54000c0c5004501c480b0003551a080c08240240a2389036a80124500d540c203214100300d595484030b070140407a9007500f450003500a000c44081e0107403207201d61280b00b550504c3c2000031f644400088d2070b0b10881c001c10694403244c480d51000c0f01c0610017650848100d48142618001080051006030300c901110f004031801c40008601c06030164125941d24455114080c9858509070b012115031540004c10050803c0980b6096071042070000034100d41904001d00400000c03102401c40c0c3c04080545135500681c88100706000070080079001c120303404000d44203881e4420341c4400460007803882c0321400900301d01f00d2124081c01c2c00002c0d00618103400355442112002000ca07161449100c1c0654002e0001d08141400d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 691568012 1250 691566762 691566779
    0xe04080706020403110103200a030207140618060901140c03060102030d0501091b09050d0807021c0b04020414100b0a0314010f0e01050a1a030a09121211040e0a0231 72
    0xd0f01099014415680c0d88e10501a060040440c0c00820340303818010f072900001d09000d4840d1560b8071020074548603103070034402c1d1005000c5c1809039005060b03080751503e80c0c0b101c0a1030309a582045c101a0b2115500000c1000703a00100007840c1c0c000010b2040342d00380803590100b00140c0b2001e0f4480e24a06c0e6035802008410300301440c40d1001c112960034489112841e02020a40c0754140a80251600d800401c0500c219500c810b4020b40c2150b00d424102150022814460300c44002920101d01c280c0c81c1045c416041fa4403106560b12500f9410745007189149001504070750340e4418a0540c003015035a83c1c178400c4010101c862113010f003026820003d5043e00348030300446000b6040c2c0040713204110302c8a0130802800f11660380b803460400c400e44a41c0301d0b190f03c0a448068851100c0040c2200c0801800d40601980300c031450403c1500c9035000c1c0003450b083c41c0e40c0c1c803880c4258040c812000c00740d00700080310800560000e0041c5d0340c011860341e01c28400d0b840f06006120280710080391000440c04d04000e95003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 691569262 1250 691568012 691568021
    0x90108010c0e041d060405030919031a0903041d0105130e1f02040315091b140628080f060103051603090c0e090f071a040e04080706020403110103 64
    0x80440081002400644001d82265001200103202d651601842c2040c1c0c01e54001c2441d00405000440d10241094034055490342c1040d40142d0040c0e000110701c0761224000044141142e8100081c641d8841d000082c0368a827141c01025004c40348020000016441011141d4501544c1d2010783e5800d81d5040008014019040307a028023030140c00d198100000010102d152001c0c1d68410074200480320000b410480a030047c1c0c0d0024001c0e44e0740c4dc04900300001513030003128a451040307803007032078412141410b04012400760003004900c80c03126006035940e040c144010b2074060a0118150003c081400810040c1d200a550745e10000b481d05080c4080c02540b400c81031f400c1030303090030f090015107000b00303908050f4103552017210101500d5691010600c18a001c07080090410403410504030701d40340400a9644285140740c1d18a88144c0000040400f0f100130004202c0034201c00b0545494600044440480005401070391540d6040108500040241c8000c00086128841d111040d01c2450000340403034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 691570512 1250 691569262 691569269
    0x605100504090b06030907061107030b100312030c08062419020d0e010e09071101111306030605091b0c0a0c0509010b13060f18091425121b0e0901 64
    0x10001401880f0038a02c003c0b1f10102a20b289250030003d0614a04000303284c800994400703480807081c0d00c28000500906507c40d0f0a49000710450080c450200c2e00440440d1045525100007441100100e01d00f403400460f10b010a400b41256442108802961038a0a900903000210071040c444003004140e034042c00b441d140d038070150414402c0c4028500010f001020420119445147c0e008005440d0300d010711071402081d140c80d4001c02100c0e003054000495a400720390303022111890b081000071281c1c401d020750303c140c4901429250381c036210040c2c0c4e0404c0000503251181145002d02100100d198108030800e4064040c50016011510304000e015044006030010680424104540c1480c5080c08248200711200b51420007142d03405020f085070340090f108400e14281e5141040018281010b4101040c58070b5a40e0741107510740c50b102e14106000042c003815000b810020001d6a212034025581100101040180803410003641400e007507160010041c1c28010400305020402d40d41420401c0e1400f4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 691571762 1250 691570512 691570519
    0xb060c0303060f1206070302070606230306150d14070b070c0509010501030c270503100509010f022706040b070b0f090303070e300304140d03090e07030605100504090b 73
    0xc1e03000e44c81c0c2c40e42c0390f400040c07805040c5500000c1080070004150b20510092041c0c1179802c62182c032448001c5510308510482e83c1c403031f1090300007080b61401e103d040c10410b10b00040c01c502c402e400c1b07642d41c010500d554071440c1c1c4c5980140e0100090101c2d908009040340742c460142091505e05003801c102d501c0760113800c0141010300c0c244a014000303070000310043c900c06400d084503030004200441c0003455811600125010f00962106281440d003c2d04000d016000d02c90083c0264010010710104902484841020118607550300d41c4c0e420b40f408841130740128001c0d140e64a025242e500d900081c0d4000342c03044480240100800c400381404104950300311821002071440c0d424038001c01007658142216a40c801c4070b00646245d040c04018680d00a03400520311072000301703840c000003962690080e01c100c14070310718250030400062421407800b0003069070584420804a003018810801c0031070082010f0207250351032001294654942112148014065403401d640301d044c03162900a40d0030320300c0258007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 691573012 1250 691571762 691571779
    0x1d0a0e0a0305040311040605220b0d080f0a0905090c0c010e12090618030609150108060103050a030305130606030503040f0608061c02031c080f06010f091502010b060c0303060f 77
    0x82d92003000c660440380c110000303c0003400c036040090003c0c4099031000d036216840d516123104020061944004030031500c0310400c8107040d52010f120450210041c01170100c48100f00c0c005449004038060035448540f850b1610310302d1348842c081408950300b528038110141021680c1c219480090240701036016290001d4a102990307148a22401d004811010b0700c100e2000c58059010071131070006190065000f021140395041c140303038a949030340e00102ca108808903903100106601000107a054122540200141800c50349614220b00070040a00f03010240a500c004850220f078039802408003950148010b5aa104d20301b6040600351006075003c01d060103414000c000b10740d550100a81500038044600340c01c1003000380f00180c02d1405010b018a040104440ca0b00320b0182c0c0007034528422010904c1458064580c000103440c0300818a241c0030028506080c18001c1d5034200c0280100c8508030b000115072112a00000740803600b00060680d010b074008010000c1030700e01004d00e5030703030054252031481 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 691574262 1250 691573012 691573033
    0xd0e090c0a080103060b13060f050f06040b09100e0d0605090c30010225050d030b0d030e03030d0204230a080a06020a0905040504080304060f180f0c1d0a0e 68
    0x70b02d002d00512000d400195100807054464940b40e0380c811401e00544020890607840c0e2a04004884040c060280100281036803140c89082810440b0240d0303400038107280c14041210100288080c2c218441800c00600c0030048005403558402300614501c03c2101090300c1c6050007125113046550b005841c0310b041c03401550f034002d040908040c0003602d07001200201c1c4400140c0700901a104656500324850100080c00a07501e04a069140b4914400c0040d58201310580504400380c9200c460100d40c04101d4009801c002800307000f00c1c00b80d100c0040e05882c03d123803500d1300c0b220482e003240e408400a001220308407941c5030010710491894400440725464202d080940496a83d15080704c0140203135400a0fa882d481c0c0d0007030440200a041c014001d001c07034581450300700010f803c2542c04550450810b0306407040c06120740203071010034803463b6a41c820007456488070903c1e010104825a511640700c40c0104461441c003205d040005240c040f40c81c1c26003042aa0001142d0400207111807580007442c601 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 691575512 1250 691574262 691574267
    0x307031505010c06150e0c0406180f0b0c0a14101b23070c0906031a090d0c03050904021317030c030a0503070527011107080c010804140d0e090c0a 64
    0xc00d1425003000001421a407000c4203520b0703214486c0c000c8030803105203404001012a40c100100300350391041c0e640f4058006040c1c492151101f460085045842c1105014003038240d00030b000e0b10305a0005000c481640c0c1c0d032504c80e018481070303000c1c1c1c0c0c03003041e001243c0b02840e0b20340b140615201d2041f8040d0281702c6119402c1d0050405100503590b20200003100700c4903a071b14550b0001d0300c44d038680142d104204c0703680e14080c18006040394030049584444d282c403240030402030f04203c5032003003820f00007034550041c0a83c400c940310101e14000f01e050140c188132140041d100d0f072020f000054020702001c0c1e1040d04008090201c078504050700042c0381e000b04000ba8600c8000b009641d1241c4941c1403503030702e0380c544850580d214007541c207041c01010f0088030b0801c0500700c8400880e10700e0500703880e032204c1e8058101c0e40c1c40d2606e181b0301511a07154000e02e41c0c40402d511442640d1350050144001c500320700911445d003800c080c2c032603808400141440c03151203114506241401c4e0000082104c10349003c040343d201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 691576762 1250 691575512 691575527
    0xd2d200316020f06090d09060503060f09060a0306020d090c1203020c0d1a070e1005072d0807030521070e121612060e0a020310020f0f0a05030703150501 67
    0x1141103100380514202000d6000700409800c24045605440085c640150607603603407107100c008440018003280e80042e550740200d0482e0301030b00001e40340e03180b1103c0b200c0500004040140c0401e401400702c00c000400b04e040b40c4064000c040c1002000308521819040007910b040c01c0d07411148400161a05400000e500050040c0141005031140c43c1e54010904243c1c9000d902400011742c612010001c001007a60b000709000ca40071000c40b01840740b5846000d00301c6840c09150300060503807244030070240d001c28031a00c1c0d180a800d030388207000c404c81c1074580d40d000d03144c0c0200c441100030500100c1c815010411000801401c0a04d8280164461a141c88000e200740b5034046054040c48140c1d40c0080c1c5c0140a110012522001c0c51040c006d2941c1d6a1025151407240038050f506d003440d000c1001c00c3c855021038030508440c0c0081c000e00c200d90000660000030741c054a54000300c07032030400c101600b5440c4640600705940070741d1203460712031230321040c040c09480d40c00d62140b0380303415004801e00c0035a0700070b9070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 691578012 1250 691576762 691576771
    0x50f070f0b15013c030203060a0b03061e0d0f1406011221021e0a051005011401120204090603080406081501020319110106150921080d2d2003 62
    0x1005507103d981c0c80d2250440c05803440d030404c1413010880803a105a03400d900114003a090982c1c182c0b04860303980e00c28422500090b41c8069005064021510003100400c280707404031140140056014017031581c5400f940e40c0c2000e02101e0f0f075890500340410240003031141e2801000c00b082075080740e2045544907103958405030130401150449400f49507609108004e02d4080e04c180d8124062220442c3d101c0560303810380e004040720540304d5150082c0f050b10b00c134015603048812140c46802014000c2c0010b4035003045140700d0b200399903400e210010b500b903828041c5800460064880315980c0d81405002420b1034001040304400d080329085000d0181d038000222440c0001c14040c4c0c0c007071510310341d004a0f16820110ba585254ad82001800b01d03002ca504605900c0c2d003891520340c465859a04c009640d812001c0b103104d0399036000002c44800c0032512140003041040c2c01c4032000128080c165610007401d0250304841203035140c0030100c000300a07178144140b01003000c50f0341030300620001407411100340380300042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 691579262 1250 691578012 691578047
    0x50a110c13062421140c04140102031305090c0706020d06140103090c14010e043213030e0a181a0609090a0b0409170904050f06030d0f050f070f0b1501 66
    0x10420000111300d6000c09107601d5290b038441c50500b0565034075156500701d07000d10885240244a0240f40d58000004c45440007030000749216050715023800c01600010040042c80805400c210102c0050100d02c000d103025043c915001030042c0c01c02c850390300782c0d04a0381051410300d46812856030101e02e80d4007459040b50149110b00b0b610411110049454140c41440a42c000e810104103004030021003840d2070111042110889260301c40c412180070b04181503600d005031308650038503d80807a01c5441032001c5040e01411062243e50b4551000703400a00350b49403c540d641c0c0d55003517040c0e01011042c085415800c11a9014140440f55000641d5542c020b001e10030701c203649000c0070180e40c0360342e00002c44080d04400340855034103d81d40d191400790300c0001c01c141300307600c1c050003d20380c2460420214080c0d1400380003030a0500f00032000356141a09103044005200302803106140340702544000f007255070311400d0380215401080c50150030810010300944c201c801d401004034800d0364006403441c00741c0d0801 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 691580512 1250 691579262 691579307
    0xf1103010b03010e0109050c011806030f0207210f110d0813050a0b1506070305040509071e0203040603110c030f0d020c150613050601050a110c130624 66
    0x40029004251540489406500740a01c1c0b0350450010346c481001a0300034400d940e00004c012004480440200c1c100e81005050030740706200061280e40300c03152070003d003d4014500021529000e50031521400709001c8400c440c1074042c1d01c0307507004041e003804000f5401d1845080600c58036003619650002c150208010441001402089106030002c6400760800255500038085051004070310004460440200398050300f07000c80b07828120b04990055405503901420541010201b01d5401400ba086504110040a07007a44488240c0c000c0c3c0240c030000c0d001503680ea0b141a4001d42503d4480348020318a282c00c0c45080441e0700c001c8204d9101e102201c90060b6140303889803c05001340106280c3c90300911440c0c548030341d00e0344d0300c240c0240605800c64200c44155031280240082e207108580300c0e03000034401e11031940030034008c5402890659074102070700d4200354a000894030741864170803491029511420104000307501e0701d00e803003260060b04402c00303001c03004544058408d0100b4840a070140d0b910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 691581762 1250 691580512 691580543
    0x50d030b0a0504140916080604060b010e03100b030f070509060f060408100204060e1c06021c051e0f04030801180b060304050d0e010c0c090c0314071d010c0f 69
    0x8078000d0303030060a0014020404c0c115500013101c0d00b034208440b501c406115000103000404a60040d08084480b50700041070183c0d5190f41c3c0b00c016100205025050081c00010505150b40510006280d03034103040001800d40083e9040510b041e101720a100e40a8010400034006900c5510416500c4501606d88800402111010030070f184036070742c0081802c0c001c2901148d050f4485800500c11505c075555000d4440d1141e80c00c01c01680f0f90005407481701044020070380e00181c1c1c40d030050140d07905003142c01100740740d240d407070700b400c0c0c1e0000c40350584003e02c04000c51002000200c001900585c5001c10760070f941c502550058030940d41030080406614200791042000140754000c9041c4020261015031241090b19080390b448903241c103010040350416801a54551007009640e800c02e4108400241d86481c10848000a0007582000700406860b000c6030300c82c050704110380394000c0c4d4030b642c3c6140b0085903a07001703080d80b602d1905206041000030740c1d04c00c002c5086140d02d0401c440d004800704200c101c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 691583012 1250 691581762 691581769
    0x6120603030c07090501030b070f050a030b01120e1608030408071a070212162432070b060a12060b040e0708070906080a0503071b0914061804050d030b 66
    0x90002d4a030040c0c0f00307030030300842c929109800c200c1c120391003510b1000710350302c0e0030398142c441200d18001840020024000414120320039040f251000c0011304042210203242e0f2038000980f08240c400b442c06510003541107030003a8031200a1001407207180701460402c7c0c28a0b458070303140c0006106003501034844450108007110900b0444a55507030080907880406000d08440d80c8554101d03400040d0069039490000760508040300464403a480451000c070201e85c00030043d03855a0031802d03210801c1c8030403654040b000b100e80a6181c025408207901a460380f001d4035100c40b6041d401081203004180c8150100030707850040198001181d8004000325100d50701d000407a00410101d150000e2038401d1550014002101090307a101b80d40c01c40200703000365600e808096585080c1c0707150040c2240c1c01041004089400980300140e01404601e070342d03c8450751924158103071a00c00030035408403101001070040510300a1060541c018161284031460300d803907150302d0345803e007c1c00000245503ca9110703010954 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 691584262 1250 691583012 691583017
    0x40b070e0a03201e01080c390c0301050610120e030309071511060406020706140103060509070e010302090622050106020d08073f090f0201091a03011a0412030804020f010504050612060303 82
    0x205e12440008c8423102e01c0d000d840c440d40d01c5a41005000305d4080c0d010034101800b900e8461070029140d80329000300041c04950100000d04520b40702c43e83c40141d041111014401140549040f10090200c1401c0c500e80c41e03d03901140c81d1400070310280049900c0406004508145d00907000840140c44140c0c504000000e8400b040d900764a020f0184001b0040010f103a0085000d15600700445200d5500c2e04260807c03102c023808040e40c000d07d01400982d00e1320f00084e010382d203c1040d1480405240d02c44070300302d040e42c20a8200c8409a00440b0030b02240c168003054a030780c400564582103a20b9000d50032200c3c880080b141b5540c150700b28070502e440452044120349070741c03c90b1042c41040b0b40043c5091490100c1c40a04049001a9054000141400750081280101c0039982c0c981450f51b40b814000fa00001d10103440002150b40c1407100141c4c0c00c20206143c1070480c082d8540000c68034140c810050503259088556050107001c0c8800d00464841109503501c0034120000340445407a250b000038a9070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 691585512 1250 691584262 691584307
    0x31b03090302061c05150105040306020702040b03070806073b150f04080f07151b240b1906050f0d0e0f0c010305040b070e0a03201e01080c 61
    0x3e400004c0340201c5644200707003509074803443d003801c11040d00e440c841448050041b290190001360280010b0020864550040440d10f1000300000b5900e03d102022031300f4540f03140d01c18203a503008401080812500214030949046004003924041a004040f090504c0440c00c0c02c0c604007040c10301003010a0f205d2a0740c02c2010701c1241c281e01d40b1503c41c2d00303807201194881c0c01107d001e4040d5412903018840005214001c2d00d0045c0d552215610180f0f0b012101c01d414503070b1898104c4800380d556030108880240011145601400d0034650005c04910407051b191241002c901039900c25841c00e07034044820f01840140c500a203845aa12070405020302c809004142c1d48420382450b02d80401e07031032400090b00345040c03d0180c064070f200040301c10040d021246c0c220b402408032804580024807803441082c80440b02100245081c50b460b803280c4a00d10224004000d07810303500f450301504102490040e102d81c20700021001b04803915005000001c0100340d000d0a0b01e00544004512100414480041c05555 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 691586762 1250 691585512 691585519
    0x30501111e1b0303130515090a200d060203180708030901030f0e0f010c02070b0412020f18040b06040e07230a0305100b09060415030b0703020708070b04030f0804031b03090302 77
    0xa07030600d02075658010b1024101182e00b44100e0640c41f1040c0d0a04908521498820f405000d10389a180c0303400040741080b8181c580d034843d4500349001c180d0340b0400c015031081e005500061700c074070b0084481e98611030000c111125680c40000c040002d10b0000080b40d03003444081c40c0c081a40c01264081d01c025080790203010301d180c052004172000d1235505500190940f110f9900702c904556407140f4480e200d1085016604a81484000d032402500740403d9038004200080c1050b06d4210442d401100c4005054604549440313070201400064581030180d482c90403c0080607240003480c1c03a481440710003075100080d40540710307110100300540e58a04814010b540002c287d841710007442007400c00a0005150b118400d11498020400074241440b41c28002002403503018880360a54994094695000300500c0425400b0403828000508000240007414844c94601d6024186071601074201030301c54000e241003102078404c21000c02e1740403800f03d190440b041c00705034a0940c14142142c804210343c01c060340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 691588012 1250 691586762 691586767
    0x10303030e010b04111918090c0c08030708010f0801420b040e0106090602031e0f0c03090a09020c070e0619030516063b040501030c030501111e1b03 65
    0xd03100302d0000c1c070202c1000d0001b09001084140250b40240301101940c403c01441c000505c905031980d030110895090f14106011000c0c220b5482c00580ea004441810008a81c20010040803105e00c01810250440000a010109050700d40300c0c104654240d24692200b00c041075040f40380114410110140c0f000b40146801c40c1c0c0f903400c9201c2a82c458852520b20032990400090300501c9000300d0b50075074a580d4082c519008440080a0b040c14402c900c0460a03442048182041d04508009000c2c0303038111000b4584900809042098140117a44404d0301c40c1e00412400e5550103001c40c3c400152a45003180c4545915648041218040b11000400d44110400c001105001e40001c003c110180d40c20150b04000b922404102d4010000074401004040156000142401c1900704881e803450110721051455107500c002070180e500030380c0151200029110280280718003805409411080c007001d40b071a040d00311040d06620482c8010081036194007251002c00340c0d200c100c9400354030404108a94 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 691589262 1250 691588012 691588031
    0xb04020c0a050a120305040c0315060b13030507080303010f0506030403032904180c060e060903010914061311060a022a21060f13050703030e040f050f010303030e010b04 74
    0x960303c50304200182c41140000d500300c40a0751190050f640314030761006200e0755040c40c640d01c100c008d0640ba08041c00050700e03500085020005040544003c42d0000d01c4d08001c2444c5080032030409549401588484c1c0003000103003d80f44202401d801203903000e5403081d42e80c1e40c903401c0c110f000702003819011555400d1380c62910942060121107840c2c1e400b0032603080000e5914100051171041c01800c008005d050104000c201d41c50045200d4000244083c0c0303507034588001100020b0840701c540c2c07800c9803407000c540d00c0300c0c400000401040f6440034809040e02d418290030307103c00c04035445460501d4450000013070388068141c424090f120800722101f008032150031940d041c461081e068100c03031500507851241040d411410240003a00082540303409010180c561107450442914010070b400612846035100400043c010420a030065002e0f6a03034000aa01d8041040107507400001d401d80184c1c10a03007446940075880c05910304481d4075040c001003034210701e80114050004543c40540c0249048101d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 691590512 1250 691589262 691589273
    0x1609060509240c15060406060f020c0910030b0f01060f08010303020a110604030b15040c050a0e0d0c0f09020d0b0d031b020a080a0c050907021c0503060a0b0301081f020408100b04020c0a 81
    0xb45d01681003100d06000c02074a40100300d4030700b03407001125001640640303d11580c80c200914401d822540415040300801c0e140c0d1590340300844251044088206410010410250300c9807909003000c1c05454218140e52454a00030340e01c07841d9540c050300301c0c41080d50a05540e605d10f0101c1e0011340d885213610400c1c2c640b041982c43d42401041c040c0780035034149482d01469a22800480c0c4244040c0e0702c031040354009900500500f1000c1c403208642110045102103030080c80c0d032030700303070f000304070612000d0307680d807400d00240050361680380c1d1503400b0350f42200b031000c0001d1704203414140364800c1d0300300d4640703142e294000a41400580c2d8400c208030b0041c0d03c40c050601a045610740207480003a10081c00e143c41c0c2450880c2e64042003802c0500d0200c00001c03501c1e0a0303110b4801540c10000003480014519215160017000c1d600030703070241006a202c004c0004501d0710a0342494041c1c41c0e2000c0850405103010740280e03c03522041c10f00c441483c1d84405018080c0c0e20b550540b108038080104035451440c061034030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 691591762 1250 691590512 691590553
    0xa0213150201020a0f02061b0918130c051804080d110d06211211010b04020d0b18151c0b040605010e0a02031023091609060509240c 58
    0x9131000034a480d0401c00003600010324680903003003401080c002c505054488031996044050500d40c07084400c00c140914842021710140164016107005400401919055030b1080c6c1d1a402140150015841d406405184d080d8040d0710030b800002540d6240e01c0820389400600003c40d0b03100702104007084003203c080060348050240c0d5130300452010709402c1c08003c650180030540000b00035003208030800e086035106800c40038a24483d2000170501a40020004003a130b0031050030704114903a00d62401c4424030303184031078220000021721f44020078244545004c1030203009280d018040e880c080d00303a0a2241c034070b91041e461a5009004040c3d40d04103840d0a0703010b00030a01c02c14412820351404102d01e0000c1e4400c1703901400b030810260040c0d074a8207418480d6410390040c81e040d0720000300e000307081e1500c841c1403403486025503400b0007442c5455040060103c1e901d94005000304141401908280c0d26220001001424003903510a003503071101821096901c105e0080d100d02e4003031103c042c3e148414203030340c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 691593012 1250 691591762 691591777
    0x100e13060f06090b07080a181d0a0c0e010806060705250506040f050108070905100801081207020a1214030d090224071410020403030e04050108010e060a021315020102 73
    0xa880445962414110f81201040c000c41c019071004010850000e40594024990800203003491000100034095881081071298002c181226100215810055000c1c4840c2c0e80b14407583d13010010043c501c5030080112400026090500c2500b50100b9084d1b41d42e81d05039151194802d084070014940c04540d00a80c8100f4050036800d02c01c0c0c4600030903946403200503202070310302c0788404041c00c41c904401100d40c028080c02e46070a102d6400004120b503140c81603100c91543c081d441f20002540741c404807924207044415118a400c10a1000500596980700d0403401c0300c804600c00380007000d81e410312940307503e1030255805940c84005400c101e481026044904028021030304c04401e49521040d0351400c440c0140a448000400c00000c00010054102041500b002808480b058660303119060102d030b1044d041a8003007076040c16480c946141c240915400341504100a003c101001c1c0c0c00c2c4c0d0380e61500907015040303041c0c0102d0b01141035841003d40034000c05201103914070300b40c60104080d00030340c460310 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 691594262 1250 691593012 691593029
    0xc03330f0f181b19030201080408030a02070f080304050c090603030d09080906070b0108070801020703120e0106030203030f0405040f110a0c050a0614190c020309010e0a0806040c0e07020c0906100e1306 88
    0x8889130260309003001c054048940603160305805070f580ba680c0280c0303039000802c0700000e40e500748840b03000b00700c0c6c2414148d42c940c4504043d95a070f040030f040013458807400c4043d40d48141c071382e0f400b0072400d62008426100e058002080203c1d2b0300440b46429036040c014810090f0300118045035074401d000700340855030304842d1041e0035500c0054407070814609034480d4000103000b242d144500b035001d800081e4000d81942c62900000104a078495000908607071025004540110010405002610f4644103c0d0310f2400b41079002c0216804491100212303001d000b041c0c070b09115403802c0500902030203000030342d041c0d81d000404000142c1e2180618403c85000c1c1c407000080860401e2151500c66140714912961340c0c65001503041c21803004c011900d02c0220b00c252a0446090b200010300010100b0600c0d000b076100e80180c21f440303420400880d405050092900085501070240c10800d911803c482981104040c0ca40c0410f0031801d00c010f9031506c0202c19032940003401500c0c40307042c0c102507901031800d641c4440e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 691595512 1250 691594262 691594279
    0x20a0212060f1311010c0312050406020a0f02071d10030f0609060c111b15120402010f09030c030303021608070302060906010501170f090c03330f0f181b 67
    0x2483c0e54641012005001420400c407a156108558000d00ca00c034000f41c031900d401226084c420340c2000a88400f43c4003207801540102e0000515504008800c2c0003107d24801010080d01d400b100c002d890348900c61001502014402182259800c03050900107160448120310203e003880c5800001056004400c0d02c1306403400091382c0c011031182183d03185c940c4442c4001c1003404845a414400244440c2060b640105209800301700c20712448090404451914002030091500380005440b2402d20080d18080050308007007400003d41689403607081d01d0300b5181c0187c0ba0106126403241080c00080003600100f008941c000030181c1c0018110701ca003d05800355a0f0031399895005443c0070644c0142ca0441403515000038050f070030b200080f03e03131149943c81111240314102012a044c0150002c0894004078141701701d0001d0242840c0c07903c0c500311600048074561400401d10742c8240c030080e140050005030100460001030b0707801102d020714070018040e0382003c01025083c00384449000788440c0940300c807 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 691596762 1250 691595512 691595521
    0x10221010e06060921030d09050f0c01091809020609060c010c09081606110c0d030f0807080c07060b18010605070c120b041e051501030308130c0603090201020a0212060f 74
    0x20381c0a4500012015100c00345240c000021a0030b04448441007005d1403205100101007903280340260100c1ca401200a0b142021503110030a00380901007510905200084400f08100303140c961f00000c46089046000510b40300b14800034015118aa00882d804134003c1000500500c06500c945140a056121443ca5541e10408207840d00c500100e035418203d81c00f8001c11246010f094483c0150b542c0d40241e07002c20780e43c030f0000341c80e80c90106400d038001111900c640040940009074540c029682d810064050310382040001624030500c500184203a48900d000051501c3c0e140c81030381c0c038014460a5880c25a103919005080e50045402a51641413584000a29070404181c940380366030403945152142e5555110300b0f090500c4d0160141c0c1c00d0b2081244107010a00034406034141040c3d68015441c25451800d000f848220b01400c00c0d031140c540d402414000400d10008417046808500b400700790f910450005030f0400304d41c048082e4100c460001001e4200c140441d00c00c0c818441100e0840d8552075 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 691598012 1250 691596762 691596769
    0x12010605031f05060412170406030b090903090a05540108030d09050f0a0305030a2d1a0d0f06140403090909080919090501081207060e010221010e06 65
    0x2e8510600d03401c9007041109001041401801c400518010076a092030510346c00986842c0c1d61080d40a000025075800d10303190035140c1100d210390440208001036082540c080c0000e070b24a403207882510322508101206521201245800c0f40c2203022004496a84442c0c0c041400c0300c46074062650780c4000b5071101140c07600030880c0b41180c1030765240b4006608200c1540c61f000c0080403034150980741d0388940002d6000760b19080280380c3c5080e20940c0c2d03540d200d00300010a442540d0420a640041d0781c504101034010144001d01e80c42007043c0000081000c01003155500c03040942250000d80060291003440240412481500e10032ba204400070403d154039082140010329090310010000703552088204401000b940214182ca805401940e150a0442000484c1e11010900c02c1e00200141a0b04200d04142849001c0c010320901000d4544503452456440c8148520603008040d00e550341d143c20402da00960684084020001c04400142c40d6003841c0da800c05400d11400e40700010300d400150b10381c103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 691599262 1250 691598012 691598071
    0x6060315020f031504060b0406020307020a21020114040816080d0f050a030b03121b0601140f040203090a0b070206010314070b0706020306030a020616060605040515090c1201060503 79
    0x24440000b1811510f400c0d0513903490000c0000116402511840c0c0460000743c00c40092004251940080d5035500042c4180a843d0409500543e4511415541d42c1280100c500300401c01990920f05000c400380e80c501d0307600e1607020b80e400c1050203200d0012018441c000c40840182519506411140d040140880031034004048030200c20000f401804011002c50094206902c81c00008040c1d851a00d000d20700754815802902c00801c1c144220310204042103401c0c080c05014190700701e42c050700c180740000403c4010071108003480c040c6900000117400c1020502c6480c644650142c0c501c0350301d003082d0200955610b0207010175204c03507108105801030002d001076082c048a00400760141070a00d280c0b0340c0340094000411240d0140166501c8900607074071140100006804048a0161384a4505012007250010307040709004514040a10000e0b04c201d007849880000c04507154142503071003042c051a40d0254072002c41000d1000d4001048558024028600c80c04614601c0e84408224646440484 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 691600512 1250 691599262 691599277
    0x2180406060f1101021c090201110c10050f0705390a06032304150f140f0c0708071a070c12050a02011e020301151115041e0606031502 59
    0x10b00c49000181414000e51212001500c010001410910810402e54040600880000849a9841d0b1180456800205101c50340030350100524280306100701081100e07050920240c280035010503041204401117081713807400d69000c03041c2e6440d00c078032401141101d000e0318030690701001201d45c20036103041260f185220926000380304a01e020324042081e001850000d84140a00d5011404020001145a0840d0045118484031080364807907215035030407944040b83c0c00482c02d00b4580030805081901101c0380e0003150798440c940460300c030b65003425042c0c459100000d10700240811007d06000c28842c0882c142100cc500c070181d40c0e5280201280e0b0000031020091040980790800a0345601c40c0001d007000c41e51a0000282020790741034048200321610b00d011802a03000030040c8900d458003000002002454100300040403294219152280c0c64190029160740c2200001000d110051502c407141c4280b1b41c0d201c45005020b8104034020f09850f000540c0c00045030f5102d016000301c1842100d404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 691601762 1250 691600512 691600517
    0x151608010501050f0c1c020d050408070b0901020c03060a0b1512042303040e01030501180201020d05070f17030a110a0c03030b030c06040e1006050a0519031e0218040606 74
    0x26801e09005440d1134201d25540d00d01c0d1003040c44054a40d1004005580712100c0b400900b000b0b00c4200480207140004030246501041414407040104400001e0864144c4e54180d4850f92101c4034900100d2420340d060810303c1c1d040c8181010300502002c0c561081d5400441690f0010784c4494403c0c1c0c0200740d2080000450307048882e00d0001e008070345400c41410b14561440313602d041407220002001c2c42d5400c1508442c182190b040010800c00c4400d10070710081d07151a08048079076405580010b900c80128485200c103004001803148100440113000d09020f99005001d0040ca884c0707680c20391600e401c200d900f812a50b2400c50310940030702c404020746000f201c86655510200c2d0b91a601200030301842d00c1c000b5010b1050240e41c88032655444e002e0405484c10100250451900c8610000100301680c014000d1100c2000b242e590594400215510405c02c017400c1c0486650000e411001007060b410030034128041d07401c50183c1c0e0703031294008108042d20b010841c4028844482000121000742c864a0301 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 691603012 1250 691601762 691601777
    0x200c010c1e210507020c0103050a27050709021b0d18050f06071502190f020a0b151009050102010b0609030a0605061906080f0112030918090f051516 65
    0x99208091800401207681201601030b001101580252501940c88a000d41c00c40020303c62a9680361042c0e550141290f401448025a00c0183c02c0158111402a5408142804a40042c4141000488018006038108550341c1c605803500104042d190710391507805008a4a580000078401e0b04641e174074100824411150b24a40020441c1200801d19401c0d0055400d01c10713400400e800709100940d035006c4000145c1e44480c5501c0203d40c41c0d507600c00c03a81c1801041480b0018441d4000380501c1c809070300000c0c1c40807984409850345030320000c9040c070075444001c803815a80c0c16580309180d4412202c00307030028003140c6011002c101c02806101c07080354065104010501c042f801581003103400c000040d000c92100e1480d0755410815802d20f1b000f40c00442d620b802402081040407908a0061a03081c0e1200744c041655070f80100724004034440d0b42426403009001680c096820b41c0700d43c2c401c0b50710042c5807130b40d86032070b103012521000350103035860f0b5906100d0000341d0681481200c14030b01c80c6041d80c0d01c15 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 691604262 1250 691603012 691603067
    0x70801082a0301090803010b180907080609060414070f1202092805060c030711040b091b041d10080109050a0b10031205120718050112200c010c 63
    0x81d070599030700c0300c15a06640300c40300000828039510040d4060107041c0102540ea880019011014009012440b03001c0d51464080090b202d0b481082e464014000b1244018107869440004026107039222201504003c40d030140985035420101c590740103a51904d500e450841811001800c0f4002c3d03901c025081194000b424840b0014074010595850300201e1205c2c1e103a8903500481c1c4250487d034035540159000045030818803480e07917004481e80104030740911a020011001c10042070740601036182c0d050600503c1c0043c50140c2c01a2406000403110600140841c1c070310295603078005542d10490a80c007c480494090b0044c041d00c81000d1300100140301c3d40c40203030303119010040002c1031002e18410b0b41ca8080001140c0c011081081030081d51501d40303490240d0340000380c0f0038001c0c0c03a0105200080760340005900807480c800f0210348007428800da1096680500310f0251003807490f200c00300050a0186807001411101504030991400000c000066140e038041d034001c070706110130400100d141002131 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 691605512 1250 691604262 691604323
    0x2090a1a03090f0c0303300106180b0a0c15060e09070911030f010e100510030b0102100b0901050f01050702030f0f0f010c1e1205010303021f200f04030f0b07080108 72
    0x10124501041f0911024074500038110641e45000e800041c00101da0166440703100402c08140c07406811040b1a00b40303083c0c40300801505070f031103d50000b000900c281c03c1d4001c2c40c10203540450001c1068518941e8145010b0280985581d203074007400d00098a0a9103032014106088184e0b4400e590840b0140096400c001d0841102c04005044104001c80c0318004117103a200d8410551140e24951800314081c00c0c0c50001a09010003842d4900123980742981300030395592550b01070b40c11148240d0b81d01101065480040301d00c6d2040e110040e40602c645004484032107000180015196441d400f9144001c440d0302002d070a855102c16050005a000300024140c0b402c100004c10388213140c0c0c1801d01449000080c1d10003030382c0c0245d105030090b030014445e101041200c1e800340e0f0211140324004001484c040038044941c048007400c400d210000200f4011814040b190858001e55040304610580203182e2405c0d03200b20004480510018034001b000180b0740e0000109030f09401110b1010449118940a8a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 691606762 1250 691605512 691605547
    0xb030604240e1b030f03120709060c020d03030b0301020702040204030804050a0824060111010f052208030a020729091204080a0b0402031e070f06020a0209040602090a1a03090f0c0303 80
    0x3001d44c51300800140d484442005c000400c04042450081981031500b0040941641c500b684000148442d5454032801a500c46042c21004c6034141030018110300d064010a00a0058140003504980300081c01701c00d106040010f001100e204075200590652200e680300d4a07007000a0f01c3c01420490300d01503040105c081800240c0c881c42c113250841064404119035070070b458a0f80c074124a026aa04c082c014541086000809490901c140b040540402035841d01a140320081c900c1c4125580403e805042240b40c8010b85903106041c50b01108040002c480d00360320318000c1d680c102007407040d40301c220041c0b1320031015641200c20303e0000d0003a070700494650218600340140126858080c0b9011198003010f0100c08001e0340d5030a000420206040c0301d4036881d0b24810741c2001041d580001841c000581e21200d516074010740c8003101584070420030010545645454001141c5074900d14008052281464040c6204101d1a0300711014440518607603a2201c009105054150308101300007445500b11404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 691608012 1250 691606762 691606813
    0x9091a060103230601080601050306130f02280906080f180f101d010905030901110703020d03030f0b04060e181612021002031812010b030604240e 64
    0x140030400d02e00c00301d0455200c1d50b1200201025038a010f06100e900e584c88014183c0c06002802d110b0300e1800e1803800a4460200004010129602c900f450104078250f501503c0c0d50009001a500592440b104035100e45030340c2d4101c030000030f0900100043c0b07881c4130384d009502a6030700c41d01c40c2416407138559a03441e0540251440448902c950f001c501da00c2c813000c103c41030b80c9011a00300003851451403607480c52a10443c02c0a22000da04020041010580110484200346424240324401c1d82280d140c003410805642d002075805580e0810401c1815010340101c20983c0507403008000b10105181081300301c555600580601c594100b000440c1200011a4030710620290800c03100203007030b00001640c0402060300b01c1000c0b2604144030750214141034115401c41d09150000d1810128949d0058200500c6442c4a910031005420281c810690079070103943c04400140a0754082c1c0b429081c00f084200c0c21030080301031050044c50f44d0709120b80c02c1c400c0c045041014406070240203900c400c1695008094030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 691609262 1250 691608012 691608017
    0xf0c060a27030602040501090e100501030c090f0806010f150e01050a030f050114090726060111010e060702190812061516021009030305031b0c030c0c090109091a0601 73
    0x7030024084a580720444005510907140981d031241070a00061011240e80d002010400350041400444600c072800700c8251102882c00140160340701c042150700c0c800c3c030750103d04042c41d1104049031020000c5401c50590300d4407403845622907510030302c403400d090000d05880c0001d5001d8003991508e41c40368004140750459841c003c54480c10040070704044030000c0e4040c610ba10205820000c55043c03450074107034810898100800014054800c0380b1a1502900d401c200325408800001c10f0303603010b2100500f5641c1000020042c1e00118111640d0f03038003013981d030300d0094400d061059040945015110318219400340b0542c1c200070705000d000b140e82070301500d0181e00109280c948114624036901800d5129094451030341c140d00715005000c0c0202e40c0c60341450070041c501c281400404d401c03c00702c070f401203407a550115000503c0b02c28100706001d001001d40c91340c0030008240074400e50016040951410455a445803641c0e1003961004840c06410300400c040c0f8412140c5a0008100940592122060 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 691610512 1250 691609262 691609307
    0x50601021006090603110f0307030f0215030a05040203300d1404050d140a0c0b1009151e060e0d03020c100305010905090d1209050c0909010606020f0c060a 68
    0x3007200000da6000341c100400c60366a4074010014000040744000e81103805842001c290200c95010984442140c00043d001e40385243d580c40c2191580105c44100045c1c58111686a003030540c2400040c2c04240d4090f846446001d1910032280901d80c4440a40d0301100000c05000d10b0142550046805c450032140003240d4030440b819000b00603044031445a4420300142c2003140c0085805400300c82130041c8001f00700c40500040c102d00c0e401100c0c5011158229480b41015542d80003150414141500074401ea60b060440b203103e41a00744002e0015220168500c511302003680000c00d10a10b442e12031000010356410710a07000f82042904440c40c0b9001c0d00c1540c01a1031b445010940311501a0030101c00070782d81e540100030f5a031103485126044a4a000079200318450039200402d0f004513030009058895403603d0740000c0100810075010283c82c0685451035500c1e2a111041c000c2801c1c0c0300e140e0140c05503030300b02c000342500410340c0d0000d480010002802c2c5680d00c94100e42c580300f820400301c0104e040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 691611762 1250 691610512 691610533
    0x21c0207080a0c08070b0f07020409080c16092901050702010c06050f0703180f03080a06031a090d020f070b0a1b260f1206030c060d091a040206070605060102 69
    0x10310a11118501811045040600c1c00c02c1252401801d58040c000c105810301010601111f107008071540a50112408030b0052002c0c103000c81c0a10596407041110700c2603014560300c070301c01000e160040b1056041c0403c0781c10b10000424020307884039178028131480107a8005040540c040c5000c0c0c80310342e0040c9000e00034028030341c0da520110303101542d4050081828800b04600258103025400384000e082803102d070000210303914280400c4200000034107000c8801c0010300b10701180d9101d1720043d81c00c442c50b0221002030220017116010107680700c180b07038007031800403254250000500c0080310019000034103c01c0e01d00450801d5582001c00c84c0000c019072002083c071514600740c1190441c6014844200301240c00403100d20040d1502031140c24150340c00c0c402e00f200901740c10103036240c6914a40c000c052664405000078105800c190200754001c401198030683c08509900100c410752144030040600f031541c0e02410f0340d18a045400a41c054010009100096000d4101940016043c0129004001ea = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 691613012 1250 691611762 691611779
    0x602032205070f1203050306151312150b1813020a0612150501090909080c060f09061b0f070f02090703090b010f2909041b030c020d021c0207 62
    0x35284080ea12940040002d1080030700700c0300000000d080c40081030750501403070382e070207400350000404452146901880325900840318070b04a030910340c000101c1d8207e05440d008032441c0e4110800e4240e8194032100f81c05030889402e44074201503803c0c020007034804003800d090120003811008000107800001182480016102e1000d200054000398841054494100708484202c860b00c3d852500c600010110401c11079070001c082c2416910940c80100d034030145030030441c050f4402d0100180d818814503081003804160300220078000d0b920203094030241d4440440468150027850f128050180c01041084139640741c0750014034600e4400d091010207510b590b0001103141e002250010301080e207820401040154010082d805800e0200c10722010508180d014180303014035403044c03981005c1c403d4862600302012700940b480c0d000001d0040c401401e52130343c901c0012140c0d0074840082400c04140d80c001600125821903009540d90080125054401c44420010724410880082d4081e0440200b010310 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 691614262 1250 691613012 691613071
    0xc1b2b0e130902011b030806120a08300105060d0e0f010f0209010f020f0703020103200301090204050a0803091807090b07060c0905090f150109150804031409030703060203 75
    0x4090490008100c40b00d400050103912901e1011202030400d40c3e04580007030740041400c0e41052041e1040c141c2c4483e4101d0580c41c00d0540300c00980401004600568050f00c0c1405095031310312101d5012002465903015840018428014994810000d0013482c03000445c1d94842e01c00001003100715460a1480c110039421204442c401c02da00030740006149120b960800b0b20314000152034801403118107401a8000c4d1035440300d00000703040640345c03000e400f814208403503d20091100c4034405552035a561100d20001c1d8403920549008240c0e0200c0010f04600200c02d5800e00d650142500f82150001040720010840017804901400301d040004200f040c05003018000c020301c1100300044540c6000030180445403240e0050784075542c44003c002e84803d0751a0b407141c015a480400074491561900141d51403c829040b9900b15280000300c03110580e80003458900641c02a140c0740301101018180707030303503d00c203845501e07806600c0380030100f0000300554002c590200e500400d0182a00001500302c02c0c41e03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 691615512 1250 691614262 691614289
    0x504020310090e0615030d020c0d0606031a0106020601062a030216030c0f05030d0f030e2e0c09050303040512010204030f08040602151311180c1b2b0e 66
    0x80d13105004202c2100d500034200310b101d000072001000300c00b50b20140250384444108400340a03445124505c1d041003416046a4041c560007603441e000800e1251481103908003d205d800014481c103000014400c0c01005c405100c188100d9901d02070241d402c000d11404500d4410403030461140c0d0050400036500b84a41002443c0b02c0d06052140c246002d07115401c94030b05400c564030940003800745592680d04503841c81c0e2407582c90304010410744107074103000c2d007040e0b681207130440040d2216000c00550b42030f01d88055030a034030403402081001c1d0010011281462107010f0b41b81c00d070b40104000d00c103502e0160302c40c0300303244400400545010b441e5941d13290840a094400c031010f43d000301301404125010300c0346a0592007031503007110140c83d15101540380c006400d1030107410007801c44c45d03e1000f80c83c1d04460010b98502c2e048441603a00f03140000c21100c1d405000311640000c2241c015110100000c2181c42000c0c803410150a040e03e46060212002d2a1b05000c007170600c00c1000010030b0946918000581c007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 691616762 1250 691615512 691615541
    0x906141b010f0204080f01020f0301060815040501030605070201050907032a0803070602040e070e091b2215050301081e0f070f06031410030305031b0403060b101404050402031009 78
    0x4076417901c404140b90541c1000144016401445a0400c07d00408140da044841924080241d40c440014508070098650211a0080e0500c000030042c81a01c0c0c00482c05681d10364020841030791003828458072013600f40801810898407102864010006000c1c502c5101080d0344840b080a582d5a0341340d180d82e0264808843c1e05401180400c0070003442d0750516405005814a52130001505c000507006420050a20b18000700107404100c16803188415103043e40c40c0d2038021000070b602d070154181441e07118801d0154825441d600a2039031031141050f2812564000c005000d8120249d0813040021004000204544109048904110000c002540080a107110000c2d41030341040c2000301a42e69001001d4058a01441070012105814201c203089030380518059440e40c40d000c3d200818912404580c0440880c040b4012007407014551002d003d031081111164000503a2000c15110403d04501c090b1000c0000d100c00c06c0035041c070b600119801030240b03090420017911146803204441e00304000802 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 691618012 1250 691616762 691616767
    0x903170909010e0903040f03050d1107080303040f080c0d030501050a0503010e0c0907020c09011d01090501082a0d060501050315160309051515150f0409020d0617060f070906141b010f02 81
    0x60ac150803c00c89041698003402910005050440d0207669100162004180103520440d1200b405014001e455a404184003a280c1c1030700322510003000380c0030a0080714403c504c2c5003000101860144180c00c3d8010741c41e406404042ca40c44204000303aa03004008030158094400d0f2503540b0742d62000c10301d010f0301380445103581030314200c02c5181621105802101540d03140100510246400060701e601c611071802c41c1c85a09403800c11030b010000c800d100700e0364014000552042c20803110b6004076050381c40540c03c40b0100d0010300c02c011310102c02550078642d034940454116641501c29004284146c0c06001181c0c0da1400c041c0d058a901d1070111540546407581c940e22005920300303400c2251036004001d201d00e052480a64104006200d60b208220610ba400503103041c0184803901b041e4014441031170001002c0700b140300c0564691a0880d2501c0b4440420000a8800c0e4003030403448080d9000703a41c460150607603c400c00c800d80c1d0300c43d030304019113581d0315008040c5101c000d00403460100c13014080942c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 691619262 1250 691618012 691618033
    0x30210050601090e01050d170d021806030c1902030702091302010e0109060f050c0c0a031a011e030809060c0601081f020c1c110303070903170909010e0903040f0305 72
    0x604880c4050000c504009a08008020070107040000c241540d804840c0f2009113042844c0125010501840081311408007144000c580400b540c06041603045215a096085400c0801c0103600c0c44220740e00c0c0c07089801032205140107502014a404408000d004892074401c1c1600047d000104c00c54504510303a42c80c480344002c44d40c0c08819400222800e003418481d0506108000d0b114001c4141d0034001c0040204100d4025501048003840108003c0d19294000e42c0364205407007400d50480e96202e44000b81c00000450700340e25496961042d44080c5641c003203604640c0d44032001e0b80405200c0e17178001d41c14002d05c501e240091040c0381c02050a8801018030054180304e0009624025920001c510310510038254210b10102c1c16884180d00c07003d004e0100000c81030f007604c00c05543d103000e0030b4912000c01006451a0030000c03072410f507802080e45d070301d8003440c90025000c00d00c01d000915800840c010010000400c0315044180c00052070020f486c205038561401700b004985941c015109540300e0440c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 691620512 1250 691619262 691619293
    0x130306090b1509070e010e0102071701230103050a0b13150b01080105153f010e01090c020a03080c0903160e070c02100503070504030c0905060307082e060b04030302 72
    0x2d0192410a5490380e90a00d0300c01303405010740c10f0320102a0f05000014a501205a00c00d220440140465881c848011075100009600901034585200c80076131401d2001340b5076220501480d412243c2c000002c0c403101c0c106a4600651501c080c0205030541d4901c14044001489602806240f0183d560300040d1888070340c000400700241a0300590148680e00048000ba10002045400094843e488450441c50346480060100102d1078030300c9c00c4c00d42c100c0c1c8c912600e07210814010704036035010004c003107140d803110082011542145548005a400521980c0009000b01440d59026201d00d1700c0605003404400428106000f0f203031180c031640c001000c144458a204408607800c5011032601d685141da0541c08620f40015800b6908140240400010003e905c5502100c01940c0d00ca0003c400e8907545d107004c0c5000d00810740d10341c2e209000e09900882d00302000a5240450000ba074031000c054a0b19070001380c0e403522192900141d5948900c030224221483c04d0041c00214440d500502855080c0d0582 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 691621762 1250 691620512 691620541
    0x110d11090d030224100e0402060d0920010807050d3606180804061d1807390309241b0b0406020a17010e19060509010b130306090b 57
    0xa01c41185004060104403a80745680c0000c0d10051b04c20b00a4035151070000408601400e410440c1c26030030089620704110084014291a1031a600390250300e011000040d41d900704111110400503006014444014242d03401540540c86c00341c50f084201042d0340811410f0400b420342d1402100e200014407130030091507101d0b1003000007030703101401c00720307541c0f40d0390003015108900c60441005428140240b01c00c0d540c100ca2500048020483c1c00b80c0c21224820448580c0201d445901144035044015144c0b400c6440100b02641c175411741c50302d1110141800f01d104036801ca8190108808a5404901e100d12418006039681c0703a080d00044120300311600418915810503103004440a4540100005221445103034010740d02010140c0c60310340090080b00c03201c181c403468415103d920400069501c81b90f1185902030001c0c030a18140c800c0c0d0f10280c82c01500c00e40d119068100070074600410140740e4880c081c3c42c405145410042d2115a640c880d04103444100c6000e613000c4076004207100c0f051074070000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 691623012 1250 691621762 691621813
    0x3120c070909051b03120309150f06030c091308030c13080304060816050c1e010e0c01020a02100309080c1f0605060702012001020a020307050105010504110d11090d0302 74
    0x42c08914000e40da076a440b0102e46080f40c038110000c0800000a44d020b001e80f11482c05801402900d9192401c1c140ea940c03400c1c45074503880e0401c0c1c0b101040000440e076018600c03900c03000e40184001044081881003143d00140170a04100c2c18200303e0000030009402107000c0e402d2a039299403a001a264604100c50390f81d40405156070003004104200c54000090940c00000350a038040641d140d0314050311140329130704282c80f05000b69401060140c01c041c2c0d0340804901040c008202c040b4440304aa560b0f454415083c0d405a07002d9000c0b60700501d803883c10302001c108c40b031401046101c07495036203c403650003c10849005030061a58481d142c14880c6070704140c20803103e02401940e180101003071451140c0790f006410492400038020100c803c80b01c500515542050086688004948009481e40c200780402c40b10395090800005180c5014000c401e40c00110340012494802c82d490301c0e0f4000c0c032490325a0b440ea08000c0c8407019259641617000408940a42c02610858041c60b010f911140300140d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 691624262 1250 691623012 691623029
    0x1060f050d0312050a0f020705030a09050103020309030d05060609092409270109080c01091e0c050105031923100e0a021312140d05030c0702061803120c07 68
    0x1844001181d801100d00343c03294803540f000615900d8002128010701650001c42017030398000030302c0d0b104000001008003c100303001d42d47d00610703540700c4004405900c402d9030810401d91050003011400348880d0700181d042003005040ca8170708003500f40801d40c02c1c0030458081072a8007407440f07000c1010b0441000280d40007011035054145182021182d44450390b00d041d040300800740740309030780200701095200e000c2a1b074000c0a440e88a0445011242c0602040300003110588501d060686582000c5014000201d501403200a6031908010044515410042c10621141290fa109403983c14045c07054610710300c1c040d5160b40f101d81c150a404070540c440070b07040413070768081d104040184403046000e043c0c01242d070040259403180d00c01007100e915001a0025448014022140001c10542c03012050f017255102e42982e440d80f090f54003e80e290f000843d8105242101000a2030041c030b0048010880c8040150b001302d2480358200c00b10b46015034816500c0106172000a5061200c2400c1001e0001408401d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 691625512 1250 691624262 691624279
    0x601060807090312020c09040803060316030209011217280813030f0302070b0f010f080604031416331e020c07080d030c090e01030b15040b030a030201060f05 69
    0x1034100070142c032454400500400d02c555030f04804c1602c02d0001e0911040d000300345100500b0142072050499009031042d070f10a00c58861440c0007003c442d01107000b2030790018002c0001d0780c44d180c0d15a05056064800b2180003c60300c1d070421940210202801542c2220740e00309202c101c01081e2907002c4d880e415100010b024658003002480c84642c58940c844550514104241e00801c80d016000ba0180e000014151180c03038042001200f14102000d04a400504000503087ea4544000b901c034582554050001008001c048440108400051040e00c40c07401c3c15881e0910245c40e03168580c0c075148806840c0306002e000f0348072242a40c0ba02a0000700c4500f0082268070320040c07502c1d4501d9285140315070070a0b004110488805014000c0c240107103800130980340c6441c1d4000d401402020f54103442000301c3c101607801320319202d4442e20541a00d038004214040c80c0c42d80c1c10001d16aa00c20701d030096001e80c80c2d20030f4420b00d8509100030fa415510a40000c24900c0c1000c0096201c007869800c01e90103428030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 691626762 1250 691625512 691625521
    0x40e0f10030809040f0209030a060e160e240907020a02040608030405011d0406051005031009110d0e012702090c1812012a11010905070605090402041a070506010608 72
    0x5404407402c210b404c40b80000c00614090317251000e40107807840c0d00d506000b0300c50401c00740f25440e000b140c031221140302a5054018590303086152441c02c0c1c0103444030600c5100021341d605012021900f0000860600d500c443c8039800c000032031400080744c1910040e04030314068011410305018030806089900017540c140f90a04000070445000141001c214125142180381a030701c07150700c103d0243c03a000c2c140381c02940c3c0e02500030b08075170f01c10383e10041c1c1504080b400050440c3c03180b00c0e011480c6c0a0001d01481c00c001460080058203070303904282170300d5585800160410100c10f00d0490b43d102032000218549040e4010050091001491081c40c07103410800305d514510003d020083ca6213040b941d01741e1001420003114014050151030404807000007182c02d44c900300c00c00c1e05802302c04c2280d503505039a10241e10a1401d0700c50b05503005029600a023410300003140503c000c0d000f0300c0c9003d0f00042c100780c1e0b1001c00101c400007924014803100c10018659003404403e00c1910302500042c00c00070081e0a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 691628012 1250 691626762 691626773
    0xe03010b030c01020d0c17030f19020304110120100519110904090c090c030f0e21180406090b0102010b01021b060d093912080a050f040e0f1003 63
    0x1c0d020f00c1e04c0101b044c484c0c0c9890410030103940814040600241141c0c5914104098010f03581065405000450310441c016899403c00d008403407241c0c0e40000d120360514018001555190354032030890002500710264000c00d948100101c420040040002064904001100c078458425110711712038140c0c02d2404440b01c04210070200c0364800002d5034001080300450510400854590300700e00c06460070590000d07041a41500075070300d440580041006204000389510707955428100c6d1a04d110385841080290b101c041001402c10040c0e0803031445241008000001e040b950a9003004041039900e010340e20701c0d544e091113106049082030000b07102c2c404c0c400c0c0014144400681116100300070015001600f400d4030340200c0c86c150f03404030080309030440500c00104070a50f2aa00360440c02507003180c4520f1490100a154200c5440c200c045502c2c1d18030b600c0310701c541e41c4200e203070700240441089161010036011300140001d092400d0f40208a0500103c6e5006107034001d42089410020b18009001041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 691629262 1250 691628012 691628023
    0x181d1b010e1e0d06060503030301062309180415110d11090a090b0d06020414040c09050114090d050a150e06060616031202030c090f030604050a0f0c080703030e03010b030c0102 77
    0x108460740e803c02c01a91400030040d20282d00a03c7e01400701000018880d070f082110700360b801c40344610f0500e2520010072464100d000b05000e15034441100340055405048580c0c4264006028080c032111180b00146414107503240154082001c10b00050b40c03218180d840c3c420050308501c140a858680060000043c00d100c0803030040340d1100756a502d00c8482c640d501c01d503800305581e01081c1552607503501c06c11500e02d8420300495901a9007480c0380d00081c80e100d10b0024040e81c40503180c60082c4004c000c0100103503080b05031003e030080c0e003420014001c6281041481c0a8a104407840d481c0d1840d0110035034155a08011030900c0c42d4000c0c0144041a90751005480d05187d01c0060a40c0070856800c048540080c0796100d031115501c000203029801d10f00a0003440e5940056440740c80b28011101410b80d144001c80740644641c01c181c00d1000002c11541c070711030f0458000c0d0740b00100c40703444285040c01d0070038960007140030410220407003800d4102800360010746802100984955100480041d4450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 691630512 1250 691629262 691629319
    0xa0f1d1e060f0423070e090c0f060301090b0d080f03070f0c080301060809011407050903010b0d08030406020a050705010c0305100506131e1208030103030315181d1b010e 74
    0x607000b011095603241d4000d2030700f01c4e9005403040303602c800e650b8010940351031410303500d501c914000d01300121010b0400c0e08040040b044050a850f10303580c42d002448004021080005601001d003144140c08070742020081c2c041102550821503490505410107840280e1012440303081c4a884445500484e41001c01e4a0440303009041002c0c0554642c00380b940140f41e85926541c442e540030017400445a88280540091403041d402001032882c000108400c114009600902c050700402c00030340007070403940142103110001c1c100b0500b85000d80d52034500351400c0e0031494001a0340c0e00c041001d9060580010070041800b61107a518102030300a00d2140003805002d0b070400d543c880c142d280d40e44068407910034014400c00355000c0c1146668988100250700c288400c2d40042e0400c07040b0038006281a15503411035103008560414040100c070850050a04d8400c0542c1504008051200101c7e091148501c0341d03072410301d080c0242d0f64000024002c0440707500601c0c000c0000c01003094003040c6055466420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 691631762 1250 691630512 691630523
    0x90803060f031f0504111c0209090c030703080c0109020a091415010c12090b040602010203090706082203051b0c100e0612090c0d03020f0d05120a0f1d1e060f04 70
    0x4d507546040802895000a901e40d801480e04409040c0fa00e140c02d800c0c46186200f141d01c0070b096110a2105991190204d01d031a60541040e001040041d40800040c01500d041000215101c06690000781514005034800310b0090f031200f000110001c0400860780e40818841c0215a801d50b5101c0024a030f04042d031001030030140302406801c26075001c0c805110081180100d07083e511070b00c07404028041d42042e600340d104d07449480c201003030041c000c1e04100d00c81d040500b850f816464044000d611600c4003010b05909100701044048bc0c10011350800c02da40d15010002000e180030040240040024400b01c81410040e010016034a140e07180c03400c0b01c01c0952603030381d03412140c0c9420310180d0400c0b0100042c55400031f4158590b00401d0b0300410b00d0805070141801359080002d1000f01a60244507035180036001a0301d6174000380e00d44c07d06501c030010405640340001041e5180300808541c00e001d804c0614066070080c080c900142c0b84e205000126400c01001030007a40c1441c0403022100c5c08042d00040c607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 691633012 1250 691631762 691631771
    0x305010f02070b042a080d08090d0c0312020d1118031203130c050d050a020a0608010b120c070501060306060f090216030302033301080c071a0601050d090803060f031f 73
    0xc00170071030041ca0040b814a444100c4915649241003541e81c2d2005040700c010030100000260312100214070861010ac0c10349441600c0b600e03d0307408070364072034504041d9080258284808610740c4450311030030460101382024030351360b000d0b0f14840d05920092010103901c070b5403220751706102c01e010f01c4064036084103507225140f410800d1850800d050328029080207811200401c400400c2c010300040214601c0d0003034408641e2944c41d03407001c4610b40002d01500255440c1007000303c1c0c2507032001004c0307a48090780320b04203810485199540303400d4481c01c0e401a501aa150101802100c940d4600c001c01056040700461034980c8203800c0c04070b1180c1326240501171607808400107611007042000514032080c4524690352010340d04c005200f4010800440c1400244003400080420b2500012070b565039401c441100350840f0700950700c0c000d1020050100b81003046c140907206841030503004140740184221081c1707031680341440510003d440388d0400c0c940700c0e61201104000660f10400d0850030034240000208 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 691634262 1250 691633012 691633043
    0x1a010f0207031a040b07091a0304030c14160b07050a080d0b210601140306060d0c080304030b0a0506040c080a020a05040e0403020f010f020301060e370305010f02070b04 74
    0x2818190240c0c4081c0280803e0240008a41c000800d503600c16031160450305815107408108541c850724a0040540300c4c090022100821652240656449842441d089240c81050360707a1080702038000c415074140354410030b031a41003d40c0304642a005040840b401070300700100c54483c00e0707903010380c10b10250040200007031480c08030390950001f070070818014080b0804200250101e1442100241e10001e0702d00506001041c0d01c2c0010404c40180c031002001402c0c0d9403601800c001c10743d040d80e401210315183d00d650010311114180301800040d03005041c4011a407408880003425108018000b40c4603600e4680ca00080c5078202d2000f0303400404520300140c070365010b076205984900ca1900500006a030190801c070130990b00084240200710a138000340b000340f48501c45907059010a0180c4804a020620106014245401031200c2c400c0b07120103481d594861003c0c0030a80c02400079140c000d060140e58140b0500c4801d028040318404051011071070702c0007684034540407150140004245410b00010321 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 691635512 1250 691634262 691634267
    0xa0c1e080415060609080d02060714030901060e0901020c0c060c0d211805010f0b130b060f04060f08100807050405060105070b071d15040b030415050103050309040f1a010f 75
    0x4482c10203206908014081d1034100103081021584100e007018800d944d50b0411a43c8003240d85801101d1980700c000c581c640c0076004e4040d50304010300804c080c2d0b503207400000e80d0040003199207000b948000700050392100d02a00e505c0c1072001100c829401100c0800110f800e80c000028201844032492800400380c01045160715118005801594001e50802c1000d12005040c0c41036844400c3c880c80007000078504417111b000c2a0b80700c1c3e400c140c0d441885001e00300380f000d103250440039407401d00818030340c03905031015400faa2681040d08044002107242c600810899003100800d030300280f100050360324a41c40c11400a5403292180a440e0007030b174035480485e850fa4090000c2d034056a0340305540015a16180318000d100402e42041111400034003000b2521a081c844a1300c0300f41c0550364480c51400d41010400c0c0c03101e41c80500308032138a412080500c0103e44440c85620b010b50302c2035000e59030310a8154101700660381800000c0700b0b0703540f03040c80703103054600401d01110341d1a0b02820180c07000c00500e4010b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 691636762 1250 691635512 691635533
    0x10501091e022817010803040e0a0c0f0e0109050405090a0b060d1220010e0d0f0c020102070302090411091515120601080414030a0e0a0e010608071b1401050a0c1e0804 73
    0x1443c130303c51070400070035003950200107803040c0d8403ca60400602d80c0c0b80c0c010781c02540d40450a100c04202000040f05c103d51185034080136400047c101144202e42d14400306080b547c0490b101b0f41c075a0444055001009004c6600c00d07080070013140c0c80c401c0c3c2c80f0359031200c03401510801d04500a01c010306940c0c401c16000c00d041008a0003004000304046c400011490341c030350741c004030b803100040d07001a12440c6480c0a0f440034000b00307070180d000b02070503402c55092061683c0e01030400c0e01c0000c881c07483d001d10f81d510241028859010419980341c00e032450014441c0040504d1150029000d05101c1010040000862940d01810034645480151a6400c000c3c3c0101a14422480c190000050402c01142c00400301c45046105031411000c00350380310740300803030350380c080c010607002030811008281d440d841102c0d0350410840f200300c100d0380c820644c0d9031100307006540c80c1700c40466510398040125105c00c80c4912071002549051040090111032601c0100c1383d48048203209000c2542d001c07505021070480c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 691638012 1250 691636762 691636787
    0x30504020603181c0e0301050108161a0705010204060224041a070c0507140906180c031e0a1d07030b130510050f060a06020c0d020d030c05010501091e0228 68
    0x184e0309074200f4440206000d1311441c80901940c00e010000450300000501c0c40034000142605455050500a080c4084c44901051400d500824404480440c078284020030040002d90001c003400d00b01c5004103150b0256480341030b0240095041000042074620303d582c11703e540118400350490f80d54060a550700301048801074081d01c100300c2d02084040d900000c0e0801504102c07100d24843d503500b800c0022003420407a10307003182c64041c0e0215481d41c803040b02071038100c00345070845001c10040402c0c3c41c0e18448100c80060015440300809400149000701903941d090000c00544038140c190b440311000d00e071001e0098040000d01071300709002c1c01800c4c031680000c403415000620181c04d08541e031500d060020340e0306500c2b583c14808005038650000030054004900500800241c85540d000c00c10f0641d501c0f6000d800384202003610800090f000e10444e030191415040005204000d40d000c10404840920003000862040006c100c45980c0015140c80c10701c038600d45c051111102d1202150090f48425 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 691639262 1250 691638012 691638043
    0xc060f021c120504020409140706030f020f1204050f0604030818010207170f090a09050a050705040e04080d020706050a09110604050604180b030d0507021008010e061923030d03050402060318 83
    0x222301170100c240070442804442c40f5035070034003c00016030f500c1c030101e10446c8a5200207000400106d0900e88000e601c9552203405017080d6028098501101420000111401c07800035800070104041c0d50b0000c14817100c2d40c83d1074802181800c030207584035802280c0103003000406076000b1920106880072b1800722101c1c4c00703001d4141000d555440c100400035280c29038501d90b20900702800540150b1145013501c0460315040b0405a90b5200c1d526682070076030001078294280d07074080148034085003140c040c160280c0849480001d50344201c0c03d14032036071421150008d100314000c01040106681d054191000d9641184401480851030b00300c050081c9144400c01b034241c01071380b4070103600d10b400402a107030300da000343c0b0325a02625504e1011104140d0900401d500308404d400881c809007003c0c002d185045e01c41c0d0001e168071a0715071b8414515400502c00743c1020030b150070700c400c0c40741c20f00f41704070075050700b4904080c4210300301940081c0c89800014520080f041400550100b0b00608000c40900e001004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 691640512 1250 691639262 691639283
    0xb09130f0e0d080402130510120602120f0414070b120a020702030f0a0b0c091c11042408010b2101060302060d0203180c0306130507030c060f021c120504020409 70
    0x94001800781281150f06a2003000c40450030700790140319015891141460f00b010442050802c0c0c3e114640b0241c09c0400e854051f4240300c13202015213654400381c021141024104c03210314203403502d100130700700d00000340445400c100402c002803c2c0120643d00842480701d52031000d9034481d01000e0086c02500c6001c3d5040c0314070301c4d07100780c201404102c495103e4018a0481840e40e0f07980b003c50260f200b141d030001e400c4800340011107208100e003010b9140d410321070502c00440d15040070010702640e0004991141a0382009542d0a041d5184084e0b20010802c00380207010b0899840d0000300201981d0142d1480c011800e40300110140080d0300c40d00107541e000300119200d036441194800250400c075a0b21344c1049002850103220440001c0c0c08500c41070080042c042a928a601c0d0703130001001c10002c48040c41040004000604c03e80c0104c0b015001564032001c40404a0074000e285c26844d1030000d80d00005204240141079000c00300d8004205000c10200e0f440e1518804903004250b0254042c2102a99 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 691641762 1250 691640512 691640533
    0xc05030414010219240e07032409030914191406040f120c170c190e0903030603060112032c030d0e0109082d071206020304020306010b09130f0e 63
    0x917485184041541d1650802c040080c110302c1e0412918408200721580c1d110300010800525030410400030b05020a00f0940b44500f0540c46d50143d44441d941140400d03c0c084060050740d001c100c040d03800351800c0f18406110010002c42203500952800340b00c2c05030007031046484480d02d440301268001c3c0280e8a6412900707580b2607014240100950080700c40c0c50300b050340050802c02070045118950044c0001e40b02c0100746000308490540d01d01241b81c03050b0b0340503400042580e00a0741c6540700c0c03914030002d165a0300c0c010003018140030058008002656003801c4d4240400d03440f0030121041c40f4100c0c84030044410f04400015807541104990354980310f2a442544160384c030108400d1050800e80b55001c0b41ea0315004529100c6603090450440907124101c010311300f880c51000007884500d040c0554034402e440f201c42c0300d00030002a100fa40c070039400000780411403c040114500401ea402111030600300743d4400141c1491505501d81c408a4a84220b80580b1003254070240421a82d00d08031020440d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 691643012 1250 691641762 691641773
    0xb06070c050a05101e02010623090603030a0507080f040509041a100810020f040b131d150906040e06090f100b10120609090c0302030d0c05030414010219 67
    0x40c05000c0c06000ca40341c00046506001603000d150086644825104c0512485800c020794580109101152349034207000841e0011680f0034880602110111050b08038a0300921040f06405000140607038410810170308059030002c1980d11442c1c0c49516540d0380c1c0031201081080d405641c0106610043c007030180410803035600d070658040410380300c0f001840d42d00d0000c1500603600034402c0300c03e150400c9001c0d820005c0298001c05545075120300d0315051a4887c0c501c080640c001030070301001201c00800a01c449044403801428014146404100c00d2402603d00d59159003442041c1e0301401c1e8000102d006561a904103088c0e40741021f044030014035001c03000300d98880c400d1702030140c10700481100c0840d906280c000c010030064050141c82341544640f8044894505c000e080507031040ea00c03c00480c0ca1401070080c03400441c042c00300214a03a06500407d0304140740710841c0018080d0508030b52000403008015141204c400c0c030300040b024003140340182c0c1003040b0b05c54090f02607025075004408102 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 691644262 1250 691643012 691643033
    0xc0405091324020c16030c270510030212060402061611031203070f080105060910090e190b09060a0b0c03120f04050105060307080a0b1320030606041503080a030b0607 73
    0x14005001c548181c0305c560b0180300d54150f140070141208020310130905c0065202188541d4120001d09002c080c0746002200d54201e03002652407009070501c4079010410b5150a4203003000c02c224013005010f11742095030000d082031080c00340e4017100450b4405500c0070f21080f5112021000405019203e1511516200708020340c400c072401d6001c6007100741d03808011841602800d041c1c8002604c617900d0311403050104400407140707031450010440b503894042001c001c0091224020780c1c403900980c0e1200c04480d0703030f003040d1583d00d40002d00801e0043c0400c80d482d9500440e240c11070383c041c0903050741c1c0d0341d00c00d046905520504061105022001d42800705007503150b182a403040340214020041a1203c45c100f503200d89440c40f44103c146e1008030340b00049451070000c0c1d078202c25528504040242e40366107140300344005100300c01255200d0b25a050b00c2c0d04044c841c90f60300160807078081020b0046699503502d807a03440d020240c4016404504d074040030307000354401496060010030302074452a11340760402c080f6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 691645512 1250 691644262 691644277
    0x1050405180711010606021e07050d0302030a0201050a0506030a02120c060406051806090904060f15030302030a08070806010c1b1214010614060307030e0a0606060f02060c040509132402 81
    0xe807020901c4440400c041c4950400c0c2d0346c4075400743c10300c0b1401042c1c44c0301d40002520503002c50b01800d1000202c6941e8000390840e810f00c03d40140d034607030000c00c0010b400c41e1001425102c3c42400d0108000c038940d404920100e01a90403148110a040a41d2005250801c40ca558a41200000030040345460f0020050a142c0202c6918018426810010301505000c0c1c82c140320f0300140e00d0004200021182d42100c00c00d01e4803002c000624a01d040001c4100074401d505c15009a0400918100003d81c06410070364001454101281c3d18241100028401c11403500058440d450081010034203404584085c8000c0041c03036008007400b002420841c5040b02c071401c840030b85628081000076680001c555024580c3c400811182c107550b19503400340c0160000b001e100460380540100000010310754820309001d13044035030312580c3c035210400f401380c54504d0141400901b100140010840b0b0f41d24410780a5102e00d03901c50f0a07032000310600e460401e01d0080c3d4194400a82102d80b0001d5100b240c1c1c1c01382110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 691646762 1250 691645512 691645517
    0x10608010e03040b161721060a05030706050a030b0306010305010b031c142b05060a14150903031b06060f0141070c050a1e060e010504051807 62
    0x4030100310002070340ea0b01c01e51041320b241d03410900c0344810304400d05070304021540c02081c80d5519000501d8106c08071358001655540c696040d40b06140a03641780302c8169502500030345550ba0f807241040c0000c1d980303403036030b1141e03100300000081e1500405210707030046080c02c0c5000d411140d0550b102d14210340601a10002c09000e03100300d0364034a50f81110700c1c08050880d20a038403801340184059054801c0d5a104400c1260341ca40682103290494101c9508000c28050742e5400096034100f01041101441a0368410355440c070803244d101005a0f03510140b128800043d414040c0c1d05c11800d008603080d80160302aa0b10b100e101070310301658894010843d1445048111a104c91250401005486d48030b942d020380829088a5502108202411045102c5400200c10074510310360185100340001e51080300201e03542c0810507000c1196003801619040645100800800d54554030810580f82d031410b0711a2404101038030262100c564059012900500b0000d0000c02d100441c84d14580c0b542003054905200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 691648012 1250 691646762 691646771
    0x71e0911040b030403230307080f010609050303032703040312021002030c16111518040905030304060513020603090c0114040605091e10081906030c1502070305030a0201060801 77
    0xc00c40d408440540da5511491401c503101c90b00c045841400c1e80042074008011104800d581d203011b140910300c9128141c0ea582c1030340c42d2100f5140000403041c0d11a400348544028180560303030740801a030b035004d80072001c0d1008690607207401c84241e40d0040d188440e103000004020003071002850001c50002165003c5034601c80740200480220b201c1103c0da2200c0000130f1000324041010b5401030b901c480d014441c280152107418000403070301a04180420b4403043e000801c01c0a54501414201c44400c3c1100c0400070010b80da1141c1e41c50307110041006003481d650b00002229592441d20703210003d13801a1080340c407840c00c45084c550394003c8800b458046503011041420f00d84041c0111005d482c9150b0314107041514900902c032100141c42c4d504500c02c1c0c00c6a0030040e06d625940b0303000c15045515910000d807410302d072210300c0b03003038051000001c1c00d58100a01032011406000c140b1040300c5120001d800c000010302c1d0102d040c00c1c0c554000030010b02000400a5042d49d054200350241c41443d4020030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 691649262 1250 691648012 691648031
    0x6150c2402031f1e0603020711060a02150603190209130f0b09150601021209040b121f060e070f0309210f08160305060102070306020f030114100e12071e09 68
    0x320240036a4203460000ba00e000005e100c0356101e60090203642d40f01c2c0900309500310440000400e542c2140c4280001603010030f0040030440068000503030400c4069001c0c0c881e1500340444813240b84100c20000c6e000e81d1301c1002050401c84007400600c10740342c110012004a172030700e01e000c212506041d181492903200e480d015561560b40b52000718024903051300280000e915000f6001c4590b0021032085600c503640d44d260308000e441d143c0d0041c00c04075100380a40031100d0850602d10344001c000f500400d0903840e00001380012011068943d40108250803c2d444103d140c0170304034050b15900700002c0c6040c8124811100b1221040007210b81440182c035400d0305003444440031540101c044482700c41c91045011001c407000d0295005640108040c81919032043d00c80e107440c01070f03922000391281110000401000180004120804142e4045450450020003044001c140d400c29003026441f4001c124110103c0100400c401001005011007110a0740d00c0648901c0c40003142d0704c1010b01460500c1c002c0e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 691650512 1250 691649262 691649279
    0xb070c050906010f0f0905061b0114010b0901030b04060b0c01090302010b10050d110403050a05060105030c04110904050604061211030d0503090703030f0201060b031906150c2402031f 80
    0xe0311640b0b041e5501c0607003007201302c012150816802810340600c1781401c1c0120701d1307407940402800c00454142c0074590861030b1480c0207007140c2200100c28412058900144180030300302040340e44001e024600460344204000020700200580d81c442c02c0c0050000841c0000d614064000c00300c1640250000c00c5094034103400e03c45100380c110607038400100208107820840c202036004c4c10320045124509401d25440307903a8640b52a40318842903813103a20101c010412482c04000d130744000071041d5014040605140c1c15441c0a00540f41c03183d201d20f456000180c80e0340c880f54070480080c4140c8004081c12582420f14014118600d0b00d024064000c019200c445035010380d048a010300800390082900d503107952821115a0520510401107540710540015001119805140286c8451510706d0301210012100c01c00c40e540740d842031040741402800d11282c40c5d00401146021a007010100c10301c0c080c2050030240e0008034940c1580032504c080b013070041d551070000c4c0700035143c442d03061020611912456803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 691651762 1250 691650512 691650529
    0x1104020906041206060e07050d3c091e050106050409080304080f070830040308011802090a080606180c070602090607050f061e0606091c0c0b070c05 65
    0x81c0c01040820041000c140010700d03030fa1030300c0d00850300003c03002d0700e96400600c008425070b11800015004204a03840032521f204054442e0f45500b0f21200710407100f40d8800191001100d512035006404101200c0390800c1d42007101c1c0c1680c010201d401c2d66003145a103040d210403a9400341e94641ca03004021496040034403c612446070080c0c056400c5a42e81e90b912540c40e4840c0078003a5800606004c2d601c00600030134003a01e0340d00c401c0d0800c0325450015888025140016601240780021008240070200b9006244603054480700d0f09104014840e54409001920030340640c140c0000402c3c40024000780049903d50140d80d0843c1e0780016182c01d4407012003404c105072045031800504000c03440010716180d00900a0210142840f810f156498881c11306222700207001540310b8100a04205600301d0502e41d1210715800c0440d10400750400314003240541c050b85021f24000c072481c81b29901240c3d0758410141031250712140050003e912980340030710940000008640743c2c2e102e65004119407820208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 691653012 1250 691651762 691651777
    0xc060b01110a12020f06370f0c11190b090a0206040e0109050619151b0f021002070f0e2701090c06030b10080a11040602010e06010501080609071119030c110402 70
    0x404050903640c500d0400701c060001c035114040c00e682c0c8821f00072800218020011003600c043c038001440300000001909103c052090300005810039100300c290602c1e4400300504440d000000c41c81c2c16500e400120303190100d500310195211802090008400c03083c640414140c4600d14070601082d10364005021001381c601c40f04d0b02c4400304454007441810315a00820100301254540340c0071044281e07581d080641c0d810401640e6400f140c032b20000960511414031400e00070aea1005040aa01d0590346401c840d50b40d003e14150700441c60040b0704d001d5202c40080809048807150902c292003040c080b603000781100141100d41550f80200025805e01078422202030120141030701886160310340c02290201c00007000d05102c039a9400e041080c040d83c03d80a0710181c2525000080c02d440c1c0d90000c245014030585c05541000000010010135440b02ca4140c0c1d0003000a003004600c169900022500b41340300e081c41c904900d51013050500074558420003100d40e25006510000c15150084144802da21031040d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 691654262 1250 691653012 691653031
    0x503010303030e010f0e0d02120405030a02010e032b0905030307080306060c0703140c0103060e01050307030b07022404030f02010e03191e030902090f070c060b01110a12020f06 77
    0x1040442e00070b030003034103201103041c00018055000300600c10403504804404500366201d0b490743c018068040050900c410b16444140b42058034040019644803101f640080c100b0803002c002e100c1e59107080091300b900b4183d505107d42d00c2e0b42141403003000d4109140c03102d00001d05044001a980c1000300884800542001d8407a29541d00d0070705011440d402030205c44d480e88590070000022038101020300040c50703400b902901c2581e8400000405980b0580c11082544031042c0040041c0e41e00014001e0841e0b07030041d95580d050343c600c4c009034146060000c001c42c003408044203102c0069840a04607106511903114a640341c2c00245049023221720511000540ea80304100c0420060520385000400c407007540ba02c42884090020200090482c4010440c0402d85444000b0110300e444118985d200c0100c850580c41031074810300c01403080c900114017800b000d0360350146011a034807400030400720010354002c84102c4d035034902c0e1501c9941d04103c0030a0050192a4071501c4020011a907140120380a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 691655512 1250 691654262 691654267
    0x22050a0609110a0f050a0f050904260703020106060807080f07050904201801050a02030405130605041409160305060c1308250b04032001110102120604140705 69
    0x1a51254001c00d0244001c1c1d80c041e03410310b101c8003255620201200549551049020840e150100b4450700b00b0071034200c5103954485079002d200070b40300c0c10b0000e50b229401c00c4030003c3e0700d05208584545140c1c000c503144140c0400007004002d16405406c502c013201d0460340c68011565651800726055641590504240d04825010810031031046010b802617042c014000201504e80b100039814020703840e002540501008100c10120024145042c2034040080c2010b500c5c120601100a40340e00c00e03401241d1144908050461902c0b900703600080c09000082c02c100301303825150706869201d0a00b00c56001c006d200781c201840e111014a0040000c803070f40100101003030344607410300800c03135001844c680f608800c215200141c6c14404000e007000c03140c5101007643c2c940044031810000444250030030007131340130100700800020b07511449030040c09074405500a0079001c0071004031103c0001469104196001044481082c01c0040d0a50f00680046070b0401011001901050b00d504d0700700c8800380410000d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 691656762 1250 691655512 691655533
    0x150309050a06050603030c01020705061005012a060b090a020304060f020a09050d05240f0c0a05030c0903100f020421021012110d09110d020f150f040902032205 70
    0x9600303c103800000040070344e820802c0754041142241c115907c1584c140e8040010302030040d030314241c00b5000d0103003840c2401480503020020b181c003110030848202c0c41d080690080f82400084d83c89511541001800d510182c100794a45d540a900251010355109281196110540c4c07003c0c82103d9100d207440c0c4484803540e1400341005040c0400b00d2064680c0e001d6070356002e407c5041d01d07070010b0000c5584c940e400d011307040170040c15103403580040031101c19072010000d8002c1caa0b001010741c0d601c4404c0c4000c49030b1744c00f84900400e0070b000c5c00700c0000b4001c604168011401c0803150300600103071000600882d40d9003180e21904443c11205280c060740003461800100807040c803410000c810038004c03800205207510804086031081c4d100c40e90345040c965840401e242080304854403810081300031a9450043c01c05600028801c8003012422481400ca1030b01404050320001c2c25201c80e02070307420f00181c840d5a81c100070000395004940c1c1001c14035040c8440344a1600140543c03610a400600800c5103a80 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 691658012 1250 691656762 691656773
    0x100203191a0939030403080901140105060a050d110c0d02010b1804050304080d0509101e180e09030403030201110f04140f0d050a020f030c06030a05130f0c150309050a 73
    0x40200030300300c14800303c0061060400d11540c0b41001d0300c01001d0983d039a10b05410028030701e000140c01500280d0420204040281d440e044c1981914402c55895030740f07262850013604c0c1c5101d900ca403002c09a091030008002c0c40102006405480510029659100ea800030b04130300f240c51449401d9402801d1101118402c1418800c0b658030a01c50000c13a40382c1503c0e00c01c0e95141258210386240007400005040d03105040034214104014107034145100e6400303216000d1003143c0c560300702400c1000443c1440d54400090b00545c40001d10b0524072200040c00c104031a142c403a4054081a00550700301206014070003550750460381403c0242882c6800d0504044541e0300350303948803481541c04441c2c500740c404d0642e207101c0c5050a082c0328000a100c2c2d42105e205001450a034200124800c0d00300600248a1380c840c8401c4030b074046007186000890365600700300714050b01d403440c5020300381801c000d440008100364410100151a07201c000e8001401c683c42c0c0482c2036440c90000141940c0082090b10001032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 691659262 1250 691658012 691658041
    0xa0b0f030c072a090603030804020f0604120807020406170a060f1506030e0d050c030711030a14030a11060c040e0709030b0c070c080105090d11100203191a09 69
    0x500840400c0d01e0880d803a100c05564640903900c1809144590004807610038000e0540c000031300991000744030252640c6c8002d4904000100003a0103040e14100703c04c1c0355a200f0702101e02401c106400300010800c0da00300307200e103030300050001c0340111314100000c44d04115003c03040ca0450000c3c0005d0041c1050f565501c0007608035826981079440d12800c0b01c0311103000c1d14450b04081c08056034005a040340e54041d113454441004c8030308081c0102040704001c09000441101c1240790080341220080c00e8800110340780c90349444001d4048156495001d252242c00b000a1440b031695698000c0030340c28100c0c1581d110728080c0c0e0070011450b0f040108100c04c110b039040703485d0302c202d0394101120680e58a484a05101c8022584881286c0d00020043c00f000180d808807805800e00070020072031840d0582c070046c0c0e0bd010300c1816a0500c1424401050742410030001400d56809440e02507449003442c103854100003408041d0300d0019400c15280555070031410071483c1211000401c0041c0e1621403d00c8800c07001e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 691660512 1250 691659262 691659271
    0x60806030313181e0902010f0c0305040614090a030516080601050a1211090c0a031503020a170f1b09060909071e0f0803090108100b0301051e09091501050a0b0f03 71
    0x181c803a440d00400f8400096070350744c1500c0c0100301160003c0c05d0310004040c5080c80d1742350310900800d50b1084020950010649003a595141080550005a500307180618045c0030314965110100340030200402c9008140e1007411249a50390358003003511045600c0e21981309000d107681100302180f08110301003200d002c00800c42c0c00f88007100003803814807003c140c000d1400c450085044c10006490b581c49941803040301c44c03210000502500e410300710b60000c0c508100510a0f070161150480051005e1b07101031060101d901307250b07011106003141c665260254110104074082c0301d40b4008000520600300495a503224002c881d02404825080580d900407009103185100c2421040c08008034148589007503030302c098245c5200542e11004200300040c5050001841c2d0b0321181c22007142040780c490f000741a00c2c190781040740d110010500c00c00c1000403410204800952010180040c0403203031102040845412040250f0003a07540c1c3c0340c005000b0b192200c2e10684600e100e0410225100c41000c00155420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 691661762 1250 691660512 691660559
    0x310140603040b270a0317070201060e271605040b06070302100923150c070320010f051801050106020609070302092a0406030e011506030b1513060806030313 69
    0x840704c002519454210a018101d0218201d01c1100030f4001d5400d50f041d9010005100a202c2a428036010310300c418400740404a01d4200080003221005d40b05c60708082c0f80c0d990004456949000040081001c2c0b06031285600451400070845210704100c411503100d00c0d0142c0040c03440e00d110a07043e100900300b0420585400da040080c41c007105040403242c080c850f110300010400c0284409800c440450090a0160303a50782c1000310b0000070b500080b51507061f180d00803051101e18a0030103124054102c00c81890b0000d444c00040101111035021554400e106000c020032a503070301c901c002e80c1c0d50f00c0103650288580c1d00100701003006203807400b111903101d00c08050b83c3d446a5a030f0f010116568110740d140b0b090034240410305114450380741c814800d0700340e50382c4000c1c80b1508a1100040d00c0a400b406501e0405131207c5904480e602c4201132100c000e8030083e1026039801ca1521010092411400b51a00155044c000b16a003403030004140d0760b562a90310100d1048516049264000d452080d005103034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 691663012 1250 691661762 691661821
    0xa0902090702010213052e18060f0f020601060e1c060f090506130305040b0922020306010207090b060a0c03260403080c18090613020310140603040b 65
    0x58a860800500030603090b000540c0301d090050017401100304542185000305440d048141e41421a0030603844004103502a40e403001c1e0381030600700c441a40d15060f580b00c1c607a03403540001c1c00c2e41c0e1080021000002660300e20542c1c12040c0412a2514420721030b200010301a589411410714048080c00c0b07451407d00b000e040801410f58039902a00c10080c2c21660b41ca994040702030174003400f405003580c482c4c1c861440c00c41051003658090411b020340d0081c1d03ca82e2602142c000b011b80c99400d48030103022841140c0c44001d2005100680203540200c80c054014042c00b500014184114020003070340c10717002420303181803990726131085400d030002981c19800c0164910706840c210542d40d80d840d21801010304840302030303c1c150070040c10301140588101011b460070400a206034006828201d6040000c54000d001500c9100000c3c2d450442d40b10640b06541c4004140030541c00c00d072402e1b1007103c1c00303811100501d50b90082085a6400f003241d000e044640d050340000c0800c240703084240c01c2c0e411480e03540e07003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 691664262 1250 691663012 691663031
    0x41403040e040b0609011215090f0b1303020106090c05041403030f07050601050a062a050c0a0b03190902060301150918020d0e061e090703120f1202041d0a 68
    0xc1c4095003030724240c41d802011418000c1d0390400c5085140034000480c03001039010080c0c2e0b0703030380402c2140d03054030175200e56241c0703182040001040000828581055912480341048020045031a0000c2001c030003561134403200189520f0640225101901d10f501ca050420b07150100d00d014019802d10541e80c10300040000d07441c0300c008140a041c885000c1d41c001c1c1040d41c141414401a45126089501402008004140e4611500c4205501042810b04e0791311000d0480c5402440c21062039922548401480004541c0150720006140300da045d04204a2104c905039010310b00300d89100ca0080e400407820001840385650307820b25a240c00b000c2c0d107400c0880e984c0e50000346002c40311210004101580000c0c4840c4040c203a03000342c4010f100c114018101600340300c841580f4020039101c00c00d1400b80800005503c00b042400034100454000c0000c800c003082040001b0590107845482c800130694246c20442d0111191091302d0556004c0307207400721142d6281c100740100f90340042081110342c1d00c40d8501e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 691665512 1250 691664262 691664279
    0x3100803030412120902090a0903020a080a1814150a11030d0c0f083705090105010e070302040f0e130f150e2109010c0c030503072904140304 62
    0x40d4402c1e07004002119111014030001041380150124034800c86003040b0200c8050f82c0d030b219420ba0040e415441c0060710442c0c1d89010b0381048503800b00905004004a0b40c1c40030260080001d000c914120ba0f80e9201803138441c0e0391415403140c001152034202c000b00451641c2c1d01d071200001c1c20b41004a0074944160084520228a0b5a001e094400c0da03580e12404000101504a030301c1526080710f90410100340e25015250340e1704444000d00501e40315802014015444400b05400d407101030794810244554134106c40c01c54060300080c42100884d00e0b0070000038071090302ca4801c0d94103a4602c9011603000c40c0c42c154040080b12001b40070914042d10380c8510000060300c999548034005c0c8540741c5181c1c0d00c031024810400321003448003a4112074103c034a4500010710812208880401640d0515444038041c900403600e41c0601c0c4001880b0040801010003403060002c05008481e120710071072101d41e244202070a10030b440a4400c030301c0c44102107003c6030020b81c0d005540c5c81c10401d8035040302e007025982e4005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 691666762 1250 691665512 691665517
    0x20c0f060702100e01020705100209040b040905010501060f05070b0f070504120c0f05010e010206060618130603020f040207020d171e21330a0b181c0803100803 70
    0x41c000540e024111500c50b00d5894058034060769480c100031401d002c025114a910703005509102201c4c0c03540016194400d9940e0f85c8600c080580282003000401d0491910030300900342801400042070010030b82e107104920400c03c8452859220a140c090707030700d51141880d400d44000d0203d00a006040c4400700d114016000014241d1340558071240c0c80625042e80d0f44252081600300504000341d0340795800042e41c0000301c1c01e030040c00540d0b2055440d200c0c07c2e5180e0042008060f500d41c0030410034420014140242c005d04142d9001b15000300c030300c0760b598040104910480d40b00941000840c8969400305044089540850714100952490050420413045040d02e0107000c1180740400441c0c48004121450310424404541b000d4442290500d81401110707260a10f00c83c480b0040c0c600d40558402c002881c00c4615810007802c422509500d0b84140c152542206148440010070000f040c1541d00d000d92044130034140c1c890800380603803036075100c2040f9688018036130180d402c1540d00000300010304100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 691668012 1250 691666762 691666771
    0x4020a030c030507050c0a0b090f070608040b010519031e12180801110f180913110901060f0c0f02101106090610140d381603020c0f06 59
    0x100051556207500300078040310005050441080403c0c818107034454070001d0045022600a030300040140d130740c4c8c01164540004480c03c61400c1c020a000012200d82001420f801240f003405d0840650786c0740c50a000001c0340044102501505140e420000310b2100d4042d12001000500319204441090b02c036042c440b452200c0d00c100003801c42c40a2000c202c210482d82020b403610030028800c3c40220341107200a4041e0300716618421000282a241004010018a4000c10003905141540c540240201c021600d07445013940c5665128210398038900d09480218140c88254542104c02c00f0f49040450304424098070841d25140925040c00142c0d170ac41c44d00300d409006c0c0c1d0781c8101103c0a401105410458040c0c00d50005500071002d11a00c0710942c03583c1d2056034080d218280143d00341600059511a00781c2001c0c1c010100012103140f032405210012510314192203805015041c0001140b00d41041113036040a00d0005280b5510300e503219030010b0654070342581c01c0300c5a40302d00803d00380c200001560b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 691669262 1250 691668012 691668017
    0x1d0618010219140c15030a2c0c010306090e0706210504050705011e0f050a14031f0b12010504020903160e0712090206030720030a030608060903090a03080304060b04020a 74
    0x819210b001810400a0380c034113400d4454040441ca20004d55a5a0102400c40220951100780c5001d04402400508560f1411008104083c1011000d40c07030300c48040502440c002810110b000c101120203018445c06000340400815109192800440d182640b08040c0102c1880c00b0300421011034113401458003036406103010304091480c01001510340070b460100d0303034042d01c080d604c280300b01d41e00200075a980c001241000380d9611403c28049070000102e824900c240c00c1d021040c49540d0391240300f0244504162208440180e440e03020452050056410710501c0310008401400641001d40117010f8480e409000c55070140c502a00d0784131880403a411001404200e6010007140c1da9200e0b0610040c0942d60b03004002c1060a80c01190b464400201400148184091284003203e40c01c10350b01030550307851050740d4803815400300c000d021b040d07d0f100b0340c6114426400410a420004003ca40c4014070060024103203a213182e6442400b500002d005541c525514102c1c0304560301c031400205810303851503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 691670512 1250 691669262 691669283
    0x201060b040b0d0b0d05120903160e090c031605010507050703140318041104030602090d05070f03050f011419291807021f061503020301061d0618010219 67
    0x1800c41040710304413003030b0600c0341120303002c0c2802041010804110803400c2945081d80c502c40c01e80881c3c6003664000700a42447c0310500001071110f0b0005441d40528090004d9812038040e80c0c003019a02e2550204036513484041034002c001660140000b809054420001c1e640c82c66030740d8451407800484521841d045420005d03081c00864071000460b0380180c3c080b5410400800007400b81c81d4035010b18040181a9980010040c03415a20104541001070340901100d007407984508d40c00c02500c003070344400c440c80e01c2601c01d43c4103407100c18010b0b10f101100554140842e591540441c1e1205514464513040d4282e4480807030380c14142d14a0951341044607041810200380800d014060307040344030044803082291020611004540c0070848103168000742d034400c0100c5094805900040c04581d0142c0e440300d0f1250710103c103d64040d00a11304840450729406819491491400d01144007118100c0d804202040703402c041075a0480b4420141c1d00610450780c6203003402c6c3c545401c85000007400d5411071800c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 691671762 1250 691670512 691670527
    0x4030f0f020a05030904050414060c0a1d15070201090e01152c0402030a2903070509071b0606090507030e010b030a0221030f0d0b01020c0d031205070201060b040b 71
    0x100d080005800ca10050880c075109840d80341c0c60340100c2c141184165142c2c0081030a0213082c042c481d1500705050191010f50903c0c0203801455402102c0002c00f050413510004022417104540074140d003000390601001001c0318590a40030703844607808a044c0090114041030b42440c101116010309441c0140d08040c0100400107002e005944121f1102c42c0d085e0307110f00e2031603014400005824101690701581f42c1c0c40704e55070500545405001d20658154159404042c80c000c005031070041e40c1c0607402e86444a0702c51041c00310212044452202180680d00c040501e1403100f4000030038203000b6a40040c07983c1e01c80c0110000d48030286e9030708000940340c103854035030500280b103032010f000c5003240101503d948681c00b180614001d0359080440032618075001001100500450b0003c44a4002c515613404002c2c6109006001102c3c0c03090043c070031050380c0c2000c1c2c1041c401031201d964041e219152002100000b5501411008029a045540b00c01d00025a201540090302c00340800010664407200c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 691673012 1250 691671762 691671767
    0x6181a0a1b08060f060a08100e010e010e0408091509030d02030a0912080706090b09010506010201020f0306060a090b0c07030b0a0203060a031412040b0d0c0e033304030f 74
    0x50140c144401503240414205040c8400c102080481c8103905040460350b68000004580c0500300744203540007000015880720f4240d020340568070030400403145403110b0380c5504e25010701401c240588092504041c005000400202d280b007607205100e006030f64509076408010415000d200a44d0040707612005c07445651602d07043c0014400311949100031800c06102c2e01004181800c81d115030310303031402800052030030701440364115011280c01030300900171031025107013102d44107204464624055103800041900d540c0706000329141c07850845041805c64071803c3c1040390941c0850b40f50410b0020b181c00c000703403003d82e0b10081c1000640c1b400107800d03102e02c1c0d405c200140030401005440064810401c000c029a61840d0742c1c0142c0c0c1c0c01150929125410340c486a14190b1000d42400003280045000101501c5d052f0080000b44c1e07610302c051126159241c010303030b0314080b00380c15241d05400407070280d81c1008502120400030701c2048194003449000004980988009a4050740041e0310116140c10705038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 691674262 1250 691673012 691673063
    0x30406150e090f1b240a02070326042c0f0a0c080907172b0306060c110f06121f120503180a03021201050406180215070618 54
    0x1000c1d002402c1907a450611030071060040c122100c1c4621507014138042440d1507803a01c14400a04c040b42a59606d140c564042d5480d25180700c215200c01601c0707100b180d002000071100600b244035071502401e00f41888014404c1101c2044242c01018010300f82018440045d50190b00801c10004400034a0928010040a5500c401c09880c2070201030806e00c8000b000c009a108115041c0345400c020103207a10092a00700b8601003d50400319120300d00c03040c04003440807002014090700ea14201300341507440c0ca003500c06074010130002d0286802c0c6e4207030f4036107030400503a0740310112402490305191584000115040b200141c0d03a03800403121311040b0300e50340c1c11f07a00345150242012080072050007100c1d61343c0d15680d100e214281c0b440c412000c0f01d441060340f40d1402c6039001e10340c001c180328075841004480a0080c14100c0d81621041d0a041e00030031641c1524598020a503000f0f409848a441080c1608007907030700c118000c694455881050107560080290b0080c0c03210301c0341d80901d0116a40700740458070310 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 691675512 1250 691674262 691674283
    0x30501030605011a0904150e0c0d0f110a0f0210021b070602070b161b030302060f07030b0d0b060f0a0e0f0a0b0d0204050414060a020c010e1b0105030406150e09 70
    0x6510500c0580030901e00c42e8240d030103424040f640451200b560913010345c0c5081c010390026030349086660511202705400c00c00f0740001340f101002048490700c80041802541e04036140d15a900c1070800482007c00c1c410311003940c5844031801280c620302a8010000126884140e40c1c541d03443c0c121f0b40301c030303842d0038203000780310007082948001c0c0903080c10b10250594520560956140c00d50764004400f04100340c81c21100b210302d03d240050008503589040103511040c084800440c28030414001641803806071069418601000e081020340b40071710360321032461800140507103603c80e004071402d03082c940e03030a000714000c0c103c030455004490070140c00707480408501900d8101d03288d05000000c4903580780c501c0e040c0c00c06501100c02060a840c0c90900782a0304418249180450054208004082e1030507002054a82a41c500810038030014200c06a1504042a00c050032800b1243d140040d40d0b2151003c2d54106014450000301e001d006681b5a5940105074410b0705404814030030080000c07014020034824 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 691676762 1250 691675512 691675529
    0x8031305070909030e06250b070f0306140618040614030f1f02090f09070513081c03020c101509270201080a0b120a12090f231003050103060501 63
    0x103000c0c00d0358000d4111012402504c6c0603800201d0710511006400d40913414408005112180442180c1899240f40341c0c03c4452501080b1000d0185c00c1c0c00380303c0d20030354040303d80181d54540c0e000544810800c0c0c41d40b00170102c85d02c00204144048440d51940f0501006080d0040b650356552901e0061509000e03a50500038001e410170700c10380940b480c0c00c003121100100a13a030700503981c0c4070b00400100c00c15401103c042c0c01c14250010825081d402c88000c00e0217841c1701d481c1c50300703e40d51340103a655924004501303014800f001c0f070070b21b0b44091302907006040002d02d0801078626003001944040200c60040140c02000d15800f00300b04007a003218440d2180c21002c040411602045510780b107102002102c01c02030403c8111000540c1031425540101080c04000780103c440350300d028081c0d503407481d80c1c80003902da44a00801c6040064019205981280c0c90880103204540c0f8001000f5240468240714041d4200106c880801907602e415024140e804d4544000501d5411030500400301c450507042800c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 691678012 1250 691676762 691676771
    0xe0111040f0e0108070501030c0c060527071a0702010219030f0306051e22060f03061a01090905040c1706071d060904021b01140403020f01180b06010309080313050709 73
    0x260300114045081d81e07020b0030085100000688100e8041c0403901001c0e051618180034842d024dc0c405610b50449070291507210150108180d25544801040c4111403201c02d8088061012031203a90250910500500540b450300031494421142c0b441a404105c0019481810304d9040681611944000e0301d0280c034480d9a02c0c6201c0b0f00b52a52405c2c40d50410b2103038203240b120741608407808480e0008284454028004684d6070340300140040c00d1404201c0e00c05042444030903580c90485403d80c00000140d446000003450240300c80300604024205a45001807044081201e40b0066290614140d80e54002e00e05071406100082104010544840300280120004117559442000ba0b8241140803180180d9424000002407500080d1410407800d65092403496659400907140551160b40030f07030261240e4042d00c8881608803100440c804003802814078614000c031701100b000c250700c00410705002030301798042d41f144141500111641c0030055000d20310320003040014440d040040c42d000b4020302 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 691679262 1250 691678012 691678019
    0x206071a04060c0e091f0504060f06021005040305041a0702100e041401081c020c041b20060112060b0909011a0607110105091302120a1a100809010e0111040f0e01 71
    0x22207080001e4486e9402d84030b5807610350340e4400c18842c014020400144100003003030b07503544540c400704003074811640580a81c1042403450070060141c0c0e84078650658404c0e10b0181040e1151509501c11150030f001c0c401c050000c4401038030344422031000e64200c2c2c1c5a045036858118100820783c0d01c403042260a0b0005600100502a4005090940d5000143c0e140d55031390103144040346030a1500802e01d500030308011811558025807a05406a0407066440d000c900c512030703d01303040512a000c1645203650090004108282d050000a0f020501c9108045440e809545c0041d962510a441500c100d940d50060078038a0072401600301c0d40a00300b40e402c1403c1c8246c40c0c0f241c01c89000c000c5442411300400081280b00381d600d17441041442030200c182152186035502d114a90040b0031075042001e513103480117151070032400390044180d243e8001e144143c0c0b40d44520007291101006840214250740701c025040d6000030a0103021000c07184810040c1d103444c9861104000c2e0005588810103a103004001031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 691680512 1250 691679262 691679269
    0xc03061309120302450105070807020108060a09020c060f07020d0207050d020d0206030a3620060f030a14010515031e0705071401020309190206071a04060c0e 69
    0x1c8080e0640c180142c8415108220320000000b0520703640119144540f035030600090580300e1004172090300d1100c861802e082c001920f070313403041030000f5252940c248170a0700190b102c0c0b109aa481000030b807a1000080d5034078101002d070f80001d0305c2c9e160550008420410459461300b200c40c0d20440c2c40c0b0051003044501070000c0d445032181d0144070701805031140780303034150344504a104020315409000a0fa40340340802101f400ac3c5a030500102100154400845031031103007040b040031200c03500801c0c0b42d003c1c0842c0c3c3c6480c6900405c0714101202210f112004010b90740344400751117242d0204d21410350f00d16000e40480102c940000007509a41940c5006000799100c0421020301409083c05050703a80e203500c0d0040c2e0b00103104612588141501200b0006003d6010000e80516403189400c0001c2000820009081c1e00040356003100320f1b4002200c41c1c500d8040000741e42c180c0c0380043c00c45440c03c0d41a860b0742c01080c03568004200014804410f04c0204070261045005d100300740e1408100001051000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 691681762 1250 691680512 691680533
    0x17030415050709140f0a120308010f050910090f0e1903020606062a0a020a1215050f070e060d051501080a050f0f06130e1006140609060c030c0102030c03061309 70
    0x180c1d0701600700c034880084152208850f6002804d001031400740541c10302e2400038812703c42400f66036205500c0540c001a60300f402000300c1e011726502891441002c0c1800c900f80700400e100c088490a07240c541116000702c000901280c69040c046403003190390584070f03050191510350050005409101c0801031105003260b0380809501d4a1080308003a11000a120015440c1c0051500084d5008804040001d281544e485081c41c0c8588101020054a100c01c00480115801110280780d4030403600001410f4034818514078403c918011700c182e090210400400c4105d5808851801c504001c24041040300c0d0380050421781d00c4060084e06108a113000003507640640006400101900098004940c0313503940e180d400c40ba07603010301d00b08110001001c081c1541d595a82d41c0660001071814202061034110500000b100b09000380c00d240c9043c51940074003610340d005a110f00e156010038000c440300b9400c01c0c0021070207851181e988a459040c100b04100f402c140586c422495203141c8180100080c030403002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 691683012 1250 691681762 691681799
    0x8070809162c01031a071202030f041a071d0109080708010f110a0c060513060f09140c030601150201090c080a050d030c021f0b030f1c03090b040f17030415050709 71
    0x11081d8546c1c8811005542c507402034840c1c0007910740080704100d400018a0005440b035401840c0801700b0800b060000d00c0c46101c182d03411030028000402c2203031031021100510078811010315005600c6a6507091150424605401c94946651180e03904848540c860180c04408219400e416150599821001d08855144a0010b09040c3c4660004402c41181c507100e01c03500d43c011109000a041100c103101c01481c80c5541198142101311804040c8200001d080750030b01d07030180040c4107507400c0c454240c402d44040b441030800c41d900c403048640050310501e03c0300700405101340146005605c51406da030610319510882c0d010140b5000401019543c0010016070840707801031071001041d06c0728180c00151068071240c5070548146000c1060800c40061a002420308210f40d46c481c00b8000b06040f030940780c0315200a0420a801ca0105001c2584035202020480c4900741c0701032020f0380c0300c5202c0c1c2c10350000c44090341c08070180501309000400c24000c1c10b50045245c40c20a20315424040d000103002000d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 691684262 1250 691683012 691683053
    0x170f010b15120a110708120709120f08070210210207030e0907020109140c0901090c0905010522060f03050f190209061c0b03071508070809162c0103 65
    0x40400c10340c07682079220980d604010103615951703100c41d003041d541681c418061110114045000a440c080c0301e040f04500385c03108040c082c3c03081c10207a200e45000903803924058410600c01c012580c0140d0b610301482900015540301c0c42030145000800d001307840c4071031465600960041180d4400a03911021030f207250a02200c0b00070154031001d00c1280100706136040100300300d400c00c1c5096038038400018600c5594408548102c0240e03215000300c801c2e520307000e400310040794110070203101940c021409090a440300403030030902107510000303604074104140d000d0000300d00d80282c1d004506030705014480c1e121402040031102d13403c2c80c205a016109030100e0800010340e01040810099407084100c8440e140107844c19441c001c41c0043d40e00042201c2050b00b4031130300c103c070000640d0314401c171800390821700345445840e070540e42c82000751441600240701c60703802e000f10044016001c5000080c6006030412003c0c400e4040310400c142e0030301310320802c102d07461210700c00b00400004440014000010042d036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 691685512 1250 691684262 691684297
    0x6071e030504051911040c0327170301030f02010311090d080c01021c05061804030c0b06060d0c020a12110c0613120f03081003030518030304170f010b15 67
    0x82c20004c2c20120001ea0341c2c44a990058041e4080c000d00102c1000c03c508200e400308a401c2980300c040c2c04a60b42422030306036008924242e013502c03011460041c5001c0380901c13092040060854054a0071798400d810880390716880880308805d6507414401c0302a09a40503d103203107131218400c0064500d41e45400c0050034080001110b081c5040c0c2901036504044640100450500d1004410702c0074003c00c4540b0f034080c805d414400a04584219021802281c00d52a0020950241e0725200e00203070004140741d42106040129010403400d600c9543d01507030903079011f4500360b255868005003031443c00706001c04200401c0b550104031070022920500b80242299080e580d040d00f140d011441070180d41c0040f038600b074889012414440403817807808001d031296640c202c04d0761ba854504520755225010150000e03005104c5040d00c0c480807203ca10a160006045a00b0950740d400c80041c0040640c44d0310144c0c1e045408620002c1e0400d0280558007481112444000ba40910444500340035003200c855008852 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 691686762 1250 691685512 691685521
    0x200909070e0a030c0509060108071b2613050603070210020c0106050405010806090f060c0301030f020a180207020f0d0503070803130c0f1403120414010516060b010206071e0305 77
    0x100901403010720003401101a030741d501d040c18407002085100d0740b03002d0b0412030002200c0f50320840c004c4d8400c604a84403049424408101d0001030a44924221148080c8441e524072400459006500c000c4840c480686e43d01c520070b600208099880d0700c0940030f024140300b0300c01e0142d00410101e545400034040181c490100c00302c140d003d480d40da4886a0405c0c507240001c12040800f04d43c02d44100721080460720980b0700820241d0b0b84050880b040d0a100c001400140009110401c841d840c20b80000d101564658480c2c100607034001740c00d80042d022541c00100f00045052404005541c060102c1c0e51a5581941d078440a4507840381e0a0010b024450000000d0a600440b0208065240c0c00840c0c114000c0d8a443c90100b0544150081d40015820300141c0000b40c900040c07003a558400e02d841050a252910b40918900500070100905101c814030904421f002d40d075075540e116602401c80070030a00c0c2044006810702070058140800c10030a200103002c0100c500c0407503030410f07210b80fa0020b02542d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 691688012 1250 691686762 691686767
    0x516170601180b0f0703180303170703020c060705130906180e030f0a0507020406140d03050307020f1c1b08030609041707050f06010501090e0103080a031107140120090907 75
    0x45810226000304003143c4c03101d2020b032040141002912136111030140b5500da000c0325030303200083d1000030000307541e08801b103441105181d420382e009595810302500304419403c900381020000c80e03406002035408034400005c80020305107070000381040c0c001003010500302000000ca1001d5408a28001901c4d40704e4240310100070130488501880c4036104503100c4c07a000200904c2c5501c0f030002a44035906002c00441c078091103070402c0c1c0580f140104210054091079600b6903c07500003c20080650150000203903840c8030911a80000b00c050154881600440d03100281090200e83ca800311829502d0400300c0000f41c0480803240c21810131070b00944595580c0c030f001b85c00311100b15080d01200d00003047d084104280000d41106064131442910116a2280c004481519461054006c186115001000407825880040c44081c6d15444d0100701a020110f2201039039012001c110340e60511201942c1c814002031107044111a103000c11313881d0065010500d004c1a000301680c8034031910080340401c400382d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 691689262 1250 691688012 691688057
    0x50403020306010602070509060609030c100302041a1308010506060a032a17010e240f180a0b0607690803180c0a090516170601 56
    0x40e8000d0403200700d503840f420000d4450607640300f458003860901c80030440600c0d0000544500c04800b4000301150855a420030168030011f14030030b0103151b420040800c00000c400454000c100d1504145030b1b43d00a030240b481d0501d0140c4d40481003e0745003c042c4100c6503034400c00c58907540041d00d00850000415104c442c031800503812101e0101d00111034100c276450300465948115480c000f2900030070b81c7d81c1d0307207030030a40d880c101e41112400024030190745440d841c1c41c40c0b880103d50060700300c100e610303078800100700380c01c0d4005151402d080c403080c108400501c4900804424040584050341449415030b00e00e0011318074286140070643d1001000345404a469031a4944440101c40c140d583c41c0300052680d0450001c840c04207076801940302007601c0c5143d0303002c0e5404269030000806c1d06e107607100d080d83c3d80328040001008040d8000c5100980c05962100050030181003055000105810801001916504803106800900c500e500700c800101c1c85401c1c600f64024000e007840340404058100841c03124 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 691690512 1250 691689262 691689269
    0xc061c0513030315150507060f021210150203030604020a111b040b010c0b0406090302030712120b0d0b041e02060d050105030c01080f01030807030311190207150219030504 75
    0x94904400c0000c8124030088003105035000e62010801c1403000c0c4020404440315000c0d107141045144440380855115000a00c00a80955400203032050100001c20070303030b8000280103511325209004d0194040404186900a1807044000c828180c03081d84040d4890000600f028481c2c0e5001c6540c0f1a6540121448200f0441030016519101c2c0d901e1001d0240c1d20344000307035a00592030324115040300d50044189034501030300441c0555446da5260358010203803034100b1044045010078403150740026800301255600c480182c81c0c103105840c1c90280c8038110745601ca0458810002015402c0c00b2891900195401c507070040c4a0403030300004140c18400d1100c0c12500250060800510040c01d14000c5d48180e040e500202d041e514500803001c011942407000350744400d07a0f182a100100001100c000040810718800d0502182d0741700c141103071001c55000f10b28401d8049403040154a0940c1d414800d4034040d0080401c66035910800d00300c0295555440f40003000700c51b06056920051500540c01d0360002d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 691691762 1250 691690512 691690567
    0x6090608042d120212041a190801050f0604150e040608030a0201050906060f13180602030901050901060902130509040c050301021c060609121113020a0c14030304050c06 74
    0x2c102d031040d4a0001c010110805503180510307014034085151001c01d003060030040c00240c040c1020708040b042c0c02d0007400001c2445011408008085103000c103078010301848040d546a071440c80d0314000600c11302541d00314500d44904402c10040c080e1080707000c00b5a00c110b40510f07040d20800842310220b00106825007001400c4e100121b4100d2030f056054100c80c1c440d070102c000740c4203192904000d0015403c0310f4080198401c811444414200741164821040311070107807070700401c400503a21028126070054070038807803c1e5121010056543c00c2402950010401540c04610741040c492549039409418002e0324032854425021909000d800b02c0c0100152000500856461201402040c40c001194581905a500f00040081d02d1805021010111001500b050310b00711840d56644007841c034442c89055110003103042d1204014810300c05850116696181c0c98101d982d04c3c05c2484c1c1e94034205856031160342c4100100400260702083c41070394020290307502500c0b00340400500481108280c1252030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 691693012 1250 691691762 691691813
    0x14010b0a080d11010c0203040e0a0b0a14040507020a080306060a0c0510050417070203033708060a140a05040c1b06050613090b1b1c020918010609060804 67
    0x2000800410070001010b50740e1030700985101c403510581c0c2656600c030080300140e0414002003089029450500d5400140404000340f14002000003d8820a898000d850442411540d40f400c9050910506800c031a1b140014460704e141d541e2050780c13910000b001503002d62808240c0c1c0720200d00510105804a5114081e41d4030522001c40000c01014101c80680d41040c50004285880d0140c0c0100c6440540140c0518039044070b0003c003045001034020312254450203049210360410b0b4103450a2450000c2d507640d101d5a0505d5810006d46000c0d0b504003410b07038251341c0707001002991441d41e081c0845505950108049450110903640c11141d900f4110000d8403038608081001090ba1015204460803665200740340031038448030007214103c0710021b0950f409400484c04c45480e42001e981201428040b4130328040d00c0310b10094010020702000c49001d6008212400309142401c881c10303a07000b07014114001585484001410f000041c803c079020700c403600780444c0074800303c440e007041003101e60048d010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 691694262 1250 691693012 691693019
    0x9080d0e071508150d024b0409080f19170402090411031009050102090a0b0901020a1712010b0a02100221090715180f0b0714010b0a 58
    0x1034504019411003500811001050000c800100d6104140701e82d550004581c0c1d40f9110421034980c0c0c07568980d84800380164880041e130314055040c45c0d19120b1203201c1502c20b426407800c415010b29100b40c2c013400c02d0a040b42401c5c00c2000460038080c0404403000b081c01d1400d030602250601c0745030003041c92500c0c00640c880c1469294000045401c03400c5e5642600079156440e83c00080f00140ca0083d807045805011601040c400c0d46201c03000c450080135585500e211408020807502c110074102c845940104030007950b441c058104000074015a00b086160403d0400000e49454124000404040201005c4032884031031201b9280d0118030480300c0592540c5540c400c3c0341c65040300c142c407c01442030400c222481c54407070007580c10038102e076915400401c03060821004040030041161005200f00540003c1c401e000001e400580310b201c4e1260a034001010b10105610303180b603003181d00c1103404d00604022200042080320008c90b003051141d8801c2e401002c3d500e01521323042d0107940d4401d0300900c011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 691695512 1250 691694262 691694287
    0x1050c07020411130b0c0c0a260c0405090f15013206070804050306070908070501050a110a0b06120a080d1d150105130509071e030609210806090117010908 68
    0x10103c0c59407610841d104404000c040003203c1c1c0c0701e8003d4274914008032440b8800c0300c860088680c0c0ba00e01c0b00d82502c10b00050003001c5402c403401101c000815901c0302d9110340d541e5109100c45070311182d2840001e80c1c6581000030040c0d8a440300c1c2c02c498140417404031001c0c00726026078075030a548000103100300d075a085141002d120b560098020244640509808142200c2c02110b03a074044480501c082d220003407500e4010358294200ca5040c6090200c8105001004d020a004114a00340b01d2a0580340608080040c440b8203003481251030920740c00400e403140440c3c0a00103440062051300804198107401d9101242c4e50800300c8840c41c220f21403001112070001010321814103881060329180165402940e100c0c09a134400c0c1c840012a80004074140102c680e0301080c1d00103d0007020111184031b60380c3c0da907101100c03148402500c00b00c0c01121140501c00030b044c1c00c119420040d00e07003414541071007400182001c40601c00d01e03500c241c08115016030000c0079002109625000307200e00340c80f83ca4880aa = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 691696762 1250 691695512 691695517
    0x918031204030f03150e0a06180207030f14160f02090412020d0203160209130b180c0a0302030d0e040f020a020705030c100f030504021306030614060301050c07020411130b 75
    0x840100b00c4a40c0c1c8103d00030300c00e2150405441c01c0058400d0050300c0c4c413042c10403200f4050106100d13642c554801248402d00c030020000c45a005010051b9600c402d42001012141c00c00e2102041280c09404000e1a00e80a402d41e06e41044031074500c10340118030700c0c2c82d0b02c0e003613810140203410540ca0317010881880400c070f2018190f009660250391484800c807808a84038440d0020b004001d000851840c0d000d81031120f003541d8010240c0da818081c03c40303a600d8101d6505070440713104103050669112141505820700c40c940c2155015280045114115400251125444843c00d0100040e030000c02c55542e03200d4108900c0d019900800b10351300e0081c600001d40f00d000d10301a090103440380c0340079007041d420312240011000c2c07410741c0e4844544d84204130032009407602410603079020850210030a108040c0c1d10607a4021841003000160042c413a40740200c00c0c2100400003446640341404100b42007001a080b620150f0341114005458662080344000500640030525283c1442090100b1014840c100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 691698012 1250 691696762 691696771
    0x10030813030b0a151e0303050c0a051e07051e09060f12010b01090e16080a23040308060306010b0d02133503030c0a0e01030e2a030307020d0209180312 66
    0x1011250b00c0c1c8901c1700611070f04002c900c40b0b0484280100400100707100c0c1014008000000064402d0041c030b9465551034440041c043e80c00c01080d4141c1000e00344020420000100020303110704202e80840d04110314450000c0002e076000c0d80508001a20540e210314a074000d80100078a10742e52000544422402400ca42803130302c1c04039969440104800000602c00c2d88621075156a0b030b010300034402d904445402014056070540380d00c429071010509e900d4a600103d0100e0b01d15480903d00e06401d00401c1d0740c0000c2c0c0f055002c0d4201c00300520000901c6804c0355210707465501c000d81e40b205504a9040081030540c07084c1c3c41c0c500f090508131854421110540300100000d940c1c0621448031942e0b09849100a8440030002d2008111016100b0700494244201c280141000502c0c806602c0b2401e04020f0003146619170f040c80301c080c0d0f04013902c800d20035440591040e0015130400c80b03e9408101544c0360703107101a200300c00340300020341125a2002e920440d000948180d81c0c5401104c0101c6141120658 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 691699262 1250 691698012 691698041
    0x60b09120606131806020409151502060403050310170a0b061215100b0c210702010903110a081c08060108132a03240510030813030b0a 59
    0x5080398464280058141c1c0035a00c010310310560f600603601024000c090f0041804004101000c000c008544540b000e440100103044010823600044210301d03c1902a80e000003809134811980441c07000e6000403c940c0c010760508150f0340c4e03900c54081740f1640e02707403a034400d08a030014a001050340c00c002154060489115645002c1e4603110001003000f40003464103801e11a5105072420703203148034070000c0e05410520000c805206140c444d0340f5031805501500101c00b075580503255501422014080e001d060801c070800c90380c105009940001e00d201c546101c05060071200d075400107001c2d5680400840144402d508449e008501e04445060394989a10340c800801c00620018410354024241644281c40801804d02060150f0703990545901b0f20818000040400380444d50141220240c00d1002c0e50084040044203d480840145003071840c02503491514109020b101000f400c683c00d18080c2c83d800500952108582030301001000340c6548044c01490004051080051056004541001004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 691700512 1250 691699262 691699279
    0x30b011a030703230708060a09020310090b0a150c0b0f010605030c070609020a12150e0303010501140c060103080403120801080309010c1b171605181504060b09 70
    0x8480c0c80c10000c00310168040c03038080800008010303d20941c00003805400032a1000100010001905100c920455078880071400481c144060b07407500b090004002d10464005518620701500b0b40004c40c401441241a01030b1a03000c04400b55459503c014041c24000401850320526110024542001c2e8401174984030382d81008540c86283e9102200d0503601c3d00e441e580d1454451030240e220315404150155241582d03040181d005a4440002c84001d004d200010440018a410501054940800102c20507854840c01c80c1c07040c0380110540c1c0c1150300900340940c0e02c0c0307004088504070380710340c1d03030354542c54012107001008010040020304140c9000f04400781144100c10b0003518541001e000381c0e05564000d00080100390300ca442901c2e0744612030448210014102030808610508030b0700b01c400782030a0821100c0c41c0000402105042043c1c030001e020a20742f420b0045040c03100924a00c0c1c041140e071500083c20b20b450000d40310f4680078083c10400403d5915000030040790031031b080c1c180c41000340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 691701762 1250 691700512 691700519
    0x50d1b062a05042709061b031d0607051b1c170403020a060b12030304080c01141620240109020f090f0d15021e070827040f06030b01 58
    0x90003c0c0c8003034541010b00c10741541004049407400e0300d1550000e28031251641105000030300d9502401c02c0303400326020410010b8064034005016074070440040004560115070000d51180d00285080c1c100c4a1030401c01e80e1412034104119100c7d808548442c114851001c166100c0140c007030b054070a07a032503030307035882440c0319404032004581c94151405401607010000b180c000ca10b1076480002c00c12001487c0240d24481c41d200e503030440e001200c0c01d507000040801c0c1d500d150340c030230b00803034200190b0740100b58103615109007034004841d1000c0e154000c2051a4030520394000110f105070304107482c140c5c01c48408044082c060744810b2400c0d150081c40b02c000c0c40000a205019000785c2c0e1181d80165101400c124a0b03d0500c00345001d4504035503031160f400300e0703800d002c41d007000c01130b5001a10100c6e015076206210714462030003402c01801040455810400540840c94660a6464a10210038070180407403407451070807800341c903041c00c0b241d0280c03400390400040300d180d078080c0c800c40c0d2050743c000e4a242c2e039 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 691703012 1250 691701762 691701767
    0x1413110108040b07080601021606020a260a08070203040302180a151203180f17190305030a050a0621060608011a010807090e0406140a09050d1b062a 65
    0x4042d18001c1542481c8400f00d14140d0190003007561003c03040c070461341000e1480d640c88040c3d42041d4071000140c0c011031110014440000308406100310f90842a01c4409409020440d15204804110b0100405040031440a070300c207208590041d500104030b10642c04000d2944840d83c0c07005d5643c901c1c058070300842d080c002000003188004403049015034515001ea41d44054038100b0241540c500e5012041c040444c21101003c1c10901408001c0302644110001025462034002c1110220f00581001800b081c0000d40c07040c2101e0b4007001c04640401c50361115100100500607503003100141030340c000900464400103100851a99000d81c0081c0001030351844203608960503504651221180e8580b2540d03039501940c2c1d0744d40c002c59149081c18103265610100c03101c450b400e480446150713850f211342141008800c15503d4118045607003c003c0d2030402c0d034607181c1d070314000041101440003703104220000340002181d0003498000030180000c4019a820340350700030118480f41c140445202040502c1071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 691704262 1250 691703012 691703027
    0xf05070b032d01060c0312020a0201050717010302061b0c0301050a1a010309051005250f0e0612040b1018090606080313030320030a030b01020d0c17090414131101 71
    0x88010b07840c0c03030507401d0480403034080d2000c00090f002d01c444084902138540840c402000d12030301d15400003481d03082080d4000c2400c1112004180f5003c0c103080180056500e84c41161800c21b030421240400401641103d03080004402c3c07641c0d0705503e0b0030304007c042c203019080301252007005548162008014401507040741c222102c05031496008100c0c004c5090410fa000e940c00c8540c5250003603e10048a00d00c04a510350504610f00107501400f1644400d5041440040b05e50002c0b9001c03424010b51500741081d921000784090000b00c144000303d50040380124140001c0d1096040c012035990304150444003500c1940740c00c883c40707440c0c00000156502c0c0402540c43e482045042c08075005e00e152800c5403c4070b441001d079000780c194070030108403d4000300014200808076031404121001000d0002e418881428800320034010b6400312840000c0125144180128558502c4c9440d03d41c00c7d00401c5c020640d0480303680c2154180c80c00c0c0500c90091480342040c00d03110721030b04003481d0028001140c103d07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 691705512 1250 691704262 691704331
    0x1815180a05070e0406020c06010609050a0605040b2a0102040b0c0f0a0201080c0903120706140903030714180604081e010902130c1403010b042408130f05070b03 70
    0x10740200c2c0060104a440086607900540124005070034403101c80102410a803082c0c0c0302501003800d5110412090401000030b1009008604141d4182898454225041d100d103a03d4000200c007804c114050134200c0d91000d60400302e82038021920b80741c0301c8042555542c440b510500d550300c0783d284101e00c403000001d000c098450b03044e503820300d00c1d0712000165016900462400ca0345030180340e02d810000c0c61000c000c1d02a45004840100e0f041c090640c60510141d0064201012a001001048645a000040403d01c00242442d1a5a4074060b003107400c400310f1440852a800b20000400242070b61001aa082c1d5143c4281c142c550b1408100d2041401c9460342c040003074114083e41d001450200786540030300003500450401002c1e241020750000e405910981104007000c0c40400c007807202c60304101184400d020740c5504441040c0c207081c1701a00d9950001c2425425441150100782005500090442d809601c0021100e0702c2e03440d421104201d800449a14150f500071003a1001100c0d141d06088004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 691706762 1250 691705512 691705523
    0x1201020309030406080901180b0a050f15010c170c0708121204140a02030d23040b0708090d0f031e08040b0118020f070516080f12031815180a 62
    0x1d1604d0b000c07041e100364000501c1c41117655650102070108074400380d203411005100e20f00c850401d240c12040c00e821a0806448464550050341c10810f4507144c00f2200c400c1c180c403d080080000c2050300d010314400503005030b45400c2ca103000c01c54078080c000000b242c0c81610300e01c4c4252482c85c01c5141d0004c0041c0200c40c140c061f2024180049004039100c20358413000c0c0c0c101c02c0161070f0041d00903004203203801c0783c1c40e0600f4001907c00b03100c1015000c00342c03524001d44d0710b000851442d003407810131030340918010900f018100d00e04c0000c01d21002d560700c01c00c1118290b13004d207016003012000c1c1030240100300c00c0100766011882c03900b880c02000744284003030f911865004103040307126402d01074200d0441c02c01020481c03005608002101e000607160000d0070656102e40010070380c5104001403488075101c15032104900340c1c0308021252000401280183e4440c0c0b01840003503c070b03908e464041d0300e244051000a03801c0d0050403800c0310401101020544500f10329402c4008500d502880a41c2d05c0343c803e60082c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 691708012 1250 691706762 691706767
    0x5120304030c150c0f020d081305091303360602010218120a0b0a0b1c05010c05091e030304090f0b0405090d0f0302160c0f0e070302070c050d0510020414120102030903 73
    0x10f00c0e0600c0d54018140050050107103043e184c2da0303801c0c8641c40a000349c041c10700c108104000740d01e00100003a40c04251442200c00b16030391070350040d001007540e1454500c40700c03030250301e21001c190403094405c810018043d5034082d9507032500080d000303510034038031400c003e0071609805006041145070044040350b000028606e082d816254064030318406131802c8801612030105010070765035410301016015200c004d52030850418680ba5003100d02007148142407240c10700419000b0358500b1038414040401400c1c00318589c0072100000e00754800c640041c0c801501d440320001084035107030b20100e40c0403010780301000540c90f1000800e40e10a0040d2600d00001c27404901c0c0800340c0c0c800e07009000c94524007004042c950321a0396800d011074180390080c20800101031030801c202242c45103500d4200c82e42e4201185080c0c03694551244200d190701030240540c00021446081280801c40310300c111019040441d21603440d0300000551040003140f0522078802030042d031503003010610840b070048081c07100440c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 691709262 1250 691708012 691708037
    0x6030a05090f0d0905010207090504020603180304050306040f060c4509050906070305010e04020d031b050f12131505070b01090b0109080c10120605120304030c15 71
    0x60241500411031002409001e924001c008010042810758040e0f81e02c074401da44d8100f100091034881e842d40210ba41505103c140800740c0c0300c46007100c2e0070800302e26800061842d0360070707a0791451046501803600751240303c08210900401c00c00440480e84682000d0040c40241c80c401c842d02c001881a81e10040b0700c0d81e03c250080707580c44083c5141c54500c40d209290b00c01c503c22144030700c95800d500181e4040e403a01c0411511f0b10081c400640c1c42001e070b08042002c0d5041400c0310114020040000f40200d03140e50341c50b0241170041059101c00500f05120f0301c2c1d500e50501d800e0307807207a0920004245074801c80b481c451010702080251900285003400700740c507007450010038101d08120a2102018400104007203c041245256143e02034810003502242c01c140708800105a90a10b9102c000c90360003640c022075044e0b031058402c2c0303140c24252902000c0e4140b00e0003a02c00500066003c40e612035070402c80f2804402000c00580101c1c1d0140404240b281d1741c45120001c4c0a00c1c0c00c0440000030013040c00d65 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 691710512 1250 691709262 691709281
    0x14091b010509010e0910090c02071202271003030915080604051e04050f0c0f060d0c031506020606040e0a0507030803190f023f0901090609150507030b0603 68
    0xb00781c41041454441c0219500d0404100300c803c064420303c04560034040e09000c005054020140c000b0b4803840100f1070140b030030b100c1c400c2b18550070310b00034407400c051405e013200000362040c1500440008500400e440c145034180d01c0780c0038142c0c8401c501040c50000300090034455085614280403268442410a546030070421000b0316004010308001400c81650208826a000159100d584218003c1400203140c030794407032429007903c2c0c07080c2c402d0001560301c0040c0d03250101520203210074100302240d0009143c03030a40282c10b0706030b4002e640d00030019000031010390000c0c155000702c0c002e541c200031100384c1c20155515810016006401035211b00020000a00d9050055a010300c00b03a80038940c1c90b05642a05061302c0701c41d0060360350740344c001c01d48254000f04c084681111030104a40b42404c1c3e10b0007000c040308100c50b410104541909030000503040802034004100f02540f104007085810000d19050210003803d800c00b540041c40c10000031181c070b000b8800d888582400802160030350760780701c640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 691711762 1250 691710512 691710517
    0x4090c02072c0c07060908030103060513120807020c130212060a03080a11100204090c020f0706020d14160b0712020c1f0b03121b07120318030f030314091b0105 70
    0x101074100d0421513a0046140c03842400c0c011841550610703542d514600380300c801c1c0e50300034003206980c440c075218020029071180f98014070303000d403814890050703501c0c4581603003044c420141482d04841010112188103042d41e004028901d03e900d502d00154642100f40200d081301d50000800c13286080041c00012400f91000503210741c2008111014801381601203801d0f81c1055000b00c100c140c0b5090030b00352180d01480300310a080d01c2d040041c8110b51408030000e649070b020400344001e001c044080004800c01c0082243c802e1800d4912580702c0440520b4066034240080310003c00140f01500e6031903c2c940f40707008855a0104000c003c24100c00f0a525240b0300005030340b05110302a40c1d40c05c1c0541c05072000d010081c07424030104886500c900690303160861190407001e485400c1d4100d030304188146075020342ca40581703c0c1c0500e0400004075503004034040403051504040c0140400c030f0300920405505030024950303515201005001c5446030351303081d552185c5c06413500310061200d021141c09035200384c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 691713012 1250 691711762 691711771
    0x3061a0418090c0f0b031005010f08010509070c081206101107030201140c010509010902040b181506040e010e0702010f0b0d0b281a15041e090204090c02072c 69
    0x1005280b0555440c00f0044c00d42e0264400340809030040f040000310f0b42d08545410051200303080c4110b1440030140c00410807001401180d00c505d07614004540b640e4480c441c80b251855000b18002e50320040318200300008841103690603c961807003c00311040c2446201c0003d0f10300c08010042c08a03d05542c01900e642c9050406101030203070910844080117401d02420307002b0f100c190000030ba0401c560040c0808d41d64080301050080300aa01000c00d015240b50005510400e0340038a50383e01c030622000950b680c071440e440706403180d00e5100007051a00388035401500481068000300004079008044605684203415907545c414180440703080400c450241e89513110321620080080460504541004808507040b030f00d092a99500c40d0301068100c015015152007400c1380c915025000c070901000480c4107a01507002c11034080c0081400d06584c145a10300903101000d800d6440b01d03200d02c800720040c044d41c85170300d005106a0f40c001032007000050385041a00d9406110410710303400c00c0b6130304200c0d100180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 691714262 1250 691713012 691713023
    0xf0d0e0312160314180409020d08070c08100932010c0e010306051c1202010b03070314060f15010509190308070c06090602060711150703061a041809 65
    0x1a0905148100e4401441e20b038800201c6048981c00da0300b0000c00782c0b40c0160701d00c120024200010441c2052a205200f0f040c00b0440340840e0610301440410900c210f0808014000c2c040030a0740d208002d5085420310560306000121b424034000b40d02c4800a80700c54200c0a00000d8110200802c154004040480140e85140c0700c030b02d074807890000003421540040c0420707000802001c0901e4456906008610080c1030071903c00100d030400c0e0141c022601560540140000c0d180300c0e000c00420b00030340001c0e40c0258000e0540b05110b95a08150780300600c1d01114590a0150702c0028a803001740c410a40d0040c41780ba0607940720f1446080056801d54007045c0740c994043c0e030a01802c01f0021801440001441c42060303c0b9488003110314085080109a810850622042c00418441958000f50340c03540400c0707914112210011401c04981002604800001008500d1040050190701a0040d0701190b900303014104d40b40e122282502d1860096014420070010050981c00d00c1c0c0c51282c00c01c101c07260049 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 691715512 1250 691714262 691714273
    0x901050609011208090d0c0f080a0506070807110d1e020d0f0e01051b0703021203040b0f070206070b070305040b1b040330030e0c04090b280903110f0f0d0e03 69
    0x1400160f091b501c00d0305c007101c400c079403100140315160910700c5c405c0c010109507008085213011981c030140c441800428207400c2000c1c0b09d0000c0c80c1c46200300190001101e084080e10402243d000008020301c04090741e0680506101d086214020310008900060700250355030b61004c2c1e100504121140300309004400d040000502844540c140340100d2420b0001c101c10040074860f02d14814800004171042c1d050029800500040000c521a1b104442c4030099440309e042d61950b203880050800d005c2e00300e025058560301c40408c00540c0d01580494001c80c002c500084169442d404001d400b0001100760800100d814441000001ea103500328070600e0001000405401a102100342844c00b01d910764540003948840c08000c0c5207000b071050032070891041c1e90500c012484c40d10355040420300a000708154900c2489542203881641c44408004410310030140103200250038010103490010020151340e00a00600c0c05442070009202c0324004036000242c0b01c6100440015113209150700002c43c0c260049 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 691716762 1250 691715512 691715527
    0x1a0a1d030706080612031c0203060301061805040204050105030106080d0302130e07020616020c06030412030e030310030219030f08070c050d03051b0601050a150c0206030405150901050609011208 85
    0x140070500150101c0e580b01015441c040c410052046000610507460782c000708444090541c4c0c00240c441c46103110200543d6070f84901011038010880359020312a00c6801d14460b511103c2140c0105014034021102070280b070742c8807000c160032940345204880e00c0da80500c02520f80240030360090071644840e1154000712030780d00c1541940750501105d4640050b00040c0800840782c403010040300d030009452000380b41c00703104500840d0b81c41c032010300082c0c40d03c6801c0c4e0310baa4003070384a070304050145041315082d20389900f0314025044110f00d07079000803446140e03a14602001c80e10b41c2c00341d040c1104d0300000c00d20948542130700c942c80719521405003a104007412030400304c2c0f6608c3d401c6038104030b280b01c0da54a6075039020608079040003240c4a0712044560b04041c00400c916a280c1f11580c084e501c50010441030003101d036005440121034034038000d40000010040009015000c61420400d5220000d0355905590b10a03446088030411038803158084611401404124220511041e070381e0b100d800c00340e240880c03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 691718012 1250 691716762 691716769
    0xe0f2209060c120203011203050723060a06050105090303090409020a120809010f0c110108070509041d1618090206160c17070e160e10030c091a0a1d 65
    0xa40300e96842d0041e4550035544980c202c80e00003a240011815541000801640c5103484d00380542000404203102d01407058514803115213680c0340c1281c0300300300404c080d0036803124800c403000c2c01d0842c5000070001e00e550241c022074001c108000c3c0a186000300c3c280401c0000c0c40c1d4035a05a0300709410300c001003645820840d00803c0d190041c0403a1741c4564600d40014065031007504000e0412010003d158009010718048035481d60090800c5402551000012222070240070b0499900504021080001c1a1440c2214500001180c107480c0c401558100201d03807100719206503201440c1240080c04107840c07541c80444202e200525203440c24600004a0411a0b1108403e4540e5006502c0400c00e100d00003611203e00301108002e81140c601c1c10700145110030008000c1000406c1c14003246110b541314482a442c005130090041e4010701d03000b8001401004440401008201c0381e540107e00e00411035405421100189801351511094281c2203072894080c5140300c0700c91200200390740059a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 691719262 1250 691718012 691718021
    0x81b0327100207020a090908070b060402090d080d0c03020301060906050a090504020a0503101502250509240103051b070c030816061d07031b12030302030106030c0e0f22 74
    0x780300349030140e100d107864010024841500e40c82138400b249004580c000141000c410784000a800c40c03407088481d034910002c50040e2181d850456800b07680c0c0c2900800b00540714001c0c02103070010340c0b0b04000514094805500302d110038000c00340891141941002003501c1040200f4030407803240b8015161039075550100d41a60400d11210000c24030200070002c8100c8107034140d000900c101500305180060141019448094190718904560b0070195007400340402c22220380c000b810082d1642d00145070108440d8042c041210382c0360007180314103d800e04d6035032080c001c180c00703031050707504280380b03c5c065002e00441c40d84a1a41100c61000313500000003c220841d000e803030241c01100d0b200380506694a4500101c5d4100ca1080c25800182c05d014802d90b00700103035010a40c0e500c1100180d4003038030f20107001c0d41d071021a0300070710a03183c228080904060303246e00034504031546614188410384400400303442490050950340d400c02c0a0b88010641850105051120a15004108948280d42c1003121007a01c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 691720512 1250 691719262 691719283
    0xc032206111c0b0103090c061d0904120f020a08030f1e071107050103140f06031009080a1d13050a1d06040209060105030c0a0c06020c1c081b0327 64
    0x20704820841080694940034290010f0800d2808000d101b406030b84801076510140161003c2100f41029221903d44081215400318802000c43c0b003946061325194600190712200c040001e210129038904890002550b512007580c07040703069045541c0d88607980801e181c010705840d02ca248403000c084a820401014902540841ea47c21001041c4484090b290000c0d80d808141054039140c4100800c2204080ca40d40080e1044d50300d110a4681b0b10000b4580440f55003440202860500c40104001e000300c010464440e05480b90070401e10000c0c001402800c0c003010158200c0c080d00404150950180d00c0158061104280000d1058103101ea146090440080e0000c1c641d100744148015803514128003540081c1c00d01e0918698030b80f00c404001e86000e0800700c0d60500c0b01c9061913104100b0240c069a01402003a0200d600140e00000517894040718100b105010900460208460351150305150a6000a40da9421700c3d54591811075080c00c5420205080005400300203c071030100b0900c44111072 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 691721762 1250 691720512 691720537
    0x6041719020a0506010803040f15030605030d05210105090a0903091d15091303080405070e040b101401410c010506030a0b04030539060c03220611 64
    0x301002c07441c019203003810680007401c0c607a00a00c020405006090900410b5410072090700c1e0601000700d034150054095038000d0b0307503d13008003c0440060350b88040949107c0054034581945140d410203140c062000a0041540048111002030500c503016000040d00500c81c0c5020040107545132003031a2103c01c008035000400900c4014000014803540c480742c54941c3c1243e403081141021070448858001c0750134001d040c4401b5000160906c2000d20050f0010300d8604039414940c80d05c0e2424040083c01280d040009855542d40030034806810400389030220703010385403c0c03080c130031490b20032001500c00f000c0c44030304040d00001e2185411918101d503401e6103140d482c094a42c3da031f035070101d421f42d8030043c0140c0c0a40e005603861004210000040358129405040c582d0f921045810a5420b206081180d20740440301c604100d0784d107030300c001540c46e6880000e005030f030b030961078082c00040b05100a40d102806142209414803013003800001c1c114400707118a2000503400750a00146c1100e400480b002e000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 691723012 1250 691721762 691721773
    0x51b0a0c062d020705090709080d05070605090a02151e0c0f1c090605030c0723150f0403110f010f0c09090c021b030109050105101e03050604171902 65
    0x1442592003800e50782c0c6000090940442d103902c480025134559207480b42d14842c154500c04900c90901400303000b40601710b02800d82e205d0303002c1c1d40405852540b01202c21130b5101d25050016507130311404500382112590051800c0c11684e4180e901104d1508420b0b540300c1e03803101c443c0c880d603030300000c2100030580e00b6944800741408031080c0044a00b0718080d440b552030300711460b01544c0a0641e10030009825541c1c01c0c04d060380c490720b0b51202c8444a02402c0c5000300b841490ae22020350128803940e400340c90301c21020444003000081cac46d10b03504454041e1128071003c0902801300380000c0c0642c01810031082e01c03008541d18605840c80350b0b03007941c07414108100b415940704110941c50307074004540409440141010303c208200008020f66a11003006010f1039425901c0104020b44d40030342020401c40d8005002b84030504083c04070404800240c4250340881848400b01142d1f1036078203400d601203980240140c000c690320740d2111040e001804200c004242400c000a65400e01da01c0c90f1501e0f0300120354000c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 691724262 1250 691723012 691723037
    0x60d02120126030f03190b060a18050406031a060d0c09060e070302070203031e090607051b01020c0a090c05120f041506080705010c020310022709040201051b0a0c06 72
    0x802c201c1c001c45031007103a50020804009103107292001c80b078002122038144140031030f1009950000380070105960f0b600000c00680b000f810b81c1d020104400c0d8039600c074214811141c0c0d9070108401c5580c02c0c130004041041c400c1620411106486501b03500c200003400e69081c801c0b00750303601c00311442eaa410482030079607510f0050041d11a0300d1341c00d640c80311284c101140740000d5a00003d40e42c0c000c0c01c81041062a48108181c0014102d106031194035030080c1c0469140c01040c50300035250000c2c405d110f10180982e00c02140203620006140e00c44200261180140b41d00740b000000c060301c26040802c0034800104000e00380703540e43e151600c1c820707511500e401e907075820b2902c0c1c00d4541ea040340210116050030b01c00107120700c040c04120040ac5440900704128094624404a13080c07240d09501e4500161010036080c00342d80000c41c91803401d519004816041a01074410001043c00c2587d01a00149050000c1251841080034002101c501c41c000c49880725400daa48080545a54000c100041c88035000003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 691725512 1250 691724262 691724309
    0x5030c010c120f05012d05130f14010b1e190f08100503030409020901020c090109050f25030b0103020d06060f0315051503180a050303060a061706060d021201 69
    0x72590304000a000f03004552414204c5c0340c81c05611441100b850b0000b8643c6c40c02d02c80201d08020003003001500040c0d260400d070004400030001d103400030359920704008c19804030030346102800303040e11300d207000050500400440c1141e003d601c58000141028041044c01d545440c8902c001c914030b44a9a90059400036a1364000d2035944064210240f4815101040c01607503000300a4a003030b5210700c81300684400018004030319010030140043d400406580001c40d103010f1a170401840350a03190440b0006485403842d40005c03a0080070700c40070704201e40b0408411b80d440b0390040a40c40c5414900075051071807081c0c41c48220f07034007580420080f400710340300c05030301603018010502c8910b0303400c0001900c07501c1d000c003240b0300310079003000c0a1041500000103170030b0100c004070780e0403881c0785e15080300c1d03485c085e910f4865902c0d4025610702c1d115079505000020034501c16030b03075503100700860f400402c040e88441041c0304032500044200000d20740c00740304200b040115112018000c0c18008150242c2c1910362414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 691726618 1106 691725512 691725521
    0xd0f020703060914010e15010302240c060a060b160b04031b0303050103021305071b1511180103060b250b01032a06020a0f05030c010c12 60
    0x110740501c01080c243c03246840b0240000c104c2680482d0106a1f598100500d02d201c11720318400500050410b01c01707200d271f862507110442d03502c0080ba1800d024107400110705070b1030a40c421070070030003120b1060003000003c044e1060018900b4001d40608000d100070300801811421001001c1020184981c142d41220b11010f07205907456091072030020301501c000c0c0300a900c950858488007401d210180305950281a0341e84882d85d50a108240392454a01c48407400c0e1000c109042c0b5194652000740945402d00d1980200305585803a02c04d031a0b07814040c2c1e08c042d40d0415240500510910706100b089075a094000325220846d002e0301140b548000640d04d0004142114001c000002c02c190700c0b070414003c0040c0160010350000c02d02007900350207001c0c4200780060784260302400110700030f443c1c0c08a449024409036803800710105a0a0f09448040c0e400b900015803100800710386401c217204 = true := by decide +kernel

theorem cover : BRFrame.Cov 691546762 691726618 := by
  have h0 := BRFrame.cov_init 691546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 691546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 691546762 ≤ n) (h2 : n < 691726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
