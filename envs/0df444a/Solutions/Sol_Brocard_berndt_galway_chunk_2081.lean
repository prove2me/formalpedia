-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2081
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:36:53.363506+00:00
-- url     : https://prove2.me/submissions/124575fd-8e3b-4d2a-bdac-459050940c16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 374100719 ≤ n < 374280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 374101969 1250 374100719 374100743
    0xf0c06020d1d0d0519080307120c0c0204020d0e010608030c1c021f0e1902040f0b010903061a0303120402040609062409090e0a0203010e03090607110a03140307 70
    0x6036114019881c1440b00314140d00941000da4400c2000803243c1c0385007500d00d07001d2071286010f004116161150b44503c107544440d200c0ca00404050109410f1415900d070301824001c1100885038040028040c070740d412680182c460440d2124000145886284030b4625864114041410720001024200c0c0485460885894541c0340c0031820003281c5005080025902180304c0e1118107031284480b001d80100d2540001e0f0b48a41050300740c0c0740198071807010202c141035500c84015401c180c01883c00c04500d21001348401c002c0840001c040c600d251001402480d0350b51f020100384000080b0300d41308100300404407900c4549c40e1041824201c0159403c03440f8510300b190000762105540240d0741100c0404905007000841845208200103545080d40d00b0828800d102150030600e40c400e0160a05000c80201028041c2c1c0c030501d802c680254440c01780640c000e00c00b040c3c155503030108440030180d211900340ca0002c291004500c20140c1600002c1c01840503401001450800101814055000c0c00001c001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 374103219 1250 374101969 374101993
    0x40b0415110c06010816051012090f1112121e09220f05070f0f03271407240c0f210c021320160c0602030a12050601020a0f0c0602 57
    0x24140c042c401c8a40004603042c08140683c0524400c4c0c0001800500108400501d5078bc1c0400048000d0412102131090b202c03100d03007a041035140000900c618400a00007010f0b1082d008500d402072507004903020351341c0c001e248491042041610605e03c40a091021503401a00a5450960002c0602c100c942d1510f14030030400c3c601805180d0084800c5d86901d5441c0300385107403c80d50101030f07511240506031280720341ca07503003205030701d42c0c0c101500600030022140410740703860f4000c00d00031004d50300380d94011501480400d00c048100d010011081c5020003c0705525041580c1c40111700201900b16002221104240302c16100c5040c0014290000d40c5003500310b29500ba5006068048003a4116188500d088100c80407584520701450481d103119406003102100d031040ea900c22802208080c4810549100300914001c0f041c001d07140a001450800261160041a110410540c011006e4592001c1580c2c0d900920010342619009102e146282c6001e003010b85010801d03105010040c428284003030b00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 374104469 1250 374103219 374103253
    0x3040e0906091014010b071a0702010f0f0204030c0519030b010605030403090909110105090409050307080c19080d0c030b0d06060e07030903050417010e030307110c0603040b0415110c060108 83
    0x400060f00081130180b590818000d420280c00c440c81c00c542030b4008461005490039803842682c45901c9030760010502810124400f030030b482c0310b071414100150042c0000c1c00050b649084840555509864103a49101a80304500d02d12079242c2c4050b0402d50050300110700c96034454000d41c03260b40243c0310201129560170b188802c5424070200603105030194110121950701c207130300038000850000c02c00f0400013095240c2509691181008407000f0303c002581c040074072001d00c0a55082510100c0c16592442181c4846803180308103a00c84c21000d45c2c84210350031550095018079809040074140f10f0f0003c2c090b00d0004000c14880c003460038410450000500464800e020f80c8407035075855078402d0700b014039012400035a108419100c0000d5502d40d950325404170741c00c1002d184500e2403641d4070200203000c031107480e080c8009400114020341c010001c00c8040352100f18442d4009900642c076010040014690100a10803489a540d180c100010b540c010700c0c00c001001411ba076200c8058403040030150719211 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 374105719 1250 374104469 374104481
    0x403020a1109012103090506040806180d1202090112110d060e011203050903190c0906050d11010e041b0203040303080c1e071704120624150203040e09060910 69
    0x201c1211015032040354241c1184c0010840d2074401d0400c40006501c030000108107410030303040b65426900070b204001e0b103d440801c031409004c48400107003510301d0042d44010100c004040c0788496081d00041c840400342d110b0400583c041d507903500b040000350781210080e40d595101070001814035042c040040b6505000c284401d0480f09c00c600318900c0580c499070241c48603000044480e82c18016800140c03802612400b400c1c0c9564030070613615072203e08002e020400c0320b14a8005034000c00b60040381800203000900e13036a41c080f5090801500c80c016602c0001d0142088001c0944800c8141500e03114a0340c00001038400d81f4420344034081241e803800400c030400d01036415a1108046650444c079040c00040300141500f60080041ca080a0003e0003118044e61040d0701c225840e01748015601c00b030040602c18400b515520740b03120480d1210088120040400038080e08031140c070310f841c002d8401d60003001160010720b010091031620345069807500b034440c101105c0b00c0803e03004401c00c80f40d09052900c00c603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 374106969 1250 374105719 374105729
    0x304060912020f1c0302040803030f040c0608040201020706080903070c03050609010b0d0f020103110c03071505060117160201200c07060206072a050a0f1b0506070f020114030403020a110901 83
    0x205820400050381120b0071340750000480505500304008950113605000842c4500704c40c0c0c0c596605400c01d07141025213201aa4816820040e080d014480140c0c3d0100380788003220740710710700200c141d180e0a00707036400c5110304080100040440c8400004000005c251207110f0820003000300860500c110070302c10344940b524001070400802d02d03e40d000560207548542c00b00c0c01e01400c810b052a03443c2c800585507502c510700a80300401341c0110114041001d0040d00d90054080c685060300d0000301e903050008000140100341011003001041c00054802d44c40741c602c0c040c0e031080000001d188183d00140035800b01c89900360b54011140c02051807400051841e001c3d10349170741c1c2e00c101c070261740d60025100850100d009210b00041803e01001c03880c200f003850f40302e0340903079500c0014041d945050180f54088607600750140f000d4643c10403039595a801920400c541050000480000078030048030300001c000c0e0f10092045012090100b0b00d94000303030200e00746200314180d429a580440412045000902c24 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 374108219 1250 374106969 374106973
    0x90a0305040905090f060106021c050406080711100f090203010c020109050d0305090115090212010e010503070515040308130e060d020d0f0c05091f0909020f1012020304060912020f 79
    0x10030001c0a0b042c0c0d0090703a210b100d41084e2500d00905031030b032508004081e441480180d01c4084007604103120ba008500c1d1100941c1425031520303113000030150014030002d18800c24006003c039411130801c024420240d11104d44c40c02002820540a81c02e0700900800c3c200b640298a400c1503404400c0c0144503880c04c544d0008000c00c042810a5411400380c0703001000072510f5521403400303c002035141c0c042c43c0090121500e0147c2c44260700210744140142c16404030301d00300205d4004005545000c1a4030050701c0080e107070501c54502d10303820103a03548140e9100800340d1070001220000b06211900403002e40720240001607064131064100f00c0402000140030b54009000071120b40001c006800e00610540300b043d0000d10035555800190745600211591101ea54403805003014000f10a02c00d078001c0d0180000401042880f40c002c01e40c9941d815182031b0180340d0420150310182d01030720a40500030b024080a6580346450328201d4064010b40d00111707034801c6200c3c03903030714114000324101e9103650031300c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 374109469 1250 374108219 374108227
    0x60c09090f0506091b0403050601091b0305010f0b180a0f2c0a1d01090308090d021204091104080f28020f06030705090405040c0302090105060f09010c03051603080f090a0305 76
    0x85c80003003c1641c0e03509519000001c01000000070700034400b6600a041c81100000c0d83e20103451008841e10b0001b01200c10145448014071001d00605138200c1035800b01e5003034603107803491034203032007094180e0000403648858031610001d04082c11144901c203039500d007100c103510303224084120440c414808003075a40f003000400000b08400c80940c00501a0340c0714070600014418001e47da50f0840c0c07000344003540020001d4040094001003040140c291043e10720092407014060701e1140054040e5006a591280e101e52a1014440d500710a88001c5e05001060303456640760300f1181030303441000300d08195070007041440b29600312003010215140e4580192846460360304070400c00400da4401806901031140500c02000e0a403034038402c40b07101d648501c079010178070b07821401040340701301c0141c3c070241c458081005270445080b4010182c841010003803e20301d00c230903243e01e400d81d403500420400305202e5011248600c14540e000b80141e014100341d03800c1c00420f488102c81262100c2e8003450240c0482c400300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 374110719 1250 374109469 374109481
    0x5031c0c03180306020a0c050c0a0503190303090c06050408010b06091011100905030903070806160c0c0909050c090604020903030f090a080624030106030f1b03060c09090f050609 78
    0x541404258404451100b5005031a40d903000120b0300440e06440003c1e40f010302400410030100201c0d0704130001203c3d801601c9191500003a0b45050300e1a81081b441080c5260808043c020f4208405c2180d0201c101d108076030700e4190040480d040740c8201401582015581000da040c42c5040720380921010b05030300104a840030b000da6051130f029480041d188950421113403402603a10603551440c1c41071001e50380d10300d20700b8101447d06610340c01003100c030f4214005100d5504450a4645010b821a00b458502d004046c14000e0750380c081c0d0390044407c41e061008881c1005004900007800e54412221503103140c41e01c1c0144412070041c40c12260301544104080050000104060300c030300d10004081d4030200d6245e108450803c082610108610f849180f174030103680c001c01c104074182c10410b40003001500d1a40e00ea0500d46001041e000d01042c0c0c076400020b11001302201c450010319000318040c0010308240100905140c02c4d03116a0002526003d180c427107040d03a901900d0f0003284000c0c1820f6031601d8031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 374111969 1250 374110719 374110727
    0x90f060512090c03070803071403040605120c070b040c1e030b0a11130b040302010807050c03030f090f0f0c0117010e180717070509010e040b0c09040e010603080405031c0c03 76
    0x20b010002c59200303078840001942d41c108903107800760001d2805141c0703e201350700c0d0248850810951020380390b001403000344043c0340d12800362600000c101c1e1121089482d40c82c0321030807a11880001400440086041106000d01411000102d4400c0314544c28540e01c0b4515000c00d500c51408001c00801c0c494012030340345112900840300030701076051203c0c580500c16019210b170a906500a0404a201180c00c02c150341c3c12061560f40724409081851411801c0103200c2e03128030000344090020005100410381140c0100200079140c82243e04940012aa010f0300666425107075800c00c0c005616141b4101c0e0320030102e0402c9040750b2104001c00c4032a16041e103618802c541401e144103840c8030f9510300040b5002200b0712002210100005402e04600301020302641d100140c11504481c80c440c4240b00c001050005255840544c152415856804031070004018114030f440e021840c1d820000301005006172000180200e4204408403003c000020060784000040004120301162885410402090007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 374113219 1250 374111969 374111971
    0x16060c03060f0602242e060e03030711060a030b041e05060609030601030605041406010608010e010902090102100515130501080606011e080903310608060d020607060f021207090f060512 81
    0x5403c0343d1588020045841c106e2071182c500440140e16403503104000c0e05400042e58554080103502440c13414445444071284421000940303802600001030301d4402074829445080846e60003403041c02a941c80f4201e508162480c021025442407510000c0750b074074903010781100d42800018000d0305403a03295403201802040024070564480d030402d41400c4008109105140c060302068441803031a504004000755071100503040000c10a1040080d88440ea03000a580c80b4500d000200204556988150300807900d004020440d4106081c413440b0100350045402045c141c5036500c084a042d42c3d500e40044072850443d03015140c44466080b0402c3d8550303c11040d540e40711080408a80c54042e03400c4010f4030740380c69180850703106810314446171a0440f04550440051002d450030761028113120000900b00d0005004c0207104000005400e410402d09801c46041c0035480c1600b15107a0051250b8a43c0c01c0c001111000c002039069580400e100c1300c07a14566080e1411a912141422030380f0841c20b1060038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 374114469 1250 374113219 374113231
    0x60c0304120b090601060f0c0816140309031b0d0b18060406060305100c0516030c05120a080a0915020906130f1806080604030516060c03060f060224 65
    0x1040002048012a07180c0329451588035400310021071074a2100c440c00d006040c0c00a01c100b088104043d0107095110308c5250340c02ea00500f42c0742e80c07450b81400d0445140f003401c100030400d4503440c44803a0500c0380400504000d078400d409442482c400c2c0e40c2c400d40e000510440c138560201d0701c0d14800c0301091160f5801644031030302c9243e1040c0f0502c4209071603c4c2c41402c0310111211500da0784d0600c100003007448086100088550706001d200c030107c4c40a403d60050440102c0c94004034101402450300c21140d092045810500f5559400080584403682e948900c0b48000480c082d000418882c4060307204000b52181c101000c181d03542c00c810030310000b95110b03080c02c503803002d410f02906075a046030fa40c54000030f020b011190350360507191803000e90f594059100c00f8000703240b40010800800d180801c0e42980182d261400542c1d034400103812a84c01150f0001c0648654a05503c0800c0d441d0541d1080d82a1841246e1109400f82c1d204400c80e5154482e01c65520000c12041ca500589051112419041a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 374115719 1250 374114469 374114473
    0x705130e0a0b0c030403030e0a030c0201030c0c080d0b040510081c05070b0f04030e030a0b0c16140109152f040b0d091202070b0406080a020423040c051305060c 70
    0x141464442024811003034910400f001400400d01c800c0640600c154841d180001c000b4050121842e20060600c5070103500183c181900d07170341811207040c030a1061031410f030b511000e8035460322420300c40c00000b030000d080000e005500d0300d400f0070341d42c0c000144500c08443c606001040710020000c1c2030552140c218403040c041c82020302210000515055041e4803420000300e90710174525083c20010038100801403180c0c0a07401080101020400d84030301e103070b07100101710300c0569525004126000001000c84014205d200000c9884101c040103400107580ba42c026502881d000f12925401012a8400314007800d400701c1d01070055017180e03a070410319810103441c81615810030b955034880441c2ca9204402d2001d1a90ba200c00035001c105082c141c0b6895410a840100003090a1020300505c0707204038001c8000340070b503a8ac001040f416403501110007424210010002c0b81d440f80c2d40720146041c030f0392150391256040c015114a410b2081b01610b04030381916a41050f118a0581809681c0c0e014a645000794 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 374116969 1250 374115719 374115733
    0xb0408090a090204080a0c0b0f04030b040206221d0c03061003090b01090902130c1b05030c07120b0702120313020112021209071403031206040e0706020f010605030705130e 75
    0x1402c0600c0034100819014002d010034040b0303440c20303131a92201a048410740d20310034014141d02c0340300389d801d039825213600035482125500e440c00010168000c08180d81e01d03403028401c1140c1300140802e07660003100d6414400d008403400040c42a101d800084440c8501104240000350040c9130540714400c20201c1e130304000844020540300d102c070052017600304941c01915084000118100700700d0608070b00a001c807042220000c07c40303008205903c5030510012120340d2519840c2405414401c8640202e488002c40301c10a940e8044c80304080840141550b00601300740009070100e00200e40e90f201e986802559501d50f580740108601003500b0010241e040001c84100380c0350b807109910042c10070110780480c11a01d17103403007103002d0300d0440c03180c11003000100c8010a5401c5a24000160340c80c008401301c21441340e5807100003250007020110100c11083c420010b00140701038000c100c0250a821240017480800d480700d00381035450040c3d01c9910340000c080079544242e500e590340302810560510b4162210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 374118219 1250 374116969 374116979
    0x11060a0b060c0a08031b040b0306010e01170906190209010e01050c16180606090602060402211e0f0a0209010e07110a030f080601030632031b15070b0408090a 69
    0x1d403440d80242207686134000014440f1912490780c1c0b481c07003101c0d19000e5603d00f50030090002c031640005070200b8148900e288240410380e002d941c4000c1000d8140310705032114644140082e0303840c40c0903a0550070401070484112140d60701402160321801d0180c4030102c04a000c01c0044070749501002d45045507019024240d54441500c88903200200100c400d401401900341c80c900c1c044a04550107d024001c140008200d101e40210b24642e010750100c44010f0702c0752482c0160041156158030100c0e1500802c508912180010310f140e0381c406403824102c40303020011000666440c184128081d40c003403140c2c00100240741305056941c0c0d01c02c4151402c2950301070110b2a880c60300b500484128041083c0c1510414115404444a40c0c8810246000d0010514007940400407002020001041010301851074004000c002e111180038003016007200d085200401c25496138910400c50a407260301003040c0d20114031101020b40302142d821580090007919182e03160007160b44106501a0040050280020 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 374119469 1250 374118219 374118223
    0x11030714120d0e070519090207021311130e191a040903020601060210150b07050f0d0518040606020d120603150504050c0a060e0103020c01020d050a061511060a0b060c 73
    0x50b9000792031001003034004075a003400742022100d80103d4099a08102100c0d8060504040d40341120201d8200690324003450020500c42c200400f0070800c01414282414600c08074000100700c040d4013881400082c039110500c1e0342e22014140c3c4d0300c0c0304040e0700380090030401000391320000300742102103800301541c400e60000c50203480c40544c080e0050b03008030004020700c507014484c2c1e0115840d0301404009044040c0410300c4e140042e03000700300c6408804203009007000010410025076000c08803c4551310051a00003c1042d841700000484002414000386081d080c10f00508080c0c55854018088060340f8140884100d000c800030265102e0700d4600c000b002c141005c5481150307070460300c00814645003a0030120320304190032a05502804007000c0402c00c00358041d0407038070754070000d00c1d016a54040f0b00800c0e43c060b004402141c1c0b006032a05080c410514150b1344800219400f40080503d07000c0700036000d0300c0c200041c0d401c68200b50040400170b01e402c211540178100301c3e000200824100004405014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 374120719 1250 374119469 374119477
    0x70209010803030105011215030f08070b01090c020f01021812030d0e1e1501090e070806091e0325060612060b030f1603120201090f031205071103071412 67
    0x74941d400010040c03205580c4540840c20403260803005110180b00d500e07001d050409140f001078140341e1025004030402a0410445200d560030250900003961111a0b1000416034040c100015212305400c1a0300780d04103009540d11140f13100d020500301c4603680140f2620103540290b0320500d0104000000345150b00340301d420090341002008201d640c90129102c0c40300140c01940010310350000c000040e428850540a5054444000c00410405490301c0361510f0a292904100d0560007402d003004100741c8002404241e6401000c043e0700242401901b254682c42804200750f607420220310300380c41124a0989845409106500004181e0342d40d46801a401d80c011008071401621184070014503d4104500d031641c038450409800305403090804424980180e10000f40400525140e00180e103000798440d410b801e40110840d40040303603d01c0d00904008070641d160610310302d41004114001d11881c010046540c00d50001c0d03140c075600340c0b00c000d00c21035040c080000354403640c0c244015460111001d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 374121969 1250 374120719 374120729
    0x10e03180d1a0601080f060904060f500103080c0a06021b06070813030e04090f150e0a08040b03040c09060b0c010f02030c0901321c092607020901 64
    0xb9151410300800041ca007540283c1806100380507101441003a40d0b85142c40c641240d07209000250304010189c010000c3c0044100c2201200e1904030307140041c00d082211001d14407410071040390585000e036071096201108004040340760300c407000140005a40140140000c0078000104c8240c0b402c103580720003c2c1d900ca4510301184a941c3d101c7d2518001b010043c4640003802030a08001e140b80100501c07103000601c0602a04105403c0f100c0c40c0e0382d88840d8018803100d81c1007017030040f12081b1030070050005d01000c3e40c1d21611510340003080c007403802c01240c040d1000d580020024545450070414900c1b0b81c10150042c2c3d449242290000fa101d00d0358498000105100080d80386c465192055003403c503452040b5048d00240100108042041d030304081f42c0307409809091405000e03d0f140340e03c1000b01002d000a80c0b02410020945100c02c130b5580181035036017500d41700405003240d801400003c0c2c8188910090954400825251991191070300d034000100c09d107a44941003440c81d40008503110020b900c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 374123219 1250 374121969 374122013
    0x190e01090603060b03120a0309110402070f12080106020616030e060a0f0e0703021302030c0f0a0905120a050d0f11070e0103030e0109030c050402030606090d0309050a08010e03180d 79
    0x4100f0000e8600a01040440440c0904010600940d4504451207074000880415507a50903076401c204c5160381c008603444d0084c00031520380c8150725041c0c0f8041c2442c401560901001440c0780c1c545403145030100d050703504a502400c1b0a45034820404980c0764080401001c1c507490300400c0c450000c041000c80e1140103d08000700d85a0280c4dc0c0150449aa06010183ca0f4000010501c0581c49805412020b103103800700041e5030782e0f640c1071052810b0040200c1202440800601d48114503400181c01c010384030100e44c04220504410600c99039440407400041032071300203c87d21444280151620001c0d05201d091807861030f0401c04680e802d100c0141c000210384600500103105050b8440000500c0c0c07102030034003519990860b103e00c1c01040c118815035100d07680000008034642c4a51041d01d103c1b01000c1c0c13400d040b02810745005017400c038407070185602070170f035092000880b008140110b404855007034010798030b010300d5600310818034010502415004030b06072216900150880015030006082400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 374124469 1250 374123219 374123231
    0x120f050f061201060b090618130504020922020120030d02030906010902030103020105041a090402030c0d0f1a090414060403090f090b01050f07110a090f0b0d11190e0109 74
    0x4200312011500c045002c02680c07520200340028032082c411038510072001c17555103032298080f06108201041710384070981c0100c505600c0c8200c515280d00b00c540030394801c07252441c5076907402030010a074600c02c00700000c0142c0c00804500155005684c09621844080300c1c00e07015544400490349136501c01c101e0f0f101110342c00810455881800d02c01c0d076016110016003541707154035540000300580103500410520a4001c804820324140607011940c0c2802c000e8030654803464000c150846a400100300d40c41454201726503800342446621401d0348501e1300303109101914500c64144088060010310448a840c1d18491854910000b0019148514425a625603100b8104042401081030540c44010f42d642809413200b096a00107041d19084800010a07548896442c00c024644110004041c0e07006000d19401054620300ca4008007007080325a20140048402d0806100d14006080c2c009000b0585d50b8691510034a041c400c010181040c01401281d05a11008440c0d10f290c001c5e84200002641c0306 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 374125719 1250 374124469 374124481
    0x1502031c0b0a03021c140d030e01060821160c0e0601082203090e0f0108210706020a020a150b01090e0f070f02100204080604020109230411040306020c070303091502030406120f050f 79
    0x10090712750b2402018003d0002e24506151140da404066460400443c9020050744e110702c0740100785c403400d60a8840e4000c145c001810a200034414034003440000c2103c0a0006640f5401901c1ca90b010364880b404c1003154802c903c445809072058810114100309840a00052054000050f6400f81c0440e0040040b10b51400c8a8145030102c61400100103080341120300c2002410b11f010344410b00e40000002d40c0d03404050004a080c510501030040100c0d10804951701220340513800040004c0080c0c803240c84081c0c40c1d80d04110704400442d40140c002e1101400900403600c6107288400d03288090045035614030420101c802a0313040341d005206140c3c0400200310a5607481043d11300200340d0325602c84000c030b00c0404003940201c1100c16690040c1e480700f40c1ba001c0701d04503600b01e400541d04810110344401514100c1a190381072071000344c000601d8410301103039000c44103051810381f44036074000750329148c90300506803081c03183c0300b0103240355545e143d640030050040b9001c0d0611940b00d00070303221014a415 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 374126969 1250 374125719 374125721
    0x70b040e062103190e06070303090606050301020721090f17010b0621180a08031005030c060a0315090e01050601030c230903071502031c0b0a03021c140d03 68
    0x140388107410b0b0208218540c00d81280100480700c40c400300f440d201d814682d0308202039510b07900400180d900128006003103c103040d8158088024244643d005100441d41d8108060a030b00503602c028101e1250301c030040c52040350f81d803000b4082400508101c03100355540d80c10b100c130031852a804000e0b8031011540d0744802c10001c0c425942c003040308540704c1d400c080840c444100c0352060814001e01c6042100c000c210341000b03030403810b45840c0021048800200700361078518541d42084e10070070030003520000301040030710300410540210305000c0c0245090a00dc141708401500e07210340d41c071403480700c900310104101e125802100307040d00494002044609145000504592486010b182085002010781d07010181c0d1f4428260500d03d810b81103a2561010302c002410f102c0540c0c401e17100000c230360322410885c64011018002100032204501881091198268195844110152782c02071440324144018505103170044415030012402d0b490400c0d150355072080801d005200e0a5480d0320003440d6042c2c060349 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 374128219 1250 374126969 374126989
    0x106020a150204030309091a092e0b0a081003020d0c03120801030b01060f050f040815010605030c03060904030509090c031803040312030203071e0e0a091407030b03070b040e06 77
    0x1185421483c161468600801c01449030094000d250744581e86002d00c06040340e900452300b100107100e0f0a6500780000c44016040e03140aa800d20304060f040400001441017107030700100c1e13100884040c5460040d510444110070b0040c116450111a40d03000700c05038172185501c1411910640300e4140141c150306162110080070303c801d0080003188801400021141b076541411500d0b2070401c1c100200c1c00480507200e40c01001c07109406800086000104848002908040310082d440c122380981d8031410b04840c2da00c000c9030141c11451041010541c6400c00590560380503010b854403605107001c03030000400c41841a42c610002a10101c240181d400c1008181c0059003404001145800d281d507a580e1400c03403000b42d0703240a040d07020000810346070080b50295042112120258044050f00501901900c0d40e100c5040c00f0b04001000404c1c0a549403080c1c3c00e450081c410000260755034404100d010f0f282c003041c056094041d601c070010341c2c400320790090000743c8902c820344a500d01d8010144248809 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 374129469 1250 374128219 374128253
    0x90a050d05211005010305090109081303140f060f060a0b0310081006060e0d0c0810020c0c0d02180703020d020c010605030f010203040b0f06040902130504020306070e130911090106020a 81
    0x1100c280100ca45203040f000c411200300b8200814259580d030b010300d0042281d010060001c0c8800516000300c04644c00901c000d9a02c540e0400402145c0c2203c1684d03079808040e00e800d440ea1080004c609010035500600d0303844540200a0400e2546690b110581d5400541d64681704403004e84041c045804140318414902041460030014640f50042c01440d2694480d0114001c03031351003554400b07100b2030001d03440291041c0c1046030310002d268002e80e0300035840740355004a28043c11f01031803900d01c0e01890140185400804564405001c92a000c2111001500200070b041d820002440301a20500107002d80600d90000060503920700402d06040801c06190b47c2d405910400820000507803114a1641110030ba10340701a84d030340c3d244042802406148000780d40000c010200c01d4150500b038000c0c81c1308501c06e41c01e64500c0d849080c800d1b03031440095907200381e205420094020081945600012502c2d02460f05004925040781c0401d607111020707042180140c2113484030106100d030046407030f14031213 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 374130719 1250 374129469 374129527
    0x2012101406030709111b060906070c020f01030c02010e0d090e25120f0501092301050a0611190507050a150801060c0510110d0c020321090a050d05 64
    0x200c0c00a000070340b51103813401100242075071360b81c440d4613013401c00056401e01c40b6012207130300e61500d960011564840c1c0442d01500103110351000102c20502c0b0f83c60340d006040c2c1c0540003229920380140103401918940c0c1e50748085646c0d5600151400000704080819568117880d828540b034100082c0702985400182186071480000103400c0440c442030302240c407104101d1030000b200500603e100301c0a841d1071904107454a0500c000401c43e0100ca603c8011244a035801c1c1ca40b10744240c64221044d85801d01c0703010350002c50a181000f070a40940520142140410252210441c4000801002c50080d240035201039202c00030500c4035082010130f00000e420b03c8007801c8424012894000c0c00110305005140030071044114030301c01c0200800c104595000b4008003481140740c00000c000c0e040d000600c04240c15820322103d006000d0002c000c6a174000c2e001c004540c021006001030400900010b002d14200344180f59107840818804c2c4812540005540c0c1c2c0c4030b80d2a010070078820101d80d444400310b5005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 374131969 1250 374130719 374130721
    0x3070504050402090a0b0612010305030d06060e010905041107060203160e09040512070305070506160306060e091b0408030a03050405010b1e150d1805100204030b010320121014 77
    0x544d0315241d41c103501c880c0008000c01c0119600d030110740d0300c1c042d0454520f21241c03071030008010003101002801c0c409a60384010032646079100703411509400380c1804940801d449500600c92410150003d511b0600061030407480e00c0400d598180c12640201c07000c0c403410f031042e280208101d80c8000031440140048844038110309054490584030315015110f005840c10010f10700f001c0500403010384800e5500002a150146012101946a500700ca094000044e10707011000c02e07450300400c0a002c1c035140c06030210509541d8030004c946000581c9115010004084c840041c954a08200511044a403564041410305017840d0203420b40d805101814403541d00b824180300d9184003885820001242100c041e0070800814040b1140e6104480e110104a81048800162203040c2009801f415100d0f508461a200c45946414120b004038000109124414001007001c00c001441c00b1224450002d4440100c40003c0c0000d1000380f418071920245402401e20104601d81c140b140388601c440c00f052420725 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 374133219 1250 374131969 374131973
    0x306080d09140103140c16020a06110c0604080712020f06030709030c0b0f090603190606050702010207290d0f180b0a0608120a0201061706090f070b04060f0219080306030705040504 79
    0x200c00790007898a044910041580c1e0500a201016140844e8009e44820702050712540c0003040c10440c8a1b80c9100c034480c00b800e5605c1820448101c60131195010040d1042c0b508208403000d60200100c820b990002d6000d4241d105075550800840c0a03451645a550000d86549041c0b03010048076480b0340e01c149400d020801c08504d44000702ca1502000f20750003542c81c3d90320150102c1e080f002c21030700040035150101c08a000c0f6002030090070600d000742c0869514a13500c50408400c03150201c1203900c1e42076002800381e02c021842015114201c0090b50105411a83d8030059003201c2419180c83d0909070030511040500612181e0039400140050041c086d00f420000c03110356910a0980c0055003a9001a003401064801e40c044409000709012100e0640203044d11035a84d00300a5514980d50700907080c82010503140000c1750401c4a10440005080c10b00e4a1400d4420403805001c0c00c0030740c06150503d8462140101d006104e5030b21580f0b1075030b16070030f0003000d1515105c0250050750140e8548010303c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 374134469 1250 374133219 374133251
    0x30b160813020a060302070318170f0c031216140106060908030a0e060310091d0d0c050d0302030c0c0a1412090a0e0a090f050102040e060f09160306080d09140103 71
    0x3c244d58440c01c000d82e03500c040d40f90880e8101c07044001c0030100306101c0008621202c03480c80a110800101d42102e10003143e44800603103170075580740c200d076050703120f5020414505412800ba00104800c0c1441c0c65200c1072a85420340a00b001128006d41a50360303c2e0240083d5401c8900c0f0409401c15000560904d0088040646092180d41c4010f00c260b078007000240040403603a1015006d0b104030042440041507504c0000d800b07070350f001300c0049a40507110894034007512401041c05002e030890000d0902021122080d4001c0d400505030b0115031404001d10215004100f1440c5091441404c00030301005030885820704002c6918554090f00004004007541d6542d034200842c203581750300014002c0da4171001400070003081d00b94001000100406154014840c1c190b0140c8111000084188850b039144070400206c81c03010344100381d0080b8101c0120710b0b80c08880218800070003050400003055a2682c5110f80340104120000c000900400028000031900340c3c11001d03910800c2c2000e010300034203803200030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 374135719 1250 374134469 374134489
    0x90a1d0c090c03090c1e120c040e1504060c0921060c080c0f0d02130e010906050d030804080a030b060f0706150f0302130902132703020c1504030b16081302 68
    0x41c4560300c0e94441c9450280310240c03a10140710000c0c80e00f03441d8000c86141f940c50b81082c0344c400d0b100f10700d81102d040704d01c20007086602001d40300801148031541c996603610010704403100c01c0e60030010724680209902c5594622021154002d011030f03203c3d8400d910704102601e20f486829410090f0b08018480400065800d46080d00b92502c00300d516032140f41080c000030b000364806110313489400c039000a005680d800e4140d06854411605204664450003400300c0c0310042c0320700030005034010000501090004002e8448543c0301d140109a500e0a41c0006407950024200000030075000170707051003004041d101e403450f1015a600c0444406150041480c3d8017596480702901802d0b0003c406480f803002a03114410281e40204049015004c05240000810102821b040090841c04003010100c40300c0c0f0725100041e503d030b4000c0a1508018043c0110034080310040020003609010200006070400c581901c19a1482c855546030202a080280304820140554042c20700c0c0303030080c10258407141060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 374136969 1250 374135719 374135743
    0x313020f2b052404050706020102070308040602090d0b070206060112050606030f1e10150309020a0510030e06040503070302070510050403031b02030f0114070e0906090a1d0c090c0309 80
    0x81c030015024200942070005945803100000c1040907810300285194080e54092406581113541c03460303c46400b030b0300704d120329807026000c85e01c00d10000c2d0004810f90010142c600c0060860904d00c4410313500d03c4100c1c40151112400b6820583c10401c0d00c1d680074200041403510312000344107038103140c0301280251001030305900300745104e00005900039400300180241030030b5501c80781c041d0380f40c81610b2120a03001ea0040d03520302d140b080d448401041c4039000c2c1c1c98a135500100001104c1c2d140c40200005d00c4502300207a018503442d9400900e007558140203007489140200061541d0f10014030f0b00030309040d1141c10582c40740c1004483d1190700c036445800c0d90280c0c1c0d4107003414242c100180c00c203001c0c80f00202c0070095162240c0c1501801454040d0044100766030350a400d145143c40c2d6990070b450f1000701107495608540d103c000580342d031811043c100e030041810180010b441c5034a0344121719040c1105903100c0c041d030104224240303604044800c81d038000b1413080c2d054194108419540d490b99100408 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 374138219 1250 374136969 374137039
    0x318150509010209030a0507080d110309130e0a0305070605060103050f04030804020a0e190e01050c1c0209060f03010e01050d02010f03200301260c030a120c06020313020f 75
    0x62a000c90950441e507000c01d0017011100900414502143e488240c0d000d44455070240c0e030640014280503603001c809848610014500700b066000510200b00c0422640c5a096900e41700074500042003440764001c0e143c0640d451603540c495a0504030166040a005d140c10945481b08000901144503001074200341d0514012403e500c0742c1c000150650b109400c0700d001007850707600388114110201d941c3d000114152a0130301131110021000343c2281d00c1100c85106d079000800c02c51030300780101d5042c0c00056003006c01c0141006441ea001c41c0c03007500980c01070b031140399001005209078800d500c5450f00400c401c0307a0100000065600080c00d50b611210f044051548810368554175000d02d44600c0740907103c3c0703102542c481d039555680a09100b803800c01c552621080c4041c1290403000031808002880000e0b0047c40c4030030050382c2d160403580c0d0201407201041904084c1100050550004500640ca98250781000b80c420b401000010b070714005410f0f00c07844a84400a090054480c3d04500d09010021 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 374139469 1250 374138219 374138221
    0x2904030c051e0303030c0a020f0606060f0c1606050c0f010c0c060902040209040c02031305120303071103070c0e01090605010318110411070b04030e03031314010e031c03181505 77
    0xc001ca80c01a2000106503d80800320421007081070100240c0b90944065003140d0340c411141c2c08450307c8200c01d4851030f801c00410003602c803840407a0310040503001c3c2e4000c1210300885070111000c8113034441380c0040001901c00100d00f03410032010802e03181717503440100c000c01c60a41c5844028280b5074a0600050449450710717800030540d641c6506507041d218010b0300910030700c07c00000003074481d80038034030a5902c44a42c4001259a003000c01400320503801d07201c003c0d4a15100c55109981181c40810300f03143c184405c002241c00a00321420100003440b550341706820320b5050a0095043e80c0d030b190005410113280006400e81c600c45240090b51441c3c0009100441907405000b09010b03000d480e5401c6081e0b0b4000648004015503994600c0c4950f010707a481000085040c1c08050b140c0c0300d5240440d02948183c5006c1c000c44003940003800c000312050400b01c2800d0b00010109040070007000700400010500101940055050301501010b40791b1440c1031010443c00303943e0710706000589807403861121395400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 374140719 1250 374139469 374139499
    0x30030309080c0607080109270b1503030d020a030f020c030d1116050c12030310171c1e02120a0e0a03050a0c080c040501060f0e1305012904030c05 64
    0x5021940203510b108107031042443d190340082e08540080c415652a18548000305405540b8655000b0000303a00a0141240000e252503403080c20201800700107941003440ea90308103541d4100018410030703510100241e181c0c01100c0c03015044031004000b0146890040141000062010013103038600d80c40c0100000d850200b18600244074048c070341c0b000e0b010801c0341c540b000c180710300010440341c815812520345039404000f12803543c59000507a880160303403813260380038080c0d00701400c51455584002402c961694031610000000e030901c0c020000c01150010f00031803080c9054030166501c42a50340010b00b074246c03401c0181540351054072540d0342003000f044000403850b900c82038454001e54001c01220780392951420041e40e00900c92240e000b107031040008500c06400d1900686040f1800c40e10b8115940e01015002d65100e160508032540c00703040100c422400c80014801d0901134a02030001c4203912400071000d00d030000c082003190802c04010f000410001d03205988000c00d40f081aa104014501a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 374141969 1250 374140719 374140733
    0x1060503011e08030307030204030c09020703090e07030f180218010b0d021305150406080f06031c0e09010608190203100603090f0b0a0c0905062a0f01090c30030309 72
    0x42c0c01c4000f42d4003000091280b11603154001d0f02c180c902505800400d80e036200200812807288500c02000308400d40e80c10010703840c080022a900200508001c905101640803013822507061a000c50144c400750703044802541004001c4040c0d942810030000c440d5410501c2070301450080d0040d2918441c1c0029413070075000d1148000703000800001d0300290021300944510120754010380100000100b22000180007007002086650003124050007802604d03d440c0c0c00010f01880b11070035007050040c5405041c850346c9400120700c1c002d011a584009280c10a0910710100c444101c2c406d02c0b0060050040c8030100080f91507a13411940c19003000143c40324036203040820303010000c1c0090303d6440720790104440f00005410030b80c5540000d07605e13040126100c0081218500a1442c43d50010504004607075024079407480c0001044002c00456050107070b9528100d003912960201269203000040d03040012014412494042c10030380d0200040444c40b4076102c0f90040c080c800042c00705511a44c400081c00f000c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 374143219 1250 374141969 374142029
    0x1f060c0b0f1008060108101b0f05030601090518100b070c0e090a0503030403020f2802190902070609060c0c02101202040b0a080412020309010c150b0306040b07030e01050106050301 79
    0x107509444c581d41e522942240c645040c0302c042c0010720305129a601000c80f60030800e106207203981e21011048150108200c426800082c100c5051005002c0c3c007140300e80d01e43e11b00101c003400040340b2180c549800351340c04500d010a64002045844244008000170b840c40220100383c0d9030707004442000c2ea41d5030055614190141c000a04280030000034001030641c0030801281268807001200c4082ca0581149110441c0300160100b0b408965880c0740010300d801d200c01403500c032103600c50b1001d13507031a1055002240c2c07048000300d40d5242d49403810010000d150046560225550801c01c4075620140c020a4066490640b010200810054007806100a0354140c40107842c05a5106883d0700c45010098020302c01036806840d4003c0c0c00010503142880041101c280c00c1040c0d4648240c01d00c80e54894007140703030302150403414036150000304000d51800c01c1228821401b031030f10400241401c030005812100030380802107550b418800140541c0390800b044a0440301c03500c2210f070040103400e0841c1c1e41005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 374144469 1250 374143219 374143229
    0x30907090207050607030c050901120c0309060e010b010305060d080a050c12040f0302090f010819240b090a0204030c1809020907080601030e01140402012003031f060c0b0f10 76
    0x1201003100c2c2c2c280000020303414400d101c40d450401c40340f0103134241a9250700881c50b07400e0004884000ea00c4500341c0301e401c464151301680c1030200304031b411540c6640c180c48490401e10b81d169542c0703540b0116580c1c03600900d07801c20b1040e030b02c40108181c1602ca00c1e103030344030f08411003050110020307a000341980b0420046c0c002d4280e08140740d4a4648918010440d0f01191009a10405005001c9000c4100412034103040302d410800030104804000196100c0740101c107410341d021490a20f070300450018100442e41111580600083c100d0760791010010b60b424050403003500148140428000038003000c01e91401c0c0e681c01d240c101d81d104514034080020744500003001390031002c1403041c0040a40c1045006000300000d03241803040a08240b03000c0c0c01c03200f5000141301c0e100c2128020070003550180800f0201801040010310700703420040b00705483c65009480c00f20701c94400403003402d81c40840302a064054981c078500403203100b9460326008004000a0180e042d09500407000c918481d180d00c0b10b603030080c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 374145719 1250 374144469 374144471
    0xc050a0b090303010501140c0a14030403021810080a050a020f0a030221010b010c171308060106090602100507051b030405030a0f05010c03050603070306110d061205010c2303090709 79
    0x101c1c14810454694100b03202e006d001c1031249260003403a0000b01d042d220381c800036800800001c1040c3e1a041c5141403003028181140c00100302c040b0158031000c21500c0b40c450301c01c00c400d8050402c1c5180f4807060542d98004021a00541e40e00300001d0000304920006c0b94040ba0b10b00401c00d80c42c0c000403100c03d05948000e40c00202c1e40e80b00020030340312181242d0828900b00081000c40c0e140c0d0010340b401240c0310b03802000c403030301c5011842550358140007800c213001c546071803010380741d4903100002d1410a02f13070005800300da210542080040d504120f541860f0402c15001c3c4500d0400380c0d000741180c080c007414080c09110104c020a0001c82c208161402400003e0031a4445402400c100e04e03201d60940b006e4603d035080c48180d418140c0240038107400b03080045c0041101d1440c54503440300074020711183d40c0d641f000800510a43c0c6407d0f00844c00030b021450840582d0050a1902a007140c0000f5103000501104c55800f07082d1142c200d00501d03411080d042d90382e40c0c176039071746100030f05112140d00008451 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 374146969 1250 374145719 374145721
    0x30702120c0f06010905010b04120618051624030f09081321020d0312180821010509060d0f02030d0c0c06170601120902101d0609100c050a0b 62
    0x41d00c0000d0184500001034042d90103d90726140d82c0d50a03240d0034092641d106078104420460b41c0440c109480c2294040c1d04c0000352401001002e509a41c0f00440c10307541d42d40040401c00d101500001117030010048030080e902020104200d5800009940d11204285607903500050341000e0325401952400c0e502031082c5a80b64880d0310024802900f5010725002159158040c140c0489810701414560390024a141421041e6540031030ba40031300911843c10b81511a4403455080e207801000d041102c2c815210183c840400c064081032a40320500e900c52214004001041203444084400d90800b1068a00000031201803c020302c0c41e111100f4001d42522403901c11403040c9a000b100805d8903407003400300c01c8100360b8992040380d80c07509081045091100380300105940c1d6020302c98841100826040214205007150001801e00800c5120440483c1c50642003180d0701c04844241008060101c84030383c1080c00a80c00300e030b107404059043d1030901003d04450f078140701082103100e04090748000d5a40c05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 374148219 1250 374146969 374146987
    0x101d04050f09010f090c1a0c100b1e010c080318070902070606150503010e0a0b12160609060e150c0706020705090a091a0a020d23090a020607030503070212 68
    0x503070380111800c5016510b01010b0a1190b40e1a0045200140d0446510b200060410400d446000441d0200402d410b4007001000d0030344c001806041d52427900c22800084603010501407200d210a400c0841c03020700031b4603541076004d0303070082d84414002e070304030404e9a202c1e60b8150070702a02041c3d4040c96035440c443d2000000301c64100d82c00906203540302d11010301c942070342d820740d0b000c141091241340700204009000511220890b509001d40c0214003030303004240842180082411510302d8448906541c02214405550142c0f02043c0f000501d00ea280c40c0d1100d500d80303034000340101e070000f400710321038150890902070f800bc0d0101559507000b820006d0f25140c03543c070440030350b83e07190354032903140140a4040041d282d04014401c078680d050b045501480c0d0364090001429508400a103040710641c1e0901008252280e20b201c0c40700c609801c010b25054240c074102003202040d9008081060312b83c084030400006846000583d82503540c1414800d89075103d02c03609174140200000d402064860100354028 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 374149469 1250 374148219 374148241
    0x1c0807021c0b1b0d06140f010201060602060c0c07090222271521030206010e0c0301050f010909020d0e0c0f151333030e0d1b02090a06030b0106050702101d0405 70
    0x40000003240c1f24001d1030090b0f4016800e0354054400e81000d6042a000140c071080c801000b0808241d42c40c050f260080d8442604000b01d070000d10042c111034000851a00c400c84102541002510b40d1001c00c5401100001051030100c02404902d94016100c00101c44a402c3c0402d440001d07000c50740c22940304002034131864420312480c1350194010311520f400000c400080b07041c094062419402658a507078281418000c030318101148050403c24041e2002440c080c1a2001d85a095011741020a8902030105080c2ca01015503818500c0303483c0c48614204117035200820102e541d02420032060303d030801540c001c4081e50345a03000304002e078000302207010006a031500e461030003480c015000400003070300003086044400c603070309020180d4061031400700a540202d2040003141103194004061031002d070b01081c1c481509a40c51020103071100300500400400854a07400b400042ca4442e042c0445500082c840040f260808014015029001d85003080c00c48014091150050410300181c00e05c0c64502e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 374150719 1250 374149469 374149499
    0x40501020715020c07060e0d1505240a031b090501082b090306020f160c050429130f05040506060916021005061c0807021c0b1b0d06 58
    0x2903100c010800003140b412001d2007a148090700c9900100703510760400909550b007180e09401150b12510308804100050741c0030250760035003004441c020560382851072440340b881c072185100c400311452a140d80340894544034111011290004a05200c450030307032910248490030341d0443c00c801c90802c0b00126084100081404440c00307416100318010503591004210410006102000a00316420030400f040305034001d8041c1126510510346004112310a01621107000c11040f508810310140412403480d15109001d1004003501c40007c1c0301c0006200800e407107080403c00d510070b00d0038591072403010034150b03c40504499080f0f000c2085040c2801c1041d0303115012509503126244030f00c0040d81021032801c00d81803001880e0001d196813004030034454094140180780941180e0b40e50030001c0c007880c0e0303e5110341d82140904400e595440c41c50042c0070f100030124500c0d0035200c0010000000285040101d5580511810030303000700e11000341e06503ca90710400303240052050800002150103004540c10f9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 374151969 1250 374150719 374150723
    0x12020a050412290c09281403010c05160f08130306090212192006040608090f19020108060102070306060b0d060509070c0318051003020c1e0303060f15030405010207 72
    0x50a045580a501c40c1c004010032140110418404c0c480d010315400e0050007950801411450441101901c6c07422043c519842e502c04a0205001c1d110900141028810a440c65200345895803502081520207003003d13481c1140140b80010031424001405180002c1d036078510740002580c00c2c00b95680c1420406420014420380c81003206210440703ca0400007030030000a078100014442c20421520ba10344003840301d000005903402e80702d100341d80650f00d010080020b840561504a07070742c2400252940342c40440c070380e10b0307800350300250301040114440780300208880e40c246484c8505544200c0100d090032882d45c0014806410408081404118034001d0301480345058070070032000c2d42c1c40d0100056804192103402c08105080d1200011038401c5200603a200f100708805109540c4e03071030204140c99807000340c00000a601041780c0f8010790050054800184502c0000180101482410780c2c8038480a08564480c02c0710301c00714600f6441d01d00d2102401c0201712026900c134905418014040e500c58141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 374153219 1250 374151969 374152013
    0x120703020a030b0307060912050313120b1308090409060b09010b0a0e061312020105070503030910050c030420030705040906051611030a03050402040209091315020a12020a050412 78
    0x11944a44c00d00107600d20803118581e482c0c41c042854041c0c65041100600741c10342c0e050204020701001242c0d1440c8080080403d91a4813402d103c843c01d00140e110400352001c1e42e0340c20205203c0d000b041000003581c01b40313102154009130903107181c5003200040c4140c5041d81d4002d401c0c1800095001c0d00704e005050b03480c0f210740b40d0903411440d00d000c100c0507110700c107000b03007500a0f885400c0c803000e40e00104c407125507441810481c0c40d004454960920750303002118407014940c4214100c0c2d088801c1405180d0300280b08507011400c40c14699112000610580040040f508082c3e20401da20394040040d80c1c0102005402003040b2045410208050002281c1c81c44650041f0040700442d244a100d1078820404082d02a40c1000605a41180a06409030080c0e80c400d40900a60086d5130f200d104440c0039031511183e0500c4540c1c00c0c5041801142d58000c1402500d1050020500a0350001d40008440303c1e8800d005a50307010000c01521707035000e540c01a640000c8003181c0c020400c0310000c1d81131800c2d00362040b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 374154469 1250 374153219 374153231
    0x3010c09080f0705091302030102040b0d0204090606050901080402090a180302061006020c0307180914010905010b04020c03040608041a18070b070804031b03150f0f020c071a120703020a03 82
    0x4070b010341d208a075200b000e8001c1100c8001070b108040541c010743e04503100500152a007591107a2200e0142c10030785055003a541d000400f002035034024401c11000300094107100d0704140c1042c0004c2c0c490302d00140040d00950300c400000d40b10121591100d0702003c2c05100c1d255805032107040003036481c542103070b02000032100590003081940c00051a0700d2100c0004008001407810144090000b809003920300c40f5281d02c840303498001540100c0510510307514400000303040d0f0040d007011401c2d00c51080165014030303c100102c4865880110489054800600b8144066156071621021028160300304100040818040c8071103200c1510b1480b041d03c42801c21202c21649503044075200c0c1c405d100c00100b009504103c1040040c0b2544452460317100103582e01d0592540d03a07101c100010708a03100c0703c00000d641d0a07151030700316203510906ca031040700e118045060035400d04605072b41d0070f1503025140e50b00242e401e440d12090f082c2c034216220074003080f104505a05240c80301130065008a0081000b10741400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 374155719 1250 374154469 374154493
    0x90106050c1e06071d0306040f0303180c0b0c25030203070e010f3b0702010c17060f150a0c0209092e0b030106030803040606050a0605070318030203010c0908 69
    0x280e01c0c050a40c20380c00241c405a12003290030b0b640c01420b40181c0241d0703004400403440556082c0f001c00d200303601483d401c909d00d1001d498010204c40078080800c004201c0c000b61344010841c641480801d0f100070400c026940c1507d600d038980380021140e8841c4010110114110008021000da40c04403171082d01121401501d07500c50354055603007409949103032030104400308441e080410411510035070105916852403180d55011906a05213090440f02425450601503800d074248164600c3c51030516115000a8484240005294000c0c2c2901e100e180d01e0844040d0310703540c640782c401610001406d5290b80d0056100c0182c0071548649099108102c00800541c01e4903000c5481203840054040000c008041c0190070180f10004882120420350354400400003601c1c24031455000c0d5000b24440c42c0c40745407510345807060f1a482c1d0882c3c3d00641080c0e900300045608002503601c51641420030980d0b0340340109080254000c6548060350540c24100d00900c0310385c10500d1b6038241c46d01c001c1a01d03180d103c0c030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 374156969 1250 374155719 374155753
    0xa080303010602100c030e0f01090c06050a0909113f0903070204050903090301060f05042d090f2114160b0907080102030705030106170105060412020d02090106050c 72
    0x1d108a001613042815405062400d550200800b0b07a02820f0000c1c0c003003002d200c05072516801d840b140005a546a540314184840c42a110f0010102481c005142602904005019160364440d29800685802c040c03018403080c00140c03555401d0300350398229100c142d690384028010700e08100608000c4070030031000141034140c0d4035038404c4e1094001146024402d5003440300500e40240030405500040c0010041c3c1d607028010b500007802c090542882c1e56007420101300c00c8410003400b800d9002c254140c0d1410044020040001441d040640010b120505d400c0080d1a140c0c40c080c001d046405010b41140606115140a80f00c03a50305d5440d00c520302454183d0b80c07a1031107102070310341403401e41c00b041b00d0001e0040b030f80c0c041c0d2042044090b1100207644a03d05402e90700240c80740804180d01200620030154840c0b030300b2060060b14860000c0a5142c503001c1805803096014898003440700303011980a40d161380d03c1c08030f559580036009190b19030751400020500e80100c0340c4446680604820419100c0740 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 374158219 1250 374156969 374156971
    0x2a03040906050a0308040b07050a050118050c0a1a0309100207030804050c040b060306061b07030b01080d020d080a05060301090c0602061b0405031504030c0c0e1b030912090109091107020a080303 85
    0x202185c0140b905003801c8550302da40c2c02489084840784900025500059800c2c040c004022148070020010294540b5080c1e05201c41004018003550002200708a00b481000303080e8070215900807041d0f5642c60b0005060f01304603003030701001d00f00383c00090001c041603800703400240700c2c900480c142e4280081e03480411003a01c00c03200d402036201d941440420a1450071100500325014108040f141d060a880500790502540e0b610643d240c0b000b46004008011007400016034080561001c3d01510840d100081c00c0b86101130405051940d6400010b141900c09600083c2c2c07503500009038280342c84c0e441c4402995400102c0c0c1102d0115030b0402084410610981981c0c240c500040c090140300b55101c1421540f03040c01401034042050801a0b6030210b80943e50003001340c00c031aa20030095281030140340031107921407403004c802034400704108103d001012601290190b102000c0384c0da960310301d0340100ca030f244054200808051400035580100c518a00c010140c241c800c2c2d030b005640580d40e48505850b800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 374159469 1250 374158219 374158223
    0x4031d010302070510020315090108030a0201110c0601090b221e0905030906071a0c070614011d071809020408150402030a03030e0a0b0a0515150f2a03040906050a03 72
    0x408050b5504207103206802840e84814234501d042d4010079810001100e030582030b0300c403c03001c0e0070000c0d48485803503080c0110344c80e05041420040c642841e201c0f200f41d4444051107980c018580d2480302148503034a01d0f01068401050b10400b1304d000024803010001403030500c203403552074060360403d042059010b00540f4405a00700002e1414400c401003404141d83c001402203402e4207a0910310b0a110084050032400398032001c024036200c47d5240361400481d0504030b0303c0042f00300f050f80100b03c0180c1c40049600e805e2a20442d118094031f0707418094844c0407880c640c00a8066480303202042100a0354041c0048035a40d070110366250180150b01d2070380a0060742e01a402d60813084003000800c0c0607801c210f480c015048100c4500320202e0322001d249040968409003103685a00c284000c0c0e102042e11601114812142118000044d04110445226031400b01580a80101b403054a86490b1300050050710600c180f04160b6030200c80050b51030ba07100d03000d01c0c144a403410401040a007040800300d030581f5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 374160719 1250 374159469 374159473
    0x140105120a11071b0e04020a12060e1039050309030408010606051b0d0509130e0115061106091b1f110d0203070f11030a080304031d0103020705 63
    0x1055421030100250010860009103840b5803907102c8200b2100c0003060700c035000710420304108032640e0343e040f40c138a0a41e0100008585000501002da6180c00403078040300c444000080c084010b502e0418040c190310f41442c0c40501684d00d6182c00c0b10225002030b00c030480d00341c1000c1d0b541c150040105800c1412102012001d0364542d40d8100c20b20b01407001142c000045408032810260386407081c80c01d403003854200c100016804940c02c40da40f0704c14030b050b03200c9841140c060708840c400b2010003803850040c403440500c43da10925840300440741651003510304000c6c0c20000e0002c200384c180140310a0b20144103000c0041c0d0540b80e8560502008075100e4040c001890140c4a2084140c1c04001d03d002c55020440d40802c14100901502c82d8080c1c0004891100740c81d001084210f1440303150a04141d01442d405541041144030001440e500204110035801603c84015540f08400f00345840c416210044c0345100c0001440140341e00240210840d803a0100482d0038205c01d0b1004600340c0c000c40344010096 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 374161969 1250 374160719 374160727
    0x40212070c030903061109090105041404080a0504031a0403080c040303081b1b0601080c0f03070306110c070e040510090203030304030f020c0409030504050301050f19020d0b12060f01140105 83
    0x14500c144034144000303000f460f02c0c0c0310342910782e201ca104441840201e1180c1690000b56141103041c101d240c1d5006001c2113404104407480f00c000210a80d100410040c0b04000c00500d02024500070400e84010b5a0003180b5680c504c00762821201c172606040c0c030280d02103000840001c1c9001020b5088174262640340c1e4a1024039281c805042d02d52504401021403030460520000d4400c2054141c6004403000391030041141303524068480d810710310542c01090081b1443c26500203161800030700201103d078031150000d80040789070348124903030060b41c1c1d082c0540c2c010180001900b500b1110303154003482c000c20036280c10500e20744441c0e0850300380441c002d405030000d10004d808203006681c00998200e450056860703801003800003e080341c291072011400300b000450f0a012508003441a182c0c00b60f5045018000b608080008424029104c580c00e090250001075507852101c4c507400800343c440b00030b031005d14104503914180e500d0b48800c4a0b034400101005000140710300c40340007010b08491040e15001d1034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 374163219 1250 374161969 374161981
    0x40c050406030f061a04020a0807120501081917070807060b09010e010b07020d05161a1303150902030709051807050114070302070e0915150307050405040f150506040605040212 77
    0xd004440c0c009507801c13291745905080c80d01c03240020041c0b60b100d0350755620940f51559001e0f015030321168100355501e10300801440181c0d1700003400301e82d41c60380002c008088407035072a205406a0440b00104144400814000c0c100141a000740610070311484081c08050b1410051050b281c2092041c00004401000100a00141d40300113010311800035010b00390804494840728600304080d114400e2220101c0f4042007402c0000030b02983e01d250000342d80c3c4c80d0403000303003003580103030303024040544584004598445044216404240030f103602a060320307840c4d940e4820800040c00112414045a03075440c0c1e486040c030101045041c10b0355016142c01c6208602e289485201703030040c0c0b200b10705608c54a580402c40c01c2e40d030b008003445500a440280001d0441c0700c80c1480c01079028091280d034a407400030135800d035940400c000c01038070801e40b000110313580c603410a41c0380c11090117070103000c0244030b050100c0314100c640c0003903101c7c0301d00751410b000704d40d614420710049104159203801d0203013038003001c100c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 374164469 1250 374163219 374163221
    0x60507080a030b060720010323060910080d020c0a0803070b1906030c231e01080408040504091103010e070e040b0604140a050610050f0a0f0908100203040c050406030f06 74
    0xf007400c030050a0981054845d6840105400e40d4120002d41e80710644031400003503130b25000b000c020101d06901000b075003a000180c03a0819001030b122502c1900e80c100064868812000600d005007800c0040b14144408148040e4803102848411800341381042e41c0880c4140c0000b0071140c10b0340c1c2c0708280408a1340c40041d62910840d076035681c1d01006440f40400008100001c8400014020004c215000d80c0105003070b48090200d144901401000300c10784103d505511004422019542801d180c00c0c0c07550340b843c00210510540d0002980f191500f01d4160511051f03c0c00c99061312402e070020800002c40420f034564819552140304ea216800d08009400140381e020003d41010700500041a0012015040c03015600100d0702c030307041260f5038400c00003e4541807039031005404803804c20301d02d000c900c00c804507000c0c881d81c040c00003400906404000602c2c842ca01001c020f141030020f48220721948a000c070f0296200b61800e99020306001c00c003003103515080c424201182e0384125031000d00e9040b59280c1d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 374165719 1250 374164469 374164481
    0x81006021020070516120819020a1205030601020607110a0201030b03030c2a010e06030403030e160602010c02010e07060e10053f090709180609060510060507080a03 72
    0xb40c1155012a0001c190b031910003804107184100090500800240403101070008164420354910340000031480c0070407030740310440e01c000400b228460fa84801c407500c103a240c82d1014200500c403441c100b0b200c01c1c0c41c0e98400c0255000d102c09070309540c01600c90f034108442002c2400e03011030050701301242901c01513000790f0081e0b003e507102500b40d9040514845807541050b001c13034140104080e00200c0e19a121081502e00da0362a0130900306000e00e49222800b00b50f032070000501c0102856030740c911440d502101004034594944122020100f0700e900c60307030024041c020100c8030002542c00d04c0300c3c0c0e072000c0c00c0206961069030600ea5440b224440c0540811a180040c11007420510108000c0c4d4040c01e92101e0b0f240035040c8031030420807551050180403c0b5540f05d210300300ba0020231440c00b4040719070808110748080701c0000b14041040c55401507035107144030781010300030226464500a0706c02c10146411003441a00f003000300140aa03900c00c41900c4900c0741040052560f1001c000d484440c0740a54041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 374166969 1250 374165719 374165741
    0x609040609020a0201050403020f0105010b040e22061b020a42060312051612030b0603040b010f060c050703061509290148120810060210 60
    0x425031640e1507540ca0103c3c2d004044110050b51140304210034103804220703a201007600040204a21740c54080320f02c0c0c02d4044ea00407a10194072050106201500c030200985288401c10f05074058101c503440d0010080002128009102009681e0307400098000b250980e207803034102e1030f48031041d0143d03c01080381c01c002c0000250f50665454910340b103060400b9800141d2403400c980007030039a0460401010703403060040101d0030071804001b0340000070340300046240030702e80c00f069103007070342251400c02d6001e000512000e82c5c200101108020604c12180b2015040b03502250000400e951a490100c1d00307140807010241960740540380410000d8415801583c2c8400c00d50980b6102c0d41d00c6031700c4d40054880d440b01c010700c11a00b07003a100908100e0002480355100302401d049410300c2d60140701c0103500c0f030781d811403e100c4850359003c5800c04440891035100104a05d8a42c4008101c5140c45100c441c200c43d8400e0024400e50006014440c2103017100041d1000c58000780000b8804d09000d01c098840107044d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 374168219 1250 374166969 374166971
    0x109090c031e0b1b0a12020c12030f07020606030d1d0a090c0201050105040b010923120303040c1a03061014040f1e03021f03022101060809070302030606060904 70
    0x40040030402010841c40c02900e490401c007050841424400c0c100f1201403d00225404041a1051200c604400315520010b050800020640c0300041100090240c0c403a88185d901403580710901e07488100c801513106640003407500180752a43c441c1260380b460b00f166096010360000200147c0390b4014aa490380000000d940022000315080125160728a140d01c107080d03a548070f0328042c44450302070146501405007680d0030048035101c0d6000800e4440d0742e02c6201140c4103900c4c610751244000281540b0f60040180c002018005440c45540c1c0d640d104450aa900c115450400f04402c8142e01c0d0700030002e0300d49a01241542c54031010030011226200747c600501c907086080340c86280102e0050f00041c0010f00031b80c00e00313030b141c59050754441511950070451b01d1403880b800c4c00145d0320780c003600c403864150034100c1c070424812900940003807050130000b4600c0380c59500103c80513103074584081e041c0c6940b03507140b0340300d81c55401c0d8669650000e404000c2d8940c2281001540303a09115001d00410500208 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 374169469 1250 374168219 374168243
    0x10204080c091005040903050a030c020a050c1e03010c0509030715080103080f160510060803040b0417030d0603110f0f100e1507050106060f0c030210020f042309130308010909 77
    0x10001701102d000c50340450201c1c002245140c1c4458040c494150310710194006816002007982d1802d0f1074541100860744145512242070900c202c1610b001c281018016000b08501d43e2980c0000c5d041c0d800c411502d9203c3d2090f001c004c0b5507490184201e400e5029513441d003a80c2c60f421a40c655100350081c080404402000b40315405943c10111540083c1c180107202606104040301e00500507036600343c20040c62907004020801140701c1e18001c03541264a0b4078030038002940c0e020801d40c00c6120b440b0314580700904000c00801841f032315072214121180219642003040902c201403f0110701e01c080d802e517012101124041c03071f030b80c0128042c940311040141402e80b03840160980780c5140d00010030648141e03550300000e000d69604070580582d90103c50600022898660794025030704c2d5154081031030403070f40200c2c41340305948550040c1c034050403901d41c804103012800c4400d400440c2c841c00f1114070481008000c111034800c40d43d20004165015a01d4519580c241350036040500360a500460b1b05000502c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 374170719 1250 374169469 374169479
    0x90607020d061b050f07020f040b09071d040b010c0b060406211a091b0f09090c010210060f062006091005161b020109090c0e12010204080c0910 63
    0x10000366003141c0318160000d00c1060b02e861050501d5180e01c0c500c418804c2c02c05c0010840030301d072815200300399411148081c0e81941040414068402101d14a401c1001d11061211490300200102c01080d990301d04001d0402101003040141c0c0d10708002c06010400e440d12000214000b014070303d0f0700ca000030741301159169450348201c1c01202140002c8071014100f05004080000301c1780c0409440c0c040210a00e02c905080c15140e489040000c0c00702c7d40010080e010800c90749414100101465009040d00824070340010b225032202d003050700c400d00502618200455103001e0788640e0069a41c001c50030b071482030509000b91030f10062150101c0e43c10203040b81c640c1901e00104691031140c040c02000c2c050715288620035000380d40c00a089042003501003640450810351205014102010110004074251120700050b204010140c01c6510218100541c036582d8982010500c1e6440e1010b8500080031000381e03440c54202c7c042c03400340c860b09070001d00f80b0740038038a031040090782c0010b5400c2c040d0020075511 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 374171969 1250 374170719 374170729
    0xd0201051b0d0f2303130c05090a090b060a0e150619030221060906132a090909051002030601090e0106020a0c080109020f1c0b0c03090106080d0c0809060702 69
    0x4600b90100150000c0c81030340f96158409401d64240a03140c06246114018900c0c403422400000d006405020040c0f80f2036045c002200a00700040101506040c0c0d50706008000801900c030321101a10b00c16101c60100c3e0841c10074a420f00121450340b50a0102a200c03444000451507031554046c1e0f00c00814400303d0042074a81c2c0c000b42c0540000c0c0c0b40160303503001c4110403045004001640b504514444001c0205540700d50305c2c0030380c1c0203504889500b80c0d0300000c16084010301d00c980c4841d0343c100201180c041c13011200383d149580503a083c0c84c0c1c0c1034100d42d180e00384410f0b10002240141550444951480102d581d50040c5800c480141840846107841c0ca118408001c2c09a1001d40180d00982081e0180080742d04014081c081403802441101c0082d00821341004d21050b02031301070310160180c0d8160f512038140b00380d140c03507000740d0650060403d403000b031a03560070640b101040e6510b40500051744080011b10040c244120307842c0c080c1450b184c2d07100c4590582140103c00d40107001000003100582d58 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 374173219 1250 374171969 374171983
    0x3050901030b060d05011409012409090f050106020c0d0309290a03020418020a080621070801020409150e010b030915012616140301150303080a0510050d0201051b 71
    0xc04032000417650f140010202404926a003494028800040140000c210701503186aa222101a48100d6400c0309502107605080c08c1d440a0f40280c0b07845ca40d207800300c0043d0041412180c5a50864051100c01e4040221002103401d00501103441c1610401c241c5100344000c4481c82201030300e03803070502c41c6440285826480f0304112400a940010705101114032079440c551100c0350000114100005184d001d40030040281a240c482c80b00c0e66120300d8100c41c20200c0d01d40c0b450441040e41e04080d0f492507014042d400c00c1c001d500031541014501d04540c05030310110030489150100300101c43e403825070164000c2d800907203000c113540540e14000b04400700c01001c55008000c91283c19081042c40740110040650718091a0744603080031416941c0e1211120030309003502c9040d50380c64400540c1c0400a8010000c02100310415a40800d0020606411140785c0f0f01c42e0458200a000b2a52101c682602500042c085c15511050107400c18016501c1940076003600303810b001c0c83c440102918000300d860501 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 374174469 1250 374173219 374173237
    0x4060f2303030310061d1320040f0303140c120c01150f150f0206190f0c020106030b0a0506100f0c0501050103050705030d21020c0319120e030c0a03050901030b06 71
    0x1c02d81804111a81e4010345c00c0c051b00000001740e40341c403810240020301c160b03800a00d01903202d485043d2a5440310209880b801030100c00d5042c2940d481d520309504499400302c2c4020b40100f005150f150081624000848044407000c9020780103451004c042201a070300f0414009815658440d21040c458001d4102440900300c0c21a01001080c54a02a400441d130140c46000c1045140030038002401d400089064203c2c0d907100003514410001541c0c1002410f40c003490003403240c2801007491056806622141c2520f00510a0801ca56128a014420384400b41d0b01560810781000c008044c1512a504503c20020b040c5841c0564189944519003958002c3c4c009403000d8004480811151030b0070003280744501100d00302245401c01021845460709141807110042503000074100e01d820100f130040b11002e00c5001c3c14422000c0410030010b00c005ca0540001c0046443c007510140511000015100724403803103001001c00c2d50f1940d40c102c8054002801d49414035131a43c1c5101c41507a200740240940e03007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 374175719 1250 374174469 374174491
    0x1110304030609051f2c0307081206280b0a050702030d031407030902090c030403050f04080705242d07083f0c0909090307050c04060f23030303 63
    0x45e48140040d801000c0354020103110500d000b5981d10701d0082c00740c0840d000742c03001c2c142154207010030305040e09503c94150010309030900001c3c20f8083e100240c00e081c1c010001541c2a40d400e00342e1520500311030000440c0b085210044901c100305070442c40006040ca0ba9443c9012030515585a000c2882c0218900700740011984a1314811700c1c407040d500340b003980510240303414024041c0710f030003080c2142c00240c50300145440002c005070515000d0421280d02071104102940d84030ba9030000203072201028012140b0610300b0801004007a00042c02041001e41030151032494000d00411074580c4812524242c8110000380340100d58020441c0f015003400c0303000d012095a00c0da4a66030858a41d02503003c203040c280040822481000040000784140100b003100501c1e81c0e48680760318041600900f5000c69005130b80b4800c1044041d408009032031024454011503c01246442c104010344040b13008100000040280820000d03c80b00320140c40e403d4010300d04070882c0901c4001c2411350f8030480b4043c0200c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 374176969 1250 374175719 374175733
    0x140606030c0405060a030f14031210080105040c06120f05090a0201180e06011209050115080f120a14040510030506030f060c120915040c080d0c0c050111030403060905 73
    0x504051040c00718041c03049404102900c1c01000140c194a01d900010b00b180284140e000100503081c1103504600da1003504403512107800814221070707600111005103a8110000700041c01423014021107001d2503000080810540c10124200c070310398045896540d101da114480304190000314071540340204481d801611a2000f14000074011203250038112040f11b002d400300308090584802c055030000c200b4a4141c80640034005804d0142900c0c01c4081c0c01540780000c00080041100c20620494070150709846008154180040d241d10100c4407007401c1032020484848194403e00e0b080280c060b4280c8034604142d00d0f0408103e002089400c000003080c2c5d180c042c01840e141c100410503540d00340324001c1c80c061400300b081c9085401540c1100c49202252408540d80440a011100341841e0710300d26032701140f50604051584002c0c51140d18618007582c00741e0318086103d036001c2240d903a040a21010304900c1d141c011245000c0130b040b6100240424007010001500c81d01070540300718094030042040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 374178219 1250 374176969 374176981
    0x20d0615061b0203030f070c031a06040c11150601020f060f04021804050d0e13050f0f01080706090e0c160503090901050d0f02130204090c0c260d0c05071406 69
    0x200400102c04451004444400d141c016900001100d6500c019044503546580071352030004d0004919400007008415000c1320096401d0084084500c0350804590500c220f0040701001e0384d140e66031281241f00b80d04500b0440d440c2000345481180c00001c180704458514061030042410072006403007544295204405100135440c040b94015001c900d040660340050805a450680d11980c8044201c14414240e014401c90303500d0070088000d00c2d4a6000900c20b5203020b00000200c2c4008841d4900601c04240c000f14070a03000003141000c0d1051921008c030001d007414144d8102001c0140440c51111042241e40c40b0407460000b0250201d20400040d5110b0740700c0001c0140070300c4142c01c106e00030381900f80401c001ca00040c06000040d9015900740742141000c2a24502074400c541050b040c6a0a0a2044259030340c030894440300c1d01e0203410408094500030700c0d9800051004c0d000c0ca00c401c0000e00c092028025183e014000d03c02c1d507820b00c2171500d00b0b280d642d0004030003002a03140181e0410420000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 374179469 1250 374178219 374178227
    0x2040903020f1009120f02060703052d07120209030a06020f04032a150c020d020d02041a0f0a242106090c0c1709010e09011410020316020d020d061506 66
    0x10030107007806d0144415403400340080d0b8600300140150101515103002c43c1100e0050402c42c000703a4103480d042c00003060503883d00169603100340c500d0000030303c44a040040c910941e20070baa01e1050001c0c090f000b00b888503190071019412000c148403800f003040000000040a240c1000c851000032400840c05502151702c0070004940e60380f2412444c60418038100410380d02c05d00344025540e045840c005007401c1400800d044010303c90340250402c3c500032030b03030761140d001d070a29900e50041151450b200003440c106201c0b25030110320138407001103074100d282412030013a80c0000c11000b801d840e040c05041940c0d240140e001c5500f00042d50206d40d50403060111700c11a0142d60002c40e15400c0600d96100c41ea40ca0646409443d525103d0004000c90004e200c0c0e1300c12901c0480b9602d0080c65903440d0350b10382c2d03480018076032800240c0b0301c1421005580d03107070240044140c814031100c001d42c901a2140940a0081c0401d4180c0c0413603003d22000341080c0018040d208960342510b5803050030062508001000d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 374180719 1250 374179469 374179493
    0x150102062208031e0a1e09080405210106030b0604240e090304240e180a09022d0102060907052d031c02010507080c0702040903020f1009 60
    0x4580010700d08094000d103200e0001c0640d00e5031100606582e41e882c003024034880340340041c4603884201e600051140c2a0f801e90042000b40b00050500c0c0910715154091900b2600c0f00c803070040448000340420450703450110108409080001c0e070031050f6010242415003143c0050700308a03032840d464401d2054a0a00d03214802e58580c030821414080302e0001c413403102c4102188100c082c91454140010403888090003614000e240f100f00f4903010306801100c110f0307002e0030f80750342400068500d00f011619180596034589809a003100000e62500c800320080080c00c0c200c1d5043c0e070810034a5164200c0c005da0341002004c0100c0032604890b02e56421000203084c010054031400c019801b5000c14011035560740060410450400e480700001c4020303480c14034680c0341400b007140d4035000e0607011184134a80c110f90101c1500c0154001c0205564055090310343c6c0d10192001503213900c080c0403810040c10960b010f116541e00a00407642e40581c912079140c901801140d00e844050740f076449c01010045000704034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 374181969 1250 374180719 374180731
    0x3100504020a081303030b150c0d05190f0c1a09010b01020c06090f0a0308120a0b030105040309150306210606080c03030a1d1008090606030138030615010206 69
    0xc0d0720701600d0480c000d0034410081e000c41e1300303018007200710030801d4000ea1004100308409491030399002c0302d402054580380c120b040d400d00c690161408803407101d071281c0c0c112000980e501c0000303c2c9007280c240b0111420600507070440c1c00d0129980c1c40c41c0200b004810055078480100c1c8104289141401c4001e00750740101d0200c6055511079448a2000e9031038000b502c0c800c42c41903503d541600d080030000b0740384101580c006401d46000180c1c101007101056400340c03085007025030500c907084159080c18220380044038040d0008a84107014405914400088890301001d803601141e43c948903201c40705400118518407203031851400000e010014103005200003082c81001900c03801c2010707000700c3d8507417050f800103030200480340110800c82052000c0e509000300c4080d0015042c082000c0000e0000041030f501d400e00e901c1502d00080c10b074a0140501401d03105610000c0c2607441c4a40c4102141000c201c160609041180001d94132580b01040540c0c030404076200b0614400c0031080019003003210203044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 374183219 1250 374181969 374181971
    0x30201021e0403021c080d020906190507051b0108280507050414010302040b0702060a050c0d09030c05100c0813050415090506010503042006120a06081608070b0307090b03010b03100504 81
    0x101d080070500480546204030005400549d0f900311800000e0f513a44a00b8114002c0c044482441c10000da0b0300001802000384900304455a0070718001004c40c03c008103802c00e40c001194500000c0984e28440201450801e5101490885004081136070741610707011141100003a8000c6010002030100c1c0c2d005251115003820114a400d082202482c0c4031b1051210280c011900050951552440350b03080310425508ac50a617001007105082c0102000b09610003522410200c010110b0039181404010000022a490b1010011080c0e48ca0700401e41058014042d2a0401da42c00542038032103024401500c801010b00302e00d19418905c41c201181c50250a4a04118040c000c1200141840814810400c4030942c03031a00400e500307000414500c106024180e0010000044c40445145c50b041917086d649003c2c2030380c1030102c02014050400713450b885948007e61000301c3c10481c40c09100e0045410640d10b00c3c00000e0280c544c996554281d100303a000b00c4000100004000c0219442200380f005484200e278 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 374184469 1250 374183219 374183269
    0x20306011403070302061308070b090f040c0f030b19030501050405060c190503090307061a1002010509030405040e030405040501080d0201060f1d270a0303050c03010e0f04030201021e040302 83
    0x20200e540d503001c0713020007401a1000071f11001e80c2c1d0611010a00244081d07822184056121903c11100341c0060894a000300703221003100c1c1e0fa901d01409003105220b03113035890825400030311204030b020382605500590041702000c2561812a45c80b600c2c1005513001d00c0001ca2242001d2a0403480d0210040a124503c6014014011414a00c2000049a141d186806074490302d40c002701c01e080d845030090080071305141c0f640880e0040c03c079020402500804071038440240449400c164241d41048801c00c02603001000180614a80383c0c3c007203440c00b04548216401c203520342e0089000c503002a0801703850f5a0202510390b40b034942c240038900c050542c20700349021051500c0b242d5601c0ca50b5540c07a030f40c0014200d50011b072121461907504403110b00c484001a8000364803004480e11060345400c1030340000d080c040006c040d01c000c5000c036412122000c8042c07060340c1d0342c0080002d0f043d030060004c07070865408104c07103002148540f070f440c17400710752113180140c0e9949184100101c44034244000480010101 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 374185719 1250 374184469 374184509
    0x30c0c0316080a150f0c110d1805041104030501021201081b2409030a0b0106020d0306080318010c05030d050f091501051005120f1806090d0f050408060f0402030601 72
    0x80750112160758400d4a00e4204e141a41e14600505070046240385503500e00951700402e55844504032000d0b0610300306a851070044071104840c1c21724580007142c0e1051a1035030400443c2032a600c03c9501386e450707031944ac1c01c058495454500703a900811080c10b48012400061000751824801c0c20f0a00f258000c00403402c45d040400326070350700300c9c50703c0800038106000340c1c0d200017002e410215640c52800070181d842c00c01d020b290110005c002801100010b22412030080c12141c0203204460a50384c6400055040201104000c030340c145401e40c0c07081c10041503108080000c0c804102600da0360780a120046968503040c0c0b0610105a401043c0c0400780d4415854001c080c2e08180b54103055500c282c403c4c05140a0152082c1c03841d11440500c2c00800111500300a280c403820501036028088804944148020980e041540e0305020b4458000c03d407c0521400742c00c600801c0800c4c00e9000701c1c1040350401c0da5441e121803c120781201c9011a10300c090b81004118a41400460b0150032850001050b801d642 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 374186969 1250 374185719 374185723
    0x11401061407030e060d05040b130f08070c0e0a06030204050a0c052d0705010501141503010e060114030403080f070f0c15020d02271c0201180305030c0c031608 70
    0x81c206000301d8000c000341d035a043c50321410b102460b41d00c000e08655611200300030341c6402030404a40665405654001055540384c2c0c0ca10300d24611a08200340d02c20f41240c1e03454102c6245d0021404403081c0c405050001a04110900028401e24803a0800a080c615500502040d100f0080079902080d1600081d00c007402c3d0490b06454040c0c5003031101c400e0448900c20b080442c951541c0e100603840f0004140e1404101054100b54140c0e80c40d4000340004a00140c00d003c00001c1c040403c0c03145c00d00034001400b2003100d030f1040e40c2e403111051400c1d800140d10b01024403160340c4143c405900080b081d0081000c0d4100c0724901a400c02c1705480d2070321030060399500003002c51016450052004000312110f00c10003003250107a401500d01c60801719035440005103405c804841c91030b02518007025000e40100f41c0e1804828803c550b06803141110103054541c1e004543d100741c01194250b940740710036004400729500300094a180d0310444002d103d901c010f4000c140c039066000c9030000c0380e21046d940920800c100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 374188219 1250 374186969 374186987
    0x30d05010b0c0d0c0b0a0c090302040e010c1b0c03141009030c02031e1b06090307080a050601060201021201050f011209030f11030f070f0302031603050d0507020c0d11030a06060902040801140106 85
    0x80c46c03002541080419086500308010b1344003941c0a03043c5040c2d072042840642c810ba156011030b45814504890b0713030300440310901d0f5504000e81301d0403040d07400300f001c15200d1002e440c201001074241c600d11100d03542d0071811510210000e900050300300350341e0350460400304120b089006503072060f0303410203404079079141d030341c9c010041d441000b10302c0b8600802c2142c68410503110740d5180201600c0c0b44a4692179415a00c40e10350a003500c8511500000048150041c0308850165204c00041c001a0b8208010320003c040e42c0301c18241084208074001c0310f132307081c14401d142030b02e0300c41d544200d406140b4000052203044070b400c8411217074004000c3c1c4248104001c044170f48166102100000300702490506a045004a43c000c802a0045982580406601c440107042c40c03d05000c08101d2901c42c4c140c120303607843e241e43d40d003034001322110014004107102201040200c10000c0403124100b901e07036228016110740c0d9004011141d00441d05111009080c09602100b42130231034004055854140d0040a0701c01b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 374189469 1250 374188219 374188231
    0x2150a2610090b01090321030c110703110a0801090b0709050612010e0c0f03090d1202040323011b050c0c010302030c07030503192d05010521030d05010b0c0d0c0b 71
    0xa0ba0720607a43e45030340945004402035410020901300440c00074012550b40001d09200300000b80340101110000d402450004801501d40d0300a041e070386c3c155500c42d020341442d59402c0ba8071106c24800010102d400f4040d144120784580554001c0342001c030806402c24650f604500c1c402c1c0720a001c159030f1030322103a022504584000e480861551a64000c920282c410146550001000001000107a4200250003014252680d0700d161241d07003200c0341c0383c00300e0145000040c25042006146c101c10301700501512142c400000000400d081b041003107016106e03111310420089440417a418101113424004040020340c02e007030951a41c508000c0c5d801452066560081c07e00502002082150051216050040940003020001016800380d80ca01d4005c40080301120a40c1020302d140d11703014240a014100e40e000303060824081400e40e1040d22010346001c00102902c801d020500021a031402100c1c028180440d0303540e510011241000d040000300968182480f4030612004002502c035107680354007030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 374190719 1250 374189469 374189471
    0x20d0c03120209040c05130b03040c0501030b01021c17060d1101050705070302030d0302030a0e120d020705010b090f04020a06020706120209010221090a0f18050402150a261009 77
    0x200194003500028003810b035109404c6850110707582151a08040100010901d6034840100c01750799120f0681103200c110790003000c1a820080401142d40290001018030380f050050303c590042c00e1004043e41440d95000c0c000042035408652880c250030640b06402c0300b0217450209261200d07846910650580f80703522810020005211800d10100780940c5018550040035241260f41d9607100074043e420507a8002d14081c0340618200000030000388003c05440406c039024100415140d40100940200d007050300c3e25521010800c94955500d41580c1c4696440c0c1c00c1c072101811b081c01403040d940b0080d0405d0066601402040c0140d0360001e041c4078031030186c0790000d60b4038684000102e041044075100d18505a1031010745120117441e06010700450700041e10000100303690b40219181040003072044490709800c03902405003032552134010550160028040e905e00040291501c4443d602402564000441400000a0041c4e44c081c809100348000d182103460b9042c6204c06da02c00107101c0c41072484017 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 374191969 1250 374190719 374190737
    0x20d020111070801060b1206060a0f0305100e130515040507050f0402071e060b030c090a050a06030506040605070807080f160e0a090e0c03210a05120a1b020d0c03 71
    0x409000c0242d68041d104040080c00604c0c0c1c4c42003080c94035082500e1100014a1440c0002e0580c240b180c16500d060505940710002413900712000e4000344009040c1d0803c0c542d0781ca001040340c00e80204c00e5801124075600e00c070f21000036030520074140848040203d82144a0780144030118400084240545800300c90010b40d62000704000f80c000c1c0304814000380034801180700410741140c1070094682d482c1c0120000e0000000c41c502701915034a4045826134040410700c0843da80c8000d03540070503030001c1928800146d041e10307500c0e0b0700d2801104686c21a44c0c00d8558042000103070340211100d41000260070009004d040403203108010220041c903070300d81001402e2816250758420300d98861400070103000d5040c2c00ba01d1303526081c040d080803125070505125600181c00241800142c44a03629504a5903020207010801443d41c1c540c03000c191141000001d0048086250155109a0041b41c1413040002d0b021141016211441c0506032502c0a54004407010000281c010070f0703849407942d141c43c0c01030700c3d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 374193219 1250 374191969 374191997
    0x21b012f0a0210080609160f05030c07050708030301090e0105060913261b030901020c06210112050f0c01050d0e07080f0610091a0402090105070b040503090a12020d0201 74
    0x242480700d0380c010354040d1440495024484c0c0211866004c0c103019210144596200c0c4144440400703c1da00070b100060a03500340d28510303803080016541000c00302140a03c1c0c4038540d00d07690701d05200798000c82c5907504004010010b0706214480d0442801c0c01d04000d0101e0b00d4090000780c5002c0c1c0c0140f0505a0140101140c8200554140c1d50032403000100d00300c0c8113620100d0585509908070104500d4010303250580d4100008001041d16040b6038164002c1c4803484902c41407041941014070111503001d074203040a029541c00b03d6420307001e0a40400b000140d002c076410b00519044e40302d2955203060b0054591903400740d038800200c8800c543d0344100480e9080b48605054602041d5500c020314a01a2001e200d4145001141c1e0f01d01422028003980d1895403543c071440d08031104039501d502181d4400d02c4028950600d0340140003101d03414103003a0705101036611040e4040000716811111504001b031401c0306032800801744030182160311210140d0440540c04903001b01400c0074068140318842d802a64 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 374194469 1250 374193219 374193223
    0xe010512010603050108160f0b1b01060e100e040b0601180b0715060f060509040903110105040501060305060a0902280308120103120e09180715021b012f 67
    0x10109446140300c21035039440300300900401e000e0103100c640780541c0c10344003020030500c02500700f9109600030400003d0703d0014464070b240e10440c000b200b2580d40d201c240d00c9000080c07040c0070003420024442c4040345083d001c40300707000c0d40c50f422038030340140c0076814000495200001aa400782d402c0c00c140b44526a0300b0b141c1e0385c0055440e441740c01040d82c0080d0240800140190248181c140c0840c1880f036907898030a0300c1514420741c010030b800224213020803822403526411180040b40070303080554802119803081402e4520841e004d0321721b40e4544000300200042017020716481504060708100030007950380080c4028500f0a50340140d2103801c600072040d0754100781ea140080d5030051101e5a10b0a903803409402040c424401500d0380f0400701100c0480c1c1c1c1c022030581014407002006170a41e592500f210020300784900c40094103501c118000441c40071f130500040d8407105200e030003c3c101005007440c4585202c0040b400035041041220203211603442c1d0100300d0b644a9455240080c41c01c0e9401c02c014 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 374195719 1250 374194469 374194477
    0x150313050c0d05011e0c020604030c0201030b041b1107060507150e0d0c0c120b0c03100b0c03040e090705010f0f0c1506060e0d03021e03070614010819020a05010e0105 73
    0x142e00207429a0480100481580f11401103482d81841c00301781943c1c4401982200c68200b03072480560889800140020310916407011060300c14140004d503146600045002c852200068140e101b0190610040c0240c10082103003030340780140700030a581814954002d00a0040b19002460000b4105100101c010070b80c0181d1915100e0004a0300c02550b261001010751805a20541d0302c0c2441d02404036400f040c801d61500b01d150801448209a11010501e841d140d20040100190980880000c00c00141c280000c115680500006640b92802c064042c0c3c00e2140282c0b280c14240e00c96002084140d030480101c0c130840c02142001309815003000c606484100b40340c10b0007001a01003040303040307200743c9560203a0117881082d40e072100428880030512000b60742e42800540035034424a007411103030030200000f46d00c03031040c07206407414503c40703507030703100580720742040c10340c05003c4000040c0441c60703041002061441b05544100d44009503a00030a5801c0460301030300381041500c001c02c40c8641d004604031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 374196969 1250 374195719 374195743
    0x3010b21120d0501031a040206040303140904091b050f030a060903090801020703022406090c0c010908031302030c06480105040203121804200a08040209010515031305 73
    0x69521022032075030341c0040c0005d00044845100a0001d07150840e0341b8041d00c0e00c580e5004d040d091406056840940744a042240c00003107500003042908216204c034080c401c5850710503003192400c4003408421400461850300440e01401c210002c1e130803141c0d070000e04911120381000002400c12001e0608681078495500f00202e950300018130342d0109540050402c00080c12020319010322400706096181d607050175107a1a51000b00b00c13021804100c1404010201c020000f0000955400e59940d00340c0c0503002141d007411007a072540b1821081d41402e1100f05010780c0300322120b62828404400381800071402011958610929218802500b03404142d01e101d803681c60b02b00c12440d0019030b5041c0e406014202c0f0104d003e40184041c1c108440782071801c2da84100c403850000c03660b03d10704205210040064a200e51040d150380e00040c11603441420007840b00c3d9049548801261502d401408191181039104d103020b40e1000025010261523442500d07001090101c03515180c2c0300d6807c0061400c0a60340790 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 374198219 1250 374196969 374197003
    0x30a0e0c0d08030403032901030f0b0a0b04092d09031b051f020301050d0201120f0603200105071e0f02150405030610060c0b10120602040503060603010b21 68
    0x1c04414004038001a6124510958050040840d084200c0e182008a0f01001c808240d818203020820344c065007141c0c02c1103e040d00d00003200c44482d40000c0c0120701ca03a22060201c8000138041c0103034185070141005a40340341030700d819009036012468500500310f4962019851f5641c40c49010503100d10514000b400144041c000c10007814185183c031225042614508801c0d40c0c00c03403001001c0c0900a0f40e04942c8010403000395103e50750010740e2a81c1c000450b2144480d030358003560f12042c513a4450344028601030251546540701c8025140707040d446a0141d241844000c2c484503001451040c00759007213200311200f250340180300b450465596010080b000394000000305a6000d04a20311010384100c1c4e50480031910795454040b04000d1504882c044c6000140d030354000c10010a0b400280d05c2d810400e085001003030300c0d64a1491110040051000329070301600010200903a1a08002c0242c001000720020000c400499000480440d020760780004010b0b44103180030f2100c0c1c000e1155540317180314150 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 374199469 1250 374198219 374198239
    0xd090305180108150103020c0f060108030901080a02040b07020607080903060c031e0105060a11190302060406050105091501080a0b040203040c080f030c0d080c040b1303060b060a05030a0e0c 83
    0x64050400d810030600398440344101441000e89610440069008440555003100c000b040705004501030752003001c1c1640075214880c030b08400040c080200500810703245001d50344992489000406802c006030400d212140140420b019490210044502403a41222071031340d03079042c618080b03a803030088400050f818003840c0704000954900000851060451040c800911002d440d03071994068402e02a050708144140400c0c44c219004491008901802000315680000d85401801041e6181002180140c1100042c0010002d0f01d0003110b0140404035415404d41c035120320140c21040b420140d4504001940c40810b80d08101d40e800000035802c040d00075981e9251a0801c010144200e20400081d44900c1103c8100c0c050080151000034100c071001e08107240019204890b4801e001e03140401040c410080040d0b0903541c80018066007606004080129180d4280801260080e005a6004450410643e0b8480d9440800c981e480410040000707012859002da07140f074a00c0c02d03101d09030010441f60b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 374200719 1250 374199469 374199473
    0x1e0d0b01030b0115020a110409141f05011206050403051c020c0601060f0203030106180e04060509070b0f070209041104050702061506390304180605190e09030d09 71
    0x1492030599018800c01d00e140d90313807180d60491401c1c02e1138240c0c0068000c0041c02c1c0010706c82c00c5113010401001003004c591710600da2a0280320041c44070341603450b07034042c106285110680d40b461070a07503088048100a41d40c9004002507440c02410030090806940d10300007410180610306552550010011201703402e101201e81034000d510001d400d1210744941000003074864421340076407100c000681d0155041d43d10b0070078169200c0c030040c40401d83d850000800840c07865008186c0700e01c00c6004c3e00021920f4281042264181911a00240c0450720f042021f020031410720421100ea80d6815150900160760304e09100c042403151340f03005a03105041000b400402640000c10901a507800c01012503085c803a502000a18400d414001403003085000c001124407610751246070241d000c41480750f00a2011010b114210703405500f04175000309600c100101d55650521411018000c1941d02c01c207180c52107001560104114443e0340c001d09501c00000d1102001070060328200340240100b0311201c040d80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 374201969 1250 374200719 374200733
    0x90b031009060b030c0f0304050f030d061409060a150201150321210c2007080f03211003050114010512161a041707170f06061e0d 57
    0x501c81c202001c1d081080200300e6210150403a401680c0c802d0341c040c41c006036440307440301c1d580009005540c0781c081c01200706d2005030309000500c0c91501d034090000b8a507041502d80b96125080001c020700498401d020000f4903299181007000b5260701b10000c1c030110308262400c80c05003a6652011003600d131029000000c000a42c80b051040e0744005101000c61030314034500321200014040d4945900c60b05510010036201c0940c0b16110364230750703483c003007608140320030b040488040d03510b4410115030300c400d40c20410b450045c0a44080c00080070003079450b100401d920500c441800225141a4081c0031011032a1010940801402954000000d101c018441c109110b6601002d101c0e945c0600d031051503c0c0d0300c154010980f0042c90b01400f00d82600389003803080c00c03810101040341100c4829001c000100302c17419002d103141c200740d000d10010400e441c00c101e07041c0303d807140700c80114036181e01c807284014403039a000c40c0066202c082074a400c2c08802c11a01c007040310107013a83d10309802c1344101002509014507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 374203219 1250 374201969 374202001
    0x501140117150d0b101a09060304062307030501060f080a0b01021f0b01140c0d120b06040e1602160312030f05070f1701050a0302060c030d02160b100f0312090b03 71
    0x707041941e91b4116061060440740300d603050150080051611f607107883c6003d950014002d110000f40e2000c107503004c034101d100d9031034019140912a810000c945606000701c60141840d03140c03101004000c110098000b00d406040e02d965a9203c604a801c507900c01c104100603070050691014441c140002508010600c45500d10300089075030f80598901c00d00715003250b500f14441001404000c04008088810280e4404011006926501000d16030390301e40740504040e08845084100714148040c4044201481100910544d0003440b50344140c2c404a800c004200c0c0d400c1100241180b00140048001308101e1044500807484d103030503c04103a504c8034107803885080586490840159002d00401c040c1000d203c0e0302d900c904c80300018001400d00c5070181c007802078403408aa09140000e4420426600003c4003103005c0070781c0d0507019090100041031913030040102002000b5007820958070801d921140d02000c1c02000f0b1154044d2003061082c03504400030024414040d44078100940441c058103d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 374204469 1250 374203219 374203231
    0x6233703030813080301030303150f15030b0d05060f0a0f06060c03080a200c070b030702011e02040e0103140a022206080c0609120a05030a050d0501140117150d0b 71
    0xb4210300040c0c0c2082540c450000310301d400500b40703030460b0310310354040303026000030b030790f000360040c4188400141d03c00205490405841a0103103240690f0312654010200c50640d120345202e24900400403000c62800300c2c085411121032100c41060380e40b90030400018110511640e0003032450080300051b0960b00040c20031a05100ba6101056515801c5812094074004013400d01c11036860103403440800d40d04001403074420b80c140c0541d580103a9030050703100c00d504206d44610160b5101c01001d01c28005101d50500d508038440b10450905041800c80300c030345031050000410041007407541410400b02001555a403e60007007128000c0e01542c2100c403245501d207050340007814206200451010000b064906011034040c0060303040007404020080500301d00f40d518032103400f9005a000c003051043c4000c010011003500d449540b402d100c1610805c90320143d20410b4910000002a5020782e40170046003243c508804c000a0075481e06500d40034511074808405500480c0d0b403544800700600600c0c1c1903c114 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 374205719 1250 374204469 374204477
    0x2070c03290109050906160c0c03120807050a09120c0b0a11060c0a021917040b07020a0f0e1506160501050a0501080604021c050102040b0c030d0623370303 68
    0x790f80c034010702050315400ea40c1c00c02590080d000140e4140202038100e59a800240b40c08c464486064440034040c01480d00b050700e4195009084215403600010b640e5003141152034a1464508003410003050440139020300000940004900401d1140015510016060100b1950703a6503020800c0600400c41b40c01401c2d00764010440021402100f60003910030862180c2c010740900c1141007480610f0700d0440c0c0d4111040f5220b00000da680640d0980030704040c003940700905644070583e00400c10203664603802801200707001103052060140e590382c0c0c980c10082448118074602e0031040041c05600a0f05100c0076a100b12100000900005411160048820040801540e40c851143da602c964017250040d42124207a0758286950444c01100981d507405100018186a11500d40301441d5020b1224220540e0020950407464030f00c501c9400c1c0149003014003001d5440f03242c0ea8106c401d544105410f40701e42032100c90754142c8807059900c7c40c0001200d540c0e41103000851078102603800550b000641c002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 374206969 1250 374205719 374205721
    0x902060d0b10030501050310090f0f050601030510022b0b10020709050c0304080f0c010b0405040f0201032406050d32150d02040e0a1401060612060b0d02070c0329 71
    0xb103019114440c162034010740501040c1c4000303036000300a000c6100c812500040703200c0d415404140344003042c180e581e100d18003a220175403450401c0d900d05020071150400300c600c10840c06455a40c20780b031185602c0d5650300d482072418030120108000305061003102e5080350044403810360a55011507001c0a59400342400c000503150301c5d43c00d50340750000701c42c020907000041189405200184015060000c521030010070303042c00741c43c00b18094aa0a030780407070780404c094100710115a01802568203d0207000003122030440410003c50b5007440c07510681051041c00035002c11421020703004005040b90b2410f07481583d600c0c4054046901c00c208444000d069804c00205c1d500c402d00b403000e01c00b0000000c05ca420320031819000c120042c84000c80e01c0310644100e480c407000140c1d00350003440e4070826000001400903d008000b0340804802c1500c00822880e1040c14004442c021003035401008041d540141c40e80030500d08619081c3d100e400103803490016191305541c1010340c0c031040c04816102000e8807a1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 374208219 1250 374206969 374206999
    0xd050606071403090415031a06121009060c0c021503130b090304060f020d08190204082d01411014060f030f250509040c020604240902060d0b 62
    0x4485050000900745640c40d03d650b48550341c0072000d19080b250045c00c2d20002b4054109461400b00100ca110003182e803070300c4400050003000d128101150720310303043c0140500340c1640080c880c03218002c0b40c107400e00c0c0d0200c041006071404800009203654883e80d81801d41c1044036007603949401c58401c00b40042c44042c9250700140c404105124a03e20701d4503059125124040110b9185100f21030728a40b05600341b0000446030310400005a51048209101030b90664100c41c014402041c111100340980c1410004000c1080083c410a07414407030586506012182e6041c0d0710049240034000780707010720b068040c00390052801d1980c00c101c40388503160085824080d030911203140101800c92003080302c20300024a0182402414a43c0144081c1c0003072082985507041d0b0398012841e81c00e8000140300410201624141403103014900805400108103034070b49951107501502c4034405002000c8007a80b294220b913206500559101a030041605484095050031000101000711407a8420b81140070b800c20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 374209469 1250 374208219 374208251
    0xd1404050d0201060f0e06030a2a0e0106170402190e101d010303050c070b030a0b0310050c070f170a0c032c0d03170907050306011a0d0506060714030904 67
    0x400c82d034240c5d00001c501d5103010b0006001c0e000041c03001ea00340c001c098840c40050403091000864200c00d414408100f902702a005e0a203540540007a2000b40304400103024a0341c101402389802500458000c070a1341d03461002c01d4600c03000500d40f81d2800e000100100c0c00e212501921b5101d600c000342031581e0242d44000c03e8802c04800d41e000c1c0103103003c0d500144007182c410401030810120b014121184541e5614207141c2a50048400b240c029550760040c141614051001c1c040025a040091003d42080345072170000348203071940104900c81d001020070820030174a00850140915201060b15103c102d500a40810010103086001034980120020040c1a46a991000c095940c0b005074810300d000b014400c4001e5020016010b01c0007507019040131007000001c49202c3c00d030000244c400300f0305d8a0145841c098040c2c2109154007002d03407217018005030040170381e800c4495034175001c111600c5a02c0812032910450401800c003981025189003200800001000e41d140183e40411402c684039040a03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 374210719 1250 374209469 374209481
    0xf0102070308060603060d05121309020331060c0c11010c210207081204030b010b0a0503040b040807080c010911100c060230011401050c06040f05030d1404050d0201 72
    0x901007520000403d0041c207082d0085c0d070f40450060705d180b02c0c00d41c45032601c600c1c0019984e100e0108440024007007500c85080c800c09030080000007019800c0d400c1c1b1400340c1c03d0501200b080034208404806510040900f15010082040e0300020100849480f0300740051140706c182206480103407c0e2100d005c55944100c503030000c10340e0002001403821001d2040d02403001080700b00798045110700740002c45d03843c03000d21090b07036031441600060303507140d26510b030122140713a05a101d1204000180103201340e46800908403a4013740c8590380380c141e03940d02c1c50280320398050350201400204012459462030b81055006e007000900800e080d0b42015546000c0041440c2e40352850070001d040548a080062040c2c0c02403c100010b161125007241d180c500d51411940d80c00345000c1030803a000c001004440300068520000700700a190442c5005005181103694803805030000700b94100420402c0140030303060007030320700c0020044001d2200d0303860080d01c048401d85c00d5905844900451624440c4c00c0c0c014030070340c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 374211969 1250 374210719 374210723
    0x31e0c03050609150d0c1d100803030112060228120b030d12052212030b030d050405091f170601051903031b020603010617070908060c07060605100504080f010207 71
    0x19105190358203051066508011748116500c0e51004408611000200443c2025642c1c0980c00c0c4042e1908443d4816501826842444180c00030001408150402c0f568401841d800240269480c00701003c00494010540303000e408408a4404415540d64080002c0f000c40b410380703400788480b5035154105030b20f58244c1a14640422071850150840600d40d400c10307640084941c2e50b580310700c0c1800c140019140c0200c00c08481c040750160b07904072196014422200ea150301a40200f40f43d1454010241451145004992185070802d001855890084604c1940d808040c2e51003c03a46980740003500501961040b070b20b01c079000b01c50021625007040a40000d105141c0705059282c00d02d141c8080c1c0d4041c181c501000050b54640c070545000d038940200950090a455440441d0301d0300600c0f4540000402600240400404541c100b201400014205030400c1c5080901c41d41d5078a645494030003443c5650040b50400e5400c0d100500d01d540000262041b50007520507a91a4010811418201e1141c8400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 374213219 1250 374211969 374211991
    0xf1203051602010e0607140c01021b07060e06040e091c020c010905030327010203190e0411130312110709060302090c03010305070603091104020304060b3607031e0c03050609 76
    0x94807003841f80e000310300c0c42c1d43e40d02d41c1c907860302c0e40903640c0c2401d81c0e000c0d0300c00c0c10442242c0c601100e401c0b03101300300010040580b0301d080510b0200e5000015824403e612408140f00810740101d85c0120b41400f0744001e0f00c88040b851401415030b10406034a4050300c150203408903d910783c0000b1103003004007c613000c422075044a0403200c00300d0b83c8281044600315115074110711007401421001008034400240c030071003a49500d240900c1100810068450072030f40c58100c010280102c020606400301340d4801da0340d00c010320400d02d160000d41100c00c08200c0b00702e17462178860400001000095a400002603d0098803c03000d242e0b65032a0703218541c4400c0c07000510a41c0308900c108000c42c466846010a50301c02c5400d44280580385000030141d810580307042e68078954610007400c481c50048598840c44941d449590446401c0c1c051581c041d2200f00c8401d0744003e0044002080940301c0c5c2c0c810203200546010900c007091450503810010034000d04200042854900856080e01d00a21424840e000c0842 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 374214469 1250 374213219 374213221
    0xa0c0611030417010204050d03120f022821021209030708040e06060f04090e0706030e0c011805030a0302031909030807020103090606240e09040c120f1203051602010e06 74
    0x2043d03000c40034074440c00c1d440c0c655080c00003060070355400841180c0140642c4d03d05541c4040076400004a5005801316500ca82c410007101d000004948403094071020821449010690a0a03050b190441e001d80d4285080c640c00100c01070180c0c00368050803100c821840d18804a90721405126900d10420340090580a018481001103540081401ea40184080c103410300340150b9a00c8601d01c1c0e00190003100e01c0c0d41d280e505461005004002210045c845407405104204c0125204c1d40c8075001445002d0402c00261500c5020144080e03080f002054003400303c1c2c00804260070000d4803034000c6450801c560b9030750103422845620a12102054030307000050b4510b40507443d1b006400510000200f114500c0c1c95103400a900584950505854540240d8510021039086001403204102c4e54200d480f83d0b402400340008039000325841810b44120711480c0030542098200605081d030b0103131004001c165030440f0b50251580c1a001580941001035090f403044480d144260b007030760b440d150211100c0d4010341c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 374215719 1250 374214469 374214479
    0x7050102060c0c03360409020105041202040b1206010e01122f120705010f0809070504020f0f0d06030b0a0c0e13020708070602070b18030403020112060e07020a0c06110304 75
    0x100c02401c1400010003243c0c945107084105c1e0035420080904801e040e1528645410b00080001d44c1c2806400d04440400070741d03d80ba80042c210740650700030401500008090601103480e1684000ca21440080403284601c1100010580d2404240107140c200210103000040a40080c00002030250b407140d0505412150b0459801340c140d166101003110065003204c15020762a0f4448003075400b003c1e103002d8180282000000b410203080031f0300c00f4003004014030402c850aa4082054015180c0c121800350380c031400d0000002c600c2c01075020301d484000000136072828141c4c1503488803048034440c03211010130b541ca0039441c0048071820f64912003c6031440850160610b0312210004010701c00020040c03c0c03900940700c005035030300020005c64160f41e0004e090780034400c1c20742c2508c2c0d01142504810f0301c0c0303040320800140c8034003c82c84000c0c11f01c2080700c02c1221a0801d0380002d0003514607061a501e80e0320300303128002c0d955120100142c0f9802031300350340850031502c680c8420f80e0f103200a1006528182c604 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 374216969 1250 374215719 374215741
    0x3020d05091f0314011a1602010302120901020703120b0f04150812091f09060305040201050405061603031a0f0f1305012601050709090e1507030e06090705010206 71
    0x9055958402030b0b03161039142041c558040300c660940310350340010300c0281d0781c1c41c40113061106801a01100305504c801d40c5c06d4081000440784d83c07801c1a0780e6142c10081920041c0c020380102d00d03c8001c01d4900c6001c20422000542c050000c9500030740d139a10303135904031400c0041200c0090b00d149400413910795032805c1504185d000f8228072451504201355659880e55094102001100b244140d4480020f07003180b2032034041c030644080d48040742042611b004018018081d4040d0744030f00b000749621080020256070280d0300f564001c0070050160b50b41e80e0b541c0d00c0c9800f441030340b9103000c0b0003003498002e8182102070140c0b00d443c88040c002e0100441c010b01c6c0b0040001d98514071030a0707544035a504080c40f104514074001e0f14000c0c4401d045030041c0003c0c1401c560011001c2d203a4401c0160701d40420030146a0b13000d003a1404481c0101c0300040c403401c102c6880ca050800074000705484030f0b4070f0414000640c0c0e140e130000800c60007040c02d44013039803580c00f1081d40341d83c6584209030040e480707032004c00d0190540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 374218219 1250 374216969 374216977
    0x613110d210e1302041415190207080304030b0702010c081b09030109060e061e0f01150309060501030305041e050a090c090911040e0a0b010f03020c0c0306010b070c0e0403020d05 78
    0xb42425071851060200240d148070294000288480d0040b80800900c440d0000025500500704c6084000c1c10410400d13240501518040c24401c2080318140b4003440d0090184038040d00146040ea0341c0d0f19100d0500400c1d603001915000019840c106541403048c1c894540240580220401c40421002c0380c0060074054120341a0140e041d588c8400610005030720f8410184641e07280c0300034000300e10304070310f9001c0701c55800030549500c0b095940c10402807000140d4414155666410711106441110304210024001120020909454100040305145e0040042d10071034910381c0c008078a94880006c0310281841610940c0c3c3c200d05100c0050104400540000c034081e68a45048181c05640b00702c5902680c0c047c58446241002c000b90034031412a440b40744a0340114090401c0c0003140100c2c000074102c1e01c0600c0c0f003c04159010490b10300c050414090031480c040700908030f820395611032031590342070350100c481100e61262400d0002004104000380703c0c49581c02d038024028100301c2d1001911507500c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 374219469 1250 374218219 374218283
    0x4050a11040b04020408060106030509030a0903022e0e0a08190f03030e1603020f0d030804030c0302071d06180108030406050705010b0a03050a110a050d02040e0f0613110d 75
    0x24885040c486543c503076101600040c14100010181c5514101c005011503501410a40c001c1d0810040c403042c80d03402c900c0280c01c40b54180c0f003952500d0b4952070030010345010404104081c5010502d1480c48075481214868165401c5410ba9078180e6503c3d103041d600c0164416201101140e1244440030a020282c0414190300074107011915140035446241492485809055280300089041c03007035080ca42c03400550150280c40354400307011240c601401034000100000d04100d405100241054400d00420009140090007590381c4405441c0300703034403050304850041c0680c201891400515400796100360403614014055803404e400c01804075180da00a02c400d481564a511400c0d03402e440361107801000f14058000340410075102c6c81d28252100e80c10f00003611656941f030040c86103544901c034000c510f40c0c1c101c07000200d44c219045086e0400c440d003012416103001d80420840702d05101000e200b00188a41c81d00c40f00340c2a1042048103500c08440043c000510561000c48403010414404106407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 374220719 1250 374219469 374219471
    0x120906090d230c1b06090d080d0e0d03060816030803130609023a050706110f0706021528020a03090203070f0f06020a0b07051e0301060314010e04050a1104 68
    0x38030600e401a840c3e808144140601d502030300c041050000c140400306200b6804540c4203160509442c001030380f043d103801c0080c200703410000f50811447c01980c4039441401200040c2c40b414002c1890140050100388a076142070301540030005c0b0b031500c1c502480d0041e40d174804081401e58903021580e02d02440958001c544841d511164403001d42e44125003408024203850b50102d040c080b031500e650000441585002d2052554882e110011f20007082c0f800c181d03451450407141c600c00200c6041d290102c400505002806a0240455166808602c84043c80c44101c004641da860f450110142e4250b00315038030110224105c01d00001c1d0040d83c00800307528405103001324180e001a0000303410503119a110b0b21b5403c64501c010003401091943d842c00800da203002402001c3e21030b440d900d440300802003c0404110f800544060400064180d044a240307100400540761742e1030b9540540180482c81c440300f0300b000800000140401da00c4242d504c10b5500c68043c0c40c01c1c1d206039860b11100703901c400410b5405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 374221969 1250 374220719 374220767
    0x60723030a0204050f01020f120d110c010f05061912060609020c1c0201140606070203070308040b090301060f030519060e0a0602040320090c07080d11120906090d 71
    0x44410000a14041c1003803140c016510380ca40000c1000429000c3c200138151b4001d040020460780c00030901041d000750b8544070741e9803103540400c040003e0501490301d00b0340100124041d10170400552000458250741402000359481c0c61f010850038200281c104800310741609001e1102038a040000307104588501000310f0900d807500e8526042c0e070001060401254030620507040c52422105140702c80601600082026451245641040700e10080019000c1c40d030015100d411500c040105c003000b0340d00411a940c03039980307a0184200c55404052824425030130400c0200320a0203c40410084913400380050100309c480c980d1603540041c040340162642a40c0d1034000340c14140500c0041d00182c803c910042c0d9490440c580719461302603900f110180c8d61201e040030b506589138405826001003205900c60f4842034a480c10084507c41e642a02130000c0c10905c6049e042d070300386000707841c1e107011a112a1368035654803040f40e5600c90040316078803480d62000215815a500910300341c2102d0540c540641d1503 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 374223219 1250 374221969 374222027
    0x30209131e031701030b04020907030227030c040c080106030e28030c02040507090906090c0e010c0c03020d080c0c04360c0602060121031409030114240f030607 70
    0x209038400d90046c1d910b8140c001c2000114075081d040c0381d500c60840d040450801803980300b000701104100020100008003458071408a98042000308000c020081041c0400000322100610030a4207118403000310f0700b03241080c0d0340340c003010503d4649012407040c0316008642c4406100350080f11860143c0070f20050362140e01c05a240e600074144103550949600006d0f524224664080b03c0f91503000072802c9143c01d070340034011548030b808200c3c51542440c00d000170080074209078900390b84950009601c145a51034010821082d42d001c2d0101c40981d1094845a900fa002400b00344d030012100040d080c00c60300c21b8202d60b040f460400c0e000041050801e01c41c501165a11031085d11910f0304a000560300c604010480d084c010002c00c4281c103c0c01c0b1245161052941c0c01400c00e40104450307070005d4102240d1035449031025031044c003881d89804540945401c103415250721058030741003080e1460340c0c8164036000f00d040001000400043c058010700a40c1c0c0ca259044415108001d94001c1002d049600141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 374224469 1250 374223219 374223257
    0x30c0307110601141309020f012106090603060c0e0a051203070519050f0d08010909061b0e0a060203040b0306090903090603090c040b010e060a0e2107030209131e03 72
    0x2010b0200034001400b081340740310130071244942e110b80c20128141440050780040e110b20507940450072003800c0c120344220509c1e01850845d115101d00b8141c1600c0d00c9000211829070b600810216405902d007009000d03641082101d81000104d40d45421500c6180c040066050165100710030401010940381450415a01c240c2010240f1101240c94800306081105000c024800356480ba940d450090900b804040c5000c0c081407030510a0b4510390ba03542e4141e805000c3c242d0044e0091030002103548035180c0d03030a24040d06d0b080003003242d01d00030140c01002240507400041100d0a41b04040e50241c15559120100308010f04020070801d8280814040000b041d00d5500c0554000c0130401c01030082240d03000140012903285050250400c40e40120b0042c154030303080102c603210681854141e201c065041e002c540710b030f580c0c01e1240305560a00d070440705502c0c00104200c0c081e28403c480c55141d41d2180c1c1001c020141031800007a0034050b10351071841468450700d881c0c04000340310341000300d0910744c1681492 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 374225719 1250 374224469 374224471
    0xc1a0a051621080123010f05030919080a1805030703060b03030f0708180a03030804030807020c060318070e04080a1d0a091a040e19081c0606020d02010908030c03071106 74
    0x10b011907000c8006100041207604100c182c00c1117005060614010480002e0091248044500a202000000c0742c0c40e128140f180303100003003005c07040084140175451f100311698044c00482001840038660100c880003d91036031800c40d1802030007007a420703086889040c01402d0102510798541310810800d8050740c0007502030300760343d40078600594540d0400018034603409190105584500a00c0805100082e081208030ba00715416140c4054203684040041e803800c101d00301d200350320450100402c22030141103080908040461410b80b80520340c2d070f02c83c00c0800501030b00d0080010205200142c0b119101e0350401409004074180d503124a07917900b000c00c0c80350045070802013031640c588107031000f5082c00c0e000c0020400c0c010f442c10864600c2c0001c000e038690440d012400010880418983c0c107005000701590722003e140c00c1008100d084503c41c0d41c005010b02d1113800d001d401000380d00340b03c107801071190b038100c47e4110b00003e00d5550382d11407020f042d5100402c2041800381004048035100408c002c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 374226969 1250 374225719 374225783
    0x1061a09060c1504231f0f060e2703070f0c0905041a01081603120c0203030c01050106080f07080412140706090308130f0609030c0f0c1a0a0516 63
    0x9981e0f0703414075041c185110700180611048040b00b40400140b500740c005510000d2000c1242000041000588900b016000c0c003540c074281e160078040d0226024038164001409a983d901c0c020220710403c1003070a00206403000036004c0c0b80c10600994021903002c2c003039600031511400034103204a46030100300040300c00c181c030145c0d003103600c4560040764600c50101842c05040714400500d036212001151151a401a01000340310f40d5425480340b401600500200c01d40c0355004040d42e4440740451482c0c3c1c0200720034071542001035010000b0034141c0314000c0b40140201d6055860040a03034841d1612865400c420808104128100c0000351040c5440c1c006030250920070310011600d9115400c00801d04c0d100502525401464582c00d8000144942580b004040d030200d408500d002c0c440c00d00760760511101102074410040e081c000010030480045d08019a0904404204182c1808904c0380300d034003c50a440002c500d0400130900001c1c25111100003851080d549440314800011103207034911055120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 374228219 1250 374226969 374227003
    0x204020a0c050a0c0801061a0319020409110d0b060a1b110604080102070c0501030204060504050f030c040213060206160504060c050c1f110307050a080a0e15040e060301061a09060c 79
    0x130600c50402c00f8000d017030007014142e00e602c0d0800c0450707000301040d12024084503981ca502102d09001d840c119015100200040501040314000708866000c45600001400c88500d04d402188003061404000b641c942182959541d00421208044100003075604141611000109480e401c401d6444a00070406008100c00240c1c48220302d10f46108400b030103400a07414180140004d1150f25031207026541243c0044851600f44000381e400b00e401c050300445660340260001450900d90140059400c0032581103608881640c1e452002060304412121a00f1000900c20002008500c1c0701d8010240c03460701840c10f035a080e101d010700040ea003060f103485800c865619110308c410099041080340010000780406103181c200c10f581c03456165154540300505007040400d40b4010103208000c01e402300200a0f08104114624004102c15030701300d0b10070f00340e4641003003001a840c6d04040c01035400b1209040c81c0d408101c2100c004240711500402019034000b4001d00a0400c05802004800304440e10054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 374229469 1250 374228219 374228243
    0x12051005070e090f01030b131e11010f02010204050d0204020c10050703050106091710050709080a0305072d380105180f060f1f0807030f0603020303070204020a0c050a 73
    0x43c4800414000e0030048980c0f003c400410110f00c40b104031982c0074500042074080207030949801c8089101c02d0031380c2556804400c1c04030741000101004d03044401f000f62621014600b043d04102e00740c1c8074500a25400a50001c0d03040c0c0182419000b03440405c0340d0f0000c3d100f4040005942c0012108210781d9940001c0d19000104100c50308041100701400d440810002c2051142100310790b10300c00710000001040e07440e0000350301a48122003110240604506580c2d5000c80d03070900400741e41000318182c0d00c4940c4029042c00819551600c0b512406c24410702404210040d1903491420a005050b0405000c940c000581d00707213015031401c26100d00d600c1e03603030080d94106001c0c4021074131003c6410f4050001c0c2428400d46d0240c0c1c44840ea80448102c490000c103840361340c0400c104141c400a601c10f00e142100421301c0e05070304100080e1040280b03680c100200480888180c041e10210306c4060b4050b041046101c0240c1443d03001085c6040d03040c06e088050a9066464a1411a242d0816110002402 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 374230719 1250 374229469 374229497
    0x60507270e04080703020703020303030a050405010b0105181e220507030b030a0b0c0f0307120b030313030b130b070c0302011b140904061e050114030c041205100507 72
    0x4005065080506240e50010504200703072904818009040903206000c0400c500081503c03c111084c082c66005d81625100d0824070b0514010708400d0300c007103850394244018004d05500c0b0b80151003480c0c2440440f100c803003002d0f4007030010740050164112101022002c00b10125150034450f46410800600318100d401c010300d41c2e081c01c60b0805861801010f08108895896950000c1c03031140142d00310107501540d0319041c3d120f005500c00c0002d0141104004002c021002c2c0e00000d0f04030083c1080c40091201460502c1015200d218440b42031420100c50302080c00450b048440c0194401c0320036100703420004c840d49030702c0c46500040743c80b040050901e15110342099428003a20002d4100701c2c0e5000d03400b18594070301802c016030203100c01c03000c1c1e10082085400f13680c0b42d030000790080c5090001408003038110b0b845014000c01a00805010a03034090030007074081150030440740f00d0350413004554101414480e45a0300c10200004c00c0d04d0a110700c88c401e00c4201002d101d80b90180c2119100c6408217a441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 374231969 1250 374230719 374230757
    0x30a08060307030209011e081507020f060c1e07080403050d090e0f040b09010b0d0b010f0e0114010c080705060109050415090506060f060d1a0103060e0121030309060507 74
    0x1403149001e500000b000f0001a02d40004e298151101d0002c07501c2500f0504440b0b11040e00c0b0791380114020310031002d41503801a50b05d10b00b140201400d1382915040529602035543e1050181c54403100e10b0f030100b00303a409207a07039074010408092240350580d1900d0300644a8491f150040c1e04246c4e0b042d001760414000c882e4009181c4801029106511081850640c80342c8a1341c00700244050907050312000000c10642080d408034184c03034001081c4902c01201c1b420118802c1d8424000e1103d0f40307802c448086040114042814102d40080b441340805180c98001100c032025a440100c4a043c02400f4050000e107051042a0213030052240019051502d8200144d0b03100783d215803614024940001000481c90114081d90b11000c20f444c8810040300c02c80104100d4401d2504080100c1d1a006c2460008521001005505c2000360707014003d868a03902c40410200082c0700392030100107541092103004d150401501001802800c001034500107503110003058a10840706400000e4424440c0d26044200d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 374233219 1250 374231969 374231971
    0x140310050a17151603051518040b090102090a1419060320040303052a011103091e070312090f06020a17031003030e06090307080d030507170105010c050c12030a08 71
    0x8038001c503100508000c158144000080940c0004060711500051f91034190101d1a440c440c1014000342d81040401c4198900440140da08580750107502000c00c070590030500030b036010080001d201d0600d02d450318008410302c0718008001d81e00001c1280720598128200000380000300015200420003900c0c02000403d040701e04405000c881308107020520201e90301c03006031400b0103419400000c0400344200c030b00c00c41e09003005c0c0b014015800c00e5160042e1405183c090760040e0719030ba0490308841084070425140440d2105160241e0380441c500304003255010044411182d01030404800c100e40324400040d00d00350030340004016034480e20808007008006008075040341d61100b55641141000c444011800425200180c1004512403607030a0594640c01118003408008048a00031035071041f04a0311200320358420780200c0d01e0240062200c40c05911902031741c0041800d4540544c0c00e003001911402c2e49200152014402c07002120303000e844a440c8401d0000300d1400454a419020710010a1031034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 374234469 1250 374233219 374233243
    0x91211090f090d3e070609091505090412030207081b1509060601120f060f1a0309100504060e161a120a0b06070b01140405090d140310050a17 62
    0xd801082440015508900f407221102d46035645051070000c80800380100131129140c0c007041c0169407001030383d10340003180c42049a000c0c2e0f00a009030340031090700c03005240300c0c0c1c441c150b00481414001b400080030000d80c0d006108440c14010308119450711003c4158012400320605880c8065080c062080304004041d0000e01964042d6400e1520031185030303c4040107003100e0b042c00780c0c0040002ca44071050b00807030702c42c0000c98010000c442d56035601d40d94006851080300c480020700c3c05081021091203085910416501000b010182800c034010b800800c002441a40c1c0e241d9180c05070030a008003801201550305110601004a60400304801803071030803080c01203003203042001020f0929861010007640049540c0c000682002e1036800310f0000d12484000816048034500089484907101c03143d040350340d60503a010000c2d903640301a042d5469941080398400b240007a000c40074a034070301000a55210f021450a01c2026645102207084010f190704100c43d2000020380081e00a042040351038140c034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 374235719 1250 374234469 374234477
    0xf020417010504030e21010e0c010801081506090403141207030e01020a080c0304050304240905060414121609090b09060408030a0905010b060c030a0201050c0406091211090f090d 78
    0x41880d1364041e02042c18480d07824050044002c00030000e00e000a0a41201c2e000d60b4008d10400b0000a0019198081c080903240440c008400110b090000000c0c00c1a00a40d0b40c6001800381e1038410400c9842100184101c0c00c114000310300c0c0c0f5130001051b000c0c180c0c0e030521030200c014909180c2c0000d000d94545c0094068140c1c818443e07550084c1d8000f00d1290401041c0c50102d6070703900c507030900c68150310031a000b81240c100031622010220100d0310724480c2c4030b40b491780c4d030101c1640c80b8810460a40306902c94450340c0c42c03035050100940c6c900300415803d0003086604459044444045c0001264866402208042d039190249010320211221556000b10800040d00329440c1645c0c0f25002400090400200b50740d803554180c0c10030109600c050708070140101501d0703d070000c500c2c54598940c0000312850055007000040723a4825140000c3e2002e403410341e1a2144078074141000c11244480b114400d4070310510880300c03038609480b01421716008120a200c4039989203840c040e40380c41c3c4115050300320200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 374236969 1250 374235719 374235721
    0x20a0305061903030c0f02040c09180c050901030b0316080318040b010f05072a05031c020d1b0804030b010f081f0e1e010f14060607060b010504090f0204170105 70
    0x11500c0300307809005999040c05d2109001600d0b08000e2103508109034000e410a02c0d02c0d0f034405c25181c0008621084922075108014003040844174903041d100343c034000d00c000c5002402064015800794019107521030307001d0202d5042130070051003403545204d40d9100e142c031a0000070b440d003c20019110083d0049100742da0034021140002d00003844000704d20304003400c200d4081044020007043e00c14030010015015180101400010308559490009225444c40fa10441130384442d601403003150001d011010382c002c0c0100952200d002c1d142520801d0604a044045502503000240000c018201a50055100c4c100307075030402f00d94644000c525004004291302010841c1034800384d0038503455044140e40b04c003080c6a08004102d0b840c00c800026880d40c1044160b848840e1344805603c2540d1000702e9290904c115125151108081359080e03ca0980100c410803240f40880c0c100d400034003c1ea803040c54128030301a034540c150801c8684906950014a8000504100b00c01f400a602858130503110000c11003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 374238219 1250 374236969 374236999
    0x11190f0f180303030513050f100c0c020d0b100f0902040f0b19030911060304060e011a0102031e0c0303040809010201061517060103020f07062004030c03110f0a0603020a030506 77
    0xd031551440300404045d25000012880e040065808005540c40300440e9034080b0b41c40c00454803550300b410b08481c154a00301751341d011144250078602055801030002c0b5520350b0b0030703210380c450003000070702009081c4840c16000403460342102e40741c00181046000144c80718141402c284462502d03503c02c01350510217200306048401d503441003040780b89603402c0004200489252440c0c07840f02150f10300380d02c08008410041030000d55045420030392040c1c002040f040e185126a03001c00c4040380026801a40280300f40c803102c02001c00c61140030100b401c0f40c0c80c10103690308030302c40c65031744101c8003240e410b40040364103856540c0901600c0b01401080030005803880c0c101900810b42c0c1054094a00c00354000c0c0003044459000381d04503072072181803c0c08165140340310b0034098050b24142215941031341000c07101c0c03c06418654151000d5a9010b04000d0000d8a19119810b0600c980c0500da41d00c01c808050900290b030359424114010070884d1005611168041c001a00f01d5200034050340c012202c2c4854408 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 374239469 1250 374238219 374238257
    0x7050a1e0909020f06071208012412090c0605070b090105061f030905010203242e0201060f170c0a0b09100203041806051e030304050411190f0f 63
    0x4103803000000005000940c43c000942c01c00701070380d0303110f4000c1000107044081c00040380314408801d109440d44441790360b90f612450070703002501c03000745807018464070200b10980c420080c0300100440c02c080442c1c6603c0944520400d01040ea001c90080f8400180c3c403010404100015030388840518000c000c0317440d292000c58440e4200f064602802c0209070500d0991902941c01303404090780007802191130f458080000e12141c81c41240c00300f86031410b80d084003602d152090358000d0100322880d01000d94a100c0c0780010b400b41e031040621065548903c030110f90100151035060080420080e41d40750510071502ea14108480e024031a030040340344c501d041c402c1d10000400c90301c1e1190166410312a01a141070101e09600a81d08285c03110f00ea00d5030407291060f0160021026034804032100000d0400742d90700b00095a4014a4880d0180c2090004100a24080d0710500c1d01d2050640b25600c0c0c02d50406091103113408415588001c90700b182a1188142e510030220100204a0b04220445050b1445080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 374240719 1250 374239469 374239529
    0x50102190c0b0903030d0e1f0216060b060f160b07030c0e0603150306040804031b031a1306050f0a0c41040602030a0206070309200301020903070807050a 67
    0x200c4507080000c0c03c0035094070204101e510307015821800700003e5250764401d1761203002039895104e985544104540340000709100b21100c0341c02000c44011300c6141d59448034050400d400b010307a4000b10500c030000303003005044014008401d060351307149214401883c140c0050f64020386000105454000b0545400e6044039940c0c8416600b02c484903101e50707030580031100421a082c100c0b501401000148400c1100101c040c1060f02d2003100108106103110b2000708080306240700103011100180c1b18082ca0161684006411041d00a4540441c9140d9147c40003541c0f000d603102e4510740080700410102e0302c038074031607540c544d5054a0542c6010303a402a150189400d90306102580310710300117403801e040c0f8520300400d1030031101c0105e0382d84a90340d601020b520303a00040000f0303000d401280000780c485d0b48603109a480b801c3d0702c0041d41d000030117640c0c160192886009100703a0550b6080081e4000790b50100700103c001c050302d400906800341000280b141c456115444204504440e01c110700140410a0040f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 374241969 1250 374240719 374240729
    0x17030603030a200f0f120f0711010903080313150e10020d0e0703050307030e030c06040308090307032103061d010608090c13020306031c09290c0106050102190c 70
    0x3240c455240702c20500300400e031108a5010302c20800b001c9040d02c0f0200c0d0404d04809100151106100b403007044040900c1951660b0a0081081207618001405100140c21518043c0f4118201544a5880701e207582cec0250380c50041c05030000c9104081080103046014402c40080c001d00822000c0c0d4125551152802e03d122035a54002c9440c18580b01076a1210050450541c12252403075524104551a503200840c1074000407003020408802d420006038001e00c2c15006000c1c3d078901072950321840c805810200d8600e5147c01400400004511404061042020302844a08460085200181c12a209640080c41003020081010b101d40351b107003c15411940305050a4610f070b69103460280c01c103041a88501d51250103180303164200041d99001d5803040303105400b00c031725808400050306680b000c4040700d40e0026404030021f000f002000600040d284844030a500c100c0c40c014010301c1d1081d040b5410b09501b5a66480c01001550fa0400548100d50164002440402642d8580401d0703200e480c021 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 374243219 1250 374241969 374241977
    0x60e0105100f050a053f0f01031a1f060915030605090c031e040609030e01051611060409020d05041a1b0f121303020f0714040f11040801060317030603030a 68
    0x4028000750aa4112880a807807144a003802200b10018840070502c082501120803106040042c0311040381c00c7c54103041e260041004a43c0d0900789662111800b40107000c40ba083e65505501e0303a6500781c0e600500e01a0035a41c4851003a1400c0505a03c4812460482d1004050502038104141e40343e452000fa004403440c0c0b02c0170340c0c99031080a40c1110107014400904508144801c00003884800e90000c006035100303070b40f80c510081400c40112010700420a9090040020500700d000180d43c621940c103060b0f4010f040e103400d00781d40b40300c00d40403604420800005682c03100104420000d07652003652801d0061951003000381401c4007400c0042000e4600610b407210002035030751024a02805844603080c41d030303900c42c0c610310f421400000d100c1d03102407088003d4483d4a941e407503410000b1601c041900c0c940e030b0b42d03541c503900f0f04c070b080101030256001c80303290450f0b540d8441c1c05400d440f40e0052020b84116400070a0795461850400320024103c080750412540500c02e1001e03654010003264401e44081c90 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 374244469 1250 374243219 374243227
    0x212041503020909010f031208040506070305090f0f01050f1308180105270102010e120a030515030f0312070507150b0a09050a0c0e0307030c03030f0210060e0105100f050a05 76
    0x80c080c1c0c0244125415903502400360b07400002d20440c0c000350302041c0c901c159a650420a840348054820010640b4020450380002c0d00056002d8441d0307011507404568542142c205d49021b94140781040c150212851160b51224100305181074003850160b048800d10101003e1546241c681103800d0060340c1b643c03102140040d1000000e41c0c412020782d2140004120b507a000c05003050301200300503603100c0c075442c059420130b9401c4c402410041290300001031f50462503450031503600380c11002003070010494031070032108541c40e5003952000c01c140310641040c01c1c021540d400000170b802010340d000900d5a410000c080001d58005030320500548000c802243c00842c58a001d10001005a4000d4200d42884c5181600704240203125400400200c0f1964030342c096610281e809040d2154074500001d000400c0d44042000064400c0079010518141441640c078800d840c41906029224194030081d01c01d403d24005002c0d07480c5c05407804448020a061030800c0031440781d4090840c0c01184c10032020f00c28041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 374245719 1250 374244469 374244509
    0x140d081803030f12070c08090f01110303160801080303060315070309021f1805031b13021602090606130b03100f08071a0a09051302120f0f07021204 65
    0x2900300c4406400201078985400c0890710b80300c00d9401070001d1a004107015004140010300902140d02101c1c1c2190300c01b85410900b0081c040c00c988114a89410881c103d03564520300102400514059006100c0b03100f4054041c07071009201d541d040e000000c2e69042082030092581e40003400d29405a01900c0400d803603500c008064000f40780d407902c045c0d0014070b100c842c4c10390710a00304031001d0b000b000c603151401c2d0450f180c002c9850008083c011150035034042d03403c135070161160307050a212400c002014403d0074503906650400303076040070440c11910880c8000b1041146040c40b074541d803002040d5032072800d01401c000c0c1c02d116510366204129126100202044405107401001d40140c0200455524096542c20b50560350705d0b680e20414880395101100e50104034a50001c4903045a110340d510344400741024100100160040300002c40705608000c401c14400c0b20f54800f61007500c0001800300c040c60001915401c0d80c1005007107008540020030a440002c40d11810759003034540051030391094907240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 374246969 1250 374245719 374245747
    0x1305131a1e0f0a0e10151d04270b04050c1219021311040e01090207053a021014061c020604031b0314030a0e1314010b090307140d08 58
    0x5400c00d0342544842070400858900000c5e00f40d0071280c201d80c0b181c01e60080b4030300c100c0e51a080a8282000c010000c900c400349440c00d40c00c04181040301c8903d078601c00710200c0d603407400300c600079a0032298203050f030301000b050050500a003114214255540082403141d0700312551a051160300761b003801901c507544441591114003a0844504915604000a03510000c1e0088190083c1c403031881f003059a0390020502d10300e14000d5402c030a901c2001881101d004091000052504514480040703010003003040d4060b0003020a929a0304003074015008400480f0a0207007070360040065031100024503001d209903074403041c1009000121070032100340a60804c3c40010590700c101e03030010300030f450309e0701401350215070844000046900c104c2c80245601c0c0418503554590144030020f41c0819103d040325502420004100708131090420000660740000070f1440d07881d400e081c3c02c10340c0100f0001c1803040340c0f402c00f00001c201605074814a070610f41c4949000808100c0c0040f0020003511000c00e0510140001c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 374248219 1250 374246969 374246989
    0x14060916031e14010b0a170a0e01060306020a020114100603020901020a0b0405010c020610060509011409030f01060f080106030503030604110d06080607030c0e0a06051305131a1e0f 79
    0x20001c6142d400d41050890500a0500b0000e08210355284200002d24981000201c441d545c0058039021503906055502980c0c447c0020114032a0075211150f11160b20000c3c40b516001e588116001620f515910800034211600c080d100001c418880003800f48c0a8200d13041741044035014600036984044c00350040313003000c1100100400200c8108188410040c0c10340011034181026406c45110342d13070f40f0700c6503502a0054072030380011074800c0060088552043c141d43c21840c0d42140d840c1c4c138103002140440d01c1e00250710111040c43e5540c20701800207010311003281e00140004802403119038110340301c4649078800a00700c00e00c1640c1e1fa00c5611004891002a5900344007090002c000c403d683e11195034070b500007250703040300082c903100401d900e03a801400e2502075800003505801c00380781001000c0e00c080d40720684154600d240400c000409a803081481c0001d4108a000418a1503d00d1080760301c14003580038162013001c42c1e00000106c402e580c0e03036009078210225448e00c00c0c084000082410005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 374249469 1250 374248219 374248241
    0x2107020312010e060906010c032304051201060915030c050d17040b030f0f090a0b090f190c0918060221280b060703180b0403151406091603 61
    0x14020780005003001020041911404d02079130101c24650341d61004540c490b14482c1c00402181156a022880c82100750b94007a4a860310b0900c2c0e49060f480786c0001d616203008012041d03090391201414007000d05079001d48030610110100f03188130a411a175038a441d004682c018071740a010084161414444014450390038006c2d001e080310f540c5c640b119243d45055108581a00c680d00c4140081101c1c946001c20310342c420000301000d41180c40081e680d02044680240c00c0c1c0034184213030019003119201c01d0042c0b407103000d003c101d0600851481d00e8901841211a4040316035940350031160548410000ca468030120740c054001a0344400c0c0000b1491404040390351000048952810044284004035011506070400025902000c0f580a003140aa0b03021071110740d0004030a112103000640221130078038503109040d15002801d500c401c3c0d00d84054010768070680b008024204004068400c62040c41c0c0c010840e91600c1ca500d281010220b0484c42014100c00394422101e000d03000707024805ea2020510035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 374250719 1250 374249469 374249497
    0x40b010f1d1306080604350913060f050f040c09060503130507030614060406030507060e0f18070915020307030c1a011811120a0510030f030206040c0b21070203 70
    0x42d212020103171765503030440307080315404200307040001101220711a0090410000700b100c0c9a000c00a410404160400501281c00045020302d80d4840c4030507024982c00340c001040482d9405107440100440081480030440c080e03850b24080040303550f480041581594854140079580b5211804809610b005425014050f4002c00501004024079500a0091507039280c00018080e00d03261304000480b54240310060182d4007440c1d08000c100e0069050807140c2100801c81124004140040343c8400c1500c2c040c4000c0140c1e0104010710701d40c00c82c41610141007505000001401c0c1800084d54074412104080d050015000c40d90007000003400300902c1c422441c101d105602d5a541001001507080201c4503450541403400711641032440800b903404010706241d1549043d290000c4000007404003030f00c1214403800b0840f003c40447d40821120325103074400d500820245c03a05061031100b0800b140c0000c4050700d401c06c0480c011448038500e07041ca0072034880014080e40c48554099285100324000440c041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 374251969 1250 374250719 374250731
    0x52205010506100e01080601030f020405030318090c03090d050304080d0c021e03070308040611070f11011d0105070b090c0d06061e0b0301030605150915040b010f1d13 73
    0x541900150301940d0291241092000c546005494072240d55130b00a0015004c000001c0b1950321903003110b01e02c04541000103160035107440200f401e641c01800c0b05442c00c0c07081a003844503424280782c1183c0c420b0640104d0303811420200110740c0c8a1000c0054207080020100118080c06441e00880e10705d1742d807100b01000011040c01c0b0180d00c4900c0ba1000d01690400841d55030003140010044801280d410394400c211990390b036599200801c1d401d100b02c542c0f07240600040c2c001a03800c0d115501c60501076640724515500300d0f40010a0100c00e2600d8030582281003022440d08d9802c001555220703603020804140541c0c5518480f0328004882d50300c00e901552503135058051014a42c414000d59107110020102204420110030140b070070342c8940b103c0340c3e4080004001044059006d603400c010480d9040e04030244550020344009000e46580840c80d1003142000071030702e41449041240503081c2441030f6440e1280801401c202c204c0d2110216210002248a00340d9a0701526030340c85446d803078010820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 374253219 1250 374251969 374251973
    0x31b030806100f0e0d1e030c110303070201080f070c020406151403060102030316020115090e0c010c05100b04180803191a04020c01090b010305010b03120903100522 72
    0x12800050711000d014006081004903242d103c0c0040c9241d112075610b42014400780042400340403501404282c40e142c614140b85401a114041c801d01c002d406603640030507403001c50600e1000c04400103449442a032080061200503600002c1150b8455020314121140b9a24030390251110100c5490080d0301a01c0c091020484e9590601099450543d5a642e03080340c0b1041d41155450384025121180580d10600000c1c225a41d0342c0040c421f2901c2a10010602c45003001d1842e48404481e04100c01c420f444004645241404207c031204080d024a84844004440d4940c103441c1e010801511a0564807980222841c0d141c50700440c2c0303078040d154900d500c918554142403400340c100f5181c0002101001305200b65202042c01010341400d00d00304141d080b4030231038081000951040b403011440b03540351480400800d0700f100d82ea41c002c500601c004282080e4039020141450801e1048141c82402448290555140043d040f0b14940c2541d10000c0d0720b480302c8500c010041104801c08039000394428820003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 374254469 1250 374253219 374253227
    0x509011106101a0301080c3d0f030b09151c050109030e030d0509010c060e0303070c210801050909070302030d030212070e0d111212070c0614030c0304031b03 69
    0x200c40d5600606501e0041c0f806040b0704038442840f4100a551103421586204d1500d045801d5407020551018400c4a015030301032040b03440f01c90603607001c0b840204081d642258101100500c4407440c0e01c0d00700440c040401c0040e10451000d40a20200104203802007060b413510905210640e01140388040b80182c41d2521034080c0c001c11104500140d082c0220358028100001c1400760001c3c0780c1c0391705040c058010f0044410b250502030544a0707644074405424404001d20003907001d85040d9440c0d40700e4100d0750800c0303648032610f00c212029208110070320000c0260b012003c0350554000300c810441a45403441054601103098001a6040c002d1540c026207003500760f40285403418070704496850f10380e02c10400380c03036003e16258142c0c1c11a00c80e403c5030340000d1030b0255004800700002c180c80310111100380d0162600241c804220f8100d940002d0210500102c00902001080f452030044021041c912021515010144c800c0884410100100d400c250140050301010500c80304400808040342c20010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 374255719 1250 374254469 374254501
    0xa0b160305250c090506010512060a05100c030f1803030c0206190504030c0603050105060714012a02010b06190c15050c0706050a090b13080702060d050906071d010509011106 76
    0x7980f1040d0b9160001c0c103d00725024582c0b00da501611070a08003541d040c0c00c8400700310010601903001c0602c1e00041a10758076041014222001750780d4689144000d1700e00645944141c44019017840180741d103803038828003407240c041d0a60750700d4607050b0900c1d1514070204240e402001ca200c600000006800c1300d0340c42d03108000d8021280104000201c69550341c906908a820a000c0c4030f8004508020035408651114464400e003501c02000180e01e821014403250302814401954800c026101404002c81d80c0c240503403c0c16080031900384bc9482126454855000e110030741d170301c0602c00c2d0950341c1801d000c41d40b0794080b65502d10041c01e001511300840300e440d03070368007480301211aa45488081612a1400c0c8916840207601c1070b1546000d41f00c0c90a11079511100c0e070411100a84208600c60040e02d507072001e0801d01d0f080484c0480c0508286801f10b0500400425143c1080801000d044000b0252140c1c140134000c01e00b0555515826000121030428124403141e6aa00c00d00041c0198500100522 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 374256969 1250 374255719 374255723
    0x1802030d050703260415020304150504080c121c050606090d050f070303122d0203101e030209010b0f0307030b0a090e0d03230a0506030c030f010506010801050a0b16030525 75
    0xc6e0038a5444001c4804070b00090310090302941d02c1d501c001501d1803041e407285410901403540181890b9076040344918140d41600c0305202180d000c80e10701545482200c0c8560740541540c8244110300e080c4011402d40d024a00110344103480110901e001e2181c06d0048030380524403003042e151841e4490602401c09551201440e10380f900e040542a00300c2c2c0f015615807400d058004140004207042d4181c000650009882c00b03261110040380028207a0034001c01100c1c0c0d8400f0405002c0c024554010403480c80c4050b40150800c41081040700c01101c01041100c0d800380550a00082041d0518040f4220401c280c0103d0b02c2c41e85400481c1080c1300001402400c61900342c0c0e020311803038020301ca06a04201240d41c410845080100103c0c528400304d400c42c40e072110703000c4e0454085107603035000245040382c2d107840c06130580d6451050208a5920090581c09003406480b150215490001040e800c2d200e5008103441e00d0740c3e141500010941701d40101d41090001e90450700c0444901c00c000304d000c0350b40c4142 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 374258219 1250 374256969 374256983
    0x40201020607110a061e0c26010303050f0c0a0b0901021b0102130302040e010f090c080709050c0301050f01020a080a05090301061d040206180a090501091802030d0507032604 76
    0x90b0b50315214034080c41060031007001900411450365201c1c000344c101400300c41241d100b8101403a24410852082d040713890b00541d03880640c2c5000301600380c0c440c0020f0020a43e1890841c006002003a0000100c43c0f1500394100e02c550b0392410145c26909080f0000c500400040d601c0d424021550815005000c2031a20000136640185a03259400c3c03c07441000304145900004500c208050f1030580e000e49400d284040000c01d111000e43d041600f10b1780c840e0022a800c070164034060103078507810400c050240202c800c04010078204011050102d0005115a42c840c1008500c50310241c6d00c00c0c80b00590281c0d0001c801600c48004a501402641080c00c00c48d0080d0b190841c00a204648001c034110f881d05e2440d07a040c0652a0b607000e0105070380c0079801c41649240b10320070591054884000c6080140b4010b0400256541090703e60004e03103810704100c0c42c1c41102d411030540941d0380031903803903141c508030b007072045c0d64050a2070180e58250b03040d080d091483c503e0713902400d8800150700549100d1417244032 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 374259469 1250 374258219 374258221
    0x406060308280206090d12110309071d0f01171911040e1c030c020f070b1305012f010f09050607090e011d060402190c170405060909060a0f08060402010206 68
    0x42d04030381d280b10881e610141503000140c40c241c0d440c0144403400c0118221030001c41c0b004290241031149500c00c2e1071038280c0fa80240d808100f5544ca8100800c01c441101c00c03002094100492082003280b0103014840d00d001da003028006c080d00081000b545d0491101103031b03101921180c1000150005001c480340c2c01182031540c0402c1071840440c142d200000b180d200758142d01c00c0100120700400f4038001707850540c8288071041300e1205081110100070404802019915100410324a80d40040360340418180021148050211800341c10b0101d21142d51011100d15900324041d40c0e030250044104410b882403420803c001400808274125120f00e2581d00d5050030329594280201c0da0040900ca01c090b10404040c80b80d410610704100c55170407070001800503042c5491400780722050101c0341c081c0000f0401c03045c0b41d0b200700020244d10f4104460000450b5013010b15200c0841e185e44110200284540484c10010700a9582d50a1010181100b0903164100549400c9160381d00c45003a03034183c1c05881048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 374260719 1250 374259469 374259547
    0x507090e010801091e020f0d0602070510090f06050604060902070c05030d0509011b081201081e0d020c090a140103150b03010c1b05010608030c0a110f0102060105090406060308 77
    0x1014204d0441e070f000d020080d25001c414a00c802402c030075203049030701452143e0b40c0315150380c0b081401c0a140c0d024500060b9996818940103250242043c140800c03141014403c1c0e004c2741c914600962483c3c0c10403030205030b40c0e03503003c0080c006206e11f800c40100c0520111710130040c4500b010042040c0c400035400c560411160326410b95040c056503240c1c500281d030224008000c5840214000e030032a00c00c1c1c1d007107800c00038058103646056500740c0080c040c0d0790001c520841004411307282d202c14601ca02014100c045840c0320000c1d00c444541075030300d0145d00384001142140700c55074011032403161442100103440d610f92410360f4080751051541d05103130307040202d207503110302c1e040c45618034440046c0c890f00032207541d440a11084103101c0e01c0540f0795541e03900c4001400349040c000cc1951110f10405450195500e03d0902c031143c07000a142c5010300c2910500403526600001e01506489017103818030010f548070310b8410041c2c029900014200c00c0c0215580031288101a00111411510880c11060456070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 374261969 1250 374260719 374260721
    0x201141003210c061e1b0f05090d02040f0c02100b03030702091e07090611010608033103080424120b010c060501030b04051212010b090f03010507090e010801 69
    0x1404068460340c0041e05803840c61494540640004040e0f0414518481280c0c46002c200d8840420304081c0845002e044002100203114544015442c15480c505640740e00ca4020041501000b004092200010b09884140e032010001c41e90b0603801401404084051a2202c02801c00701c0c20304009803251040c5e08844101c14042c41409400203401507060030a84c1c1c0802002c0b02019107500321545000141c981c08440a13240c9a01c114540c1d02c2c2d800e005072034060014403800086000401e940d140040a10045001100316401106080f4950070400803090f1200c2120b00007508031f00382181492400010400740b4405401104c25039081250f038503015000c940ba04940940301d80001500424560004490a0340030441c121018544003118501d560341d0007044503420380050707442c20084000c120800104000381c41100f4038848216003480503a1015034209401802a0f030105480030035110583c0d02c0c0c050315803a070020010001e00c41c5061468028015240c2805a205034001100001c0b6a0f0081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 374263219 1250 374261969 374262001
    0x6030b0606040b070303112514030f0304020405040206090307060906030b040b0607060f29090c0a08070e0105120106080a060b0a0504060302031008030c060a0513020a030303021804050106020114 85
    0x10f42c1030b101d1800301d159408400601c2070703020042c004803003030141c4000103c2618901140500b000001c000d45402030030450903510302c11400c00d42c642d008000c0110314440103001c0d260442d0f41583c01284a80380d070f200194003805881c0c00540c044c8200503000801d140e1080140c81280d000da1801c0041c3c0c0081d6082c80184c44100b04e60f01e42140c0f081124174005035a5900c0300d00340c004030620000e03030b000d0020305445001a101d50803100c9443d020b11021601d1030111242038210845400380d5203005101c0030003410495004000d002400740c900d4070b02825900500849003804403104035030046603152480544680c20a80300c0c010f4140c03030a4400705440c1101406c030782070000c2c40e40701c07141405c0c903101040380654001480150000b061650000d41c0c45020005049070400303020280155103483c000e10000c6400c020081c0d03440851451102015880b1340760b200c1c003540d42624002d82c0d81d002403078030145000c40c08664542c019240c580001141c0340c0c194494010303d81b1910320444151186a00c0c081e003514 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 374264469 1250 374263219 374263229
    0x90803040611070b160309080c0106050117150111100516080717060409020f1807121a06030a0b1503060114090312070c0315060302090a090b0a0f090b010906030b060604 74
    0x350011812a11000c407a0a0781c0176094507000c00e804e0250390301c0f8441c42e088018521181ea440781d00521840d80c0040c40c9085d51059095a0b803d00d01c1c103040d603010322048803030791141480125064000460010311182c21101c0881c803050000e820040c001c80c010201d04030701700001561000c00300d02c0c850b01c00c020b25440c4600d216410700749074440070100710060443c4002240d20884050f0b800d240340d01c41c2d40e503984d0700200741d0100d04007501c0c0035103002d042c0c0045000a21401458071001000040050350960000c04003920003030707166518815000c0c0140154402c0e035522900c0004151a0420354a0045100304420b90340c81c400503421706003e0035a070141d41103059068010300b603508060801c031005000c1c0c0c4c1d40100d0104e00710030303500c1d00c13155095201003200d07109984d1076007010310070341c101000b0b40341d00420261803c00120703c080e220004003c2c8064003816085807940c40013520345085800201d00f450b01710009401c50350f503656030306c0300510f028403045800c00100c50004000b441c004080c2c0301258 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 374265719 1250 374264469 374264483
    0xf030c17160302012006040501021e0f0d02030a0207060e0601081e070302100203040f0b090103140103020d020d0206040b040608040c0f03150e100903031505040614041d0109080304061107 82
    0xe0640c3d00641d004607000030341089480c950b02c80036510110400c0f249020700d004100050ba2085180b0880e9080041c2004c89009454100300600c034424852040380ca816506040050b1640c07102060f05029114001025001e54280425500b4100c4041606412902ca54007201d52580c40000c1c0c206540c0143c11041c450394015403401c0026083c84c440c85240c0c1c078814410340b4a000e4a4400c0348528905030b40205642000c045500c1103156014864000e45038200c10054489614642c001307406011080c8000303001c2c4010a901c001103450f10b800b0349000d4100340480c140c4690b101e40008240290481c2c1c182c0e07400c800081c0004000c2d001d607859400796a00800550141010300d141000a0f104007100c000e02c500c1140c016004a070030314400e80c88a98403a03900031507250350f01702521010070001d42006104626114082046403501c80d01258050010f61700460031507900100d6040004c10040d43c03a540b075027481a11010006c511005510503481498100602100340700003904078081d5000040101b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 374266969 1250 374265719 374265763
    0x7142e0c2a08090604170d03060b030612100c0e0f0d08030f0403120c11010c030e0318040b090403032901120522030302030a0c020f070308070c0f030c17 67
    0x81240c0714a0021000d024030350311498060b01c3c40110b140395016a01035103140c002c090b2080304010046c030110a110301d40d803600340512420180d004081d40b1012b001503200d61100c495003402c1130001e2046c108190b002c00030400019400f03e0001d040c013007400b1b81443c442d11000401c04164503040401c207031039581200ca4a41503a8917107010000710030010f0425410700c00d4a6070113400c7c40d1445c3c0a8024041034980d101c4d0b010203400d80300e0600f9180d00800d900141810403035000f01d5420004251b03182c60700081c1c0808940c900c002c0200d001041803804040e04101764400700024140c00d0380240c01c0b040030380c45003a0b020541d1030310b980b203191140811090009041607030060802d4013582203540c000c003245111301e0301001e268249400d40282401c08401094000c420403c05d800c4034482e041d02c5c40ca10740058855550160131494860b2114000105030342400b068000510074640244c001170030b100c81103070300566101e041c82c0c4940d40561084800c244211049550020030111340340c031050400301c141140b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 374268219 1250 374266969 374267027
    0x1c03021f090f080a12050c1801110619020423030f0a030e130605090a090201090503010e15100e070e030c0a1404090302010e0a03050409060501020a020607142e0c 71
    0x690290580208101d00359a0415a440061140c6c1740101c19280400395540262042d07180084100441107044c44480e005030141000003040f070581c0101a100d00c0b00c0800e9403403603014024003a5800c10a40100d1500440c40e40310140a003240c4d140d0000c03412a0f13400944d46010694940709640024002a548402da004904092042e101d10308030f140e00c040381d02910b03036011480b1100201d0303810625907194214482507580206c1c0100140c00d00360000d1080c0155000700c1b03542c405850f030104889003800710018858403213540100c1c001c0d00300000515150304010200608240803014500e1184c02598040c51192601b100310380200c50309000100e0242c96400c081100802b01e00300164295500c420783c5864078501444443c1e4400e110b03450b4642c41d0750400510341d0486145030810742c19580402d1810380969144015215441c0c0c0c0b0022000c116904082c41c1c5041c503102a5031207411410b01410080c8020110400c18010401060208650070310074108454185e0142d01c1d98100145144503102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 374269469 1250 374268219 374268233
    0xa170706050c1908091f090e040203010b03121201091802040b0a03021512010801140c0c0a0b1320060f0f120108030406021c08060f1c03021f090f 64
    0x2c0203290314000d503030910355100d90302c1040103940e14044034030080004080c01c0c40d00d403d240280d09400041541c200100d00c800003c3c0001c0700358081c288902c000100000c0c115031307094001c1c0e8080309028094482c00c003000080c3c1d000702d130032001d000070111000800208282e03060344105003e1b15448491501d80703040c030b6000d100c02080400c00007030b000280c01e600400580c03524620856407050507104280e81b419017582008040006030059030b802c2c0d04046101002d119140c407010b41100601e03d10319980c0781c20101c010b107003103d0840c00500590484c010458080e0f042010300e40c00300d006220100928007100311910b42601c5a003440c1d9032210050001104100c8040301402810600c0590246000b802c20101300380c166099104800d40e40c0001428020b041e810f100c64a014270b881d10550700e20b98a104009021014020080e5002d0a016078010101e03503544600c81d54012440b01172800e524241e400c00079140c1501750f00d04d100c14080c049441900080c984514801039810103031003031303c840050b56811 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 374270719 1250 374269469 374269477
    0xc08030301182c03070b090706090605040b031b121e010905060d12090b030a06080c01091202040c0302040e0a2f040e070e0a080703060617030307030e0f150103020a17070605 76
    0x2403401d02c014808100081c6e40702c00d00d64055800c3d14003c2086518100c3c0052120354190030400c00c0003820b0004002a228000075203800c07485020764004440c09808206510b0300584600301c0802031150300380010000108540c2141071100c0c54030310003a0b80c80d614200305896046d140903420000700c601e01800310300904050218641d0300d03c0d021085540c0c80f40000740c0c40e0410b0740e052002c030f9543d10040024a44c100400c10001400b800e24210b41450003034601c0c140590044064003850700c440c042009984664111405041c11440c480c0481c20301c500d602000781403044002c08240d05146d45488102111401c5a001d01403151140d07280505213000c1982c1184050700d40d105204c04841c80580039981ca01541e4007815141c1c0c0180901850b41c140101990b405500100060b000002d03045c1301804003100300d81d4000303114240031030003a46910415241640f140880c1a0038090081c20742801860140c0301c81c100ea000700c980c404525211950801c0c420b50441c080d41d141e610944c006c0140c00e001720050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 374271969 1250 374270719 374270801
    0x2102150601110706200105010e0a110f03040605040203070608010b1605010b060403031e08070905011110020309010f050a05092a03071419050603010603180c0803030118 74
    0x40c0d903441588240910300943d50708040c0108040000058003880c0310181c218140d10050001e100a51610005140b284d40180100c0d442c01c1e155210940403010302400c0341c40198586480a50300d1600307040520051205882c201c0c800d02880b03070005240ca2040040c1410385119210701841c00c0f1581c0900b0080d440f2800e000ca90139521010760b5812a0786040c064401503001c3e48a1500d0350320f41c0c091000420340a140b000040c40059001d02008560004180342550803e0800080e4003484218151400d010180d9004155000004008495006401c00d03c40081641000d1040f52954907001003528400c0b21020400d51094a04e104002c2c41c1d030188038071600d101c2040b0410244880c2c0802d040c030901c0c2d048440c540000c51003140041c200446001e07800001604d0501d81c40e0306050008503e4801071080380101619003c041402118a04260b1402171b441401040c04559400d9030603200d401c2445810252403405a8030580000140900d1100840403443c031010b65040b194602e000d10404903070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 374273219 1250 374271969 374271977
    0x30c010309240b06071101020601150e060304050309100513060c150504140a030504061103070213020a03022b06060822030e0405150910030302030412020303070b0f042102150601 78
    0x300f0900d030744420009028140c0500300c00e03060019000700180c50840103a110b5621040002030311411154040c0102054002c11921540e5a031200e042c95451401400320b844d0b032110140200801003134002005105213500b0741242c1c2c182c40c1c2d540030240d5140c2d0b104607010340f4121003283c1100c01c03040c003036001a80c090b01c500840490f07126481101d0b854111096001c40c0810710000b018803400d500036003032401802c0100019441d0200e00d50104925100074050004100e8000c201d2114103030081e010b0741c145c13940002540064202082c00d2880810109900c09505841e0030f4012422074030a44105100d15103100c07900340b11620383c0c000f000341c1001c005004e0b402c200320500c41c0191035036240605070040d5801241001e05102e800100b0040c0000581002146c80491000708006038010003601d0442d10b00d10202c45000f0a503001103030441c403900c80001c0068040300100081c3c0003441c3c000ca4000d82c09548025450f070241c484140440000480c10000359202c80790b170a80b002140c00c8800e52000341850 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 374274469 1250 374273219 374273231
    0x602071509260a08030a06090501030f1b0b1215010305011a07030306031502032401120b0f120d021b0d02090402010e1002030d0b0a1217190806030c01030924 69
    0x407154242010f5a004880c0b04100109010040005000c0d01001c0d00090030100325a5140d5079802c2c1420f081c49170000c0c9a840c14203084107021100b118420014103003002c0c0e150303840b003a60702001c105100c11603000f0480908003101c2400d55101e031165506035102c07002420010402c06201061f5500f0820003101016103c0d82c0110000c0c2c4280070701030280c070600e00090384900b0300c1c0a40c0c0b02e413403900c03e20004108407454020f84003a030f44212b081403841200c21002408115410200d9110a08012020380040740f103c5003000c0728000040031981140261f00751a0b01198450141030b0681280c00701e1036124041c0c08500c00540b4010012a0b001131050408808070143c520110f500703a5143d04c58070016070000302e4800144501c0380164803003100100e945048107820419624800103400001410310f2800246480084101754211614002106090928489290402054030b4812140305020b4010840b401c4100c0d4000d01824281685c40058400700001e804500035840007000a92a202510b440c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 374275719 1250 374274469 374274539
    0x3110304091a100c030e12010e0303070f08130203060a0506041b05030105150339040e18010e1e1e010b0a0e010605031f1706010602071509 61
    0x1100b0820141c0080e0903001101e030102040000150703c0c01400820300040481c420002603000384002c200f107000b1a81100294415068903006007100c0e2030710041d52000005002003140c1080400e040105a6a203c804507600c1e410300c29003525120030020f4043e030003000851503010940d0405030703000b6000303440003d00b4403000d4803150f00780c200210610041400000144640c0c24030042301c44204441040f041d03d141000801c50303034041400c084412080321090007000490700700654141e0f000d0710600e00030392182d40715501c40c0040c0700305843c04240034048030b885a2003103506018445400c8400c1000d00b00940c20055080300020b0340310250740003401180160781c0c0c000004000a1a100d480c1400001c1c0c01c000041403002c1d1701e0740c6810101c4c038203030154010041070340e200c0d080301d40c040115299030301c1c240d00d030004403880d80722640c00001000c482203400803500071001071000c0c100d50f02e40d800c9400c5a0303900c40036080c3d00c114030040c1e08006401c0c19820320000c0710800c401c05118400143c002082c00d80e203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 374276969 1250 374275719 374275721
    0x20100f030c0e2101061403280b0c0414040c0c110a09061706010503150a090201050f031305060a362a060f051210180b0418020a030311030409 62
    0x10b003000c4030151400f880341d4041450074030400d805451140f619880b030701b01400029a40391060180c01c02c0160320b1580003261041e2101011400980c0036a45503680d0505542802e07558215021300341c00700c50360324045081d80c50309000d119007044094440d41c01b0080140c8850003000007181e501078110040c500c001403914880c3c17180c0c0b0001c2074512128041c61001e00310301800d000041c0e10580c8250302c40c00c4180e448508030311445400c100352103c0014410294030058074035004050038010124004010082101e00c0c2060040344144224141c5034a65030f20701d001000c03185201041c0103074040f81c02c1036008007844031165805110005000d040700641e299507409021902c091044c0800403000041100c14103400b41d0300d0040c24844c14810480001800014402d008030750041d810603512201184419444c01d1041c4054080420a54800a0170a994401601420391254040c40c03600f451900c52080c20080244060f0b8001e05141d911442c0d510111070041042101520714041000300040c04159 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 374278219 1250 374276969 374276989
    0x609010903051e15010b031609080313031e05060a0f0207081920030a0f030e0d09060e09060303160302030d05100e1f0302060c0c0301020720100f030c0e 67
    0xa400c3d100d4041024100030300d007824050144401503568101c01440740402680603aa07004042c02860000890b10310401c4600010b168010421800b0000c1e150b40c0c00210720500380140d134001c14401140b06c0e8100c04664030049100405000342d08900040b070300401040e080346480c42c0d080d42d40035090014a888500b02640400c01c51411001042030003012290486031000c45400910310f80082d0007075514a05490f8810a06a8810004106070081c100c501a502030303031241440c5405c4902080036401c011308403c940b4054030012800d1210510810b1400048182c450400940510302300160012544014542c03820f08600794003090041d40855803151044a1150b646103038070012891a001c1d0342000d000c0c01401807406510204045601c402500624200312503040e500240c0d1600c1e80c082c020f040914447c031207039055000003a101e0900c40c41d03921205032003450141d003550b440e0782202001116101032002030301084c28400c0c0f4100950080d0700041040a071824503014020091000580e0614 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 374279469 1250 374278219 374278243
    0x103020c03040905150f010219020d150e06061e010203070204051e04050619062d09020a09030210030507080a0b030307060501090f06080d090324021b0c01020705010905060901090305 80
    0x501c81c170b000c01c1c0d5442c0541903001400400c0c0042d2181c2c0044090410440005400190141306400240e0040084042c10f1034481c06a6100410602d05881801e94843d0010380b01d0a121303600409103940729400c0303c0c83c000c00d4110160011450b08500c1c0d4288030181c20014034003c00c4111460000440900305504544298864806007105280010411444030042d1002074480f502d491380c24041c08481c0c1d804503c10706840c50100f407c1500046108821510580001c0c80450001c9006210542c01c0124402624400c81c1ca40c0401e0340481006c504a403401c41d188000035410324040340d00d615595022403051381018058a140c100706859240603200c00382d00c4118829901d01c04420035025520a20016085c9540980004040014001c085034190f02020b0000b032a0030b42c007104d0010485c01c0122030240f4170344095443c1e900d64148410006040642e904807030148c01800d80140d031022170700b00140c1300c0503152800043c2c149428450a604040c06060500c003c21402002080c0100a020000a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 374280575 1106 374279469 374279491
    0xe04030509040e190b090307080f070c080303150111060c0f1b011404030f050a0909090503070209010306051e040210050c070f0b071e0c050103020c03040905 69
    0x1c010709600440b28810184c58004180000ca1214131071805450255100e40d180c4103410744904c51000b00800544040004141150a4001411169000302030008030641c07618086441c690058580c0003d40c0c00a5000104640e808140d441502c1007a01c0500440d041043c0300d40c1c024014250355070007a40340802c2e0b210140c3d440800055030310305024000c9c0203202c184400400401c40580d8182c001035038002c00005428054000c0b11104000b541e01c0300e03040c42c54210401c00a0004240444403400204160340150703444825490196006402c000b03958280411880045840382841c21444504032080101595454210060030b61280c100360355918900b100707080c10181d20340c0203864401036a080101e00d80000c2c03805070850030b103d02c82000d200d02004c51200000e04100038014042490707000309110380e511076009011402001400c07241410b8956511105031541258200100 = true := by decide +kernel

theorem cover : BRFrame.Cov 374100719 374280575 := by
  have h0 := BRFrame.cov_init 374100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 374100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 374100719 ≤ n) (h2 : n < 374280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
