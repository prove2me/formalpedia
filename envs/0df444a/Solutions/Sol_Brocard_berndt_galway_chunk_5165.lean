-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5165
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:57:39.915273+00:00
-- url     : https://prove2.me/submissions/5f6e9540-b25f-4c08-bf9d-fff12b34a7c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 928776978 ≤ n < 928956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 928778228 1250 928776978 928776983
    0x1707050c04050703150e0907060c0804140d02060412050d020f2e0e030406090506130603180605070903110d0317091f02040302010314011a0708040305030408030c19080d09 75
    0xa40b210300980340f954040f03030a001b40c0050111400740345001c110161600704a034000c6024022400d9064000803545012141580c505002240c290341d9454080344040122000003944907002103400300f0403120003801d40b000c2c103005100f120900006054180e88441580002c5561074200043c1122501d000311b41c06204d10302c6040d0007800e813220801400d01211324209000245c0d800000e03003080000d902c040004041d110032500e03240746c00c61444801c2c0700c880c1340d40700c0c040a05840d1000310078080001c07a501c64985400840601c11031801c070390010224403141c0400c03100581030000e11070090810003c030304449581350319152441150120301401a140050014000b80b050032002c03910081a40e144c2c0980c100306510150b1240e0442c800502900c00d840a9814076010b48070041016500304940d0000203040000c42a645070040c0c10900420700c078940018026100c001800104143c0002c0103054080e2400d003541c106030782460310410a07070003e80010300f40d40020301c1443c038910002e0f0f0042110f40d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 928779478 1250 928778228 928778231
    0x2705120c03030f270d0b0705190905031204120b0415090b01030b0604090c14040609060e07032a05030601090305060708180c03100b060f04030c031707050c04050703 72
    0x10810310000e80366601a004107520b180022030107039180d0300b000308511081d07016607101d074008180c5480802d003c00e03032890780070340200010000300349510302400407140c0104016aa0000700960554040d0206c45644540c5000c0c0c4034142c440b4907405480c3c1d041d2010386070400008929417802e40c4aaa94012000d00182c0c1c0d40941840305844500360b500ca079224413481400c01d00071542c03544c28140d03044880180103a00850a101581e800202c0c0c1490f0241070b00d00700c800940802140501050081401c1e402100c280d51410101142c0400400155471103240166010302240b030358542c1c841c03400c0305065a11548800f800c40c100d503c2d14020f8004c3c40e80b0032010b15000c407100340e803511050324104054480f0000700f10101d041c0074114408080c046400309408008090f94020354007c00d035510030405040000c10f40c1c410801540342d840c03404495074585d007000615103070f984a040c80d0408584034402214001d403084104414400400300b0380f080f160b0000c000e002000d040e00b0a10000c0c0c80024400781c2010f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 928780728 1250 928779478 928779493
    0xc0b07050c1c060f02030405030a11120703020105010503060c09090f1f06170f061507051516020d0f05040b03040c15030e06060d0816061506050a270512 67
    0x2510b0b8000c1c0c81c954030000d020314000b407200034100181112070307180c0031000c10313401002040301044001048815824980c07400042ca103424889980c00d06a03e03200c11005147c000403000c060503415013145040e10340c01c60654003a1744418036401450b124802c8880e412100c2c0000141c001061a503060340d200b44482c200c02c016054180350196182c0c0180c2104001c64030508036040159190038586501c5506000000d207a41030500015030209051000c840c1006000140c0d40c1c1004014044292040249c84110810381000c1d80b24605810080c0010401481001501c80006100c0c1e074651307000240b1625090300d0141170580340308003035000070000c1e42ea0400c201c4000550502070030780d002c00c0c8410b5039000504514001405820494064241807040e0050b00b0204046180740c003c803094030820461582507480f8a142490292820803221004141004800148580c0160062a101c0825690400400b801140445600e485050210725812102c0414003032400c091591102c19601c040480d8402c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 928781978 1250 928780728 928780753
    0x1e240f032010030509160b1b01140a0605120d0e01082701020913050f06090717010303090f17060a020d0b03030313020a15050a0813021f0f0201090c0b0705 68
    0x2642c2000708400aa612010458540001e00c500c44d80c048900301c40500040c07912200d00c401e405028152102040480f004140290007540304030710040c8055050003082c41c0000c5c1d614014603207031046901031045465182c1442e1404030301000301e0381c0c0d02e4456003003582c0c40500440e007401c40213107441d8041c083c04007547c10721105026003054082c0307100c0025940707501c408103200c1021503032130b075030700310a81060140140201000d0f0b180341c0c4494162040841c40d81d50400c1260703112074915005540162140c008010b25a226072100b05907a0148620101d49685418100c2210003c120840c00d9811100c00b1402103001a002045082400100841c0c0d120744540064110303801a41d680c841024292152811410111001d0006000700300c0f00261074881d0090142c00c3c2d200d121140d504109403503000420243c4846d4202000640241c1180d01102150700c03034031501610402440d01140009800c0700d245403050003400d01041c0d100e02c3c1c85d1441403420030a04100d422080c0101c1d014000c05003078842 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 928783228 1250 928781978 928781989
    0x903050c031201050f0f030712022209021516030c23060a0f0203102c04030c022e0c0c0506070f1b271e240f0320 50
    0x4102a44402c40d00076945031a0401869801540d00a030040c1858441d103d81980d010428000312484a0b51175881410395100042c0ea5041405000003020440302d401146962594010080709100b81d0301030700c100ca84005803040314050520451030352110800607000080c032990f168001d10b072044400f003880012450340040d040d90305160b40c1005a0044041025146090040d0a10154090021071840c142450340c0c840740f08480c0500d01c0e402c0c2d444103c49903480c507803043c503009803461038070144194101860b000b80719075100c80c401d80c41078104100403082072040a04070340b03242d4035180744201c40c0c2c1843c1209807000b04a510007522000e000a1001403541c40d00002000341c948500040c15810540e0b1a01e40c0455030a25680b6282d20300c005014400244072044c0c1300600c42da501840c9944d03039000048038020340000700c0d040c00c2c102490386002c0c84400c0142c102c0114170a006141d4521446604940d6001c03542c14030881d0300b1103145101c100046510320030345c2c00b0000c07111070340b1054210024001c0b50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 928784478 1250 928783228 928783237
    0x80123031515010e0d08030112080705031218060606160804030204050709030c060905150c190309090c0305060d0813080d0c061a0d080c0c0414010f21060903050c03 72
    0x540744002c60305054942e440305550150711021144030100c00050f8032686a6400140102040c0b2003d10154000784a00c00064690550b8000b00f120350724010714009200461040c2c8020209000009284802003000f154041c45140081c103e07030300704003440884619103424800c0903120203504100200150316280603542c802c8000780c884080052561600c1041904a94003540400600c81d00078055540e440790141c0c8000d80003c4090b40760104c2d07a040e1070515200008412240c0310a8500001301030b00300f48490113307090b1400801c2040240e000c00d4013943d104460103070b440014030b4444000100001c0c045d0000601484440900c85d8981d409a85042c50101040020850361068801040314a019240803116200c803120005110103001c5480c90f540c80c20024850000800c042c40c14850402591407440002032052252402a908a42e0001c0c028003401c0c4011a6082010410b03503c040310581c000b0800780c014903207250007074641c080200100b803003c90070440208509503603500c041000c0e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 928785728 1250 928784478 928784491
    0x602072d020f04050a411e04170a0c11040204050a1802120403080a151d04030315180b0f150d09081206030115080d080a020c16030605070801230315 65
    0x110103d01d0081c908a42c0150100825122480041000c0300003003804030030031f00032009515080c60302c403441c040d480d03c14110a0107451600200b0f0007001154030040c80da501e54000d030204200d83c10400240026440b407805010380000c0d141000700700c0140510321403458201241c81c0103040c0700e082000c10100400c299400e40010300040103100490100d84122403450841c0381c1030412107031401074111013201300e40c8130100c0d524000c0c1c0e000500303140c000e42003003160240b0440707203510313041e1200721100d900c40029802c03a4140703103490000b0300c1908202c080e41c070325400000c0151564600c0080a025a548012601c13005642c98000c000c0028106001030001c0d85030903500c1c01814606481414210381418001c1d0324004154001000b441101103400342e0602620f19045036140d460541c110041c1c45080c03040e0342c6602c41c0118134492a0100d00c039410a803482510107001640350307401d080b20341120030f0262100903404540c604027006102d43e0f02c01504030000e41600e02d43c80074503880f80b11a00003198907 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 928786978 1250 928785728 928785791
    0xf03030415030509030328240603060b13150c021008041a0f0606160c290c0c060a020a0606080d0311070c0e130602072d020f04050a 58
    0x760441ca901401441c0c0d0010b502c1000b18254030f4500c46100c241001c0c1c1e401104542070384a401e81e412215500455110141065100c03a84102814825450b19140c402c000c0064070b041c1010a031140d83c1402c0758400c840d6126107000322401c0000210703000c8410104c29007400f05000c1401c0041e2501100c5400c201025140c40b04541f5160624810380b441c0300034401030f580000300801907444001103401d81c00c00c5058842d40d03141e0140700c846030780491060038081c0030825041800608400010921004100c41c496103c01c52001c24040110714011620550f50390380001c8044001414007201415180c402071049400643c1607480d0842155159000b0840907007241401c840842e40500895403019181c120040c90310340039403100c04a003c403a0107000001403114001c51040c2d021040c5440070f10340c001c0021540d41a0303510b004650241380004d01c582c0b040c44030244800d401c0080d03000400094000d4131048516249030b04210003450010208910180e580703040c43c0c04040304000d0b0b001c014401c62031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 928788228 1250 928786978 928787009
    0x7170309071e0f0b07050a03080613020309031308120d09031431210206190909050606040305100506060408010c02070503070f081002090423190e070605090f030304 72
    0x501d400740b43e2103810806841204001200c009000064110000c64251908a490345c484100040d01402c051100030036660020090020f641300200041004120f4204051319250751070804d907442e11401c603844c021038802030100701252091500240001d5110b4a06455440c2c00400f2207111600b12102148000c07811040003958044c030708d10101510141c000d00076210a03e00544250b540a0100c1e02d2201019000a14411500d5500c181c0706480307000c83e0131020301075580300c4c020250505403042180079420328012561900f41002100c055a80000250003850044180000500b030081c001540000003000300040742d0b5000c0c8299915000caa81c0a44209441c14040510301001a0002e0302110045070003080359040000d11082d40d000300407805a00d86504200242c0103140e0702d0b0f40c207041020703003c44c0d5903150803943c0a040d00c50600614415030822080c0d90300d0044840b01000480a0750000409001c61030080c4098000c480000342000c3c3d0314200d52000c28115081944102c408110080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 928789478 1250 928788228 928788239
    0x31403120c1306050c030703031512030507050d09030b041209170321060d0b0c04120804150c050d0c02270f01060f1409010507020d05070510030207170309071e 70
    0xa40702e00040106140c89401c00711045c0c00c05449100d002001828181d440c80c0007500005c000d50301c90f005240300e6042d6081c0fa450f0342406400d60b408108101d8060192804005a4030300078540710096a802c48050907140c5d6547e0307070b001813004044e0440c1d4103000b0805400609180c00e041e49011100f00740c005903032211200701400442c464160800e102e50b0b02d82000300030468990710141c140d085d070040d0183c40c1a444100032100584110341000e20b440c03544030084014820460f0081c02201d0f001d0310000c41c503905544044500c00080f20004180b60040200d604100d4030400e40c40e00c5490000b403489414800190031090045546c51300034105110310310410400c05002c1151074010812070601d6036500d0240b0000810031030f401c031000c2010100101f030420490741b04d0809e480c5101d9014040d002d0201c0c4504000c0d07694000f510440784980100184464802e200e4000c0d14141944042165010200c880250400d90030040035500e40d4818114006010340c0003100c03031030001d118070b120000c0290400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 928790728 1250 928789478 928789507
    0x1815040c0c05300412030801080a031403060a0506030f0103030306050315160309120e04062903070e03300a0e0906130903120b03011401031403120c 65
    0x954200c414400020035510100c0ca0229110080180203d9641c00800f011101801d801da058095020620404680414080b1202d0080ea240d140a61541a403030781e40e50880c50707600c0c12400340c01000600034110405860300d004c009160440c4000740550ba005445e14041900d40e04104c1d0503101502041c4010070a160b094480c0d00d001d440150b018100302900343c0407205140c00c015013000321100540940c113500600c00d5010b9040280c0c411b82c29a881043d001d001004400050403180c45945441d40006410506460f521546900c1182c14240c004020504a0050300b000b00749006000010008407101d07682408100c820399490320901d0b02600c2d4082101504114500b1031042e900d00400511202d10b030454400303011003a0450380d03032060356075030f01c0130803440d44002c0301420b110380c02c202c02c000c1090780012040101c0d0700e08440030040740d40100d01301802c0e9044060002407051600006001064900000ca28822282400c49142882e0007070301c9000da9200b1078145680b840080754600212822 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 928791978 1250 928790728 928790741
    0x80d05090f0f1f090e191406031213090510031106160f0c09060603020a18120f08070f0803060405181c120f0234030c02181504 56
    0x1901c030210342400c00008240207596411107078a20f0242000d00c140d1051050540d4809064140d6020503203080c81c4098161084028003144051801d269009940e4045545440c2c40b40200400507c00340102048904035503100c0813000c07851065004ac00704654890b80106030080c601400d003600418950b062010846800c100d2051141900300309262620100252810b00342e078202c802406a2305180c9480f40c90403030190300c505080703820302d040040e00c40c2c0c140d80648001c500d1f40e150640500200c83c07040716030a8560007030758400c0394040711200208803400707400005c4500c035452440c9410808e4554917003c1d1052a802c94030301000108100700f03414180030306a08100e4240b2181100706141e154507844407500d40885410340082e0841d0740e40c507842040c614650615828040000100c0000307040080d510480d007030718004084071010b6800510107210401400110350300c075030340c104480e502100c2011500c14140da0110b1034280040c50100d049684074000c0da07040c41e10301c15940d40b803070610068601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 928793228 1250 928791978 928792009
    0x151303121112040905060409060507020706030b0a050622090f091505100312140304061b0c030905102001050f0c07020d02090711060903120114031015080d0509 70
    0x10944502c81c109486100380c41c2a03c0220502145990781c00d800703e401010415400340c0000d040174184090540c001c00e0791030581d07000380e130184000c28883c0184074100c0c0b0b0610901fa04840704025004442c0107400c42101c8080c03214407071559440d80c2c3e240d01815240610121011203907207800140801c05180e40d204c0c1e000c090007100340b2240c940701d58035094011651001821004800200c620030f28451100100351071030318110709481382003d08266008041c1e10f28050380801c1c40c1c2600b10a0907003c4c801d0030b04280c0d410303600c03859138905010a004041144403031850034000704100080c1c4605540d8031500400c9001c07800007800e032130b084a1608103a08007404448140c441004880050385035080c82440c80e81c0c054914030384c180c89040c000c40b00f000a003032014550b40260814042001000f0004000b010506180c041c596601c40310302a0812903081c440d654107034892a0100040d001c1034100c0e1280422007500c180c070303555907104010f00300241d054581e0700040e0006082d44052500740904141d400e03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 928794478 1250 928793228 928793233
    0xe0d0f1706030d0804033c0c0b0a0b0a0302040501290f0d1d1204080d0203210a0f021803010e0705010903150e01090807060c08040803061513031211 65
    0x401e000401c0c2c442203402440c00800c030014000a0906010314030f4411400307109142c010300030749864248491b207118404040385030101100e201c0d082a10503400c1503081c03900907028506540361440014002d054088215800064030705000015969511400f0f00034612450380c034079500000c02c0c0300d100c070301305a85408000c400140b10244c400c07814041074035814052000300060301210003040c4042050711030050500391154200003140406004098001c403862441290001201c10030705a86902440c0f80e01a100f003900c2009400c0304a960400a8100b0540a80061780c4000e2030b0048041e030b440058001703200c80d9441c25405107410709105402042141c400035141d0f15040400081070183c0ca440060201c01305461404040c811550160317070710f54110f4000f0084001d461425600c070703801c8218151407151804030344a142e02d002d0b810503442940d110207007901d155107003002c0040603000006080c4001d6402d104c074420412031544641c0182d80203851403407020404440c02018036400003032100494 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 928795728 1250 928794478 928794481
    0x90a170c012316200a0203100b0303031605090406030b1e0f070320120403090b0a0c031b0203010e0a060e030414130e0102071401050612060402060a030e0d0f17 70
    0x20751408619402c00f0740c4034040c081803001c8182c01c48007002c02e450b8080380118529035600c2d40070000a5118180341c4283c0944400c070480a0103802100c008003500c0b9010b0704100006510611892035900d600541405c1140c102079242000c5012154150011240c0c0a00d040038001c4802242415020a4110800340811032618001101c001c900140c190b40070300d9200c802114100c00414858803d110301080c80c01e495000f40644070702030800903541039001c580d0b80c82000c9120117159085a2810790251100725010303109641c125404000e4030139011145900c800c040005a600380034002d103100010004003812401410844106c540160380c1b500c0540c010441048900c4600c600d0000340c4008403101c129080f010851000600302d05411143d10303520002e80c00d0104901c02c03082c5091118900c000300300b00d41d0b414040c00070b4440c9031b41c10702c21030b5032040300000c0043c58510001d2400003100c0c9070200d4600c0e8000811403820704242c029102141c1400111020075034006809881c000508101400380d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 928796978 1250 928795728 928795781
    0x9080d0509101a040b01200c011b030507030c06060f030602030103050d03020a0f0f0207182f0f0903030c071d06090106140d1407111203150603090a170c01 68
    0x144000355440500840d117401c110400341e801001811250790b000d00e4041202018108010788546001904a01040350b150b109400c1c03007012281703040502d078192119440c002003510f050700c040c00200c00403030360310380c07242d001141c14442084e603240150b214a601580301c0d41140340c01828492140d1082c81050720600c041070001d80e014980d81c0340408141491141c41150560482c200105600a1915200d8441318019400ac40740c1c0710119451f00d520800c00c48a03069980c6207030740080c03451040080d4400303200c030052121210000b000c1d000d100404403403401c0c8000c41020f040051517800001511003034036203008040303101d0942c03e61104c012500e21401d9810010080c0061201c1e01c88101220000715001803d600f440e8055aa070b01c10030300c40114149049100180480301c40c81e005c030700f00e0103400e80c0850001a05001e6038010040e00c0042c0d000c01003180140000c50b000240040070301e00c920858017010586138001d021601c40710501207552071030100d07030050a503401911808041d20114034001c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 928798228 1250 928796978 928797011
    0x105130b362a1c0305190f020606032b0c0c1d16020a03081801150518060303070609081917091b13150e0403030e06010b070305070609080d050910 64
    0x20201c0101c0d030f0f80c1e0764449080484080c0100c03842c40c164406000b000503032083d00a0360300b80d0a6009035003111081e81e00c540074103441d100000c0720902950000750f6003a48842d00c40540c1c805082262802c00510b500365215503480e03d00940c41682c8a049060181c40038094161207560b00c2001422210030042111000030b42c1c500000b5006400c1081a00c0031480d80c0c03210b0044258020060300003406000100da28ae81c18180b518410b00344a08500c4511840d4501400782c018880c003c000c016508048641e02c841c0003824807103008807594034003002140322421000000b036400003159695045050240c8841008000014100100a611050305410102d4140800595201065400134504180d001c0088050301440c0700c01c460b1000c0030b4101080c200c00d48283c284c0300300d010707a40c18000301c1c0c00c1b00c0002d61100307800e000322110030f0b004100c49000700f4021001004080c3c4244d8000a041d4000e84603c0706070703005201c419107403036205e00500a80140c2000030181c01411003400b00060414402c9820 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 928799478 1250 928798228 928798249
    0x10090507020f19030909020d05070210090512130e07080603010f0b06030a0e121b01140403080403050f040f03110f09061e0a031b03050105130b362a 65
    0x44004021031040c0f0109446460810010411000c065440d14407411031403015010865102006108403400700c07a0400c01801418225070b006070103055105252610008913034059010b0307814070102e41c14001209030f519200d461043c40150b85038072403410500201825140b80c01145d07040c0e01c0c14810400c0c0955150811079402c07219082c400a048045030103c5030801d07410750261b059110010078295241ca00a20b0340e00110040040204030443c403900207150070410070303103016001888180020700004e000f00c0040002c00040132540742000d64072440d103608280c90360802c0b13401900c880714414140c140b56840030300c281002c994103c01860103201040070320810355044860001003c1b282d80c850b4441d940354001460304049054030164001000d8a4001c2030340c4400c952540c42c000c0000c1c0c10030200d20152640681c802311448581e221108a0044080c0d0340f20714071001402050118032001026102000e03814100f4040c10b82d440551801c01c1a000003007458417015102240701c5c8544e0b6a4592400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 928800728 1250 928799478 928799503
    0x1805040203161b1223030720150709090e1b0409080d02040b1201061d121e0d1106130209130602030a1b0309030206060108180610090507020f 62
    0x81c41800d2441e800801c0d020386031140903088044480d1075a0003d6442200a0b400c0b0700f10800c50111103a008120b10034501c400c40b02ca500154049001c9603001c00c04401100600311120100e90301803401500c1c802c009c903001e440040210f051107400704000d040c4c03400f40000b00360a040103400a85110500016681c46003400c9501c01c81d5502d82d80020071102e001525200d80d0b00701c2d021903c1c0c13900e642080e0b005601042042c24451020f030000205030380301da54072400c41500000d607001d800396064140000050a8121031059005142e03409001681030501880c80c0420100240408601001c010b02042e031610318a20143d00f03c8400c002044881d4040c2c5400240c1c16204d801e81681c441210254110b010350300203169038000014001c0111081e08280d9802201d44d4190b02940c000c1c00c8181d0031141c05001c01005070700150f000549a40c0a8035001c1e50088142700590354070b00155201c0d50070441c0c00c41320001104480b03182400813107202d1088590112513400100503c003a03e10300300f40c2e50b00980380309 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 928801978 1250 928800728 928800737
    0x14040b04020108060103020c100507090f1215060801020c100516022d03070f020a120f060518030d090b01080303041a060a09020f0307021b13020717040303180504020316 74
    0x104130164460f6044825180c5c0c20816202c80003a951503c102a14064807820005803040402007210761803000c5140485119030400c07021074000b40c0d905050715481d01007a14a5694a55000032071410a00081c40404520720242c00762184800317842c0c0444002030b00b41e600c1046041000894030390000b0b8100c86034480c600b6100015803444641c2c44074860810f03251012400049200c2080000d403003c028140c2d4800c4605407841c0d61500f8031401508008240900a1903d82e44000c0c0810030552102d41c004201c00c00d074961282d0b00050756403442d4851481c0f40396103a07881f600390b01404100c00300140903000d000d000d9071850a040c1c0300e036004010b0101c031095400754082c000c00e00b107071b403410300a800601d4118000d5443e0b99103169695110b070001c0b6010800b5009010310306100c008042506014410001c154150307110100c40100d0087d0068001110340c40e08286018548014400150008520a07503c000c40500b244200341e400b800e1a501540c003950041c4203000ea0701802c400014115000c030b261 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 928803228 1250 928801978 928801981
    0x30a02040f023711101409010f0c050f0711031b09090705012705090a0608010e0109122303010f050307060203030c03061012060b091e091f032414040b04020108 70
    0x7895030504400c00d0088181703078540314007021056100081e151044225000802c81c80c110103000c03070181da80800120000400810006030100850000fa0541c203015644e08100184540080ba18110411406e160406050600e408803440c0c600030055020311040d0140c1500ca24210020303000a207c0300d0541d400d600300402e0004510100c0b050f502c000d10b002803202599003000751400c0002c2400c0d018440040d401c0988066007084140103400c9265403000701100c048038420400c4a22481c64a0355074108028600c0b1848820000340c040c5001c2d1503216400d00406107800704040c5002392030380c044020354106000f044400e960090070303698170160540c0e805a0004800c0802c80b114005100c0c00001e4515203100410742ea107201024081988041d10141c020362000050940005401c0308010b81c0013010400055045502c007403112442c0305c403610310040c42922960f5960607541c403900390740f80f4507810b038858000b50500c0307000300c81c605440c002565a680c2081d0b01d81c410450002403006e41400a80c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 928804478 1250 928803228 928803257
    0x1d0c0307050d230d08040201080906191a031002190c0b0103020d1e200609060d0216120c03030b060403050a0b06190e060a050103050c041202030a02040f0237 69
    0x1058440300c0407003c01926001c40c0342c3c0c4005030403104103440a81c0045c0d802030015a0203c000641b8a008560444c90260f08124107007416024004ca246041e051103907142d10000c0301c0c1ca040000b00862004610050380303520381c100d645070a80007191141410040e044c002c100108180445c00b2741501d40588511010300030504012443c1c10411905040080c042500c6a041c070070440d207015410250500003556107040c034000c01c00d003406201c031015480301c0200410802500310754000d1401d03c52503402c0d41090240c3c2e459001c007201c001c020038000702d00700c2941d84082581c18031030780d400d000003160b1003810030341940c45440c1c0d0b609000c4001042c50500340c000c5070351075950b060390310405c0740100b203402c01c00c50f1240011080240c040d10040c4c002c0a113040c0c0818998001c7c041d1906c191184100f42c0d05203480d00c4030507800803044440c20f0381c150240c42c4042c40540c032140152011006d5500b03002d40c2c1d44040000e42c0000211090b680345e050768140c00c090121041440358213078480050b01c1e04105000300b00303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 928805728 1250 928804478 928804523
    0xf3206011202160c1d010807062c060c0d0e060f0f070501090c080c0f040b1c2103050105010e01030c080a020d0209100801080f0105040302070506030403030f1d0c0307050d 75
    0x4070090842040801c0c0010600d5140301c0c0310a414645c2420003141e81d0ba2006010307038902c1c150040720301080ca0005800700844018403226058110a09030031040c0b00c0b0400890919801444600441c0c0c02007a05000c40540004201c40900025100b03a850300c01100100e8525002d07804803075219207000a1090300f48082500a21078164201040c805565500c00409a0710301404e5411401200034071b4400380a85483e100341030a580f070242290f480083c81c0344008850265908044440611841100104501038003a06841041c10f450001d00c81d4102400503242040c81401541010308082c8100d031401e0341f20705a241c004504500158a81481c860100064020229004e03082580c20000e03500480c0d01100c0503040b1034402d0300340c441407a4024400d0307082c2c0d101181c0107005030780704503802c01c403900f0b08000442e8468028680010030004a08003001941c01400051034011600c1e40c0f442c4041c0320522405042c410101c00030280c00f0301d40404182c20b10081c040c0075210500bc00256202d00d40407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 928806978 1250 928805728 928805767
    0x301030f2102010f0f06050a1401021c0302030f180a08090a0302032b05070b0103020d06111314030f061b121e0a0605060304020f01030f3206011202 65
    0x52481c281e001062000000c0c0202460440c0916450801c0d141c0507254200c1e1007200e05070380c1c001d030000c1d40b014106407140100341c2925041c10304612070390303682c002d0404000601d480c00c00101d541c0940c1d070f410b01450103051b40f8009009007122001c00240400030080c001110102c050b40810710a464070980310029040c0c284590003c1c0d090300480c0c03484104503e8003243c2c0700402070743c2409401c0040c0a072204894500410100402500600c001070007d40b6040001d8025076115842c04110f000c5507120900b01ca41121848420700020504148901485400c145010740c10036402845c10804200d0301543c1e030540a029602800f0881002804c10035590045520134920412000c02e1420a050310002000030b803d01c180d000d40082d00401c0c8082160b026070b901310744000b480e03030b4219282d903020441e0724100480400d051603070391124800210103602440c56240030482503041d031140b030080c0540d00c1117030b88800c80400d080e40f40204882c0d0f13a0410188910b141e40c8801c0180c44500310040c50024242 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 928808228 1250 928806978 928807013
    0x11100b0a05060a1116060219051e011a030615010e13020712090902070812101a07060506030705010921080d02090f1023120f0702150105060301030f 65
    0x90003c0c0d0311003c2d0350070121100851424904407a200c0441902962100307250740030719070041e04446442442d05502c107100f001018005e40079500f280c800d400354245c0c0d0a0002008540c0343e51280180780a10020381180e1001200c280c000e0306440c0b900e10112811075401c001c0d0700c0e0501c2000c0d007600b042078586000c90b290103001010115a65441401e1600108070480c0b40e0300002010610085021945802540e0000c2d9100304500d023040480c441c0054904c0000740070058003202c80000041e243c1f6040c2a10107a42c0c84c1070611907a0f00400d040c020b0541d58001c21960003540407540401c00c80e6803000000f01100e00b41e10501c0f007028000100790300140800000a001c503140466030f282c85c025598000c00b00c41200301c504402c5030006005000ca04420800c0c2d0340046030403038001942c21a80750f0024090345044003c00751402c029142041c01c4984117645100d510002072042042e260740400001e00482006010700f00c80d0b41c90400001c0c128401400001e0101c941d401707204003086905c0300c41e13414001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 928809478 1250 928808228 928808239
    0x170612010b04050a0902190503071703090a0b0408011505090a0b061b010506210c091e040f0201080105030721060212040308090706030e0a1403040806190c11100b0a05 73
    0x14012401400340505035410b80c41250a00c4141a0215042e0803147c201c1c1c10150140001d2441c083c07620710103506029141c0903d000420824507540d40e002041c0c0b0140c28510b60568640d0304042025007103d002403c090700b6402811424407266407050042c65000c0728100010401c0a1800c010034203900403551009405001c004107032400800c190007082c410380080e6440503143c5a401503c151129034002c1c206056041441146004d080c0802440e6002901c1040d8a22909004020302004002140c042e1200c542c00c0341e04808640c1e04c0801c0d01c0c01044110300420101c0e040103102400b0f48165840000c181c20418002800c10400f901510030788001d880c80e1415510305401d010f80686001c681c200b140d80600b0780c002c1161402442407049610000b4000d00310203089954030b0300e004201c0d14a1030301c0b51001348000100c3c01d10810103148a0411240c441010311103004055040d80e00020048040c00324100711707007050700030000302074030021840b06010454852502c081010420703250440f0f03130042c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 928810728 1250 928809478 928809481
    0x60a05130b0909060405160807091208030906010b09062508030f0f07230d09120c05010e0303060d08090a0b030a0207031b0201020c220515030c01170612010b0405 71
    0x81004019100c041403e45590700d00e5541c40c0200022268110382068840c41402c50304044d1510400800390b104582d410280320040d140d000c400e0048a00310b408450340d400004c01c21071a0313403043c0310450051605039001c0c3e040020383e100003200380c0200283c26192102100c008103000790303a162010501038210001599070300701460801c01e0361008840e5035210b07101c3c2501145005102d03014000d4060303101c4141d4602d00900350704018050380124030200711291905000808260045244046034540740c031401060b41c51381c074240c0d00391080c001002c451034009100300042031300c0b0307000060b405540c400350302c0da0390310b01a0000a8000650745c01c030a801500200400c05c810007540c0c02406003501a4484a0b0029001c01c1d040241c5040ea44000b4010b0300800c0909010381060303a188822010f250890800c242c03852840700040750801c980e502c40d49000781e890504030f07050a000c00303514a0300a00e015581050610409a4084005043c50780104c80202c4103c0e01c02000390301c0f443c0c0e940030092061005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 928811978 1250 928810728 928810739
    0x180607060b040b0f030309010f0e120a0b0c0c0c04020f220f08010b0a09090c08010908031b03090706110703020319051e0d0e0f061207081b0702060a0513 67
    0x41490300500c6020324070300b00450781c1c40e1808003213030b200d400700060003503240a181000444181c0c203007411810501020540c50000c2e907071004c00b024115126040180820f1485003090b07601c1c404098007100001800300700380004001c0200d600b640b9408250780250f40d402049222042c18810260316880d00c01d11003505c07440060f400d010744400c40b100d0b01c100300f403860746411455007280c1c4000c0042c1e034881003022081004035020b0b0089503005000314840c80740944e80701142c0d42521203210703044641da0000030801150010030f020b420061080c1030141421031a002528603a0342e04180903080a01421203442d11003410100103d10240d40d000d400d43d40140d41444100c02516403034502203070a8082d2078000901400b0941014a090700c03140010255588100f0098a400c02940c4840741c20014850540080d615000014000d201148281c0540707494100d100521840026282004043d41d01b0303114024003401030244c0740c04c26012110b0a03500c1c03420041c250390600c03882681481e40091400000796 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 928813228 1250 928811978 928811981
    0x60315010c1406180738120f0a0c030c2010020a09141c03080402040617060402040501080c0f01080c0d0c0207080c01020303011809020a350307031418060706 69
    0x44e10302c41d07812900d40131703190007030403041d88140456418414041c0200f400081400e0f4414451500030402c0c0c503207490305951480d1042801290f400303968030140001e01215121a00c1000200349203850104004614040010001c000b07910184203034414001000d51302200a00044030b41c109090021075403050b003004081c0011000e4880c10604000c41d40000106041402d0b214042881c8081a0b50000480c0d0b0707016140801c025100341d81180c1d480101140908413031000c030b000780710711100829071450180304200558905800232101c5800400d0b59201c10340b641d03102e141c01c0e21400d090509081d9909403e0700410700904000620300d606108a14000540110301c803030503985403c0c1698443c841c00b03001a6035030703c400c0c4109859040c090511003040b0724650f00007000c0510040000302c0c9156260340841c0400e24400702ca8500e020790310344d03820f000c00214414169161030359010714180360168401410300c200b800c0e80c0700954800006c40c0d0381e005409250303011900900900850302d03203450381072410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 928814478 1250 928813228 928813261
    0x70f021e10020706090f1a0a0903051603150905030a03230408130b0f04050f01050c01050406020c07120807030c170307020a0b0a0209031c0c020901030818060315010c1406 75
    0xb40401c0c982140441c490071260706c00820b654041d424030101c40c16210700d10090340e001c000ca2004006107210701100184041c0965201d1107011a10315490a0071410a882045454208032000515040c0c045000483c0030064482614040c1000201d040030300b5466401c10000c060348024603a201c804100802400b10090712000c041e8095840c0000e45844540105101e03ca0151141c880140030402107468800e916100091040c5011801c041c1c10201460968600359411958030f0b80214045048541c1040328500030007400200382c8000d10540c5030302c81c141c490698040c0c200a03a401c014001d0000b451607010355039409068040d80c0e442c00010080d250072043c40c04907044945000807500900080c025104d140074010050841c3c4035210304c2a100c800280c100903010721588180c12000741e61540c0c9254003c50040c4142d0345e45410006e507840c00c018250341c0081c0724460600a0101510f04108520b107520000e082c0303e400c0c0002420701c4a000341d102290600e00e8890542041148000200040d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 928815728 1250 928814478 928814489
    0x90a090c09031a070e09150904080f121504061805041106040e0a0b010c0b07030914030a171e042d120908030316270e0f0a02070f021e100207 62
    0x17a04507079007040f40300d000c240d40044a5002100410400340380c80e0705110780013407003501410300c3c0c01c0c01440d241d02960004d950b5510300d05414020001207040d01401e8a40f1002d04031001c008150601030b55150050703441130405680c2d907548000804004101100e02c450350301c000d000f0743e25036030b4810109090103c103d8000c80964101903416106501a8442e809402d50007030008900d03540d043c900f00e005110040040e240000340d51b55841034138a0500041c04800f003180d54100f1510849003c4050201e0003031b0044884800c9855520044442c41c0121074110394011100c00c0e5100b04400c01060460801400000d07055101a400c410440350000c0036941d14015212107040964640e001600c902003100d1078840c0894216103008030600c0740070b03003c0d40b120030120380819501502c0603410482c001c2d80c000840400c403040500c07010784100032034540c0c003001100080d07142080d42e6071092000e00c65800024000c0449200c2c1d5420503404110058130400f003c0c00b03040100911800081d91911a80b050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 928816978 1250 928815728 928815737
    0xf0301061214060114060a030f051005040e0f030304030c0c05090109020301150306051e0d0816140703030c020405040809090a0510080604081b0a050303070306060f05090a090c09031a07 81
    0x44100b40070200d0154129211084001e02d004000070a11401d82d2146000c0000c05030740300340c2a040342c080f40c0b24a0b03000d640480603803600d16080c003051000311800c004100c1e2656100d149000d841e1b0900100722603015501d450104070020180c6041d0302209201e404c07480c0d002d421140042070300340d0b0b2035018504a07855803400281030424a04244e04551a60040c0b98000c0c2900c005010a010038a10003c2c20b40e401400c1c4038031422098845d00450382180e0400e00140469102c124140310300000c006100a4400020b804454655030300038048881010000340610303100c0b0001800e005180082c0c3e03103954400340108413249041c00c410402081c049505078180100c3d07080c0030400c903c000884611580d406042546082c01072629070403010901c4c4080603540c480e048080c000103005002031030240e03921f910045882802d2140247c1050880105042040390511807014295584503c100c211125400001603044da01c0c40b003125010320729003001d02140d00350700c00000d03000c80b00080306214460507560f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 928818228 1250 928816978 928817003
    0x7080d030b0111060711031209010b0102010b1c030f1e020703020108010801092d050a0302030d1409060411030309220c0c08040b280c1a0c040902090f03010612 70
    0x5554090900040c008191302400029010a00908a510842c2401401c0b81d0410303982e42d0b80d408034000c04540080699448081442c2d141d43c090103a415000c4003251929202e44410b54100c40b01e00704054003408000410080030b28540c000c243d82901460082c030303410808021140042c2d42c4d00031038030003240050415800040e1000d01071003040910342c0d020034404070b1005282000b10301d850f098081107040381400383c0004000340081000314001480394010b0360b100d5049a03007000c01c8500010306070211520b0941004044032020881a620a82c0710f01c9812a070469440484d10354045c1c81242508060070180c1110602c03003017020001e01407a00d4105100d50b000120742180c0d941450a03001704044400c0c0401e1207c4200407002d002c0340400c5414071a41210b18000c01e14504c0703c004d80300c2c0c021900e8081d552091000150091044085040003a40d841c01c000d00c403403520348628400c52040682c00705160001e175a686203407500c1e0301001802403002540303456811580001160085074002248103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 928819478 1250 928818228 928818251
    0xc06070807050d11130f15020606130c020c03030307030608010e0c0a03120521010302030c030a0209280204030503250305030c2209020c16080d0e06070507080d03 71
    0x1069184035034079035640d00741403440104448002c4d00c0040c10340e03122104140442004500042d140030024455000101070351072400b050303a001c0c00c20b420000c00454200360708218058803a50801c5e0281d03943e1a500040b46c1d0b4014104900b055000d2001c1c9030315000010a00c145186d00d0b420a10a940056000300700e04160400860380e148003c0c0131503908490381c42c0c0200701048900c07022a5181960f030406a103000350800e903090059601d503040d1414658404010720560078100011256843c094004200a903035130740018044050081c950003018140c8031401c4030f08551034942e80b4907013194010954a494036494581e440b80c020307468178118440580d40d2080442c00303240c0c60560064060312038074503603190340000c482180c0c030030320440500480131071000d1a55501c2d545a03038000c1c0b03041540141c03286c0d8103981841c1081d602180290160105403024003a007080400d241c80c0f502d500b0309203010301e540c4540200e8864041c0c200c0c050003c1c0162100081c3d01040451002c00340343c0d5544d401c028031442c41c4e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 928820728 1250 928819478 928819487
    0x30c020f01140606070c0801060810060b070c0b0a090e09060405010b0109060f0e041d0a11011d0f040e032b0524010e0d0c05090a09050a060c170c0c0607 67
    0x30008458044a00800300f00207003003410007132045600415070403140302c0e1178255141c01c0d00c40d070341d006908580c4109080403001600388036020150590b100542d05c1c054498039400b40c0c00c9203038018600b03004000210800014025540c601c024500008042150314011a6941d103d1004030f070242c481d5400c00041000d6507200e4613070182603e0b01d641324002000d102800c2181e0340b00c00030b071680340c00c907681e0340841c1c81940402980000b007004e200010001c0c60810314186c07a00e07800c0200d0701410b20000c4021000b0b440e02c0c690581002040030ba6220a01c5100c0500040281c9896070302ca80840c0400207091a14200607a80c883c1c000c40440e18509075594440c801008860044600300c0440e000491100703100a001c4d61f9007040c0180c145000c1e10440c4103040051042d2000700707001c80e045a00c00360104400c4c04c02c00002e65000c481030303004004002254071042e843c1c0085a4000309200d980320f4501411500803102c1964009541c0803240c01481c01000c0b911640c0d1251841d07200f0b82c03084000086406109 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 928821978 1250 928820728 928820741
    0x41d0c03061e07090f081e0609120f0d1b02010c1409090613150e010f06080106080c130603021c0b0a14040e0105070513090e0c0111011506030c020f01 66
    0xa006219204003902c4400195060303010b03100303400f00500071a000800c4018000420040d000b0300d0050504847c1c8442e51944100c8500320300724854112008200175820f0206409406601c00f201103642c0300011a0359070258400d04000c44c514502d841c0700d00050180b81100300c0300f2058550001c0000d041035600940f5130021503640304c1e00c50082040180f01504000e94220781001c0041d01d004110820002c010040e95007044151524601d0030b0f808108482507500c0341c40c0148650050791003407a042000041c080041406010240004440403c0107240701030112000040c0300703158842e0072500d90f917000780a9400340006a6050b1450f13420040800f01c10710400600f841c0040c54224140c0c900b20f00c00600e620398404050340300703a03106d07600c583d0f820081c000c5900c190103030340d1800d5070340001c240c101d01480c40319003003803500f140740035264600040c00181d00e0074800000d08040c8020008598801c0c003612501c60740a180c2e01c2120b00010b05950581c2250036400d0071902903c0501c10070304640c80c2291070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 928823228 1250 928821978 928821991
    0xb070b01120204020d09060b03010b010e18100b07060b1e03070303110f030711100804030f0e060412060b010815030c12030c0a080304051b09070f020c041d0c0306 71
    0x21400100041504800e5003070000c2e00c09030025080c80c150f11a11422250008000c0d00c1940c1c0310710050446187c20b22460409000900b020b14071452840702107000700410301d900a503107040541c045404600140104002000c00608503642c8254074984040645050038205025035025004021640062880020b108170003074018104c0c81d1031900c044403121000c00403007030540210f250054942e84144002d203030003401101c1008901a042c2c0500170550031900d06003041008040030702002a07417010f440100c0701b600c1d01c4d00704501c0c0d180c2c0e00098044d2040e6072207400c03860486000942089110340010419107801d032515900b5648020a038a040e0f20041441507064101c01c8040c0400e24084010b40ba012441204583c1086818540b003460300c4142d041c269604000402000100078040140380c0b00300e0014a151000c0c010760b0300201e0702480c400703801c21040c845a8020412035a00c200007075034a101d03000704148110000341d204080110440b074178030a001e000305030307003a041c40c01c00180e41401800d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 928824478 1250 928823228 928823243
    0xe160c0210140412021f170705120405010c021e030901080c040801050c07050f370b0a0b041808040611010204081c1d0a090e0c15090102070b07 63
    0x6055508104200615601c10820701424081c025240e2910401030006001e01d40c000c0720041ca41c60040000d031110b920f060340c0006281081c0c0f1220305034040c2c48000c101d50b0a200500082c0c403003202c04d803001c1c01520078907090b9081541c00c00080c00415040204074500c0b58094031551886103000e101c0d03140c0c555100702550351003040703180c03040c0d4441e00c5060b80c040881d111207030800b5146d05445080d14021399030803142880114040090004c28030402900c1d04015004002c0ea00c4031800140c1d113403000584034801081648030991403c100d40d0034603243d0a40c02000400280303400d088074001032500300c8069028502d09800c2c298050454204856107941000e526801c0901e00b42d4120b80400e1607401d07c1505540900000410a80400068460a90301c1400c418081d1603040004e040720041005071082c0320400030322928940780c0d44002d4041c1d0300e2801010420490800c02c10f0315104c10030049540051000c004030543c1502c0c24003502e000c000036400c1d03494582e82e401c00601240143d04c070140114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 928825728 1250 928824478 928824497
    0x601050604060e040e0703060c1206030b040f030c051c0f0206010810090515010e07030e0a0f02040f2309210d18080703090e01171506011403010308040e16 68
    0x543c061402c0300070b0a10700403c042004003402c510035003010315603401151007070703210360100c60749a4000c4451440001840000c0212901d59140e41040310f202400243c130903500d45021005143c421050301d222180c11100300d074540351103217000318403d201100e891800565110310502d2100d1000ca040c5040f81c0851005168003040081c000e4001c1c11f40c904100d0380d51040c0200c40c450312a42901c031500800300c81d100184c084ca800301014041c6d4421112083c983d0300320084400019285d815141c1c19203030151000202a20340c00f00340c900a1904200c0010b00e049401000287c4081d030480c0c1c980b01d000100155a4201c800200c80502d400840c0f111380c07810001808001c144c2c100a030b1009009154480170702c030480d00d06849486940d03200d15402d40000320200c4040c0103501d05160520300401020b21941c2d130160700c002886d40c4a0b004c402c4815a803070204804207045a202e0542d010b0100810792201d60f49596902d0802c81d15030107881116500c00e45900040d4184140c600b054052445c0d075142d10154 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 928826978 1250 928825728 928825739
    0x1104031e2117070207030f03020601090b060c1f0b04090f12020c010207030b04021503130215090d0807020d020a120b060d020f04150e090f01050907050d140c03010203040c0e06030601050604 83
    0x80c01e20041030750f01140b003041000004291143c5005400c14000d402901d4503504206c44c00c41581d682600241c0207160811204030601000208108041c0c10110f0b18400c1c82000d400303410142c9611050144d10074101109401031001c5203420380060b501c50044a18030006015050340c84010b5581e206001d43c01145007000030844140c0c0855025200410514607071854209070322842c0c00644000868070480c0c003e000440c00c186034807602090f00300d114241804011800110fa08040d404020003a03440864544110348600500134109603000300302400080e242c01c0310854840c0b1202065818440701c10110701e02e81090400b80d00b0b4641c000c9c0c030b1860500606002c0c0b00141410744038800e260041c0140014000b82002185400340510502810f503014000c90924203480c009000d2401a821013202000a0f54440c60030303602c0c02d50300084109050711f40041c0c203030400004d0a9500d426500000800c0308015000301c00038280d944200c4241343c1c50f241d034000e059541030240111034002e4001c20043c0712 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 928828228 1250 928826978 928827017
    0x3030c0f1005041112100c0908150f0105190e07020c01140f180d14060a24151b0308040c1202010206040809040b060d0609051312031104031e21 63
    0x8050131607104070746a40c14010b041c00207c0301c00702240320002c0d01414003441408014405a80f5580743d0000f481b07854100354030550f140e80018480d0034820a4003070340d161a8200c5140c0780800078400388603902c401d480c03c00d02c040e445d6400030200b1400075a19282e02030407002c821040c1d943c101124401c1034100001d88458103003010b02004116481104007003c10f0004001200000308101c910000e0030381810035615241c1901c1001d003003810041102034a04640f4684450400308444c840407440508030031030300b0150340c01c6a00a080007500740203502003030309040d0013101090199114402d00e4440c0b503a62940c1d54100501080000d00680025000c1008504503001424442c0c80052000840d6442040001c400c0d522040c41c8400441d1109000c003c44205481800d1340014050b030007400c00d40b041d50701c40f01c8000a0364420310906a45425080015607014192400b441e406054240c02864010410788400b5141034100c4010440081518100b0241032010b8003e07145615031303150320040380b0740103031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 928829478 1250 928828228 928828249
    0x90105061815370f15050d1b120603020d02130908040608010812070b18240f07020f06071805040f0e010b04060f051309120c0b01080c0d0303150503030c0f10050411 72
    0x4001c411b02400088020600c1201d400801460623a0b0041e0a40d403400f4008105a006c2800c001c0c0ca0b0007010805a00c5100c90400c150394101c4041144c00070300c40c2824020424514050650200450007044a94101c030010b410394000344100e842c03610152807400028400c210f00100074152010102d4285046410980100d0915000b503400a034010744003c1d00c2080394078142d40c42600d83d8018003083c0b8080c60304423a00800684045d08800514026056075008007400c100c00b04641c02c21180350101c451082c00d00941801802031000070109502c0c0c1010b4400c031a9101c600d0351800e41039201a20785446140304990740d682140148074540701c00c000400d01e1030f158040a094075030403084002001c0c40e110402112090f00c404100055070b0503e0041900160010b034115400704180c0348190342c1d040c0c8080e03040c41c5e040ca404039070408061068003005095030703c01a0144804269810900f0b00820320301c141c5c0c41d1074000c1f241d44450b801c3c1c0c681e05540d0192005001e00031801c0f65101c1070300700380c09102c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 928830728 1250 928829478 928829519
    0x4061b0201110102031e09060c1210091a0108070e0306130f1e050d0f02030d021602030715020c03031c11040e010b0909090105061815370f 61
    0x78860b01c4a40320340342682c0c021500700f100010320622040e000c0c0030003d030440d00045018004c28462078502020700072486169480180352000d1000980a00d11070f18211001e040020410310588406c104680d010400c64000c03103000c03501c604001a03c6a2281d082c4985c04100100100388586401c019010b0318010600300307448404031070742e800c0042070f40c50b001d982844160002c803441603005810024205046958841308004041d2100040d9607030000540d003240311007600040c3d803401d4142103c82c0c410020794009403d4010003100240c0404045059200103505800f80c8207c40e10410030551680301e4007481c0000a410403440b41143d03070f850f9002d40c23039100d498220f5501d400d407180800000d10509074400c200603880000d030b4102c6814540c80064100c070f0024020300031401c040001550510480110849090070840050b413a80061000c4195462000d05040c0c0081078a65040a0400b4044441c1a1400d180b903600c036040390340c0f443d10f4070485110848200741c0e2814500020031015110100d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 928831978 1250 928830728 928830737
    0x15020a0b040210030207060237020d080a060306091202100b06070b0a15030f0c0608010501051204170c1e060601090b0a091d06010e0109150e120105040b040308090304061b0201 77
    0x9000040080c030041408014101c200c3d40328004070034003e8134480001e80c03200c0c0801e400004180c2040d0300040c4bd013101010a0030206616076440c60940014249c80e40080d0401e8181646001806001c1680036841e86081d804d40c2c0800311200b2800c000e07108807684182d000801046010301040082c001d030354100380d40440105810064810b520392948954100365150410154403c0410050303041d000024200303414201503961525001078100c1c00f510360701307140e21400716001404220300c228110a074061130b02c3c901c50f00c50410051080e5074450300d441c070843d00b12240764800c42081000403000d1084605940d004030301814458014200d0300160302040a01a1426010904050a00030700311035003034090612241c2d01d00b400004050720056004a4140404000140180c0c828050313241c54000b000e00300b401041e985e990208042014104c0240c8007035207064103200401a541c11402e0142d80a0341d201c1300d05441b40b03503500f5141d00c00d922601d0040fa040380720407135215010b14060381080307005041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 928833228 1250 928831978 928831987
    0x4060804081603020303011d01210f02030607050702040614062d0d2c120a05040509091f0b010c0605060d0b07120c05040509040204240f15020a0b0402100302 69
    0x1040004076250b1041103001d0f810120052100e1020550f0720100c1c01c080460041d000e51502c429041e03401c01010380c85218520000700381c000e001881c1144008140d02400726109850090001406a04024001ca100c0e82c1443c0b000030f21051030300c1b560900b45000500151610f0038041149404900229110002c020780301203500681800002a09a030703c803249022407420340c0703660f83d5604c4216034801180c0c0c80b03880302c03c00c0007800320001f82d5081d0013b00c1c01c0250b5a8a40c078040a0310305002c0da40c04940d1001001003008514080814410645140341400c06202e1f001844a9010303905c1020701980001c05441112011460303941040703810a4015000c1e00e10f902c50340d02d44074802d0074111066804109400c99400c00b030215440b4201c1c802d07400d850441c0c00c050609001035512503000d0030283c443c9859140c01080c40c0d8030140006036a0070000380c0c504650760340b450040e6481c00c203031040c14007190b4110900003031180007144e03056903141e20980b142c11aa84a50804c44244032407002c1104160b420711 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 928834478 1250 928833228 928833247
    0x1b1203040e041202011e1518090308161b03030615020c31050702070503071d0a0219200d030902090a0e030315010201090b010303080a060503010b060406080408 70
    0xa002400394810261102e00d05030400c5a88440380b868001d0442e80341c80307180c4500c082c4402007585030440c24940404c40250562036034030710120a81202c081c460390f0150a131141011030b484032182d00e2081d01d0b07588107903588001256120002e11400070115401c0703e0322550f54080104c49031071591081c100000c11644401c004a004400c402202002d1b900441c8003c40300d180244107403a240d900341003031402100600f04068080e8104450f010030036611500450b58460003806088080c1501030103c4800c0c1c4c2d51040035541094128100c0300d0586440b5020400c045028000c0301c0c4400110000642915640442164078909906d5140307007036241c15640c146a00c5042c01400c81c0e00035541d9010903189440e0040002e4208058843e01d142c03450f1403070400c3c2e01c00c070100650b5489000210801c142020460050380540306840d00100084540b07030000c406c064211904034080c1c203080e90304000050320356051500702c13260340d00c15542c400c0b8113020400a19108100b5144c0c003610656803a8100101c81 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 928835728 1250 928834478 928834483
    0x3f01030510140a1e0504140c0a0503030f130803030702073b06030a020618010201050112020a05010f020c0a150809120301120309080102030c0703020f03090a06050c01140906070906020f1b12 83
    0x2070b030741124000391f1148107540d104030810183d00040b03011600d5402251070040084e60380d10600035071084086000c12200707011328414450000a1028105887e52413804940c001c0d21101e41d40070304100c02243c140024510b454242c3d442c103a4100b08111300c0c001c00240d407c07451202a009109507418800c8844200c0140c0312031014026940c2003140240d48484042c00180c01d64005070065004c1e110503035000d00c05652030b0598901151001c1c2004142c0b5112010304030305100d251302403282c000741d240d28000b030002a6103079a101705565583c1d41c00c0035601d501140a0301d94034407114014107244180010300000004858950501e482818006500e80e40c4011072400d9030003ca8041c1c0c1c280c070010600e003041c1a010301045195680c450040c41c5020184000900802c1c018000c40741041000705070f11040340801d46c40002e80444041c3d03510954645682c10315a1000212010703400600112000a220340c00020303584c1054244102400c0000c001521401209039031030350b416030103200f1075041c4080710001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 928836978 1250 928835728 928835731
    0x1b06040620070b0a11060c090d02060d0905030d0506011704140c030111070203011104030f031409040f09051c02060f090304030c080303040b0609010303053f01030510140a1e05 77
    0x1c184840e213500400e00080e269482074042030440c0e401c41c00400011414070401c13587c6030b0070115406007040b070007400841d4441c098252400041850191443c00344080003015283c13240c6080814445a81c2d04001118800d10038811100c002c1220030100b1f0000703c41203580d101429088c404c460f4a0308180c40002e0a42e03400c0c4035804006ca50005948089d402c0a01480807022000325146107400d14542e15951001c518040c05010461030850a90064050008803504000020018044029142c852000410507001e04813039602c68880e00314120440d004400854840c643c0160103160355101c11420000700040558040340400c01c030100019004c08000c00203000035070001d684900d01444c00c0810200042d0140b88200c29000c01080025403010440d5900c8880000b540e20005000b524800c0c00c0100d0b071f10801120f0501081c00540040a0040780d048038010000c983d102e0041015020440d00f904069a100700800800100400406d07000f0301e43c0c2030405075003030b0702d04240c107018101207400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 928838228 1250 928836978 928836989
    0xc030603020f21032701020a17070501140f240105250206030c121f05010c1403030a020a031112130327031103010608101802030a030c051b0604062007 66
    0x5c250041d0242c85070541c90705c28a550080c00200504005500c40c02c006e101c4800b40b0b422107007000140c401c10040203400005000c401c05551442c0303814203104080389910101c41c1401418401641c40321340b60b170078170308040440406031541403901d071240c003012011844030860300700034268a03400c0a0068403544020b500c55421003d0060300c501c0c1100004945400242c0801c0400b99265503880f817000c0b42d2040345045a07000d092200500b0b1152a00c0c02e9040b90f12003000e42c1728040802000f40d0008a500200b215824030383c2c0c10450407070403d0001006009000ca11440c00440d040040d450500038580c0300603a5020b410403018945030703400c0e0589480c80720368124800803001a001c0082040382d410340584490110000d22440d801c00c0c040560754642d603440b401c5095142c051001c00e824000e100c5040715500034043ea00e1003411814080c200c60310b41030302100c0d82c1c4512010310102d050365442c164a8180003e041a14243c42c0c501c0c203c0d80000042c16040d182d00c1e041022201f640390070410b5000604 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 928839478 1250 928838228 928838257
    0x9060e120106031b0e01080d0918150f15113a032703080a0b010504050405041a010e01030506010b090a050306130308150102070b0a03090510020c010c030603020f2103 73
    0x1400c08110006104040c7d2280302e43d0f034040030300088070a8004101c1c4080c1c801c1400000c014861100e1785078080c004012049112440802e804240c2c60403210a031400d0320b002080784680c00d02c0036070f012a0804039503610000c2039005407000488001100400745182c079068505d0a00c09005188480a15490f182081c000302c0d5548600d040700d80c99030303c3d65002c000041c0041541e02c000c40e4402400c8003c00030440f00c84a0340d6034180c0b230240c1e030060040d81e000c0c00d0302401c10859032a01d80390185c2000004001078600a03100c400000380c1542400d6202e041c0c81c1d010014001e1360b482d01c4419007484e004503c0d00d56001d81c05580124071618200040ea1041d1900382058910040c181005031507202c1c003400b80c80c80300c15507407611941640c0004189040724075825800c1da071901d0201049008140035007000741103004000b000446a90b868024142c001c000400070021046101c0c82501122440d03c00290000d41880000f900d5143c8951114640510380401c0300784440050003107400e55114050000c20312 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 928840728 1250 928839478 928839533
    0x203250b15010905060c03030f07020304080703031101050108070503030406140d0c0309032c060c030c030c060907050303040e01060c051e030c010e011a090712110c01050709060e12010603 82
    0x560f44440030034020401500e0051401640031200d079101c1c8001001509201d81c3d28000c1003043d13100300b003120020100305c1c050b03441441e10b070318005081c070b00d00c11001e142c0342d0708100002ca01c03030401107440002c4441c010029490549008000d40d480141c0e40c9004101450900540c5da540c89507000e940d056601070307600000e65a0346c0380380280503040c1a109003041c1035103203080c070501c40020f00310314501c3c3d041c219000303612900e82c00029461841a17029801c0c05000108550900040006240b4041e0940c0c006841d2150340300e60a0503603e010743d200e00d00002d0b034110010002e1501034821803800d140140c045c0d402d200700c6240c001c1e840c44000d80900c100fa07400011450700452081c8601144101010024040342d5410340702c3c203600c50410b816462203014480d002c0b034a494061700102c0f500d809100424041c4414000b112a40754102c00c0403040c1c15420040000c1e00544910401402c0c0c03803070783e101c800340300309003030240454540301c4407401c9010b40d601c0d40c000c004500701d001030410714410b40d81160082c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 928841978 1250 928840728 928840771
    0x1081603024506040902070816050f060c1c020c2b090503010203010e06040e0a12080712050610140f0310030512072411030709140109060203250b 64
    0x2900c100005030400b4a0b03401800c65003603441904550842e5070410000d80c0301c50742802d044080c0d2103450312140011400c090000700b00040130400e10301007012401a12815070b01c6504d800385504c06c000f10a08544946c044641040925502920003c06980e0480b1403408170380c02e6200d00902210650140c10a501d070610b0701c500d0307000b04548040c00e8140c0c02542103501d0010040c818184c0074003458410360f1541003814500004000040c80c2c15003007400002e1107400c4c044082e210100540c1c540b070004001c00100104daa249003e0503010700e1020b8826500501000422110500c2d45018925541d1040000c4118030501c5405075028100d540c100700910b43c618540285404584e001c003607045101400f0250108a16840201280ea1101c80104640c04e00c4500036008090030750030320540a80105c20311010724ae2001c00c0031309503807405040400d485403000041d00c0075042c13031181a005900802000c0082c0300f0b440c0f81c0c490842583e10101ea00303032005030380389108103c040b03614032824400e40340180361 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 928843228 1250 928841978 928842067
    0x30f0601090b0a03020f130b100e01020c0a0e070f050c010f06050a0e070504093c14100b0711030a12120c0e1036050307050108160302 59
    0x640c0481250342a10044c40d40c1d01141940c1c0c45041600d02c40c010080791460100525000403903003100c02406c03001601a0700303001810407080d0442042c010300c140d5007040003034288039044209840490840d01d43e25520610100c0c2d240c001619003008012061085100c090030074001c3c2c03118640b540e040803a407035041c4000e10144000a5016880b612810400e01040c0c0c0d8000080310241c030384140c804503685040b10104d0f017901c4c0f610441140c654038030b078041c840808000c402c90080d407000c40034240305100381c0c000d50740115401540c154031180c0d24500200403191483e4020030505115000e030941a445010020741410903000041d1405009100c108100301d52000d9800810100000d080201c2032091400901542a0403443d0740201c2c00680c0000303901d07009292801e10000300f5500b2622030481a036160001036400c0c4030030382c80c2210b880c1011946107130204901d01a6a010b0303448060719500c820100c8810440c482540050540c200669a207628100311100c5102d2400300c0d120114450360100c514 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 928844478 1250 928843228 928843241
    0x10513140601060906080709030203061303200d0c0203010e06010e070825030e1c11151b0714030c0303100902070c18060902070b0709050d05060112030e030f060109 72
    0x10150700954014400c80c1d4200600380700ba26210b240107001c2e6034a000c01554036045136007001e94544a04400c101c005181c6d43d6941c0c540c00d11070307986c0e0980821300c807046d070a10205c605090b0119030000d042c44070a180c4140940004140010004a02c0500000d500d40c01c01e0420b0b003041c03c11f0008007040009060300817501940101061000d42802c2840a5005040c500e10100712010161980340e07100000008009481e00c840701103001c400400322514001e88941c0e0303001ea0021490041c04103c80c0c0c0244d00c08240c0d0b02c030f0b00d0844682c0740441d20010099140d540080c108035401100540007109600d800c2026001c0d11005400555803420041100313070300c0e0099075001c0c08006004000f003900040030b5850040403100100c0040701e80902c500c2c000c90103802d20f40c02070100140b0120f6940301384100c0b0060117010b03607119168070a10075110024804c1440d00400094065804040108103100400f4001a400d1703003e880c0940e080424070300081e046c0b003e00159488a54844001440200b03014420711 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 928845728 1250 928844478 928844513
    0x2010206090f060103083a110406050306040f0e0d1713080a120b0d051f020327010b06190201050711150a0209150a02010b0108220f05010513 62
    0xc0ca0b0700c007600c4200950350001404014068480850703007405c00301c3c00c80c44002e68030310102511600c110710200080104032840200b80f100c2c41c1804d240800faa00e0300012102036400030703551940b03107540e60402e000141803451080603c0c3e80d501d5402d1090044c0074083d1050b070007031703030340e034040c100c0004a441e124650000b4010403440c01e84001000c0000d17540c0012a040d8140b5820400741000640312842c3c0200f98803100310781c0107110a0b602008215000c2040602c16120880c8144c1d0114591002000c80c00102c4507104038810301ca660660500c01c030840c2a40c0c043d489000426032810305030200d0499041400003a040607809241140d9041d02806096400125413818103130403503d103109140c0c0c990b08206440f0340550b45401081514903a038040b201c000001400d80340390424030030006401c9a002d2802c820055180c50f10200c0590300c02d1300c03600e0158146650303841c0c1051940c26101e00350884050b003124505079441c40040042c500380141c620032042010340c21070450300b50800d0004265041c4c0d14 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 928846978 1250 928845728 928845733
    0x6020123011511160f0306061d01060f020f010606020307151104050105070c0b071a06010f0203032d0103030519030510030605061309150c0e21030c0f01020910020d090311190b070201020609 83
    0x4405c000409c41812030448030140303421008214059801c0c7d081095015030800300754200000861a16000801010ba0790320402701c000c290044000300d04120b40890822a0203841c00708420001c940c8110042c00b15030780210303010900d456842c00b1101180e401000211004501c42c0394541505142c40081c561000080c01c00340d000d9509070300025100e11006003100440c0c440c0500d590388058980308111a40e86c90b25a41d80c507156181d04001d030141d00252070b64241000c0d01c50702c0501040c468012a8055103040303500310a01d60556440c0f5010304802040c1c0d580020707440911a0790300c0300a0184a01c0300f4058402c1c0100040080e6421040d900c0d010000020700c13441c0920724040780c0b50258450228050100c1240c2c041e402c072080c1504610407000c1070010762140c0520062101010350007808000400c031b4041041041e003c0c0182e0300c60224071104000b0655600081012959000031020311003c01080c041d054804582c80f27586c0c61403550040481d061002c0b44050855804100c40ca800c0306c107d400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 928848228 1250 928846978 928847009
    0x1706030d03050c090d0f050c0319081e0d0609060602010b090c090a08060a020d1515080c0d140a24180b04020406020123011511160f030606 61
    0x400d9440360994000d034200342e903550000d90b00200c1c08003074030740001c402024a41260254102045032601e00501941d06005425803220180b8000071100d50a500301103411a004419403221141c4e0340103101c0618444c505070b9401000b140107440204a1040351250010305281400d18210803640c0300e0700410705680c07400d60f03034821503070b1440300c42035000d40c012400c199074124072004205a140f0540c8010010301c20b0005200809032141c0242c4690248002e01300100b00807031038400c507002d01d24400c4030741c001c69403641e0010103803140c1c00c40c65000300b49180700fa107491000b40e5540121402c0031200a11252041c0610209032850b009408402804503d07070003541c0080030000341140d0042c0f2441c0d00c03065400740b10008500858100d501140301c000c00464541e990b071030000e07000e171850506420040c4000540da140f0029141600c0d410788003140504459001c0145082d9011440210810010721901020b10b091060301e0401e580580010741115800a01e103180110a80da01c1e500002c805d82103c1c00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 928849478 1250 928848228 928848241
    0x120406020a02120109121d01091802030a1e09060e03130b13050402040f080105060405070e0409020a0306021801090602070e0c0f19030222120b07050408060906040317 73
    0x128280c0d0030b82c0448046841c64041c0540600500290b40c00a290540d44c5a03101c00060300007082c0950300350500411031105809000450703241c0b5030742c0250b00303c240202501c606450a940e006d5640444010000166040a840b107150000c80030b006078071070703240c49446880422140c1d0180c4a00207010000444c00e0440c0d80d40c0404042c2c1e601d0041c86005d000210f610945210554800001400041e108640c4c3e1600c80c64810b080c130045028180b195800e01c4041816828940726540c030030155690782200d47e032010380400000d00542c0c007041e80e0110f9a06004001b151203480145900d901c1e03c002c4114184d1000000351581071240c0c400025504a284c0401015280089a0303a102000f85113203541e9a0903007840d800e050080103803420052502c60400e044464265000344101840700075080d03d8031440d002170746903d003846c1c042c1d41410300001d286000010700324035076030360040d14900384a420552200c0310589040012503e8070003d0344850184003e0540019181251901609541410b441d009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 928850728 1250 928849478 928849483
    0x10f142116091a0d081b0d0801060c2a18021218060a02090a0936051506040207150b0906010c081b0709060e011e031e05100603050f12040602 62
    0x2519540608100d940305010460340710b0803250810f0411805a80c6c0700203c0043c6642c0311040480e07070002c984075030004190700380500002440030b5401814800a182001e513080c28250000183e40d1109500f0074010511040b40072020040021800380140c581c08501024043c46078081c0032880c04d0350188164800100e00851100e9200b805d410015945090300e401085e41d072480703a8002a4540e00e0140000d080c0c101d80000c5a10b50711003e849003d00b140391030f003041c16061610f0b200404c80c2d44001000c09420341341c0c1c6481a4450300041005003045860303251900c84006090300104a2666450318500500d0304032807031500a8404e29160304a10426901d100d51482880791805a0043ca0703203904591540400901c1c0240c1a00c207000e100e21640c40105240d010b80a0040d40c50744030080d2208003264003100d42d0042201c0d0231441d030001c1038503034112040d0002081031061300d5501814403d4400004d03d4061900110b1040d0010f010307504061038414208000e8801130410028108002c00199500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 928851978 1250 928850728 928850771
    0x20c2b09031e022101020a030c020c060403030e030721062004170f07230607260f1c0e0109050c190f0e0601090e010f14211609 56
    0x1a03900391440700c070b6680000b5080213010500504100c0080415444060044d00644003e0000b500c052041c0307042460183d807500c03921800f040e0007003802c1c08200003181c440c4440b484805405400c2c0c2d440c079908c03444607004c4060070034040d00301c05c01d01d00d5424042028074400c14041c6064075140c000d40d10b0840c810301c03155104034443e031034020018030004811a43c082c402c811100d00c5a0341101c04095a4007028440d4085c029401c486162064015207a035041050807070301847d074800d590400903031b0605545103480700c0154240045020500c0080c46000342c1070000c1c401491044102e20b46100200458820b4607840c41ca1039034143d0400c085080013030070004a080c0606000ca40008008220b00c1844a0702107560b8048000da030407500e00010b002c0420401c0e11b00501c02079903440081078071440c103010340110a100710003510341038241c100a0102c05481d14a03264500a2460102c885460400e0003c10211140c01040f90004914006040902c5001d2401410404801c3c080e50704214015400e2406 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 928853228 1250 928851978 928852013
    0xe060d0b04031b0308060301060b310306110711120c06090622080c0910050904030509061206040e210901020f06040f060507030203160f0201020c2b0903 67
    0x20044003040405005118505031280f2001d00101c0042180c10010401042502c07064000d51911902042c0c00d6500e0080b540d20381d944100e0091456410154400d4000300b5000958441c82c0e41c10000c40020001d0280c10394606980110f01c0d02ea80f654200540415078028000b4410302071200704c0c0c1411400402e003c4101d0104548041c2c0f600f09080200d1424072501c42c030b02121300e1404200007149084004410103a803500303011140441480c109204a03024290b070b8414188070700075010440c40c0351a41c05960700c203110745480341c105580000402c0d07854114035003440080c0582c404100c264140703441740f0201d001440e230040440300c0c0700b0691052030100c900f5031422400d00024800045900070005000d0b048401e104a54280c6002d040c404103411444104407030150801c408101c2c042d100780262030050380d504c003100680400000090b00e440090700741071000c0d95024044440d0301841800404912202100c0c2c52038841201c11180d5026814040100103110704a001071021074520300703103e01c1201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 928854478 1250 928853228 928853243
    0x1c031b0e100e0f040905060f09060402011e141219060f090b06040503121902010203150105070f0b07020c1309081209030705011a09060103050c161106030109150e060d 73
    0x600c48020414210743c44007141d421900b0114100d0401c580058100c1c800c0c1ca050401c2d1042d0348a4101c2c90340c0700e60301a200680010303a1070b90f0721500030401c202079440c003019905004050004082c54040c3c55000b00126501c2e0070000020883c4150441d5a075503804202e4480400040f4280108403d5981a83c000c84c00803507610b50400c1c010f03440700c2040701c02402d00201154500c02e03082d1550354069014a40e1a02a0f4000c3c8610804042c014002e41e40101d003c0f80c3c00326008007100c4c00441c2c41c3d400c801c0c019582840c044044ea00415041e06516010b140a6406000400100f03001c1c004a14003501089030003d15003410000840c0608040d15040b0010540c40303100c680f42e44220615500031410040c01c15440c00701c42c4682041c142d038480c503034940141c138034000d540e07180030056003111411581c91180c06010800b1000762004411480207080c483c08000042003240700c04142031b60400d030404407145540340c1e02da440c0c900c03100390400000c2c2440c4280f14960f02d400382c049800103034142001071001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 928855728 1250 928854478 928854497
    0x5011e031e020a14040b0304031407120e0307051815120106080d0e030c220204080a0c05030708030a0c110d0b0a0510150e121c031b0e10 60
    0xd209070424039000d0086546400010001c1c0701c950000e500c100010400310300f00000c01890ba40903c81514112411110780e036003160b641c1c0c1c601f55051000c00910325140c400801450000038440e124100c810764680c0c2c3c42180c20b06d08202450310b0b010036904400d104600da403981c014004001c01501d5403040700c01c06420008610000860321442e980101d05d1459420301d48041074100c2c0000705207003144490b6641c41c0340e2440100c181515010100a200c1e08040f5000140700c40c0d14451801404061074110300520305a61804628100800c1c01c00880361150794420800062400308400c01c0038155400c003440c070b400303080d01024184103a4900e00801031070440701110107681e00d0070818080a5080071b0b6040b1a1700c1d00554081c020001120104034488000700042800000301c0d4010156040300e8980d0f5032071068a40030000c020b00030004401d5030303200da1011400d0842c2d0004202103820307019200030940c1040d54580310740d40c9070030b80406020009040c0c0d24103501d03604c50004001010302810025050b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 928856978 1250 928855728 928855787
    0x40609020307030c141f0e0f06040512031c2a140d1b111f0f090f03030e01090b060d05010e06072604080702090a0b0306101e0501 57
    0x50401c82d60004e040a0500540001c03200407a00300b480b10040210b84d1aa00e00403112080140751031003a0200000444654503d0110705005034249020140280510b0915a4800024801841411030708881e078001182203143c207160a18514403000c3c9410301880005140c1503840d550161050083c0302a280342510f92a0450088807042c68405a01003050b40d211100003060003d000d11030311024030f00d02400a90707080c140c425114045002c00c0704002c0d02000c200340301c1d00f02e0450300d030035a82c2074a02d0303940414400e401010300c107011007a0700c01c1c90400300301d9011781006000ca40d400d1083c0c00e1581d04100c0200b00042c11100195840041101c980381c070a074460030441e0042000e810510000d1083c84240402d142d00400e17000721441007c80c6c00c001c0111900b03030713000d40f142c8250f400a1280c01c1c140806001482e090a407186c0c0072a6614001840300700d4400001c4c80c0507800d1300e08010007402030a05011034012014032000c62160710700301c281060701c0d10000801071070030440007000410400c0514100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 928858228 1250 928856978 928856983
    0x703050d020403111f0e010c0302010b0d0303051f0317070501021b0610060504080a060905031606061d07020d0806030c1f0e222007060506030705040e060406090203 72
    0x401120100d0840d121901c078948509842c122141d4244901c0000c45801c510150040d8009504660f42c0d644a80b1612490b005403458142c48000b20300355500c8880061440d11084555803400b80603941c00309031400e1240e00030696805020302116003d0007884284045480f418032581901c0c0c640f0f11503565080203003011802802041d0744034400301c1d084181d0180941000a88074042c3d01c00c02d039408440781e547c0c0f4064500f41719070321980100303400ca14000d00200d25541d010703048403409201564a0168128851040880000e108440c0150344403024441500030f0000c020000390318051003035290074a00c4010b0340e11958a50000c003000f0702c0b00006440343d00c0c00e000f80105607501074901c0e00c09008143c50042a60b1440c541000011403441c2c02907034a14084508820303490310104ea14012101d51102180506200c03500d001c088000c626007002d006944a000f881c40d207000300000221f40c00d04100305400c0c41d0840d4000b62045040101c40b070640203002c11950741207a0f03c6200001e540610744080390 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 928859478 1250 928858228 928858237
    0x80402040204090e0606040f02250807050d02100f050603061302030709092406050a09020c1c0507030905030105010f0b1b0a030f0201200d0209010306090f0b151e070305 74
    0x640050411340c04e04102c00c000282c20340250340c01c55050100903d1035040000301d016940300101c0d104403044505421992008031041c54a009800c1c0c1e500c1d05129468036031404644d19942c5c8010b80c080301c030072090340c8854400c041c140303824032205205d913042c90000603544034000b900b40c4040450500440045640c100800d0000740400041403000405500300300c9415802030100e9000041c0a0103c018011240d200e40d2055840003810003040600704000b0000941011084461a01c1100c441c007010400b0300000305003c0429541d103d0707899855107001480d0f104207a00990003a0b0520b0014441c0b488403a50000644515104e200e0701e501c442d500040f503500c0e0400350030b0701034007440000409040d4818451070304203015400900c1080306012004080c80d000309c00400310100240708000300c42c2900d400501526a0514000c24016142c0c00380b082150f10f1881c01e42d201d03659074074040209060401c101000002030010090801910f4030352400d041c2c807040c04001c0322400000300f00b030806000e03900340c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 928860728 1250 928859478 928859489
    0xf012009010c0b09030909100308120a0209220c0305010b0f0d09060504032303010312120b09160e0603010503030f030c070b04121706031e0f1b0906060a0e01080402040204 75
    0x3440e040c10500f904179120307404800b0036801910b00e10005042c14010240c0366084a601480040ca0b04840a151000d6140d0141002d11115020040c44580d5a11503440b440b00c0301e20b41c10480c40700404034514400300c40b046992107050504040040003030010290503505441c0b200071650760345070747c0c50700c0c0350300140548000109840e241506000c00d140c4d2015000c82a00100028488000f420441109241c00301344801030002d4030311b1400c4588207218480d00c00b90758088401c00303d00191508000b03400300c44119004140c40d841c004007581903d03032020b011104090183c0e2401d00d55414400825141e2103200002c580103c00040491003e90000301126a07a640001c424421402c086c80c01c02e80c0c0c0358000e035aa10005090503400100382c8102400b040c09108002c00820042c4045402c040c0c83c40ca9100c503081c3c07103008071031a035540403505200040c5400051032610745400740c640100440d031840505810b00401c4188500c10703070740c3c1d00b10207101180c03003013401d00e409560380f50b10008019205a8000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 928861978 1250 928860728 928860743
    0x120c0a063e0d020601030c0b1b0303040b04111c0204020f0f070602130518130201031e05010504051b040b2808060906011d010c050c04060f080f012009010c 68
    0x700e100d40c002a210118501d8011815900c0400d0540e00c120b0b070b41e80082c04060315501003050104101e065140003040b1000d8101d1080d151040b02480d0136055402c1203406880181186d000c12080101150240410711021985040300c02202000950303402c00c9904000e024950009050098082d00000d45145410b21010303150381e87d5651601d40302a4100c0e00d0340d021500c40d1804042081d1501c125039048400d07406401d8502540c07042003441c1020480751090f418980d490110f0a4103c903999040003c81f4103000780854994940020301003141c600800201501802d181600c5848230300300c04460403280b50784505030b160f04502038542100d03a00c0d4a034441d010b0440e84802c0c041c1d40d42140e42c3c98032581003102c18020075039882d0015101441015850161603003403015a912a60241c10302d41c5d80940140101c2d810740c00c00300041000c45640d40c0100310295419881001078040401201500218000007813151181018074040d500201034001e103131090002c11000400d1344101604200e464120f000e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 928863228 1250 928861978 928862057
    0xc0d090f0f140f0c130b040b0603010f030209010509040f030f090e07120e0d0207270e03190c0f11120607030f1a06220b03090c120c0a06 60
    0x100310000d14410b003402a110700800d5101c120100d8003203400a24280c0280030441c5102d43c240c440d60040c17100c4a0b129501656540c01c1003010f840d403c0c050350180c2803800c1050089070440c0100080c40c5c01c143e014a03c141c010030304001c001b521001000c458140c0c0340c14000100d0200c000c080c1d0b03505005400030000c5182d28000c2012040c0d00414841c2913031021700040142e00701098030240c490b8041e60700440907074044501000000818003015150054032019517030400307280084501950b8118810b003c0551000c034032000e9018805d00c4200c201c8165042540c822000703540c420341c45840041010701501502142c890722510f500d4002c2440500388003d0b940c0e903107490f8101030000c00e1200301203107100d45041c1001d00003241800001c107620200a103050b042c500d01200d82d002d0f0001d41c02d1b02001602503030310700040890804010354042d20140c005044080300340800d02919070050640e0460a80c82100740d0a169214002c00c07000f80c80711407a125200c0b0b1071400e00045420300070404810003c02141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 928864478 1250 928863228 928863233
    0x3070809131802120d020a08030901181a06010c0f080f0c01090b04111c0b060d020a09050a0f02190c021f110705040c02030d0b01090b030408210c0d090f0f 68
    0x20101442d061086640c10082411010441da0b6040d030740010001580c0312056410100365800003031076114040700d00200300c1601c0104403400020222900316084882c4003160641d03031500004440e800202880c0c21024140252a04041d136154804e000d0000c080010758105c1345803e0004840d2240c0441e0024010b0300204d1400c4200c12008480c2641c4900500ea04809249000100023214500c00182c003021000c481d01e41800300503000d0655940000803410040050b01d54800324402010300c45000a11850005072084c29150244034a182d514410010005101c1201c1c0e10381c03003003d041e4540119074001c24400300300c140804e6800300b08440700c600d03507101e10298420500392080f180501034414540d51035041c0020703118400013001c09a042032041c84c0c143c90700b83d07101c0c00c100c80303052420304040c0f0380e00e0100340b0403584143c4040e1548840015040000010284d091481020640c5091210300d03100d030400340d25003d0341c80780b078444a4503503500364140040491030412403608400410043e0344c692 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 928865728 1250 928864478 928864511
    0x150e010e1608060d110307050a0b0417030f04031412030907050f0603040c2d0e0708090c06032202061204021f1b15150602010b040203090307080913 65
    0xc450003030780115400d541038a118442d500a902800020f408000404165542c005c0c034003218845054252107007030030020303003075840c0401c42c0010710349200300c1a52607050441c0007102a031182d0400314540e204000760095840860121000c0b01c0d0491209401c0c0d5500400e817908148400220503c602008400e10206240200e03542e800c4881c100e5405490300a64414841940400c94018040c04200c40081058030000ca820003201780030041da0307100c1003031542c0c40365002c00f0150700180a54010710040010a98102e42203d81201404004100c4082c000c030000e151844010400000c86400011103550056140c5c6040100d941c0200b00d240c94014002c5264050740c41114180d100b41482d500380c0340011b007030281030140804d2641d0740821060b41c0254000d241040ba61040b90420506a081105180c2901c0340c1c000801001c40300f5060686000002401d40c0d85e4400c510b0b12a910410a2181c01a07001040b1600f0a50140e64170307440b07580781800a40c110300722603031030100c1900b056805240503164 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 928866978 1250 928865728 928865731
    0x705040602010605190902030c0d09080702090c030621071a030703140408070201030218090a090c080331030807062c210c1e010e030913150e010e 64
    0x1960007040b0b0f281d40c400c208451100c203c55051010500c0c001c0901c4101e007950000c650204007811203e1800e801d2142c8102124080402983c10100c041608001c5113801c0c0c1c09580c1000782203a1050850070802c00250349190400c2e0710300484040e00324001c220b000d00f8807141d0300030080d025202d14030950402d9099000e40c000ca40310b900107482c1418480120300c6c800c4190740034a80000405003401199401075000b907102a18403001c107281030b01c4000156648a0100344a88080301d004680107070b50745401c80c0f00c1034050304085040e400500c000e01301500032411400300302026048000c590f20780030900c041903e01c03582019000c01d40c0001c290080c49003070740240351240782c074100740ea140320a08a0000c900c640d01c0b4000718055001303150200d00c6112a48104001c7c00311f69606685000c006c1458140760140b00c0c190811104510440826444000c0c400e80340c0e61050540514134040c001e8002621668218499410303031a41d5250540300d40140b01c9010000e007003c1c0c04800c1c0b43e9611540742c1000d0380300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 928868228 1250 928866978 928866989
    0x4051005030f1f091e02060d02030c0d061a0d1d0a0503030709050a0b030601051c020a02012a08040b0a110a0908010c09031e060b100302031009050709180212070504 72
    0x100c4203c080986042e21a219009800003100c408612891000c9406500b640c41c09a03440007003805034400c1e0022038801140903c0405c2d103080c1e900e12109003d84181d601a5001780d1640c40d0702c404040006840b40b04544081e0307145400041d081c03410503000203150390400b101e203001d88200042c8604100000000b0350140030300d48ca410700000e03941e01c1040f0b80410306005501c9172000500200700603500071405002c07021400701c580c00c03010308440300840413a009480c190b00180e4561403006400001c0d4140312000c003402c546000744c0b001ca80d01004d071113007001030802000501100000380140ca240d507c11080303002c000f0102a5141801900109001c1d280c4c01080c515510f400010708013607008084c99012a40d101c03035030380348000d00703540e00d4101c440400350291040c07521116626450359801170050760302d5450743c4006031a814150640d5496040a420202c08549410140003485422502c1d000c12251112400c00c0c82220408800019010345440490342c5210842400400740d0000041c200b80d95 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 928869478 1250 928868228 928868263
    0x70b0a0e0f061009110c0d030606090603090c030b0c12010608061003150e0a0f05010b07030e030f0a08090103020706151a0f0304080901050910050403021c1104051005030f 75
    0x1c1c1000300340741d210802514441048515100d041240d00940d802c80010b03000609041401d02ca54490041d062103072066403440007039500c02040c060680c01c000d00e2006007500345410130000120b039840c24654141070001500008020300014071240c00310049440742149944030001c5541c0d14a005045480203462036481032070040c5484030040d101e882000c00c0d9100700039980070744078a030040c0820071040240000e85a543c0b50005240e40c04d146004086c000c040d0920031681d07510113818000c0c040307607800c200d80d44280c0200303081500030b410005030010495040140c81daa070381580001a00240b0076041c00404507030801c13140b07180d904c5041c032001e0101c840c000245507580301d450142120605c0341041001d0142070500215002c00c10002c0500006001818102c0c9885000e5000a09000c48a1412000694001800c1c03003181001d6100c1c22007118410700c0d0324801040c541c2e1300c0a03020307030700103040740110307501e900140701104540c8150000313103006015a000b56a2000100d6181e40d10111401c5044 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 928870728 1250 928869478 928869493
    0x102010f05060f1011070b130603230c16081e0a021e0a1b0906080c0922021c06051005010801060c1502190f0207052202070b0a0e 57
    0x110058040c030303842180000c000f1514121030790204400c510302c506030142000300b40030042c0c0e82e2010400422000c0c0c198414480c0c0c03110404024009800c445402c004101410030b0206a213000303805098440c011107913410201140e5600301e0002c0240a4005d0030941c50410504050500038184c1c000c202541c0029001000404030138040707001d078416810341e400140c0c41070b200029030000b110f0031032003107500090070368250130880d4a80300322502a000c06e002000c002410104040000303031054800074501013002d04100c48030070703000861a45004000c100f0950400e4008010440d220106114055000b0072940d10f9440e50141c3c0c49001241c410116402480d01c4003040c03800120b4000303a8210740c0141e40c1c0d46000d03820078104440d204505030045998041c1d003403000083c1282c0b130005d0246102d80c40d0344080010740e00400107200014202e040025504901010300090b00c0c2d0300c001c40f1010300f0b40c14101c1707210b80107160408000d114095003d8005284d0b00d0512410740419009003040e403101c3e200321a01e8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 928871978 1250 928870728 928870751
    0x3262719031e170a230d020a050c0703030206070221270907030c12020c060c0c07030c0608060a14030a02041a0301020403212c0a050d0605090d1803141911010201 71
    0x6030b80c040381c04981011820700000201c41d1b200c0c1c0042c1110b40d01d1b49001410404030414492800f001604210091f8104400b00b01a0540c100100b2106441c0340584044010110b03245200d5840340c0400d50301c1090301c8110300c2e81e014012076100070800300082c00e803403540d18148100a0003415190032401c0040c0c4c81d0700315800b05940c00e000b5110032200200240c401a152040c10701c0749640310000041c8240102c62000000c40c1568842400a04003501c4203900d9180c55000c001d050401904802c000d4001c15802498644002800c40040c03a81600c000510010100070880b203540e17030041c1240d00d036000103404030400c1030b491804640c40f41040c0300c00f01c00b0880e80d07101313503030884504200003526107241a20aa1160055000c40014200a41a51065500e410101d11100380c1020140c92341b503100c106200324030800f0001e500070210325240c011520095501d43c40844a02844094084a4a001c0621004800380402075142c074581d040340c1d601d504140b603d4031440221040301d81c05946098024a103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 928873228 1250 928871978 928872017
    0x1b12180506210a090c080c10170f090f0d021608150403080402040f05130209010602010c141b0109050a0c0b09010903262719031e170a 59
    0x4141901c90344840301c07140502400d90003a00100f26030301c115218030421011a655110a030003a12400c00902010b02c100010f00201d4039041449000304030aa001e03000b900a103054801e03800000742d5546040c0742d2203007007040d49084100c0c154400c19003e030005c9082000c0d0000b03041309415001950390380c055a5242c0c005905c9000f0380b00d90f400f10407250800100040d1003010340903440b81c0700820008401120300583c40803950121214001401429184004e501e0b00c081c01c0d60040c100c038802442050b034044002081ca500070007421428580221304401600359040c2100287e0784098000c201c081d649050081c0d469414a40170b49061940c0c5902044e07a111040465004080c180c40e10020f02e40746035104034107a010403c1100040f40c0c400192520381c1d0741000202100650990005018801050162403150201c001d441c41801ca080c0c0c00d0a15004402c1068101d035000301c3c0710015010110150a40c400c98039400400b01081901c1e126007100c1008064400c0c118203640c0d103405104060184130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 928874478 1250 928873228 928873237
    0x903010b0301050901061811161b062601051c021c0f0c0b0406050f0d14010e090d050319020c0f0a3c1104060b1308010e0a0308071b12180506 62
    0x460131020040c078404240ea0782c12104c4e0305480b400e104900b002c0e15400c628188a42c5400400000d07401c2803300d030420b400b88d000380c4e801441e241a8004503500d01000030344a1008801107041070520491581d05550701c004c051320030002c1108201e0f0502d41c1c14034100204003c9200d04070358810300003001098480010040e40e055522540346e452904079014442e042d140c0244661103c181e4440000c01007901c00311140700d00a00811088031024144035107400d040a40283c095410040c0901c20441403a101260120f41000d00c00801681d962074290780714200281e60141c44024803c03942c512041050790f48020490140d84907543d6004d040f071034000106800c00c1c10300c0c515101a2000341101003210603691604d03031400140000f61040c4d6510f0050a140c03c07280c0c0000308480384410400c800d507801e016403070724a00220058120303011640d4000c0d00080001c1c18400410441d03440c0c10a0b0070307040606850792107401400500070030444500c001d141b50410344844150352104440021903060040944 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 928875728 1250 928874478 928874501
    0xa022b060207210e06030a0e011d0d051213210503090606040603240b1e03071202090f091f02130e10170309060c06010f0506091003020903010b03010509010618 70
    0x10550b0b40000000c000c16504040c01c00403816503207850782007144109118000c0e101715841c0d41017061a02b290f00e46030806000c000f54106100c410400c00d0340310304032400c209601220787e0b21000c2c0c41e10006e0034000400c4500e014030780001e100c600750280710300d42c102c00070b1031040ca540e0046604a0342c8100030b00041d140036100040111008a4441b03018100124615080708003d484c00035403660a200050100c0085a10645200c0903980e1100c0040c1400d00c2100041c20304003032021100c5c03540794040382c400341000380b0f5411802074080c0421442c48090000c425010013040d00707802d16035410386c96000254010540d00c85d501680301400141001c0d03503c00300d4820300c2140c008821a9140040451240c1c3d15005c0c40229804100841d9a40d5a5854060400780c402d24004242030742c18000541e058640e19000603114413424070900c140e44d540c42c002202d8060b0703a45409600c0301001404071b4050702140743c000d41d144d401c10040101480056209204485200303142035200780c0100c96810458a016085 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 928876978 1250 928875728 928875737
    0x108030f0d0e0703082b1404061d1b0306150f0d0503070b0106030209040b120d050a090b1317031c0221011527060c140601030803180d020a022b06020721 67
    0xa40403803507640c00700c5000400c0c4022b0003000022081c07110306080c0b28860404c40c2124045249840e814104201c0d54058401355000c80c444289200007010300c040800b18502c50a0b80a000004004042c020303152441e07404140d4080b196143c2c08003601070741098076440d0140303241514500080c50100b51680c04d907140480a000307241c4920784104d490781d000300d0f0903006200012100190051200c0d00404998a030100e01e28280c81c2001c9401c1c0c2120000803241000b54002c1c0058031140c1b201c443c1d00300b900341040e0300044c1c4c1d420014801000d18211103c07021007404d440d0000180c20526120343c6000d00038030f0ba403142200e45071040e0851503624624210500e150044a0a020442c0681490307081d59000c0d00300312007409a010556443c109090300304075140c04001c42481384503648000014a8510044c000c0c00380340da10000000c0d980c070032146020344600c5100320110002c1c030b0502180118104102c003811911044c9080140c06540b041508603a03a5600d500310028100307101803810107000b020384da07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 928878228 1250 928876978 928876981
    0xb041107020a1809020d0b060102070807060207120c0806090a020a080111041505040b0315181e2220060304020d0f060f0f0b090108030f0d0e0703082b14 67
    0x60440041000c49030011003a6904c0c400781d0090b139950f00d148114507110359150001d515240000900303080165000c452142d0221105000c490340100742641990050080e000d030f404c82c24201602501e5103580441d400740100b00503c051030001088209101d030098800c014400d540e80200c1f030890b1182d40041044001c1440180241020107101d4203e2041c2858254106030b00c2d2040c403402c5a20036954603200c050600350040b102d09141424850010300340c03001c510035280c10044055000f080107600f4039050b00c180d00048491034150301d90f440e4001d150020000100c1c3c2440d1a1090a01101000c40f801d8600765802e5110f181c0a000c4900c9154060014140e190380c1303940e4451012a0039104491041c0c5968480c01c03040860310501100c440e58a0000c10700b100c1c80030a10400400c1a00080400d4204002c00f100c1ca1075540100c41803150300c00000a107001c8a40345d22802c1c81d1290304001c00c0420005681202c000f0410300791059000742c0d44c0f0398134200c01c4e048a1303102100c0b10341c400d620036a4241070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 928879478 1250 928878228 928878239
    0x302040f090c1e1d0604020703031d07060207050904170309330a360f26072004140106030225200105120a0b041107020a 53
    0x10002120510200400314040140740e8a5403525040c507046402d8005018101400d10807014803164014442d61600d00c4c020900b818007150f0303441000f00303550702550700000c2c5282010f00c26130010a45413848a158500d6084450b4080c1d110315441c425000140700ba00c03400704003850940700c1d003070041c3c0e07002513900c00304000c020050b180e58000410301c0019000d089000104807860807900102c0c000c0d166200d00810623603c01c91500341c003002d4444491145404000d8240e8510b182182c1707080403400203148030860f400401120058500743c4000d080a2000074200204003041d401703c60350300008000d13a00c107103452540d0300c8070364003910101804403004048040e0a188000014034040f5102420104015410280850528800303a10206c0000c4d80060040c2d900c018000d181100c0d0212100039036143c0c01181c032140384860b2070b03450038854000b101d10340c010240e003c0c4003115003a8060859017611864030200d414014902c8140c0c040c005d60030400f2814040500d10201c4480c664000c10304a500390612 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 928880728 1250 928879478 928879481
    0x9010315170d110105042301110d02090a05150403030e13021801030f0e03030c090315010314120304121d04020706020301090f050c070308060a05040504080d24030204 73
    0x580d4031448000414801180010340c03640d440340d40400d803000900c079210344400000c000d280c610380e220405900d010113110000d2003030618201c810030001020a41d100342150313001d00500c00320800c040d950800052565915109402504100720101c54003012207944d18140030402590740c02204650308100300c2480080d0083c08285220348002d02280321840403010680201c0e4010710340001e6640760344007030b81d16540e8907000e6850b2158401c0c00c248880d400e030f56401903690202601c401c41070500443c0901a5031000c0002070425041082c0a030000d596074105000c1801401041103800d00654441d072294049450441c2d00031176208000e0a01d10b000054100c5903940307100c04049001058101d5249103540b40d001034031401c1c0c0a02c07401656945000350f10300440f50030040c4803112608003410040c0008205050740c01d1650541004103c55450100041040c071964204a5225150000340010302034400301601c4c824028050410280031000c00300b28000c40c0da0300022104000c0300702c0910050405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 928881978 1250 928880728 928880741
    0x180506100327060b0907030905010b04021c110d1b1202070b180c040f0c0210090c050d1e0804140a03050c012d050a02160510050f0d1a13050606090103 66
    0x7203800103242040d44d400181303070003010382c0e0724000242c13200e10000c2441028841c00250b183d00711001c614045130600c8e11480300311004403e81000c1e980c0c0c2d0b4090311080490b42202c100d01900c040c01c1103100c0d1000705000c01d02d145115050000741d0a0f1ba052002180d0900c2200c010ba6044212071100e0b5030303001803401c080d44010603680d65a009011040142e52118000e20125840c0100046808610024000c0c5003116400c0c000b1202c41c01c20303400b0408140d0500aa01c03d030b443c00d590848110300c0741e05181200c030091417201002800203e292038140a41c00e4090010346000d91030501400c01090101b2500303800c180006440303900942c049072240e40c02a801809540c4a00300c0c2c0d4195040415200d0900e10402d64a800100c2d400145a0003810b41c140016402d2429000582c0da0403420040400e407164500c1c0c40d0001030100004604030070100d03027030641d00f4149071040244524483c81e09003030324044114032000c0c082e031a4505010207901c180e00450f4410800a4141800c101d107120046018009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 928883228 1250 928881978 928881983
    0x90309150e1f0f180303140f070308073506030f100608070e1b07020f1003090209090a02011407060212010b0702010906030b100e040204180506100327 66
    0x411032010041d40c1c0b28403100c12100c101c540401031281c882000701070b004045030030041d0100005072141602c0d00340314091490a03a0b4040c80c0003240004508001103940c86241d0140400c2c020110705a001c150b40003c0c5148034002603911080c0c0d0300c1901ca80c1307882250030b60000300c1060500403c0c0c80340c14501101d02503804503004040b26824192644464100010034003075178200c5844200601940000300002401041440c00264040c500400c441044900f48607a0101940c00050381d0000d55852000d0000c40c1031000308102004c1030542c002400822a03080100d010b8840340e400204e40c00b2021070389400b01901a100c01c4800708201d40e0b0206694000c25044620b81e03428418401d41c50b40400013203018200c1108140e81d20082c43c000035000c0c802944c405000c140c1845184c480d2600e0328104600b99007050306002d04000d10010000f0042d0040341c110221207c0c9100ba410402903682c0c00580c016541581d440101112501e422000c0d81d000102d54211215541c2c00000b01c4020300f40c141c8080d50 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 928884478 1250 928883228 928883237
    0x10201020d09050102030109061401021b03030409142e060c060e03161a04020a030b07021222080c060a05160f0f05150f0604020c03040f150801080109030915 69
    0x741500c0c440e60860358006020356881e036012006218068441c0310302c80c050088640e9440400c5c00900c0002e55a030b1152000c8212003510700d1242059490801c141d40180c0707c0483c0c10700080380d04012810780e0a00443d042c8506c07881c02100c0c100303032200e0051111481e0b004200d05140a90511070705541d000c09600d000c540099884110540b214401e0000e000c600c1141c8200840d990b005040c4442c18021240007645c10700f00140a102c0140c0d02c0e0b48100084951021707100d00680c3e10844168142038403007a071402880000100101c1c14003d5421605000803400b121086c0d0329203074840c240c0c1e0b0321141c012280d040502001010503003409100a0f100e04401d90b01c41070324040c0e890b074401450800c4000c00322211500403020344100401032001c00741d080c41c03030034041100b49041524003c040074081d14440c0119800607000340c03202c0090040701d014040071840ca1000586d92504d007544105803020200016100320004240414103024440301d158150b5141d0340014100604011451958080807040c003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 928885728 1250 928884478 928884487
    0xf09150111010f09032604060b03010e161526061f170f06011e200a0203011103011a0901030221040c05030c150d06030209040c0f0e01032001020102 65
    0xd1809015030341c0304440c6110b010a1283e403031702d0080c00b580130700040c1d00c1c80d021644480300c0d04078038024445540590051004201e03021504c0c04240100015a082c0c1a14040e1100c3c2d48440c2c45068a2541111000b064801501c24002011200c22101c09494801c441e00341d1a08800c41408580240e040b2500a00c1c101000780401c00d610141c0303500c1740011010910401000c03520010882403143c0c440c0d21038004005519101000801c90341c0e07958a14281c802c4010b2046466034800c0ea0010f110b131009029506054040400f41ca03501c0040740c200321710941c2441740d4402c040061000751b038125101c1514081e08000c0701c0c4a000c03901d4005c441c006040503400e0100f010185060314010605030701d240842074480c01d00c3d080080f1080200d0708440d000e82c2c0110211300700341e01c1711b0700300c102407004604003543c0f1044407414070780203040d0301e600195100341560188814452200ea0030b408540140e03160a035001d076241c1308464514800d120180c0341d0f0100e47c241d103d070700b40e5408003c800c1c2c000510005142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 928886978 1250 928885728 928885757
    0x12190b0f040b03151602100c020a061a0d03020c090903091c02060f0d1505041b03091106040b0a2304030f031101050a060602060c042106060909200f091501 68
    0x4007201142d100c90380c5e800c085959510141c041c00110304060103000305001016082d00d010b542d442c0440d00c01054030b40d980c0900f88402c004403810302c004807001045c00e0380b00003503410000e5540448914481c40b82e080e400121384591000400c98520503000740c01d021400704c803070900c095040040d000503030700020100200780c1214100402024140340075040041c5111842c1529104000c5030303040b25000c1e030302d080e040392011050420106841d035107515010401c110b0a14190140908900d10b203501300c90045030224800d00c0c40c1018080c030460700d50b503201c164006802d4008462903803103c0c030000c03610104014400718030344103840c020f241d00909048065000681035542121000c644001d86240e40707050078000c5603814003d183c2c01648501006061500b011102020300c114405a540d6050341e181c00f0304100085a08900700030803d840080018013007900b030040503c500d400f0409641c281c0c100090140c0d140258070183c04c1c10001e040810035582c0d01020b0702c400c844c005012070500441c407114940 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 928888228 1250 928886978 928887013
    0x60a150e060a27180902031002073509040e0a02030f0618060f0637050a0501110604020105090d050f0d030b090106050d051b12190b0f040b03 62
    0x4504900d90f032008664108254180007041d0341820f0314400d80364620702000031801080242c00884105040003502c6200c030310000c2e203040d07501d6407071070350a50020511200307200c03e00c1541d0840c5480f10242d548100d11800c40c164084010101c0c5880740307441804140100e003026480202080102401c85a0b4221a500081d240040c8184e03501c2859005004101601401d00c00f600d048100b032800500380340c03d01c0980703036096800003050740d401580d640c0004450034219080380303070000c0c80d40400504600f0802c00346855548032030007441d0141d0032000d40007600f9440342e500f04850f110043e01605a640f03541c0c0c011100303584070300c1486a000e00074007018070104e40c0510000305c4004201000301208008284007400761801026828030a020360001044529000b07011201d14054040c00000c042e52008942c082036400b200c8420038500c80440e64403070807884000068041d5401c01c00450b090704480c1003240556402c05407030343d0803a00041108611341000d81240c50100c0000b4192680f4818415152a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 928889478 1250 928888228 928888237
    0x60b04020f0309010c0210140115180b04030c060816030e0c10050c070608060604030f08040f0602010e06090706051b0106030b1312052b09051006031109060a150e06 72
    0x1041c0c4e940d6104241c8003250100b010039807401c0700c141300388282e20440d070131038089110520943c180d0b038401100e1354030b05034400d000c0f00c4402c0c0020aa504121929a601021140c200d0f0004894012000341c001c02c88600846030b091041c0302100d009811002c05c10404c9000c0c0001303541c101881d1140344003102841d5140d15209002a24590702c1c01c1e16442005151031a00d500c070b51001d400c3c404034500380140c54940b0f01c1200e003501d8105000491520103031405440a00c6590312088105040900c08038181d0340c1074100001048020040721083d84407003520688441d40c500c20400411800c0045010014256108824400394100000340c4c8a0b580c0d221400360101c02c40c1d1081c0c7d80400e4010407810003240312008039180d070300c030f00c3e040741409441e0804807113040c40207001c0c03445c0300b0781c1200e4204006a9500001485548042628004079200c2c170400090701d801e00040b9046000c0c2c600e0804641003030301049108003401003c0e54070700c07072038450300c40c529684c004030090030011695020711180c1c86510080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 928890728 1250 928889478 928889491
    0x105042409180b04060909021c0804050d080901080702010507230d02030406021b0c030a0609060e071e12120503130c150e0103090c090c020316060606180b030103060b04020f03 77
    0x4aa5904550100402c80700a9085013070b030103103000c07070316000f41c0c980b00c84275010249011903141003440d580c20404e500e0301556021030f131300c8151148401c04100c13084001d002000c400b80ca41501a0720780500030307403c0c1d0f0401c61314800001c21701c00c050b04818861003030702c0c0400c00302108400e1420409600c08426a40229800d9401d55000550702030184400014070203101100c030080e149070120707040040d440341c108190142006450b0107540050044aa22a42ea00d00621003110a1150358a0500c0c2d040c605100840c460340546080004009150002d0390840d681d010551801424944c8010b990b03c1d000904110039646219000341c002a00030040d68026140504018252140e05038000300148181040325042508141818000039115003032402990864440030401d4200b4800c00c03451400b0348107403000c0c0c41701002e94120901030254080d000b9aa4140d5035a001c512a50600c402d00c2c18a502c90a075298000300010408103c50394041c403d804070040c07000d4900781501c140320320a038009540c7e0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 928891978 1250 928890728 928890731
    0x140409020c0706140a030203042d02010e0307181517010213060302042126120c0901020318150a02010e061005030a0b0402030a020a120b06010504240918 67
    0x150415101d00b0071021009040c9442e04003507002c489100c0c032006000d4003d420050603001b101190800c182211007002c10035400c0740051071103401c408180f03c0703904842026404180c0851072450b050401088081c02d032200710000518034001144420010501e002241c10b4480380c040010508000170007418200c4a842e40c00540c40308500c1c0801c4600705440e42c081003d02d44100000c02002d04151000350080300340411000340f1180c3c81c00c01030352010021040c00e007220240300400f020010608064000f080e1058003040c05030341c0d4540c003540c1c00d00c122816580564002d01074126034a10302d4484981465014180c00c0040041900307082842c0c006a0b90240581d4540c05610480d0004100c1990701980036114821344030700c0d202c0825103900400d10040c01001a10300081c01b50745040100c0f0115a501402025406a94410b01d50660303d03030001c200d5864180700007040f01e941c400e50549040e9420701a2a040c00c440442e5a03000f00e40e900d009030010b011109a00190700d0300014001c443c1060b00500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 928893228 1250 928891978 928891987
    0x80c2713060c03020406080109021e04090e212d03010e041e020f0d0503040e040803011a120f33030d0516030f0915020a0201030e030a080609060114040902 68
    0x10890705032120000c0030010144103001c20440b40340d010904c941150030148006039500c500f0100c0c00c1c05150020700d01101030078001400141c040c00d0364003004c0903480d10710559514000381021032440c19443d0101c10103420f0f00f440b40205040020312040b8080c801c8036007a4041518114402071990030990108801643e14801c0005102e907405240640010807074041040c1d01c610341c0040e0010339441e0b40c450164001c0c50100d000c01104004480c058001c014012586262901e07201e200b03540709008007030081c04c40500c010020740b0380e50165a403031401c041c0786952036071b221040d0a01ca072100400e60099800305042c4280840843d40b4a80a01c5454103031078101d803400c600905160001054612041140400103c1c1c1c140c0081152811030030ba0514292814090203001224800000e810045400301c91203100301c01960001981e80c5120320070388040c001003031241d80103038a0f8050301c05486c011419140000e0703080d14100d0040b0b68401014180403503221030443d4000044d4201d070304050b000d03641c00107 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 928894478 1250 928893228 928893233
    0x7060507150506032a030a060c1115040f0602071b08010b01050903030d0b03010213060305340c030203132309010f0e040c09020a05070c050406080c2713 67
    0x200755505140141d00500c003505243c0702107542c0e0350313040c0e4080a10285007078000c3d5000c0c006511440780e0b914028201c0e03002c6101c60514900174802280c1c0400850321990005c80000c40110311019010415064441196903580300d2002d80700e0452800c482141d030070414071000940e5405019000303c1d07500c0b02d8010f5207003011003590031105400e60145c1804403c1c060840f0340d0754000120390321488003600210701101c2c0030003c01d000e801000b0301880c507080240000300301240e140d4803041c4107450341b40c4401c1c0c851807190903c10624800c0b0f400c8064001c0702c2c46410f8910b5003d1400300c55990b100744100c170718000d000c2002640344602030b082588640400c072034100c24060070f6190102c22003c100c400e590039524003403050310202c01600c1440c1c07803144548005020b0085882140c001000140700c19540c13420345420040c01940728001c2245c0c40040c08002044504044c03240d00c0644130441c1c024103030445003000b00504c039294404040900f0550303031105480307040d111120a004000c900c0c0143c40c62003291 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 928895728 1250 928894478 928894493
    0x9151107051e190302150309010c0e01090e040f2114030705070f030207050315071107030b0c070c030503040608190203090a030e2106011707290c07060507 68
    0xe9100a10544480c140040c216412055015102d07104580d00d001c1c030030306081e0342080c00b142588041e42c8130703a84040c1c1455805604000390321540d81d000080202181d52401510075826100300907002840b041401d22030368070140b071202c2d00139004012000b80c1c00013a031344e05044d2210f610381d107035503448104070003046464000342141000c2c220b0140150452804840044c036501076000060011606040544149030090103544089c220190039107690b22149054002e0050042c3e5640e40000c2d551061400c03c0c4070085808015254040c4c5a1110790700c030402e1400e115048200d003a80c015a403103200000241081000700700a140585400e10303185080c0d260000c02560000f0285440ca004000300000b05402103402c072300d0b00e61325050149030405d0207008110116031030b880301e400424071340d445030300d014038000b820301d04a410704640380312039489400901d0385850883c4211807014200340c5125036028800342c40001000507040d012400c040c074000e90549800c0302c0f54411004600005201428000074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 928896978 1250 928895728 928895743
    0x7021e0c0114250c170105060108060904030c06050a0204170705010e1212030703090b070c051c020c0f031204061736030d2c070f06050703091511 64
    0x405002801e01c80c2c2580c1e240400c0f0020310081042d10324556504081041121081000d40303c5800a1400901c00c003429600800e0250342041c042202e400c005a071900e000c001c510311503a810342d41c2d2982a0040da0321480500301c0942105c0003242c00344070108481d441001d044041d04045c0300140340780381c03825001408615540060a0185000060001d8000c00005200341000703a0350381800e41e09c0da600c01048000f0004c03900010721410711007091184070f0783d1155070002e40034040c23402d035605201407104400030406455414805071300264048502417800843c440c00e58000070b026184080d0300c0105021155209402c048040f81003024403040000200c03801561001c4204400040400710035003a00511004014064600e08521610540000103000783d9070506401d00301400803070420781b0504040d41d1f05900c2411140712032010040c10202c001040c404450b0030028030032640f0b040080468032030348407880503003c1c0034201000283c03402142441180442956940c0410005000a194101300341c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 928898228 1250 928896978 928897007
    0x20a060c0c081204062018041e0e16030302060901050c090609090601140a091a0301060c0209041716060b0d110112090203030c0d09090504170307021e0c01 68
    0x7440141000011890030403520900a00b010f42c055540c4e8900d4a440501260814030b80c0c0030080d0152180d01c0041280a8240034814078000045041c0400900003141d0000a40921051041c1c1503401d00c414158003a03000d01143d10191110902d42400300090b50307416034022001a4040001c10115223002e104081d04103030611a9a0301d402600c44c0014218000c80a10307d200e40c0048002c02c07890780c02265040b4606030021011603c640c1c1c005c0700509190748510603502030803180354035520015403030000c0301c3c140c0b503c6898054221039941c003404080c100c010012280300c1585080c00311035103610009086c0d50741b6030b450341c00580841480c020040e10b0010302920f000b1406a490040020114210301c0102e0b1001c0c81d0400f072142d03e801c0c1810241c10201400380d0035010008111848443c0421959510344554560140079035440c2ca0981c111030701251701420104102e182040541131036001103801414a10450350b5050034506030360f074200d04100706c0d8910303584020320341001c55801c01c040340185030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 928899478 1250 928898228 928898237
    0xf040501080c2b200d06090b091605130906050f040203070f050a0210020f0a17360f0c09100e1305150f0a1d030d0b120a03020a060c 58
    0x201402c1c00d60069072400490b0b00c98080030002c3e1680c030781202d80c0c4603031206015810520000d482c41c004c00030903039101c24840300e026400c02030081412251030081e42225070b0b02402400481d6251650340007284c150000c0c210802c042000104140d980c2c03d103088024082030007002078501d02e800708204040c0940e1a8060146005100308054550000850203588105d030038040c0e07981c03e40c0c0000f02d08205401650000003440842c03201600d45901c03001d4002c40300d0b01d451f00040d12100b04460001c01404641e02d015001001034850b44614040d803100100440107020800410401d070380040c18aa04000c3d11121a40211701c042d1071450701d40d40b0380e03403c400c46d80003040306c040c20440c40b00d00074a801040da6502524401c989000c2280401c89000360080303240081d101401c06821100d0141030954041d0107540c2800701019042c0c1403a080400740c2034100c8021454003090017101406009030051103548600c071403c291280741c60174443ea40b00d0a100e907025000110140c680402202c544440420801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 928900728 1250 928899478 928899487
    0x3090b090c130c0f0c020114070302060924070c0305040e01030b06040f0216080f12011203110c0108150a03140d020f06090604081308010c030912030506090a090203010b060f040501080c 81
    0x3c0e030440540e60a1500514000400b00060700050b6401707510403201c034213810f00010b519400e1582c00708420f40119640020740340c40c95040c80c0e100c91910b10f03072047d503d14040741c0e0b004104800e00130301c0e03600b20440c800c3c2000c6003482d44d600081d600c40882603005565070310b07c48042101900d064410065501c1403400c0450a2001145414215542c1d8010080640100041480b003040c006c00596451600803002c1c004203603104c203100140154005400c07400b01d20b040030388000c0108040384112003020706a4807403909585a5240b00e0140201c6981c203504588482c001002041c9054080440901910000c0c10b4502606000a2034000600740768501c541002c0c052144002021558a401c607810811141c0c940020181421070307404281d001c0d140d10740c640004a4030703864041d048222694028104040f03c4251000160251941100d282d60300c1115034000488021955000c680f80c28000b030b0001a40010302000f28019610000240101c1c110106040ac19982d000c0581c941c003076040c18446050 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 928901978 1250 928900728 928900751
    0x122a0a0b0c070b0d0e19121202121608070903200402071202011a0613063903030c02010b0306011a0708040b030406051003030537121d0c0d0303090b090c13 68
    0x44111f41c40c030090400c901588512181010f58040e20780120410b0008182810445040007441c508484504007107031541c40012070860082d5442c0b030489421000007040d81e61264143c010182015150380e900035401c0c0880c5002c113801c00c1003403a0146294000181d260b0054118100c171040c0c020f44948145c0301000b2907000104603280f41c100704c40841c01d15071003020f0003401c041401041c3c8600c00c0029500480c014881405903802120224001d8900308080c07184210b007282030b540f80e811b0b007641642c0710a004008030b011107000708280b4603060a02500306a0160344a20344c41d4807603400f040e00950f0210612003844600d01c02c2c01d8120041416902c1250324541d80a0924050a440810503e0070042c0d07211440d040104080030a000521688041c28400b841c0a07110304170740c40001e05014030381899104002c040c4080c0c007a0700c06800c00107108850000081044d11528020220201921105014005019110b40e0b601556000300039051a1500e50180703c0d809808034180090710b400e02c80348044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 928903228 1250 928901978 928901993
    0x9100614010909020304031b06050a050703050402030c0d031e0503040212070503070b031e07050d0615121e020a09060e0d0809060a030605122a0a0b0c070b0d0e19 71
    0x85070f002140141e00e0342d565080503034200c240d5441c0c03c01c07001a462800420030545e948514481d0315820410820f82d26070341c008600f00c07141210000d4043c0e200e0300d00c0b00454604084040035036403107071414400c0e413106094940c20a0001c4100b01c03010840100034003003186809190355554120440041036420300e85000a603582da03035442a04002000007000c1ba284450318400c3c260007003513201906c1094280f03001c0040c101d5210f41c425031201840d0410100b4255940c140e50344660406d540c8440500d00900b40c8900101090441352411840c420783c01454280b050010340520821900d511781c0d0700346030000280007040c507075100f0391003562000705100c00955500305407801403000b41d030200c0d200c40d500042075008041680025030702c00c401c020668040100018050001441821085e10100b52020080780c1c1d00e0b0020115a444496100c05000c1c07000c00c1405030030304082000c1100c0c581d9586001541256006841c8a0002d40c2c44040d01c01c001c41d01080034903201c030102000c054050310705440303054 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 928904478 1250 928903228 928903247
    0xf0608160e01080411040903090518010522020405210d020d2a02030a0c1a030108031b0712050601030c0803190e0a1809020102150c04060f0c0b0910061401 68
    0x2414040480e0110f0203000380d10f41800084117000e40200050340c6a41009060702a0520805200d8900400250a11500445418100d0b140503026000c00846442d802104140b42e81c043c80405500f0300000036651345a207440008056044c40031902c400000f590300d800e254440328040299840341d04011405035002d40c80386002e2443e40c94510285c2c5d03440605000c240f08042d4003a5044c0714a5501c8004c0c484084030000c1102c4886030100c130001c0303450b6100c414502092054607002e4009001d003055120010700610808461071060f24000754032480241c954040c0300c1001c0d10140c1c01301c4014000c01150f0060100600219002542041c1141d6882401d900907600400c0821118031290545030715142d821070064100609401900e10031908000004c22000c18240d0042c0700700d04038001d02094020107140100713042c024041c50305003400410355090403403000c104200b01390189500b0120743e1241c2103034000d9032010003810420b07056840c900700f0b481680c0c202042c20840d00915000d184c1e0001c0412 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 928905728 1250 928904478 928904507
    0x702100c0c2c070810051512040f080f0a020c0906060304060f0e0102160c060509010c08130b0705150105030c30030a180603060b070b150a0f060816 65
    0x61801e140000b4101031028903006040450311103030710a0011550300601075a00c103c0418100200b9540d84004112508030080040614288100a51440c3d005544000d0307a015001d00d101c1c0c03061185540d04c1c040c02d40d1000e600d506d4103d01c0481d4598807581d0510204283c1d0404036103012290038090005881c40c44094001065195100c05442614107150000c1b102042032100854441891841c00413a4400b05081103802c00001e060104d2868000c50640c0c6400741d040e51403804520082c2e403060300c0360788036101281104048440c0003842d00341000080a8683c4940701608008041c1c0340304410031101a002103204e500560000710f25503c4141c0500b0800884400e200906d000071140110558200400c034007803804000343c40c210040d0440c04440c440301e06150b2103001c072a030718001101180c0c000d014498108104100c280007203074401c841d8582290121440030780385001c620014410380807940c404141200140d408100032500070040310340c44013080c4414a208a50480300034043c0e20103404c1e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 928906978 1250 928905728 928905749
    0x18010e07090801050c0c01052a070507181416020c010c14030307170a0902060d110d09050726030d05040512040f05040c050c0c0f0d170702100c0c 64
    0x9140c036108040600050112030000c010f0b50420045008290f13208510181c81c2c0d41c00c0101041d860604d0003030445920558800764070468400142030340080d84600c1055805104a038008100c0d8180889080d00406850500152200d08030140048541c2d005080e05800741010352400701d5560049031981803d542440c00c10341e03503001881c3c94a1488a02c0036440d87c188804070420103483d810015041c0c075102101c40c054a6503888245440580f010f0100081d0814014000c0200e20641c6030800794041200e036009505003905240c0754811640d080105842c250310011082101983c003407d90030034029a96610003000e02d0b0390200030b80e688a40340000c094159039030700103010b01805000c000110011900c0059880382d45040c4801b019006006a80c8680c3c0380a20360002d4038041c20403299800390880217410032242600030400000180504c4070b8100410318030040000d20a5403488483d403411410054851a10f0300520018001011503041032001c0c00d500d40000c6103044203208111101c8021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 928908228 1250 928906978 928906981
    0x1506050904020f1b1504050c0607030509030607170907120b060d02030a0503030402030d0f080406050907081e0c040902030303010314100516181d060604150f080618010e 74
    0x801e00900c2401821450440c0201c0c4444030311010342040749400c92a8070440321102282e8800c0021490f059400810076803081c140d004a03403c207800940303101c074024105941000704c083e001c80c0c1000421a0694000780103000c40d4070504a800491640100405000f4082c90b4240305516481d145d92240c041e000d00c030325a000540d00e60300d103c20f51542c103a0250030b803021710343d59292566503078000781c3e4102d1080c0201c1004101c0e10707100384112240754102ea5117105540d15151900c13002407a000d4107032809070007941400305521034200310140c21904400c078081e1030b8611791078060f82402c2d183c50f0f00500c51405c14980c040981e038000152419640c2009641c0310301d9a0750030280e85402e07616800801650304080402c0807101e141e0026100c0580036031210f40700c44000c8506003c0e44846400307a000100c01001d1600c030700d080d100d60060340c0100041c0680f454113854908031a20411104001000100108a0b0013011503204400b160020700545080050f00350444070602401c02c140180340001c0c01880 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 928909478 1250 928908228 928908247
    0x61b0405010e280f09060608040b0a0902030a14071703071115070b100501080a1b18050405100f06020c1c02012c030c03150103080901021006090b13150605 68
    0x403412145120088100c1074015940c0c3d41c80c0c54068130610426240c03901d00040040e659009400d00c3e44160342c41416031100b035130b456000318020041e250085e601485280001c5d00082c0c000803d494090103004010494189010743c0d44100100b84a0241c1c80c07030304140510800108032000c04422644c0c00c9542d40c0482d00024143d440e00c0c06182405400c10200205104071034401c120030009483c3c0c2a87c4501c25030b640c8901c00b07010b82e840708410421400c082d0090380b12548c890310181203e11605041c0c4c1110316900d40c006000d07034100f99000b0005107101d54040080e070807402d10200050426001614502403000c00080000c690ba0300c401d054140764140c3c43d0b08680c403800d1200c2152000040d580340f8200855a40c13211003401d24042c500030705c03c0020911442c58001403940a24540f81d0000f6040da0031aa104140f6401a44c08203044d07104030f0b0f40c40e007011166801984080d0071244000540520b1704410840c00c681d41429a125180c64120440c1858040e2181d4800307840c1c50b420410f51320175081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 928910728 1250 928909478 928909519
    0x31f02030702160f051c03080a020f0f070b0105040c08040c0311040e030705070806130f120c02060c0a1b06170c13091a03011407080a021308061b0405010e 68
    0x100e810f4651503540040101300201c0342c84401054aa040c0c0e940011801540d000040300c007030360040034012464441c00281000b03204d030001c0211800804480d414809003842c51403198002c07100840c0d88200001c0140038070308041c441d85c0c2442010707144c511a581010f80302c038000c0504500001e00070307001c000c804034070b40d40301c2e41c02c8181e0020040b07007200d40d200ca042c184146c669940d4016103569000e200042445a00503204008046810800307560a18101d0340c1c5600e03807202e04510341018003864a4444015a0f40c0c80d02500321001803130083c0008410514006900403109060845800010a42807280c107070302c800164110340c4121000082920b903050144414010161500c00d0314500c1900030a64050a40001101c070b00c0150f0306000b9058114101800c0e1440c0119551024a59400203051144100380c1182c01c4540d2240c01407400c1c21408040c40c1040c850b8004e1042644008107101c0b203005211000748002620400450404e414040000d10400d8101c141900c50b0b0f079115403c2c031010002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 928911978 1250 928910728 928910743
    0x1f140c0a0c06050d1a01020d05030405010b0a0807090605060a0c03030b0310050702011a042a1101060608010e06040c1b02011e09080f06100611010b0406030602090f031f02030702 78
    0x10001d8040365035a40c070350080855102c044492142070800c0c01740108201d290103a00510701058014106000030100101e84076000100180c0d1199203488280303c854454200e1480640380102c0541621807c1c0a0361a083da20560700032401800c04120010819901021301c4080ba9818030f0301084a802102c0000d181c110421401307040700e4a4603007844074070794056011002101c1400d802c4050045211704003c110303108e0100041c010a01224800c0003000c00e45a600900a56820701140750614040a1421a4155000312002c600c4560051040c0004039035210361010049030706100328102c400004107284443e002086240b40114220001c582c00f410601c40240350028241c40c0100890500401d150014400c1107810700400e40e040403010400700350544549041c4c0c1da0244100d140c000200c3d88100030818400482d5030314144a5020703580c41c00750300e00444c025040561128240d204200780c0802800402c2c1c03080c0d205494905018400e0040703606904151400182c60740e90f140c0051382000e80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 928913228 1250 928911978 928911983
    0x321918050604050d0f1205190203091f140f031e04020d08090d060203090a12080f19060e0a0903030e0703050712060603020306010b190504230604050604090603021f140c0a 75
    0xe001b51841c85003540203014200c0318104400e6420100340340755003170b80c580c46100e0003142c000e542d07058444a001c0040c00cc01d00d6082503450119500c0c8805062220140c000c00c2024405050000a001041200d1105c400c0e120010040200303860400f45c0c0040c40700480d100008181d2040890b51800c5035540c408141c580c1504000c065589150050303409450360140d070000c0310f605150031a200300d00c0e803040901c94458a030422a101e40f03515803007078003460124107142ca00e00454031443c021a40d98001d21550303004222404000c03d04101c20315001c0c069684c0c22901d82c0700b56204070402c1001c1500003520008071601c1d08000c015543d042d0134214043c0450b9000650075205000002803c0100035000345200340c40d0703030904081d480400b00c0841d654441c52055500040410f941c0c10121801055910304409004040030f24181c0e4520204080d41c21690000c0c10050390b5040410039402c000c2103100c181c2007520302002c440c0e041e44001428210b890b074107001103184003180625010000304a060090b0b038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 928914478 1250 928913228 928913243
    0xa1d031204080a060c0c0203032b020c030c07140a0306180c03150f09020109060e12060108031e1e0d090501020d05070e040606321918050604050d0f 65
    0x50b154240b16660b40030841d0200d45084c6013820a24505201e24602d43c80300e5401070145241c1160f4814862900c540300d1a02107a600149020110a5204d40b00400c010351520000c3d5071901d880801003030034000590b100d0202c05000d003e44003440c6d07582190141c241c983c0160002814281041c1400350708003c035400800c042d54007040841400b03540f142210071044c40041c20b100c1601040019010348540d0440240072599941d030502001d4018120701e03250f9403004c1c000d105c9500d05507142919054003039200c1026908006012098410f030010309400040002000a00d800700c003010511440145135035a02c02500c01052108ca0054190050041c10b81c103d4029511240520050002003000346c0e12400031074114000c0e5113a134241401003030b08582c11900ca042e0035003c4c500080962400041140522080d01c81d507924a107040c3d10082c00c2c04204014040c003140c441010054600c1b45070040034402052915410440c0b6680d5800700c400796401540c40100c01d01c07061400601d040140440101803d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 928915728 1250 928914478 928914487
    0x7140c0a12020c031e06040303020903010e062406030103111528030e0c0904060b010309060911042f090a05130f110c03070813030f060e0c04020a1d0312 67
    0x465002400702200e000840039104203c05d156072104080d00c12000074440754104800050119019a0250030b0903900500003140e50b100c42c01c00c05091500485000c8076003078458036070300031000b403c0380491000c40301aa4082e01d50350540d120090603004e500481807061564012200d88480c4c1d28060354a084d002408020a440c031409241225002a00904000078a88030b8880d41d500000600007c105002070641405522507860341400b4140305821181859100c07804480051031074450b82600d40d01400710030a0113410b520401080d500c200c40c00018203001100079106a0b11002021440c0c000c40109042e42ca00c00301d004265141030b079030320446d8071458500310718400003e103801203a800440030700308208201020800600074025240c90700f8980c1d0042c80b194000076000f500a220307203404140601c1c1d0150b929600d1601e400c1e1015011100c039902c441c01c074461071008000300301503504211819818a034112130000c00400c0c0c4c500740b55000c0412450210b900d1b1300c00b070003107000010208009aa54 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 928916978 1250 928915728 928915763
    0x228050c06092503021008072006061c050d08041b0e1b04150c060902040e100c0c08120a0e160e0c03040b01120c1806140907140c0a 58
    0xc440d0600c1c202245404040c00444910a071030310f000c429250300070a00440d90b400c2e5031048603c108014004028040070000c00e4030804160304244452940950040c011481d1581c180a02e101c0d803007400038110400c81201800180010030070b05a0416585092403582c0d6a60a26007003460300c600c5450300b0031010500214107021104626031084204446200c44a107285d00032108512540c07281415012070710741c03602c3d07205221742c842c0c803d1903016000100c0c081520f50005011280545607200c0c05a00840004070003400030f0140c51155449030815800481c1192a1141940302c1e040b01030908607921130014820440660044000d0031004e012900c02e50040508140500502d02541c000360300004001002d240e840002c40f48910703031021403082103919210b14000d0780c0a140500300c8102074042004120201c0c030541200094010307500c04603000745084110303050454401819070003060501c003041402a0003000e030510788200a50310742e56440043c0d03046820003610344c02c01440c220038030403071600707 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 928918228 1250 928916978 928916983
    0x5190305010302120607020705011202070b0108010203040b09011e0507052713110d09050304120b0103120c03361701180317070c0206160b07030228050c0609 69
    0x1030343e01c2a6844098421108941c941d01e00085a41c4001070380009000e1200f54440c0000d0b1003c88005c560250420f062035952800d00c180076000ba00c3c00380c2d030110801080c00703c01c0e565141c00224420080014481e0001c1e0341000c001c0580180c142c1ca03440c1c0010400d054070a008485e01c203c1107000200c04640c0011245c040240c5000c1414031540481801520480e480e110b05c0d52039110b2200c3d514a010119546e0038054280c201c825a0140024040000d800300441600100305216041503800b075070661038050302040210301464108844c42501d44002601f10100d40200a6101100664104556080d058080566020016807c1120000100760030300c420014004100d01000f400850f90820034031251045006000d4002441c100d000d0300c950f0741900e03031075421000c24900080394941e2500800c405901c00c0304403410104040e034130803090000c0c1b55082c0707800c64058501549004500c0c081c0100307100b0301940405a44440c1c401c1040c03070328010011201556103580940d8183e00d801190281c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 928919478 1250 928918228 928918231
    0x9010e030109120806040606021e07031a0109140702210c01020d05090d02060709030303020f0909160f09050a0e15030f2a06030705091504080a020a05090405071505190305 75
    0x240072542c4240400c0d55886e16000340801d0390f070305070700610400002e034140c0b15071040c80d00084402801250341c0840414000c1d04103980f200c02c042c1c1d881c01c003945055600800c548501141c1101c041c0c0340d606104889a0100344801580001c1d0065040003421544082d21880750809018081d840043c0e40304001075190401d91291008c4ca0594040c602c0d10203046e83c0720401100c9403400642540802d100082c020f1380a0f24903103080385041802e2101003400308052820503180203c3c903100e000a43d44440e40d218030811859400d901d018200c9506d8a40400d00800050243c6503070f00d03c101e03000a044040e00f4180c040381800c01030072a007100d1600b0f080b043c0c03103000030383c0c003100d80003c0e4074150384414404445d0b111030100702030070381d03841c40c0e039050012a42600082c9105510401c01d00d101e8120141c003001403c05005038001422100c60140b042090701e12082e4001405410311800b0000031030302c08942a01190818103a4009010340c0b014121210712030b00c010380e60803098000c0d0148034942e0550106 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 928920728 1250 928919478 928919513
    0x150e040e070e040206071a010e01170f0601060c0305090a030c1e08030d020a030b0306090607030e072102150f03070801080307020a050f0a0308030405030307140f07030509010e030109 80
    0x4100c1038406a2109464500380d00410803500030400100d0010304103800200100703405100350360a032940702a1440c4085c042a84025004507614005002d40c0060554180b0702d075103000d0003800c10000c074501c100d0b241c1105215030700a108c40005c5107818140550201e4032030030001000072049a80301d141c0080b1100c42c6016040c0544404140e5941c454403910422060742c2407031004606098000d031036031019502c170011070010980c48040210941c1c6007000014005c1e000b02024003072505c0d0030b1000604032442151506034580c0b000c40e0401441040320701352107001041c40c01803043c0b00311900114401d28070000f00700c2c01070503000913007041d0b940200c005036020340c50b07940d40c1c400aa66030704c550503600d00804034040d5104040d038400300300e5480c0002941f0f01d00c51700903051011190356925460f42e19041201d068400790000000c20502a070b00c0030348a100c903a91010403c0c1003003a032581400709030003003060086c00e00c000000c2422190303008026042d55142c00500910582c0703240d14003004101d00084c0300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 928921978 1250 928920728 928920731
    0x7031e151a2512120b010306050a030206030c0f0307030e0756090307060206041a1504060b0d0b09010821090307080f0607081e04020a150e04 62
    0x200d1854240100c0881540715460030758200400078902c01c100800310314490b008441c0740203104001038649000c901840115032140902c10f2011070018003980c1c00305244030304040c80c1a005205659603800703858246d0350180c500c541c6a6888250039450341c800ca101506421002004100c180799158014981ca0701c1440c1c240c2c1c00c3d40d0360f00d0001d400340c00151910030f08180c0741390320903c0005c280c00c0780a201d001148d44c8030450010b10211070481103c10200801c2000d040002c001c88107080400c0303400c0c000c0846200501035480d1079107414600900b1001d106615030300c100085940108207482038841540001c0082040b903a071030903041002e6022010312100c1e01c4c200300407080300345401c0103003a040702c0301c01c8045c2110080b00018090b4008400c0302820021005000044540c1c07400c10405029024041c000c10f040300031440705920f0074074010103003405c00c49038100b002802124a02940c414000003a43c0c10360607291440003640c450040c0e00025030807946c0214038140e05600541c00c49850000381c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 928923228 1250 928921978 928922021
    0xd12060314071728032106050306090c0120010908030a0e100504150908122a0a02070302040908160b070e0105120708373207031e 57
    0xc3ca1501c03405541c074800382000314101040400c07444851403404092080c86c100018842498942104051250b012210160b4801060120781400c104594000740400d00500311320035408002040c5c0d07041703116401c403414002c00c042031001a0940004042c80d50100d8055160710f004a0000000e00c1000f0303506410784600300005e400c2410611805000700d400801c0c0f5400703503911912000181c014180d044a07600c004000d000c1c01c010100e05400d004001c0b1044003082c01c1c0c221522654072803101c07080011000000c00090350030640010b405402c590707056801052100075030420b0071180c040c5104c980c5c81580c102c0b00715401c200c030505419200300c0d01d035103424044028074001100c42d4012000541c940e200b40d00c0110f04201c1c0070750003413139010025032200ba09000510101c088007584440e4410b0000003902074404503070000d0f008115411030001140e254048041c240d205103002d41c3c68642941c0c0380c0f14008109018401d40010455030020030042d0300714080c00d0302420040c00510804446c0300c03803121 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 928924478 1250 928923228 928923269
    0x3040e01061205010e3312030d0606050f0403060f0f09030f030e0f1f09050a0f0605010501170f06041104030c030c08030a050d0b040f1425020d1206031407 68
    0x2203021b42c00c88442e240700b401d000341c0880d05410449041c65154060703201700c48034640e030302c4c1d1820329407498500c051615030a82d08078400c00d6411582080007401401d0200c031101c50301d050140e5007182c1d00244040741c0e03003400c0720411001780a141d000c51901418001501c05254100a0f140c042043d103640401c11101800c62444c1c495a10010740280e0360840224400ca1404c0140744038a600c2080400150f005200e941c0c46141c48040320040720360f04e07500c0d081c1d03000303001c880c3c410309005001c01c0c20306400f05c02258007850a00c580017004001000805004520240c07126400803582014400c0103561700d0351603040c8070940884a2104440303421070074001041030340001c0151040a900b94403540e040400080b90035015281d61510f6580066546203c0140d1030041e01445441c0324401100101c1c6083c030080560031941c001aa207041740804d01d61042110341e000801c00d591001302c0c0740c8010100906400c0c1c2002e8141940040e084803401030502d9018070000c5006021640b0480010307805a6104 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 928925728 1250 928924478 928924499
    0x702090c131505070620040618050102030f0708031905090304081c0906081f0f142416050609030405011101050f04030e0409170d061d0a0e03040e0106120501 69
    0x1054100000c0d0b05002130740015889800000001004c284c00d400030301c240c000858401c0d0020780c4141f000440c3c080d421079a0b211090340700005002c0c284080c500d480d1014800241034440c589000303024481c000001190038034075100400c0d000044010510081c2040c07030b00d01d5680e801c0f40c0515006801440c504a0300c02d120210750448440f200e40710014031916054050710b03041c40040007541546900c5102600061b001140d0202421480e0b444158880c1004030101d185081464054060716504034407020074180162025000000004101e42d20510502c02e580c821041031001050351090500303200d236040d80400031f0f0041e6036007030740c5020f46813011785111400c2c2c03001a00c82c84801d02d000d02c04500400e10405c20110142005000032445c030341182e4800803962101d088210b410031010942c1c0c4c400b070305540074400c02007004185c048000d00000c13100401505001d0007c81d80250b81c0e0021a17100b180900035100204051280c1d611150782d41c40e0007070302049801d08114405464800042403c0e4040b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 928926978 1250 928925728 928925759
    0x70f060201060e010e190f060f2114030c160501180e151503040c03140f121305060a2a08161401241403100b01050702090c13 55
    0x701d01c80520182d280082201c00c45c14080c0180b540002280d1411103403102c117020b00d01003d09031a9001640da403500310307030f5603130450309030406241400346105280e2000c1d054101c48003216005030403010034140d40500789103940326a9180050758002ca861401c03034003050031004d07002c8070300c01e88810300034100000840130706a013140108820075002d0700100d55015107061038010502009800c0070b07415003800c10300e2450b640084a0031510051004424000c02a01e00704400b0b400d80c2d401c00420702541d500c00416120040c0e05107221071404040344101c5d0b03108603100c01c50014400178080303a64944102c0c80040400120102e005100d04944090801a2003651006400070703410044641c24012510001c28004010480642d0040b16106960344100020320801e0f400300720f1040011544c04940300681c68864072540060a45450b2000c40a020b4801040e0310b407a030002410002a0704008a005989a010302e081c043d4000e1103600c00c001090b00f54170002d258040c05000c8a140342d80e0b841d000e0f80c40300c0c0d24 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 928928228 1250 928926978 928926989
    0x10e150706140603030706110706020706231611210d0e0703020d02060304020409050d030914032503020a172a1b120f0607110d080c1812070f06020106 66
    0x2040106d840840d190382e10048200125404c800d1810013192900e8050b03821605003030700d0740745c0d07104608840700003022611104a100c0289244a40c9060080e501400300203010410a00c40d00c108030303007590802030048030424818078207103c1140c00d0551801030380d40c02a07466101c034a442c0694080c1d4000b00000d000c41200d40c01400307052400b1440c0d092140b580c01c041c1041742c0164944804030005101408100c0c1c4140070341c3e0700095512643d007440700d00441081e181d0241a0010004100c0341001e2441a10540103100035250b40b980c8240fa040b4600001000c01620101c074038a202c03054071808070000e00210810f84405282c41e01c4004100303100a40424201d1030640c0000201510f8003204d0b0305404800308010320383c0c0058451001d10a08014050304001d0b22600044100b012440d04200071007210440c060041441040044024000d081c0c00307480400e09290104450500349045000c5400641d00036290300030b00001081519641d000500412000141011001c43e0786841481074800311030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 928929478 1250 928928228 928928233
    0x20d020d020f120c01020c10020d060504061202010c031214010609060302030f01050103110405090a0b04180b04020f0a270e0d051b07031217060a03050318010e150706140603 76
    0x510b20f0302e00a8a64060b5000f983c1c2c1c0d54003031040b440c6e04001400f034042500818680075070340c1c94201c10480c0c1241e58a0700a07501c100d00e02841440b0075100011000c0101d5070a080c80c018900c41070070183d40d0110302608c90b41045003040c4440c012092f48100c020704982c80354a51520645e281c400950a80c003040310030140c840102e0004010940c400c0e04020307640c02101105c24030382511000030030032102084400a000f00c0d00c40e0842c90250409200c0d0300450414409840303c6201c1c596a05404004045e002a204035803002d000840d0750780d004211001011a0401140300b001800301d04024481020101500585043e40710700341f03490003140070040e0030301d2641c626141c04d00402040c03890300301c511140281841108000b20014005814992406085842d505045000b40309105642c22006103001c2c05004210300070800100c000095805d0045021580c0c8103101e0f171880100c50814400d0301941e8003c0908258101004c5400014001036004e40740501c8030070781040c80712070441d400b030340c1e00343d0035a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 928930728 1250 928929478 928929493
    0x1303081e04111324050328020114071505060105090f011202041e031b05010912020316120303061202030c060304030207081e06060d110f01030e0d020d020d020f 70
    0x1a000d03110074210441c001e110304007107045000711604072014070801c0c13940c0e4940d5000c0044405114800c120041000f10010034541130303590601d0508064201002d40240c586aa00c1c2003168001e840164010341d94191140c0ca8034468141103494030408105d0421a901d064042403142d4411411144075840180c049407481b02e2960044131300c42c03c5907201010f069804e02c0b0109104849080440b0310000c2e40303004200c1036085003000e41e03080c401c40076540602861080200302d281d0700140c540c400c5410a81c0781d291070062600100303041580c580702411901c880e060300860a40303180c142c5805d549000780e038108007258031101c0308400c6400d00140694141d100210070009454000300035036001d8424819120815a90310b512807510b004640130040460206034100000b6404218565106c00100c0b03035110444080d4603510b15052582d46840e0080010b10500e080c940d0081e002450700c000780307200b181c6054090324402916880d00381904030060280c038040280c0740e072001a145219181300405004071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 928931978 1250 928930728 928930733
    0x402090a09050d120b0901090e15071b02030f06072c06090904140f0d0f0509301f0b060408100c1e0815030d02100c0c08031303081e04 59
    0x4810410441004e05031240d03042c0440d902c0b0a40120b00802a850b00401c051000741c030800c4c14444d40028082a105010342001495540041402e03901400103215202c1010740707001081c02e05180c4100707403606106640c20b001000d54407829500d044141e00f0080101c903504081d42450f204007500010750f02c518184404205450000603c54109103d08400340f5600031200002d410300300781c00039182803a009903500c02c0c64550043c0d60518100050314004d8034140904000801030360030359074bc407040b03c100d20358000c008074002909010540650b2040312000f0501c5181180c08015101c000d001040c2030000c0c41034207040c1700040d1025103410a01a0401d0781d07070b07140c0305c000a0035040d50600402500081c3d49a0028024034000050800e583d5858014500a614028841c4840c4641030281d406003020390072030ba9020031104041c1e1038510000c01c001e454400201e8031005103160181003010000240305040790100980000c140c0b00707845d03e00c0c107a070320b0340310f03030204900400d5500c10340e940d000000400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 928933228 1250 928931978 928931987
    0x2030411040e070602100c1b0302030306040c082a0f1611040203010b070807050109150c111c080411040e1b010203071119170313050d0507061202040801020a080402090a09050d 77
    0x5181a140323030945640168042c00c0040503d000800e0300560000010706c507160030103006504220b940c5040180150900c2880c01d680d0c420315102c0420f0000c0441105a241c0070729404031182207403440b16054482524a0741c5060190100a003100c0d068091112042c0f141014000ea81c100c60f00e4042280c2000391a4807050900d5101202c12201d6541e250ba03600d002812221003940b420007151400103641016802c0540410200026180b9035402207032001301404020364825505c40681c03400000c05d845a1422401c140840380c2015401070900c2100c10900d900000c002000301802d902c000d10f00c0d1480401642c50344504100135000c002201c02000030381c00d1808040400202c02d807842c1c4200b41d500c03034055070320042c0b0020820007a040040c50041d41c50002c218031010b41800ca5081072000e007249d40e00d83d6181d0f203611a6038140402107011344d084c00f182e54160b90041c05103d000707556820110000811841d01240c003207103c0e04d808408192076405500c50703a4485136202d0700510203100710000c10b86 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 928934478 1250 928933228 928933241
    0x608070c0c05040f0506040e0f0309060a09030b0c030f010902040b03070e0d0b1f0828021906020a0c090506010f0815120105070206091b1504030602030411040e07060210 74
    0x1d4210400140009480e02c607882402810410140c0c00122400d10300204010f81c1c25044541c20682d0010450741144e10010084610720340e4215000b0703a40320340c1048161441a05a0700180109854000300081040c143c4000c62155064503c24a0541c0c1c0b502442c1c812030095001394415540c05000140c2058010748000c9010340340140203070034005031a620511200b40c100c8580d08060000d0355041c1c50700100c04264400b07061080058002c0200414039500321040c030001c0342c03007000349662568003592103110803402c903401c2c4a0b0412040e143c990030042e540d04030002082f1400c3c811a80006108034161060783d0050405030b50b503486a1035415821151020050a0207540d1005915107962903541d08081c03040c2101d1000012540c0d2030140000780c240300008107515802c1e04294003040c45a0301d00680c09810090844100c100c0e81001c80c01b121070b60190b5000201110b100101344014001403811916612130119030034444003100500c00e60711040300b48154800742c0e001d1420246024225000300 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 928935728 1250 928934478 928934483
    0x220201051b0f07050a050a0b030c0d0b1003050906160819060f031a0a090f0807030903060905060a0e0c151b01090f03030606050f0a0503071101060f050102070f0608070c 74
    0x640441007180700c05400c000350702031030424992102c0410421401c100c2400001020103c031140045840c069180040788401488a880041c002400c0d242d030382c40c0c43c0e000c01c0002d4400380042c82d40301f51b01d440c0a00107003402c0d60b48140900c280300000c0c2400860101c0c160021220350f42e000202e445840781402d030fa18401111031000e076110a00411120200c441c042d0044d40141407107210b602d881103100c4050a40503000c003040354240201030703005c82c107182d124401d01540450056a01c1e00c03075060032a60682640c1005240a041200324800d1002c002016405210b400c042000380500d88001c070f41d0745a40d0307490000e40001e00445282c0e40500303110b0240050309541c0c0c012100440142c44c81070f0865131035031012500100391161072018035515106641c05807100b801d12500d4400421303007000d42805803d4802080103800000900c0c0d07941700d40c81c01154020310360001e0190a0702c4100e5a010440c1c540074040c018480c500780001ca4444900c0715404076021900e40c088240c5681e03c0466810401e88800e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 928936978 1250 928935728 928935757
    0x6020a02010902100e01111b1e090109090615050102062a0c0304170109030c0f0201020c180a0f05040c1a070c0806072607080a0b0405160822020105 65
    0x4034000d80ca481ca072802c00d03104d4584c0c0b80c1c1c030082256400135101054034400004540d01860000c0561604c03001c0c409072692044500411109244018400031241070303001903008500c1070000140321a5a81041036200d00c108000d015449040baa0200001114401c0034010307030018002c0341ca01e810051525030004010000c100c9450080800c11500f0352220200001d9648001810000c800c100b0381402c0803050079500034419140e09480c02818010f4410001c2c1100d030088603508116030081000c4421040050111a0840e203e424180300403e4100ca01508950906101c95594110b500c07545d44142c1c2e00407000340070340d410413110fa68000301c10b00070410740307200420144d004a59100000c42c02400384000a00301443c02010050001c002c08041a0155610b018010f100303030a80c0a45a600200d5440c002c6d14943d20343c880f000280240c280180d4109140c4000c4c8419440420440b1000d44601e48544e80613031500000c0f0050a1101c04d908200e020403a1200f0006610840090465071044040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 928938228 1250 928936978 928936991
    0x3070618030f210207030b0708070509030a05011b05070308011e0503150a0b090105010503040b0703020f271206130f120e10090b0a030b060705060405150f100306020a0201 75
    0x41e8118034200d2004280c820800c0610074070300748840c1c4603250004040c0c80c0302502545d13145503541d80c61050080d00c0f05040c80310160009955521480a842e00038100500701c0c0c2e240006c50030800e0080409520a420030b00d820300e20360200c0c90088044030035040c2d060359000d40c2070b0f28003d00c40200c8254100b82c01a8603010410005865800300720b04c10b070140d0300d200c038006281440880001241c400c140143d00a20001004000d2607800c5001d584c0c1c0301e9003142d001c441d55506d0400440c000c0c40340d440c8440e000c5001184403c014840c04c40301e5501069040d1020701c1d513803c05010804095180c680034055980b00100090540c03101d0181d81260600c9070240f4081034038656034220f03030314000c800c0702c03800030380050101d10709803820703458a00c1040c20b242800308215042001091141c4180f4550000307158072030710580030729100c11003162141500401642c00c04d0425180c00b98890341d01e014015401100700b004074002d011200c0407940a45001200b0004403443c556402c0003a40042c1030503019550703a81c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 928939478 1250 928938228 928938233
    0x20304090b15070b0f060a2d0308040f0f0f030503040312120906051603090b07030e0705040c08010e070906022e05010902030a0e0a0c1a040b0409020910030207020307061803 76
    0x100a0030ba4284500024803003440c0004484c17504a2004028074400d19041004006d60509500c0016090822080603004940070840080c1c0b8040141c1c0003e14500d8002400914a0f42000e88481503549903040604010f548001c3c5912084032400050030a030000c01040000a48500001e000c203581400c2400034440519058011104104000d0781d1180c1c4031410020220f0300c204a407030f12100542010400f1010700c3c1c03280c10483c00000d01c000285580c1d2015000040010001755005000041082c4944407002d10b0041c2011b40038860340c07180401d000e0115401d14011034018081d900658000c04401e90b04407001030181041460201c0034941070305c0c000000355103d000385406004144000740e030b64202402440222400e00d11141c245410503264800040d610040c40c00440301031090301610700601a015449911a6601c003110403140010300203000070b10340c1c015186402d03007140d00c0e203407490b00c203a0158140d1040d0f100080d4075801150041c407055000380020b144018003003012041d030613120ba = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 928940728 1250 928939478 928939519
    0x91603020318030d0c03050a091104020c0a17070203010b030609030a0e060f0a0201091205040f140f060c0d180b0a080705091c141212060f211c020304090b 68
    0x3d44c8101e52050f00c4000c00788886415018030f58005045180c100001447c50f191003031513254102019100d141c0002e865260101d007041035140c90784e003003a240b502269941c51410310503401003808a0195090413034005403450041030a03032240010201a620f090b50110046032000d030003030009a803107841444498000c11188000d0034180749940c0000400d0030090402808801e0383d0684c4008201c0100006e000c0107840380745a508503070384800080e118404000014003060500703a403154000502180c0e52098070800240001003a00544039000c442c0c10841800c540701d680c1e0f0203031221019040240c201c2d041d00c240c59280c0e11000d149045400d1419641c00203801182c4a02d62242d200f040416a2050081000c10904030100000c01000d0384040e5460280c1903005540729a18101004000109180c4401c002c80d866940300a01101c100d201c203a11084482c00414850541031003100044545401d804010b214800c809070010750500d4902a0050041e244048074036400005001c400d20900460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 928941978 1250 928940728 928940737
    0x50106350103080a030608010209130e01021e130801020a0e090402030a02060408070f1502061b040509010b0a08060102010501051e03030f16030f08040206040909140a150b09160302031803 82
    0x1e20041d641d11500d01300000d0940c0e40301d820400480c0d104100036802a40e608820181002c00d90f2004517625240308120f5009004018404010101d01d4844240121107000180403410116104a154680f03a82020f802c07402407103000ba003c2074042407103002501d41400a2540303c0e10080444072040d6081d0301285d1150000d610031600e550181c0801c2c02001d0301c0c00220310141500c0c61340c9002120103070794025541d00c4043d20446113290101c2a100018501404440c041c00019141456030b5035180960f0031507600c01c050940009200c98040740d003661041c001c03175048030b100600720484500e80d03071501010704003d000500d50600c800c1042c20b4203080040041d00006c0e001014500c5050f2907801c0c040c115107401404002040a480c0070080140c0d16581910240c8544690000d0070050a01e0030300001d9003007401c02121445100c401c40200b107080580c40400351703003d901c107018500c081c109200d4503841c10390324006144180420140120b10039030180d540606404900d0b40700380040d030049800d40e0301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 928943228 1250 928941978 928941983
    0x103080d0e1c0e1c0b0103060e121309050a0b1311070501141015141b03070f1104020c031603090e01150311091f090801180b0703050106350103 63
    0x107115005400504e800c8290501d182c5260b00081c6030b030103483c0e440d003c0c142014003009000554500255281403410402c070300410508020700b55685025400e4100d140b1024881c00ca6640d04260025960f09030754014000e00400251142403d1201c50b54000f01074031074091031011026040c012107020840900418211039861207a0b5880e5041a4241090703203903d58125a488014000d070079042c007680407500c04c00f0703d0400b00e07905441340040032040c1401c0b60702c80a1403c3c10312000c50404184105000c103503555603c1140e8060001c126141400282e004070781d41016650818801503204004040c0381e04260f6100f490040c00058440442c2139008100381c001c0c01c2112185500990308a805202e80952a8845c0d2000d070300300301d2068000344840c204440c0c44c0c0c101c00f58000e0681281401900e110000e4403054000b84240b01c4c02102c6d10400208011065030f810702a0b40100345401d00a2180794180d45240e80d8600c040700120440c101c10900030002120300c8080480411484640b01100e41e002c1c51 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 928944478 1250 928943228 928943237
    0xd1112030d060f0302031c0504060e030a14010e0c0123030c0d02070308160c020d03180819110604050a031e060f02071a07050412060f020a0e180103080d0e1c 69
    0x1c4c00c600601d441e14000091852000703c10889840388103400ca030558013100c006180c02040d40071701a010a08100103408001d04495040305030100110040d008410325810300800c03182440222001190003014801a240310181a658460140d84500000303550014000080c02e1500d445d18018030101e0380114416070000740740c0428031600101404820030109858600300401d440c485d0001000405002c0009051144a01c0011000085441110020503030701c1c040c0d074440410203070307865002c540c0c0510841340d0a03610086014149001020380b801e99a01030512460b040c15669280549202907030002145082c0c614a4800144180201d01c81040e20302405030b200c1080345044014901402c0d803049180c0ca0f01c4080100d02d41c1c1c802e086e0bc00711100403420122404643c00c00c10004c1941003100d810799400081d4000745031750415505000103030b064404410860301d035128801004070030300004000e09804c0048a02c6008242c1040d12004020016105064140041c200710701440348400b00106 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 928945728 1250 928944478 928944509
    0xe0a1206020c160302130f090203010501060206150411032a1801080114010c0210030e0a05060103021005040e07030231031101110606120c090903030907050d1112030d06 74
    0x3a0b418014405103445500c2d1100c00c1c41d045500080300394801001054143c0c0e42c84c06018034041403900016040d03138024008009550312000000d407120021500d625101031406074011590400340b00b4042e506102950460640c1c0780e0000000e40100c1500c1a000c0c0d140717503080c0c00d0055110364401855540580d2800384c889001940006d4145141640201b80380345032594540c00300e90f00a20802806541103034542c08a0043d18800e40c0200b40140c5010040d2080f09400001c0110004465044e04d0003243d03219103541d445c104c1150303e442180154022041985c0100b401d40b802034000c0c00c4251004528645140282c8198407101907204654540110b01200104213020052688070501c48082c45c081c00760700003900003140d5489014182078094044266522004803050043c0c10151000070410701d01c0d42000c00039540c0e031340c1056650a00c2400391020016840ca8507003068140c90364001c0403103408003800010003031820207074503190010340000c000c1340e2405521480b41c10b021744681d203542c0522 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 928946978 1250 928945728 928945747
    0x1020601091e0c18090b030c0a15050913140402040b03070b091201020d02030c0310120b060103021b03041206050c040b0f0304031202030a020d0e07030b070e0a120602 73
    0x81040603030101c41c0c200d140141440c0400582400401c6107242c4502c04900e12240c054200da0241a04ca54810f070303e404400081a58411500415203031401102220407252455042001100c80c911484400c200c0c1d20341c88000c00307400b6070042c2c207014000500e0401c5032a6040c3c2138006a43c0e4500f441031144040508010440c5400d10560000500603002812984d080400390100380c4584500e46100e240c030040e000f88400307002d404903080b803240036600791740700e040c803a0356018503401c10b60350840c0524500e1004100d2031340d821a00c0d501d082d000300c80d001c0d107512000e005400a62080d500e0b0b0600d2404e91094000103c81080208000c0041d01400c0c08150700300c2c100801207841c007801c0c00d03030958410002000301e1400e14094407900c20100101d19603c0d11145400d80b181549000b58019181c004401c0221092165015007403444107200c0500c101c103180d50a00e61602803500000f4140c08456002c90102445002200340e9008040e0204c3d00282c0c4a00f10b40000c00d07407402048481c43d4000626668 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 928948228 1250 928946978 928946983
    0x6020703080921180406180c12050f010e072006070f110c060a0c060606080103201e1c080c120a090b03040201050f120a050903160f03050c0304080102090102 69
    0x200c1ea040003c2d145040c0300c1c506042c49091003242001e0304122084030320000320b592071380d110000802808414108030300c0c2191002d00688021581030010548000141c0c440304011302a00b8071480703800144d0440b030b0f0b003080f1114545407406007404042260b1583d000111203040d82e40d800f14280300d803000b03080c90710707080d1320041c08000742c542c0c2801007002c200c0f02c0251040340050b03000ca030070204a802688a59244a0407100791102210240106080000004046030030401c1941603a0040030740210000c000b52103041d6840b0b420000541180941d00c0c51443c0841c503000048403107200a19481e03030300c49102d10040301d000e5540b401340d81c10b00d0300044015005504216082d0f035003811044080c04c00d5074901c0d014100714a14840c0d0401804000b00281c1160300c920300f2580c0c64109050070300e0300d801544048820910089500801080c940404288881400000d0b945c40c907245241e940307100d90301942c0c0c5140b01f00301d801d402c1342030280c10300180c1200003081c4080d00103000e924000603210001c1c03000091 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 928949478 1250 928948228 928948243
    0x8030a061509180207030912060e030a03150e010e062e030b0f010c0201080a0e03040f171b06090409050f010203090a1a06010c03050a0e060a020706020c09220807060207030809 77
    0x82e80c6030b104200c1d00d070009810584090403101600c01302c0303262448c641031207400350003006c0b040380082c0000180c1d00c0c001501640039500810007854003c0c1d0b52134840710708041500003030041488401308100001c4540c40e0606079a5941080d1411140341d080b424101c3c0d0500c40c009503c1800132076210381c42036846051100894109000c240303000b811111540e00007070408038025020340b040546840086c0d03c07119007042107400400c1915a0b1b060180e070340b0710007540d5242202100d0349150103940c00707030072912544601c00450031300c0042015142108400410005241c0d1000885040c0502508103100b50020302c082d43c40341034518050300d6050080d24064440c040c02d070f02503076050340d0a82c080c04500e90380104180441c41c0c4c5404c195541d049241000d5490085903000650312000001c1c103140f580345c0c007082d00d0302222456000c4070703010442c3ca000c000c50854102c6118079280c0e01042510320521721100210075450182c40254a00190707034a03230100341d0344a01015800305203520306100c1c0e0b0440821141d03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 928950728 1250 928949478 928949519
    0xf1305013b010501030c0303270f18110a031a0a0308032a0a030b1c15060609081c12180b060d02030715021603053708030a061509 57
    0x304050760450ba1b420101e58903600005c0d0030010b20400a410b1070480800c06918122100c096000e41690342c00c029040c0d060074040c00101241100d01e0120202550103009a07038410050001d080000c458021030041404285594000343c243c5110100350329a4886038000d54080c070a200c1c0c3c0c0c3d203014050400c500302200d40c5c0c1050031800500d041091031416080d15000c40c05071401181c842d030640c00185580c0c510020b1040d640d802a080c0c4000c0042d291a94489a014410188038165464801b600c1040c014403584829800c00d1000000601125844039000411818110300640c00d5200030300454403401c080080103440081c00000b4485103d0409500400131120704040b4189035020a1321400c851198a60042c280072100e1038090003400404584044c03800440e108550301e082095644450004000500e00b5212060022000315a440300c840c8042c0021800b81055a0f502d41900b0f038402414000c01079598036012403c00d140c5100f00494448503070380d1100882c10000d07103001300300049104 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 928951978 1250 928950728 928950731
    0xa0302120406120f0209040513030306081f0f061a13090627061d060f06030601050304080a0c06090308090c01030227060c0a05070e0f0f1305013b01 65
    0x2c004281e44450910280880380001055400c4901c510201034005c03256415486400e104c1000f82c1345900710615090280240d0301801101da9424541c0c0d1109030000f0b14100e21b54000c801e454031f03a1117a030492009c1c0710039001c0006030aa03844c7c0c0f170035039190400c0040c0c09003480c0c00650003c101d030140c104140a04181c1004101d51898426080718001c6001403150071204214100b8410030701e00da12080040124100c290b4440d0240c185055244108442c0148610072010300041c00e400c112094034460841a118280f55848a44641030113821001c400800c010b81007050701e0005400f07000b030301c1c1d2591003502c0c0c102e0302d404d09081050401e4002d100b51810188107010003030440744e10115903183c440510031a04059410500810040c2c0b09032046843c0074482c4090329010044001007850454000c4800c0f402c841c0c0b00d40081003440581640d1000141e446c1c0c3c008561851000302142504600c10000080e200012700c0c07800d04550210050030b000000c400505241c52100c1c01011003104441000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 928953228 1250 928951978 928951987
    0x11e0b03070804022106010b0409051b091c080d0f0f0b060d092904030906020d050a0f05070b0405060108010b0d0b2a0d020405330d14090a030212 64
    0x103000b020518000c0c40640709a50001e0080004e185404500280b80d000d04261002c0350b86800245103039500901ca0301203845d150100151020310a54901d03260fa4441480080c0741110240c1003100c81d11042581d00501e0f54401c920303d001460240044c105003070003060104501c441c05c81c0180482e001007101d8040b00d410003ca001051307490404503242040302d840002804036441c1030181030304403d070034000c4103081c0c900b980070314400000000031b118508c25601d200241703840300d1049855001c0b901c52403010680a00c4000251800b0740c1020f41541e80f81c3c54540e003022815161000312240645081d595a0422001030110100030300990090768829188503071004200e5960490110b070051000c640201c0a22003c10501100b80360313600001c041c29030240e2200201d5102a0080d4042d100303461242a100b0707031a0700d002804a01e00748a07021032075100b031030002070400020340c44d601c850600350003150365082a044a661402c00203014807007020050216860b07a00d4080e107401150308008104520510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 928954478 1250 928953228 928953241
    0xa0821150a0e0423120c0f280209040f0f0308091c0801090c020c0a0305030c0105150f010c020415030f17040f06181d04020f0f1806030312011e0b03 65
    0x3014400d500c071303c43c6a001e82c1c200b0164803041c10040c0030803d0120340800012203d002420005404080605c2c001c180c1301541c3d651903c2c9407000c070300513492803142101c03002107102524008000940c41401007004488943c080c1d41c482c0f000701c8651100300d01082000e030a01c08101d400f0044440390402006a030048104403000151480c101481051400d40d115a40d52442e50300c2400400d00644014211031445a16840c0c001c2c0c6940210150304d120358a0b00001400b1481b050643d03010162014000c054448422001160a064030941c02e0b6003207900c034403036841d4a002c80756900c801140110007048041c2c1c00f0346817800310a40d01552519109400303100c10301c4401c070072031080702c11036410341807291340024960091700392090513902062140f00e960049400181d050b0603000d2240d0305c210788401c08100c2d1102000811103d40e80c0e907580042c8281c0715034101e003401400441c4c1101c001400c80e400d08121503060101d0f40000d0700302c0c107580700c40140c41010402c500f0710303a440a40b40a039140303815480d048 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 928955728 1250 928954478 928954493
    0x1b0b1501020714120a0503040f08010f1a0103151e060210110301050108130804031a09161e080d0e1804031b150f060f090207050a0821150a0e04 63
    0x180301c03e44240092031000c0c550000c04c004109400d076100040e603464503030760314171410042042d2007082a29420002c0da403024040c24410b58880205101c0d021010f0000840110300914899010300c0504903682d20202e06960144a880100280307810200c050350308000b4000d0400f40c007441c80e0440b4600345014003c8403034018099078151074083c86c04008655401c1300420800d8045d083c040c2110b00005000700501c04564176211085290040d400c5141d01c1b02c40c0501c0c1e60b551310380e88a6505903122030f0705100d90307001407408851141541401e0a10141c0b40d81440d82000307840707100354002c100c0c8185600810300785140c0740c0340c0030344542d0000d440a15042d02d02420320900304811840720984003c1d680c040088a0701c00d03070003422002703104101002481540800510300b501032908010304900740052050602d000f10780e4480e0b031207000307068140000d0755001d0301500180c6032501ca0035010465580405050f2104500c108100b403080640c10070039030188454403d4a0300316503400481c910812002c03a108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 928956834 1106 928955728 928955759
    0x16081909092307030e03042601054f0b06010905102c060c03070611040b1b070f0315050a0e100c1b0b15010207 49
    0xe400b000507148454401c050b1554078000000c894520980042034a007410780c0072203041a4440b0081c0b10300c44074040800080304052018070070081d40c240034030358005426100d003900000d0114010000a00300000e00c0582076609060110f007401c0d4124080c00da2620704035007034240e0380a071500c080e4003c0143e8629002a503406030121300780c43e026076402c3c030390340c070540b144820b2107518482403c0e0101006601480d040788100d41a0f01c5071200c400038081d018a110107969030780c8662424000f255140c00c02c9a041342d40502044c04401560701c01c403546030000805180600703800f41c054034a0048140c100c072a000c80041000010010301114101c60095101c00901c400c0c1d0304d04084400f294100c4030b01035101d900c01010314844d034106a2156980c00d60302d1a00d414803050b02586050740040c2d03c40b0854495402c10204a04860340086841400380248041c00c1d200b854203203800c415040 = true := by decide +kernel

theorem cover : BRFrame.Cov 928776978 928956834 := by
  have h0 := BRFrame.cov_init 928776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 928776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 928776978 ≤ n) (h2 : n < 928956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
