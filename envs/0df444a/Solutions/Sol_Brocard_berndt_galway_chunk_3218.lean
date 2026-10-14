-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3218
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:00:52.62272+00:00
-- url     : https://prove2.me/submissions/3fa317a5-323c-4ac8-a2bd-845cf22ad060

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 578597122 ≤ n < 578776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 578598372 1250 578597122 578597147
    0x10b1c0e031801230310080a0f11010c0b01150e090c07061d0708031206190909020a0306181a0f0403050c0a0b0c03070f09081e030403060203011e0e091507 68
    0x5000029801c11000d030485e0021078075120309004e03040010441803c00550b4034081d070344c0001d00d40b150007403e40c4c0d03200e483c0900140d40340c1070080100b0321400140c0040d0307490740a845071804021800c1c0070000020302c802d0f0307201000c40c05072003030380240101d0300040d83c11592519080100484c0d10242e441403810b060b54010340c0d402d8a40140f41010620450201c010840f50054001c907602d0358442e0800c000100007213a840840d8040000c00821040d10543c10045019000404604040d03540303840d03c40c01d403111035500030818440e45c101c00e81004882e114a0101e0320074014030008525207007105518015000e00084c00f403248c08902004124400c1000c1c921141d4003800c2d0034550704100c200a00190020f4500b480841c94046ea81d07154141700f85202700888005c1401400146001130402c0c03000f8100e1500c16019000400c404004100c0b24001180200803090380860b00030411144107900b0342003071300900c0c911103d440038001103100000b18089100780072103240c05651038018054038010072412 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 578599622 1250 578598372 578598407
    0x1302090a0b2d0f030106030e03070516060909450b01060f0804150f020906160317090a030e0609030d020c030d0e091602010b0603010b1c0e031801 64
    0x14440001107001621040c103060800001e1a06902c2006214114020900b103500588000d2004100492091300310b030b0000054002600c6c641001c0e03840352810488100045130342d140396288100111540511010300410301000c040205280025500303603205456a4401c4204c2d22403140c0c10002c4030100c2c0e40c0c0d450101c01200510f2244401c0c605074004000c00d00c00c006c00700381c800d0141c8036090700820a040c4900d6200c800b8840b0a842c00301c9400040c84038030003407a140c0e03038207004041c8581c43e24001400c96012480701442c03c4c60366460001d2061405042d24a0300082020900013010800205c02d41b00c503901d0304004030000145004a2018018400c0d020351500c150340c04032020300e4021620b5400300409800380c80d080f001d07a0000f82c8482d0700100070184c0240020b030000704191000051b0004444d00c0f4800070a2100d072a40c0020707440d400a0700607040c00080020584034400503400185100412403205201490500c81210740b24003560310600e5041a4000b03601d1110703880b800101c4c03030501c03406 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 578600872 1250 578599622 578599627
    0x4060915050f030f060f040e031603020c10120b04020c030d11090409080d0e030a020a02010e0d0c0611010e0105131e080f0702190305030f28111504021302090a0b 71
    0x94451000903400d44060340603806c9203449a44a0800d0301824100c550400011490034507040141b480f0058080e406400314001c05440340c1d0190303210150f540710b108040c4e481030f00305440800c41e40d08803031a01110600c2640704014074003502d02c0c080309846008042c12800541d01d031082486005911650428a49c030520b002e9000701006a002d02505401600b03002c02c0014401c040c0050340d03070b841040786020259100d05107104c0150b100714040540d00300c2c05050980380b004107603100c11000c4096081f40c4040b2f04100080394420000b40701d528203920545000b808542030019170895266400e84002d0600078010100c19110194080f440010551001e080e640c2c0715041e116500c0c041d00502c00491044d684203001200110006400c001660b800002861421b001304a03800855404a041000c04400301c45040900c1d500c0e05e417401d020444c250b01d4407040206e070302152505001210740103e028220000c01e201c0036031281004c2c2a4003001600340141d844000e1000111030040a621803404003800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 578602122 1250 578600872 578600881
    0x40503031204050105060f0f040905100c09330e0d0203151008030f030a2a0c0201033b030c070b040923041506030f05150c04060915050f03 61
    0x45401d128401c6000d94000c211540702c4c0e408111490409811442d8054516610300e0b80d5880e0592180090900c00c1c0212110903850250303620586021041c06000b185107101c0400100e010b540701d4103900c120911400740451100060707030040e00c440403008004c00081010145461300d881201c5042181c000b0101c400485a0b4030003e50b062008980318150040002c10005050000105440d4800340b00d90200742540d94441041f001040440000c0858202d418078030134207400804544003244445a4803806510b01600014054a1008108c00903098003004004c41d23480d07110b80380881000500e15008a2440602c60300d0746540550599490f0345e0040c40c00014a1f03005100050044481d41c00c024490410204002d0b42070340c02d43e640c4a07030180b070410000b50003e2074a0130074100b040420500011032544030384409442003111001121154002d4a4008800c80100000d030340c4140142d4210340b030b00e42840001803403668640309101c201206d10b40c40d01c40041c0210240d98584100c00da4450f00c9182 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 578603372 1250 578602122 578602147
    0x6040c05030a080a1b050102070c0f0609031113140c03040b1303021e030c07180e0102250206041502061005040605104e05070804081809090723010c14010204050303 72
    0x42e6030bc109400c0c9403004400085070b40c0a150003504480c1c01550360b2100841c01001d10542c214440c0c1080015960749080c568074a140140e002e014880480d01c01d5180d00d020b141010441d4030140611450070b41c100d005000180d40068101800ca010725190010040c0d119001b510b1809082d12016080c02507480109c3d9621150100402002980f00700784006150500028200d201d04062480c1e003180c08400c01411421a05d10145104e2000d4030b19032500343d03180710488523242004450401a007100040c8104030f0000790041c4c02618044504100d42c42c682000518180b00f442074403c10b101e410080c1459158204c030016903490010303240c401000100b41100d1000300800102c20480c00b0520380c90040340340c00c5108252081d409030301c030201662115121060366400c4480e01c044001842460050591507510a00e0b002d43c15400c0100349441c02d0580906841700303482c41048004524081c1901641c0c0d010300c14150544e00700503d616104100c107103080c068070854200e6a0540700c0040c56608460 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 578604622 1250 578603372 578603393
    0xf08030703201918090603031d0f03060a0b06190c020a1d070e03011e1e020903030a0807112e1806050606130806040c05030a080a1b05010207 62
    0x3000031400c003680e1602007031074941a0043c003080c0701034007505505400c41e80380903410701c8120301e401d556444142e50303072008440107071440f41e00102e0010b641d0500d442041980090700c134a5003075040f01d500c0e60003442100402e41e00c40700201040130840c1c40301d48000054992400700c40101c03104403001c10010100c080058200e5402690481c010860a000000d00079840c1c80788220038a034440d00090151510078085850400d01c0781d045905540e00c1250f002c110f00002550001041100c001180c040c0c08010710519400c100c40950580d5070040000403080c2d1343c044100c6d82c3d13040190405080783d480d0003108654800920f8950306a0348114816807901448903040d0792413201070000c240544c103401c0702d451400c0e2042800c135a51020446995000021607580040307500c4000507000358141480c0031721500c8003050907401124140c01140a10050010314090107025250540041a42003025521243d80e4072408000004001c550220440070315a50a500c0059980120003075448541c00d041500028 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 578605872 1250 578604622 578604641
    0x18030b0f1b0c0c0d141f1a0d0803040c121103190308180102250c050402070c0905070302270a050118140d0210050c01050705190302070f08030703 64
    0x6034401e8401c841000307001129180a01ca4001c0d0074000300310420300c0080b041111088442a07195114030780b40a1080001c0104500744c00c4041c4240707003d101925084820140c1b5101c031104c072511101040792140700d85440d0442c1d0008046540383e5650601c00a0790150b034008071041a00c054030b09050005103000b440303135560100e0540d2200c01e20700500c444400100007004000c42c500000040341e4020305084060038103034030b0001510300412003c0e040c60502d014880081510981e4140101344401c06003004040d00c170030b8504500c1c1007095112040780e103209100706880c075911807001440c002d110740c0540300175411980408234140001d00b40741503440c008031815409001501d600040343d61040700c4c80d030082040e5110940c000c5051034160344040060203d12500091811707564001621030410f41c0004e852182d485540baa0701d000e071201d007520806070440040050600407003082d00584110110114402d060040ea29030142c5044560340e00c410344080c040b000080208425160940c0044450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 578607122 1250 578605872 578605891
    0x19060602060106090f06080f0702160b0d0509071a07030e032d010c080a020703140f07050601090908090108040203010b09180706020a0c0306150e04050c04110901020a0318030b0f 78
    0x40d1903e8035400905e450461052200013440e03c40418016201140c030300d504160184107890a0440740d00001d804036a282c0d0001000e401d0014611429045070720600f5004124100549102c038600702614100f210034100001d420b07103000402800301400b4a0020b0009800541600c68110300d4a4410300d001f80f986240845810069090042201c8180b141500c00b000c162100c44060721480e0844000750401c0c5421414800c5100301034042e07108001c05418040c40c6000a00e45c0d904040c038145042c0700041e44031502c2141401d5051001940400580d60b81c51400c3c80c11954a07540c600001c1c0c0901680000343d50415078070820b00500c5120800100000303421401101c42082d40d484007283e549180d07100281580c14000028800106a50402200b000c5c59940c0c450350380c0d840b2445103042040c10340d0f003111694041c400710026801c4c14011400316407001e40c4118289401311002039240c4bc2240c00090410811106c50341011001c010710901450b0030180041a07484e2405210403081030654407541e4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 578608372 1250 578607122 578607137
    0x1216110d020105150904030f18030804030f03090f03050607030c200705030d0c03050d0e01090b0f040501050f012711181315180f0207050109110a06021519060602060106 74
    0x45400c5c0b05039006c0c055540b681d2040309038020103c0c00c40b0500060003c030040f030480b13410004045204440608059400b03240d848030100410315018142c0d00c0c0c2580510010075440d401040442d501251056204480e82000304022182e140102d604907081751003204585d04004c1c06811700e2400148100680d4001e07030031511000e284290030380300400f0300240200003c100704080603031031031707150400440e03580311200101d030b03902c0703599500481503c00310344150b0020070701001c000a014013409495080621039046001550401900c0d800180c1c02d0700740b40400102044140c144a50994400030f040081c1c04107254413041d01c003c514003550b0880010f42d218903100f04100e500e0065074891980c0d480901001a1321091902c2c3c842c0056100c400c10564803a80d072022222001d41f07540c00208030145c407540000504181c146084051801d6020f0600d0062619410500c01130b03400082240a070042c80c44200440c1d610380302901504421820403007881402e00d0b0001840580002e541d60589040d6201c400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 578609622 1250 578608372 578608411
    0xa03021809041110020303090703030e042705061308030708061503010b070302010b060c0c0d0602040506070605010e091b040b0d020303130e160504091d010606110f031216110d020105 80
    0xd03540e01003074034406000d409c00003040000a00403860103451440152000c41c0c0b0f6040303a052521106410710118440a61403080e40b410400144072255004041d620458040c0c0903d441e01c2e5040d01004102da02406030ba1008603003580d03214440203664904ca1603c440e502d41c0c44861005898120b62411070140d820602d2583c054a01f05040c0c4100c90b100600902801d040f902c108100402e0340c21041e20700039820040801d61740c94103030040141500841c0007290755450949074034040706c002011114590054500b8060009200341e0506030084222001b01d800c0e032580780003404e0759080070030082d03052100084844404980d078a458013150205000440140d45591900f440400c800a0032000144200020720000790a54044a120400c011440148400d140d450170301f1118580c00500106102c3d0b58200f07507407001003090008404a42e4099414581c2100300c1d0541a2806030400042c0c041c4840d2403000240700d03070142c0480034032100403941c0122103810060700a0500307484c0025010400f29885 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 578610872 1250 578609622 578609627
    0xf0726151c0b0a0510090203090d0f2102030705040b0310030203071a1e0c0f0c0a090e0c1c020616051507020d030f060911210c0a03021809041110 64
    0x220341964220740642c885656407580e0400600005042c031008034852680800c414009101452140032040003e0500346481d6501510400c42e443c01c06081051340e802c929860303a80030340720002010b040303c409a20798554074820741d07490040d1b030045050050040204000700d1900d8001c031007100d00a42c241d82d4216241c40180a004a580303800d245c5103034041108070a0220418918006468480b01c510305040b0880700780350514039410800d10450b400129400e4051914060060040c80808030810081e8111210700f600c2c2c0815004841c46800003420100700c4a0704624100c040c00d90007449241d40741e101c0d4241c0c08040c0318104055802d4450000e0f1001c400e8407030002d96010f450160010096040d04882c118041c1403034680c18000c060312024001440c20f081d006100015001c6006035850310b80040c00003980c0d180c03510b644d00c181300020742031044000c00e4600b290324100c1d1a14015940305920740f810241b6a07894030115030843c50110801c003d00000d901c11003034000c821038240381d2900101004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 578612122 1250 578610872 578610919
    0x1712011806150804050a02090c0309010b0a08070905090a060504080a020106080c0603061c06020c010b0f0d1e060605060406120f0e1f09120807170f072615 68
    0x101c54a10b11018468007035140902100382d4003a20640840e1615210b50780840c0078802c080c4d52a004046004c400d1010490080c022200e480000382d402030502840d0a01190f0340d0b40051140d41d011613510380218040b00d01c14050030041982004060110b1b042510b49205c5a40c0a0040c44006518215001c2051071000c10303083d805a00042c411415074580c41e0400c11013038084102c80c071080450f410390000150060003d465030319515000082d40000c100c046c4942d4070f40201000e84151a0982040300140304143d0741841170601c1c1c0101ca050f075a0615048008018030f41100358400c1c40890001061503021004800c3c40c005881c00344000e9071000c1303959007501d010000030ba810b0341000c0e0150030503041c4901c00c030400b4411043c0c00314011005403104810050382c030703000d18000781c1c9010400081c117810040700303812081c03021499004c5103031400300c2044144c0c0151480c42048000700641450154182105881410300031070701726035052141d0003541c1c11150354492401503028850a0750101043c056 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 578613372 1250 578612122 578612129
    0x70c0c05040e031c1112090f010908090a0506040803190207170c041d070302011b2114070c090207080c01050a06060806030a0c0b0c010222030c1a161712011806 70
    0xd107141815000d4070303041c02146c40145041e00302c0c8500c40c24004219024010083c0c5240200071550742c4079240d0088c02440505c60f0412405180c4c00c000411101b20008100c4130f02c0340b40c0400c0481c9107070300079100320b0034900300e03a00a20380418003903400f100080f0702007450658410200e6007004010500750050004801108042201e0741107004100099401142d400304d0058990382e000c1900c16445e510380d04000e0499640d40030402c0a1840302d14540e0f04010102c401c000701148013400c081c41c03561802c03000c2d0024010712800030740104c4c000d001c00c00e510041da480c0043c600b009010500d0400e03803084c0108000d00c10a000900c11001080107424040b44048141e508040395220709403c1480300d0881c0c0d80300300710b040c0040d0f41c204000c55000b510903680034411720308010b00c2030350540b86007404c860300e1400380c0201004140210415170012000012180c698490000d581066503290810103c1f803000720603070807502100000d039440300c00da05000150603188424141e4010300c0c9814210700847c0c29600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 578614622 1250 578613372 578613401
    0x314011d010e0108030910020709020706021c020708190e150309010f06080c1e0307080601030b070f0e090a060902040b0a110309012f030a08150405060108070c0c05040e031c 76
    0x80541d42d1400d11a41c7c1103041c14590041700d900c641d403644807004a90110070141c801c0b66000c1000421a14800203c280109c1e804906608098064640380d0141c421421242c0c12003959103811484980078805da8807407040014036000841b0f040040d0502654421500c000807035180c100403541968640c4162425288210020159050b20340c0510036485d5030004107498441c010006001c403540c1c00c101c4007001d0106540901641e5140d46040030031500090300e1903007404004d10b8013185072a4400d40401c00d000040f01d1640068a81c815a8401000c01b034225400e0180001004103028945600030100616aa900c540318044030403102c9803240228040180080c050100c1100803071850000c80e01c1070388041190750700c2800c90301d02c3d080c5540c0c0a03028440c00f19600e201004010b500203240c1300e064240544040c019850000700007041c0d000c1c020f11150900000c10304a45c01d1250100c030502c06444050010880300440003085a81d03034001c4200019182c0203111002d2803010a401080b0b041d05009 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 578615872 1250 578614622 578614627
    0x3111e04050c1b0d120e010e0d030b19030807110613080c1302040e01090e070e0106090306050105030f1c02101104050901150c030302070f081c0b040207020f0f010314011d010e010803 80
    0x4440d40805000c46c001700140035902c40010070303c41c00b0140490140403001c0d4900046440000c000d02c013104041c810004140d07518064100301003541e96080701c511a61015545800140000018030b03507000b06641c0c4c815214020001140386000010303500d443c0141111200c840340070300300300310059100e07a0040d10200b08214004020b075908075080b002210f0301d454151540d940d00c6038a03001803040c099001000081d4185420400d002680c414240546015006403020b4144454045e6903101040c0941c2110f2103068206211140b00b40b1800b01c1c085014681804000045007030b1b00d403690424003c09100301000d500000c1c0485280343c0c03240707601c2c40a03116044040c07001d0724298006e40141005541043d040b011410018943c600140400d006541c0400345250801e40c00408075591910258000c910410101000d07035148910b441c1c102030102c460b50310000704080100d0140c8050103921100260324000800c4000e55040024120400b0300d90055840e03a0300e0f0101d220309a402c1c442c1c41d8464208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 578617122 1250 578615872 578615897
    0x30b0f072c09041e03030b150405031f0e01090f0614100e04030203070b1303020f06190e10090308070f03110901030207061b050405031603111e04050c1b0d 68
    0x8049090f038414066503900340050901022440c072050440c82c2100081d0342c50100042c2440e21144d50741403801401c014a082c40c1c00c1c0000b00c2da407094007441e1003541174400100101d6101a0f0b400610300b140d0b64000038000701c44c0300c2c5094141000081c400300c80140c100840c01201007507141c0b21503c00e80b9107200301e4140d180b030041e0f8088401005003064085010800511000c507105140c01c0d40112444050680c0101c40340c1002800c2161b07c81031001560800d5040c0036070001450075003a5044050000010070305a4002e41c0b614000c040100c85840ca13080c5900d1006058022412a105900e03c0d2a50040034400e04411801c03074030790401103440c3e00010f101c0010554800e60203030240911581c40090240c0e52000e201c02d10009014a000000e030700000d060203507040c24046016a41503500303100400342e003141c3c0c8200542d0342114595000c0d040b40b40c44005580b00c020309000305410050000c00490a1044212a29500004a807481622240d603040b9000d81300203240000b50303a19581d00c1480816 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 578618372 1250 578617122 578617129
    0x18050303040b0c09093112180e0906190504030c170912030d0e120313080f070c031109060f06030622020301090c1b02011206030b0f072c 60
    0x8003800100c0c81d45018000301500380c40c5c2c41d00303d50003544040c0ea40464250b02c00c00b405035684c89048034070901400541000002170510001c0088008103091561035425988141d207603094880d40f08400481002042c000350510100d0180e00a2143c8088a01a15110302502040c1ca0741600d005000031030030440b58000c104940408402c44103221400b500d03003c03d0000007482c50700c010300e0300c050070342000507260390350042485002051504035001e04181c02d17901d10400410f00000b000a10844c41d00108042006441c0d02100d030a040c1a0034419255074541c14401c00c1600140400c81d421420b80b41034030309614104c12100d119050090000184924442c2070003a0f80d000074200c00e4009404115000c07007903005403500401540203000042c0c40e91b1411250340242c1d00d10b106030406105000c440d51100d01d5000300d41442d11a02800d06c0c0d140860b0084800c1c0003454140d0014101010380303810311281021401e01640140c036942d440801c0c0e08a0080c0000381c84018481152500081d0303401c6004a05 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 578619622 1250 578618372 578618393
    0x30414090a0b0d050f1603171b03040b0403030f05120402150d11070b100602060403180e130308060a0b0409050612030c0a1406131b0f060e03011805030304 68
    0x149580808030b040116800882c00d40100344608449a40101d401440c0c4442c042000d1601d210001a030102e00700d2454540e156081d0421400d900007880000b40100145110803c2e41400b05001003240e0350313659240c00064154202c0e010440004640c82001c040017403040307080e18100d02c5114015086c0d038403280c0c204541d00e40b00c455154040e030700c140150305090780c4a104500752413424126a81d80c4412502c1d01b000305c80d00c01410700700200842c03c01406074a50000340d99034025418184840c440b4071014040803040540d034810210489a1803c00c640d0280c0302c0030b580e454034840e8465160503182c41c8208031001c0e0490203021185072090004229100c240c2c2c110a030030040c083c040003c500070f007107041420340e803051a1140031640034545000401290b0b50301801000305080c080e00480c1030501c0c0d0700140404a51000e00125050a00d10001061101c4404003c15420002100300360b41e030380c0007426100c40e1141891181d4030303204401c01100303c2d0301100003565a001d8065803642d07840d950703041d5150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 578620872 1250 578619622 578619631
    0x50a0f0b0c0a1b090b191a1909050306152809060605040e011409070f2d0f0c0c030f1b092711011d040f050a05010803041409 55
    0x2d1082e0307100070012618000b0070078041140c0029a507401810328080307405682c079000340c15000e402c00b00014103141841d184120309032464904d100ca02e909410b018003d890041d00800c6d001e804205003503150701904440004c2c1224400c0d02610700710f070389401403061810100c0c2595070b00106201e550040401107440502c0380442c1051050840705c2d222018002110000e401c900d000c910300150034006107400781d03421401010f0b00e181e841e104d0b0140b140841d10740c00002e0001014884900365044d02c1d24020740c10780340d048010501850348105400002000920641503410105d4480e284009482e84121020560640c0044d210300c0030628665590b90440895182602e4112401150860050440719000300810f5132840202d0b07000420803494011405510810b40c070080d003224005c0c009401401084070004090030405c0005000d44400b05031004400c51640c0c0c418a040403220f9502004d40c015030007039401d503c080219070b80301c40c00e0594901c03681c096000b5000c00c0d0750050040d071802242c1607621 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 578622122 1250 578620872 578620897
    0x4150810060e04060f080106240504060c06090819030615090e1b0a0507050c0f011b060e010f09110d03021c1209030507021008130209040602070525050a0f0b 69
    0x701559170010007440d00743e5070062003982c0d44400c0c1c10007002c40c407078400158100609010101d02c6148103405001d52040380302d5001400038000340c920901c1425032014042035003100c40d0545d6291072103101014044401c0c142404203241c6a000f04110107001d0200185a00603100c4200017420714020860000c0d00030155071000c03000e40b01c0e800301c03042994081c003401c45040e00d0740e03a00c80030b183c42c01504101c07101e014940516420f01701c40d001c0d41c0c0e02c0b003d0300e00071a220180960b2400c00e141411000b5050030300c03807a1a150b0a00d03500f000360140b10390110140900562a90300420266070030004903a01c60000980103900211080031480d00c41d081d00c000441560421402c103e544c4030a0b1810740d2051001a17021600111b42c2805504044446c1d4000c42c089142482c20b03440c10011210030154040c80281c001c81580000801f00049981112240c2d60484100e800281c4c0c101c0891500c00604c0180041e00c46a850b00000c0e6401c0c281c10302c00695012081c6c3c440c44034140440b980030341c9c2210404600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 578623372 1250 578622122 578622131
    0x824030a0b0406150f06080108031810030908031f121a070216090507020c0d081e09090a0209121b0d15050f060406060504080312060d0506090304150810060e04 70
    0x1d41e1210340b8501008082402178100060724040f0090f02c8003c05a200c200e05400c200f1030440800c2c040c6040f46d50720a011140041100600302d0114004c050502d4028034110307000040c0200b100e0101c1500c010f07801000b10041ca40d40d1a0409060464500301000705890400c9541c0080c034007a5814443c1c0c070140c903104036680c8030b920800f511361422090b444584020340d41c0c820303c240b140d030621183c1c800d03140603078041e803520b8000e03507420709140700740c0140e0020307508404005065101c0c42000c071a0701c0b00c8002d10481443c244404400020340c08207603420321422194902d510a10320102d02c020b030b45034026020358820387e0418242b000f034541800b011100c60421902c801c4004005107c0d00c0d02900c030f140c0303412040740b4003074041c4400c40e62903410840030300c6414001040508000002c88085502903003030345800ea190400412032880354040c00414600660341084010318001002c4e0046407601003000300f100308509020f0742c2c2890180c83d440c103000301e000410f06c042ca00030885a994910081c10024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 578624622 1250 578623372 578623391
    0x120c050c100519090b0a0e011401090c030e0303011e050315011509030210020c03070803040f140a050d060c0f0e130b06250c05010302190f0c0807030824030a0b0406 72
    0x8049444c41401141d01040090070b0042c075000358420511980410300080225a80107849858041014400c0462091300d1345400c0045520940291418507411000c4940303950f1103424144008440003004404a011201c0000321840c2c0000c0360b0103104010100b110b196400c04820404641d01c01c0e01101c20710071004800401a182c00040f1121a0800e5024005014102040504196481c1c1c0a00001d80c030034001807000c4144005000c0895010419244005441201240f1207071210360203d940611030000b50428420341d0b070072441c0c4212256441940d02c90100801359900041c5020780c1d034004000030301d210489a203560001d030710f607075000386120305007002030224889004aa95021050160b440e0080c01003150590034035001e003000742419820054956406004040c10315100801c201c40c142040420354050355074080a10340040c480d65441c035050902801528042d08c103290f0030207080101c10b1003500150034080c0ca103a0010080c04003103e07c1c2d12009800b05000d003095440954404500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 578625872 1250 578624622 578624671
    0xa140705090117040b04110306070e060d09021203030901060f14010507060f02030a0c1706062d03040b0910060f050618040f0606020d0c0b0f0a1506120c050c1005 71
    0x144200c1c80703404958041c0c80c0c01d00c2c1108080800d80c07d21070290348800107102045420150b4803014120565855880d6065409500003402b02040085c4d0003000d03e5000440e121008002184250540c400a001842d0f40b8100d850560030b00b0b100d000d0305a42c040311008080d40c454802411401c2c00380002086280030240603200320b03481a1403400321955a4800040e401e6081309042003803500b600076500c021701d40300b40403c0052081141c0d00200c0341d00107880001285544299064641c0c40c1c611458a0345014031340000c2100c825a1080c00b10b2041c51542e21100e0030034000c41098070703000b002c0900308918220500c042900506100ca100402e121614075158a491103803680300d0906410210b1814542440a802c0036032a800d1704c4100182a514007000c00c18241d802d6420101c402c003c41841e43c0c03440300b42c4000b0800000998103070001c4800004009510a1100380e40c01501c40040240400211065800d48144002054541c001070590361201901d98440b6602521802c0368060380500007845 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 578627122 1250 578625872 578625917
    0x90b160f1101020c1213060918110c0f0a06051f060e03010e03120106171308030c2701020c030102071e0503041a030f0a020f120a23040b0a1407050901 66
    0x80030581800700b01000c201211041810042c01c440c103006c8403580c00c2c040300003102e0981c1d90040c0120b80e00cad24407414603440d06200712621000d244082e6440c041500740b16540b5504034890585803d030400e40450083c0c0d0307822101d541440f08102d20b840c4032510b0284251541c02c0148140c40e81950b940c107564040c0b41041c0004d12400f50542c180726030350f40c140480508210200d14021450b0b88407101041685145400100034403904040710903107d035036058140d81c3c1446201c2803030012401e441d9200711071140011059500d403200360292051078042605040c02c03401000c0c40038141c1c40d210410b01d03d884d54440c01c5040c9060040e0141c0385001d0302c1e5442810020345003d003031580a10004204008490010380c0c090b000a00f5003130562030100740550742d0308075000d2000d0420720414008081100d552441c1d00190540320a44060300b40c1d040c040010303031590401120243d803081103440c001001144076200e56a14152001a110041e4407521400ca806030482c0e2429410f1044281d2480c0201114040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 578628372 1250 578627122 578627143
    0x8070c0501110c0708120c0307080906040513020307090602010b061602060c060108150604020909060405190c110f0102071e031101020d060305100e0304290a03090b160f1101020c 78
    0x20a0840d10300540f20380740c0311b81c0d0704039400801014001011001d40c04412030f0807058000f0380c0282c0301c80141e00050308500c03c55000350713030100313030100c110302054810307000356101782e5481d1100c0c801c681c1d448605a0a8070a0040059071251040010200c00d40c854290701d00203071300180501e82050010341025103014420b03003040807150302a1010140301102c3c005c1e860303403248080d0307000d5040107540c9000c28446500070706202d00c202d480e0400036640040500d8103511003401d00350140200c005410b4041d0000c9400c0310102454000d440e819000130f01e0500031030b41a50b81c0000103620076541c2c25440303664001190b408900300021082c2e2200115000d0001e0040a03030300a0000442038030303500e045454901c5034580d03040070f0b506020740310940309400300a68003268183c00c261380083d040035001002c240980031484c400d081c0041402509503626503c0354548512405800e681078450a07266250070810100c610300103a03410f401303c1000307032240554004402c660070026091410301c803102420700e041c411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 578629622 1250 578628372 578628397
    0x3050301172515020715050c0f150106022104090207020d050a030206060f190e0702030408010905031e1e130305060412030609151202190b0414040c08070c050111 71
    0x182406590070f180b074904082d07001e500007012903520704000040802107021100301841400315075000e07442030038040b40d40d1901c2200160340d43d141c1c0082e40cac155440c00a005e8400144105200d032540d070b180d8200002462810241380b2030a051030721482c034001c0c0d4071141003280c20400c4548844005082007141301c0c5c0283c403907006000740d443d10100307020321031440600c01031042e6040041c00703508200011100003914220030040409a440c244260314612840c0e000342e240c3c0d03103004481d40610101001034a01321040c0c032050010b101205289a070390303004070801008804480c2041100100000c0c0042056030f2000d45250b6078166070392552810b2010441d41500c964030300780c10103e0300b030b54144215400b4000c4114100b1411381e540b4010382c0142c0391030080c51000310740e49800340d082d50380ea4065103085801440c0121300f0b26407544410401a0410b2103000c0254204184040461829006040b49466241d4540c01241c0d076003142200d90100c0354005484d41d55980210345028201c14009004501805 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 578630872 1250 578629622 578629693
    0x20102120a0b01171e060303091008060301151a13090c020606010305060907090303052a070f0b0f09010302090a09021641030c0106030c030614040305030117 69
    0x190b0026040c0800c914031014100e10420801c0030b642142d50f200071040c1124200c0c2d98540d030b60400071910711b05c1303210396a40d401594140c4001c9202d610100241c860401500280240c8001c8001344030380003080d010f95480801501e00c230b580114280f4024084001602c614910100d543d12500f004480d901c01c07c041c0140c0003142042a5540c00d402000e0308084140c814181c02d140c0000020500038050200a04000c4002840102902e901c01c0040c284840281e0192085801c4411103030341e4002441040d2104890540001d59800c3c1d240039214041d46002c042c40c82c140a0301d00460095000f001c4c5554041c07501007002c0b03a200d02c60b1014190700c3c02590034076440700c03100d800c1881c0170540144484804010320350380f44c031b1081200c0015041c988107a0300010580000340006a081d07001d80480c1010b190318080303001052040c07803811481101e00a00040010340440c01ea15a5114070441d40500891410401080a51141c0d4449e0341c4032034400040e101c0070f81c1d100042c0503500f500c041c410581401e52 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 578632122 1250 578630872 578630891
    0x6120f030f0903020a120501020909010806040209070f1b030309050f010507030e060c090d020a0e340e152502040b060715090311030a0c060c05040503070306020703020102120a 77
    0x34408075042403402c1001c2c0d15490343e03000400151240c000c02071181c034504900300801409405840d0300c00402040c01031a582c54110065903281c048070141d03c65001c0c0c001041030580030300801c0d80092201e0f51000100d10008090240b61364441800300d04050f03840c4545404544e0030301412184001410004c505030920260040030380c0c0038400a002c9030740041007130081d41544401250704215041d92044c11032905400007881410056100c01080c4c00110204108010441e100c041411220661400107090080c0410f81303001c0c49200354800702d030351000e0441c494601056120400803402c07240e1440c04404d40c018801008030411030101d40501c1d41400011403070180101280c41030140c5405080249035152030362904910f4490310031042e503038055002070502c160f02e45000a83c044003202d42d80d031007107240149161624002603400b03900e000d81c03c080681c401c1049030103c8100600401055003151034010096100c03140c1102590750030054041d41c15151070645d4030070001004e001401142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 578633372 1250 578632122 578632127
    0x20415060f0306180f06120302060402100f170907080102040605041d042301060e0103031706120d050f0405120d02060a0b0105030115020106080f0c01090b090d0b0a06120f03 76
    0xc0c00a4070394203150400d5010321007a41039040a2452001000011424410032005c100050840d81c110259045c072124003482495000a05c03c1d000364401c0d207001c4901d1118403012209010259800d10014608000310f2904c82828005c2c6600041100c00351200113030350300c0301c80f82280e200b94000404244049410050641d09000094180800d07030816085403606540d06005100300442d0700b020f4101c508110705114a01b54007260191000708024003181d6124140548203e1352016812080c05032000000c842d4102030b5080520b45407500020201120010020303200c40e00a00d1030b0840b07404040c0310006441d5500300c4604000100c04016128081003014000d043c0000109480407070381c100f40c94031042c4d981c841c0887c0d044481044241a4648100400300e01510342c9510a07400f62259050051200d080480c1710280c404003601c0d1051250b558213001000343c082c100b10790398070030040844500413400d0030174846d6004104034400134115848254088000d405580180c8041e500c0291003000c158 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 578634622 1250 578633372 578633387
    0x20f070503011b050310030b0a0b041b050a0e0105070c0308090a090b030a0201030b0f0a03061b11150405120a020a060e1609020f0702060705013201120201090302041506 74
    0x2401c1c0c000303102c1d65081c0302d484400c00454442001c1004000000241c580c3c00070340030a0080c1d42d000400b0081402c006608002912082078058031a40c60b10306209601d0450b1100780380120400e485160410120340e009a50440011920b03a0500000f041010006003118150398044c2d442601040d403202001d4050012001c0b0a8002180a03171508003813810640e40010100c440360b90910f40418554004002300f404030540e901000d030082c0078140044100f21040d000800441400410ba282528500008862481d1f12040c801d06a0700040c140318107022050b0300060707006000d60101c030903114502d1907002d07095210340c11950040c3c00c03170008002008003074051080c110000030000c00c3c80012548503841d400c29035114a4503a1680080c1005818040030152140c41d0b4000b0000ca89a480760300b1300c0c9010f0040c00c910502806420804c0901603074202c01c20000840c2042000030180e0f00301080c03007140040e1200c00764103000240c40c0000060741d41c6d001d001c40c903445481d82d20f08480e103080b201034180b1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 578635872 1250 578634622 578634629
    0x50f060102280f12020c01020c040908030a150b0c0f070e0c03060d17070809093121050d0605060f071e2f01030203040b060904060f0c020f07 62
    0x42d0040510300381c0caa00c1507003003916201c40d02c8850000e01e0800c3d2070980c3c8078a80e1420010660350200d504500d0168000c18000c212900a800f038403001c1d00c004003000100c0d0b0b41c0c9039009100350b0f0280701081c0c0361505c0307074041103a2091a00d4207044d419200e140c03030a095006201c0e501d0142d1321500324001008030502543c001440441c028030755070306205c001903642d400000c00441c042d88107003503003030188000c40c0d210315680c01d40f048400e540d07805075081909003030b4000540207014072811404110141c40d95103540f0003050704910711001f44203c2136900c07643c02c4240203060381c25005407544181140c110724500c0b40d00d80d000752110b82d910420490f00500b9200c4c2075018a1184800344200051031840008131908940d2180401c054074800300254400e0b0f880203034000c2d060300e000701090164454545550f640f15845254009a0302650b1401102a4031040310014a08500c3d00085a014101864810b420501c920004a0743c280303810f540008032100300c050400168010f06800c82010414041c00c0c026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 578637122 1250 578635872 578635877
    0x30d0b0306010b0301090c300e19021207180605120d0203030c1e0d06080f0f03041703090405091f09020a060c03140703020c2d1c05030d050f0601 64
    0x20398503203003c00c80103000500c15400096181d852007c8420300c074043c5c000c500362180700e0000c961150f4940c1e90042210390a602c46180d4a4101c940440c41790000e09580f910809070300014507110282d080c880c925151541c2c590491085440203e1805c2c40020f1140c12001d01c040005280341c030340400c00c50303418268001c1e03003031541181c111395425960100480398404800d051081d50f64011a00c1e410380300c1034500041402c0e000c04500e0f402e04217840d8002c81c00b103880707010884021243c0350310060382702ca0181000e038602d680108010070040741c400303c01289800e20b4030162810440788401242c00d035082200e800d032464000030000300c81307010690003424031051500410486101a039008c40c2c240c1c2268090403051140301c0b00c407103007018030800321134100c0b02e210485161101444e1401035603401d0760030507140c81025220600354000700840c804103101c0600407074030319109615200340804003040198074880755140d204050080f80c0b04100500061749054400221480c0148401c401481c019168604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 578638372 1250 578637122 578637133
    0xf01120c211a091e090312071404090c030219030603030809121222030c050c1f12110a020303160e0d03080a0f0c0e0306010902030c0a030f0f0e030d0b03 67
    0x1001c0080c2c01034208011015281541c554030744071007009490707404e1160010300702c403480200b05142c000400540821039024152680030703165194190740b508010014180300250500040044c1903464003c00c0804096040040c42d20041d041c24079049010f00c40c4c2c01d00030907140c002c00c008140d4402c0240358050804006003203a40b8007607a01000d180f01e21100c50031069070328ad01240610428540c80801c54180d200f07100202929450040d2440c0584d00c03081e01c1e20301405407030f0403407030400c1900740e225800180c61101099030708130810b54900c1100d902c8200b680d03964000d400101c1171300e54010660000760b600210b8803450b2003c01030044e10344203140a000c011986110110a031210310100b8000c07039060518210700c1c1d0b00c40348840001c0281c2c0c041c68040c1030614822203110380d080b00045c20710400c20b5007642d80d160b882d006001c060303200903940d1240d005130070041d00e0030441c401e622103c285d4460820200e840b095000340d034410742e681000008008e800003d926840c5c1c11851003000802d0100350701921 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 578639622 1250 578638372 578638391
    0x2090409060923030a0518041b170a0c14130803030106021b0604060203120403020109020904120e03060f06100203070c0306050709080a0f03050a05070501060b03011401030b0904020f01120c21 84
    0x9015004004911607940c0b10382031f1080160350340d90044010600d000c034908002203000e02000300200000e06c10905101402c0d000b00ea4902c03924099070790182c00d19154400d00f800700e84540180d42c2c2c013000440a0051541001041054041c00154000c0c05160f0051072014070307074148000058000e0442c14841c0e91304110070040c0c150084155036500443e00d400000356074440c01e00341d000d00711041300254882c13504000c21040090981c8100380c0300c3e002d81d80748184ca080200c2031558485041e41ca40070041401c00003d145490210060342031580644192810030109075940c40492111340c20031504141c4540801484543c0601ca99008041250042025003015116411544041c00014080140000d04c00800d54011300c22501110b0703001d4000c0054aa0742c0b50764200641083c007881c0070144192a980c0125803080c0a40d2400702b034000c0881c0030580710355080281c000c00103c4028140440c03088a510306207018418180000c1c0c1070b4a9190000811000040c010820359041c002d960b4584000705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 578640872 1250 578639622 578639627
    0x706050c0114040f080717070305282a051507140316030b060f0a09080d0c15020d0e190b1003050303131401090503040e011502060a02090409060923030a 67
    0x740d00c4a5044021590f41e0329050400008401900a02d80d1007047d0001d0f10700100340d4000001c0c508c000150b0480461080040030b5a0701c3c0e1f8601046031701c00541c0500d0b540c0c1410701c089000d1048801c40c00c49110103017143d07540da203041c034550694402102c01307800104402d8903007000c41e8042011040303d1840c9075140404618018007500c1e4642400c259460400c418a0740710361003191040007000c4019911000c0e417520051040c50b084c0610f503050b008070f1441044442c000e400b08240f55901c9281c000d00742c443e45030140029004801c1005103d034507884d42d01350300c51041c003411560304c5010406a8580c1d2041c00d0065030784a016020964070700d4104402c002260020003681d82082017212088505452800c2c4400c100456910410341546803203408020420000700520803201c40e009020700d03176a0788507003045800c10748442c20005030300081c00207000d0002a9000b80750301c8a0041000a00000d583c40d072000300e8408070012501c07a00c25165461041d52011030218020350990000c40c038151801200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 578642122 1250 578640872 578640893
    0x240a0c0309030c0605100b070605040629010c020a170a0605060612040f0318082a010503040803041707030309022e1817073b0405030c0706050c011404 66
    0xd840e082c3d0781d9002c030312131948504604000785481d05280b074448c20345040003001450207580c100d50b03507850702180d034151003103010040940f1241c100d16140c510502d54011758405512000807a8004000c8002085510706e102c00f10300c07422a54001410504402d151a000b2100d0103042e540c07040005100c03010400003c0303540c1581c0584c1c01020380f00702c1c42d030b1032505403502e501c148040c40500c03150a1021403940000206041100c000041c2d5030991b00a04110159080d01e001044c3e0000e2010400980132520420046406c244120b050100c04201003800d00e80e42d80002c03408800003a00c400380b40c0158508407064029582060286020004e4048030340145050501d12034406c3c8031010440785114242003900718020030080121700d5450490742002d85d01d600007405038035001d085841d00d40f00b000c280c40c44498200c0f13582d2041c1c4564596a09541c5c400100003c0c03044a051000700a100c803888818400727500208090744502e074442c036582e1040c030709581003126420084510781c1d00b040045480c0f01e08 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 578643372 1250 578642122 578642147
    0xc0c05070f180e0309040e0d02010c1e0f1806051e1c0f0902031e15010e010b0310030614010e18120d0b09040803011e0e18240a0c030903 60
    0xb03000468840e5100a03030300390301030509415405840c040300c020599402007058039446007154000c100d82c0c00080c405131441602141c1d201020400c0c03400c0f0f14040d6000b00003040141009041038805c4034100351481d40005003035040000050004180060071182c0c11040020102c0000e0000b428580111100f00d0160144090a60120340301e11030101e08004035401146026000b03030545160f8006400050b0400d49020031070001c41c42a2001010110302e00014581030ba8070341e00700c07800103900c2c12490103501d030405030464503500803501e1b0001c0014054415200d041c0a4005490082c1d85400d03c1041640c200400a4499102071200b03030441c000c01040c00d150f21070084240720703111345a414401c8003e20180d14901d410600c1b510500040c09a164003030b42c100c1d699001c0c0103c06c00119000010320305401d1040800d00c0d043e04000c034214417820a444002000b5010480c0c10507450301690503481001120341c240c5506920f400c1c05600d9410b03010341c544001c0036080a00c0307840c440d0741d00188084860340 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 578644622 1250 578643372 578643419
    0x70b15030a0609110a031b05030303060904120504120b06030d02010e030403031808060112151401030809150f0904060f030c1815140321090103021b010c0c05070f 71
    0x281c0c40702003210f4120041342030003003c2e10000d0744584910b080e402c10f0400300d0428203288a1014002aa0300d000400ca9105020140c5a203025440703641ea00300c0101d2628140c1d409100041c4404a66518030980610540e400f0341d12503d00b6051130024103042c5810000407408690404814803c1c40744000100c4040304e6051a281031791864511100001d1200b40e0017544150141e179000141c01d000103001041c03694007418194000c184603421801c00c0310001050070002c2d480c0309004002042c030b440701030302e104880a03001d59007100c042c0c1418800c560010f000350a1500d008140185241001d00c17514025201a810001005086855189114000340325502030401400340008080030076400409960709840440c41030343d6114290f16000b080d900d503030315000c0c1c0304024259009020321884c10207903a115228540c5080c0c8840f0045000e0f502c4203104000c1184000c100125140003403040c030401640c660744019841c0050703d0551308100090340511011070188809010214002e0a10348c15900c851 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 578645872 1250 578644622 578644631
    0x131a072d050904090602040806010f0e0405070501030e01020921100608073c05040f0203071706030708060108060f0c0a0914040b0303121f230f090c070b15030a06 71
    0x3200003d0241c0030700c0e00001c10b42c5001150010700e05000040e424161004031301003001668841c0c8120b0040070040b20040c04aa1080d4800c22940d4020360041c0c0d111603004002500e0800c85101145a41e20300c0c1c04409411115104200380941c1c0a005451041016000034008545802002540c4814900566401d49904981e00300c001030320b000164824030300f540d540c800600c0308000184000340c040c40307064004c40c00c005882d540e081852003102c0c454012616005070800c2c040041c07001c0c2c40001003189816100750301c3c0108140c00200030031802007036140020030061501341d1841c0300092000d8502d140082c010b200419689802001031419103010440c04141e5104200c006406046030a074400d4060200080010815104d00381852040d080008903105181c007101c0e040007803281d40e21030011040c02d000b490604003080242040c90048008013104541c001c10f90016411540644903540d112100150003c20003c0026134940c0c441160201302c249560b610020945464204200900b559540c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 578647122 1250 578645872 578645887
    0xf010b090f13051006050405010506040602100903180e0108010f0605150c15090a1b05030c130f02030108160f0b0a182706141503131a072d05 62
    0x1807140340c5804a42003c1155902c0a09216401c000d00180c09003038007403420500003241a003020803c8a0450303041d83e00800c2c070032036407000c020002c10081108500300200002c645101c1041f1194200207813201d014114000e51405000710f08445108800c0200075040140810a40e5194411401c0040c6084103050f50380e65411131039810600454600380c0880280000d0010344400001c506180c548142d84030320420400d40c240501c6003545205499055124803900f441f681441c040c24105800754410104451203410341001c180e070003d0f00200781c00e5210740c100480c1112190340e10002403043c000840d08203420070404100354481c0840f04814060501440035440501d1402d400041064450b2006860b00301109100702d64081555501502d042000c0410300b100c0c1c004103e014000c005007003041140c095080d000103508001c2030364442c0b80c60416181e0101b0803108124040c040280c220740d4441c0707000400130300351700e84141d001001d989000f00c07a50460300030751880380c1c6c0d04402401d2076a00c5211 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 578648372 1250 578647122 578647141
    0x330040804030321020a0801151106130303020d091a0f0c0909060f0415090e010e0c01030903120603111c030818190f050708030f040501050306060d1803020f010b090f 73
    0xd0801c135000364510000303a1700005c681c4011040e0603116250300121240070244001c90f0b1070a0a0041071003580c01c42004148070f06448400e4400c100d1283c18003500f0701c00d1607190241110110135041d525500640400003402c44490b0507580d1103a40320400d00d0042c200655210001d0041d030341d12901031810b1101056459560b0f50003481b1103440100203001000c00b41070039501c252214824200c006040c8841c0c402c2050040c041c1d6440d099480c0d00401040400e030b801180a055003c8043c0c051040c50810780a6103000c40c0681d0010350701520308610820510000d10040364104400400c4004510904000090b440381075540c20503902d030340400d40c078804441010f0406c410302d812a4a0301d41c5450a840c104100d007078085003103901070300a841d040c550b510340071900c9104044007038003241d104201c18441503010700c4c007550b00032030050541414141c1d0740d03c01c10102c2c0d14464061113150700c0e40142c441016410041a8134200350003000780080b5105e0340200f000c03208003034505a00c460800000544000d0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 578649622 1250 578648372 578648417
    0x111504020105040b0705070923060609010c0b070201020a0212040e2a0c0f07050a03020303030103080c0106090f140c090a0b0f0c1e070503030304020109030b1803300408040303 77
    0x5a0003107940d949174598540703075583d82030601c0740c4003c0d5418114014449c00412944800c0c00b010346400225aa48800030080194420208581842510680c40001c198120901e5200f040a500010f90382e038800000039190034810070780200903040400060102014103c60607400c482c20520703c103411050f500214003240300022408880c0d00011501000c002e40001e0070b240e06802c0c05040c3c80c01eaa854a06020160341c803800069010b81c000c00c01000010004801450724a82c02800041c0f205d80701c0c15044103450708000141c046944610780c405400e961040d00030380040d0100141460404650081460b4001134480e9507600d40c80030031007c40d070011010803100b01c0300d80c1001350380841d40c0c1c4900c464125040c048041446200f044000300381030400004031f90199030140c44403035000345107607105585a800240042c0c118000c542c212452040200041c0c0404100c0417040f0118400d0407200072045400c80035811710b1031100c00188804545403078122401da83d01031407c42c5254400c440102c2030300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 578650872 1250 578649622 578649629
    0x2010603140a0309050306040b070c0606030b010b0909150108180709060e09060f0108030f0702011b031d040204030f020f0613081e0615100c0204050103050706030b0111150402010504 80
    0x804003a111090030310004607404064500c00d44584c0d526a4544050556880d421100100300500040c0072030666801018040314003449a00c0c0824001e483e541c55044150302070b03101c1002c01c540800c2c040500d00c0c1c50b02e0b14984c4210041600200d6440745e8000814400c009020030340440e0200c1c04107400d4110034800030024003484442840a00d654100d0780503018411074140005000b03890100710003070105000b0504968000000307500b80b603a0307201d480038180d0100008a0500085018520240c1c2d68617169800c4140691203c010001d4540c003968801c0a01250042c03089204004c140000b851071240310210b950140d45135994401c0070b2010940328402c801a40c440c2184c00c03c0700069941001071009450407010051300030380b4041e2036400d43d607007005849003e80c2c25050407000c00340d030800c0804080028100d1500102c220807a4020504541c2c085c0c00545050300041001e1003c2500360017040400403003843d00c66044000d00080c1a110010303201c00b000c0310342000000c42c042d6071182084d503015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 578652122 1250 578650872 578650883
    0xb010506030c0409023403050a1d090a0905011d060c0703030b09040f02040b180a09060615091406030c04090e031c0c0210020f07021212041e0b1c0c02010603 69
    0xe8249410f580e1007213480300c02c00e40078440110040c412103c07800c01e04030700d807041c0e15484581c10603509d548140c03040024404418101c148034084c1e01c845556521000c4d01552500030000b0b54625641025400d4880742c0409070010102c000b80070b10900ca000402e40da1012507611900e8507500d5600d400c50242c5610324040da8468003207018401882803491440103801d2003260100090003000050200041081d0241c13600d112800d000150406826040b212031940b1400d000180303e5192040501100d20104500c4001180f00800780043c0490b481d03c640303140d404940050442c42c01d00740c1c1c1c0c402482079001d00c00c60b158442118220f500b00070010385503491958100d14072a103420312182c40c001d182060001005121b00f400c02c041040080c802c42e518040340d4141c240c42d01c6950b03000c0c0300d4040401d614086080c0b103107210051003400140c0180000d0700001ca4070100701c3c2c1c41034542c0002110030790060208204204018450080590b10444034821a01004290305c3c0300d140301a4014803075580060030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 578653372 1250 578652122 578652127
    0x10080a0e01090311060109060b0d1d012408010501080604020d0302240f06040c0207140625052503060903050903100b01183f03020601090c08040b010506030c040902 72
    0x101038212425444e41a8110f0864400341e98495041040d11807600c60101000001c02841000149a4002100b070141841419a00c00190641d807421581d81c160585000307902141c890044078042e00c860b00081541c14001d01182d4106624942c031070b580900300078400d402c150341610405009008000d0a8a1401103a00c0d9502110000e10003000d4101c0342c00000152004c005006450140311741c4100903100e41c000d215031814160700041802c0c82a0103e584504144808001c07000c41d003074050314412250003411480c8c0401d1400510f811209190903405004060503100e0700006090400122070b000440440c1d15030007414166207600c038003140d0ba078060041c008985401c410070b40192500d0102070740c41c07240d060a014511040c1410900401d801c0c0c52074450101c811128804c00c809d40700c04d80150304980b518580ca0303459607182c03c1400071005a0490b000401c003c805a11402c02005131504002d0010311300390365280750b0481c050289a100741d1020000c05d40100100080e5400340038011070865 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 578654622 1250 578653372 578653391
    0xc0f06060b090109090903080f0a180503070507080604030c120504030f065117070503010c080105090609071404031b05060a080114010315030303020a11070510080a0e01 74
    0x84082d80808182d9000c01c0a11a001550b03450902c1170400880d0199240c03440ca484202c160300d0b0f00400038080c3ca0b04251603002c00c800c5411b082140060b0399100740003e41d5560310310300c0c0407410030740b1b40c1e4480b0226800220401002c20380001d4803800700c96100d02c1d84000d60b4400d110036a2140180c0d0009401c05103800c40343c0d4100410366101601e08210507922000e04260320490307407407090843c001860311a0101c6601714980340f5024120300d540c0102050a2112900d911106100d03d45406016511b039118040801031410207102e07803002802d45280038901c0358108804100000c00161042e0300521640002603509480740540d02900000e103641683d555131382e82400e41c61945101e090314284904650300081c2481e1220413180d401c001619090030903803074850b0300303a80040402c8649042c181c8480100200d140381c40c0b10b200141d80700ea1401603c0c2c910501004120b02c0104280031000d40c0204420300c0b50366140030409407040e081345043d002a86d90f0030110b40162100400009403507081c200201d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 578655872 1250 578654622 578654639
    0x10315060b160b06121015050d030512010807150509040f060803070c051009030f0f06021c0b0a050619050912060105100305040f080f07051501050f0604150c0f0606 72
    0x101040e034018038045074152241030400c14100800100d800c05903011903046c5024052903000305045031944a0b148a80c16613a1002c40d9801101e488120b00040000a0840407580d81d20341107805004110014815107090226440c040700001c1c1d007013014410042985404d03560742e5080491041000d24050001a0342e40c140d03266607030041c0808a0700c162001c00003041604209803404002d20b8140d5488403c00d2950711001d0060a00311000c0e103220044680860109a140c001000340f03039030540c004031050524404043c12240b512401e41c0c4940e004260400441e560441030300c5032548107503d490618a1b000b00c06503081d2060b805010f810800040301c48142003c046100c504035001074549407040800e0000413030072075070100e8000b40070700b01841d5604040340d60a0b02411700f210600840c28a080015100e01d0310b042c0503411034482070168480180490f0900c0003101140181c00e03510281041e09000740701c04080850203116042001d000a00024020454030a201c0150410410802642c030b42c3d101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 578657122 1250 578655872 578655907
    0x180f0d020106061412100314061014030d0f0e03161d0135030c0d11070b0415031e05100506070b040210090812070b0906070206010315060b 61
    0x41805035290000004045016440c2c010541600d0740c4500e282162800340c0c8a41540c0140000140e018604408000281d00700c1c0c42e0391a403a03800340204424902a00c004001c0036807a000724010340d05103480005541c800240304018080142802003507a0580d02c012660a014094215814401c1d4003010280d00a80d030a0442034491460072051036003d00c1004d0711300030b9002e1144102111044100000304c400c2d002c84904101c4072107529203060074040b0b10540c0f940d007240d03603003260640103026030003005174014203181e0400381c1c494050300f81e42c2c1c9000d0902005015602c107200c4d407125810042d01e20b8500c241d02c400700e924640c0510010f0442a00a410300400c811180b00c400c44210120204003481d00c10191501c0b5a030280c40c811f03031540c8541c00d20491203846e105500c240114000c010a041005200d1a41c06402c656141e6468021506250381000c102501d6014aa0808418808080c1d80450300c1410f494005407020391130100411a5001801030360321840300300b0b0020680c400700720100d03000c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 578658372 1250 578657122 578657143
    0x1f030602040e060103062d030204050103061e0e030a0305090f24060103090c0918020907032003090712050703080f0406031d07060c060b0d050109032304030803180f 72
    0x81c80c06549038001941224064001d42c00548911528150341c0e1503035550801c101c020042c7d160894641e80c0e400324050f01d0302038000b2290151190402c0c0c00c1500c807203445052181c005a8244484900789a109031a80320307595001c001c05480f000050342c0e21004100d0390808203500c00850309402c81180e0004801002c002410700798418800214800e98444e02468400300c0e04039510040d80c0c0d24103942180204912500b105a0a44010310800582d0f11030850510030312031624042400c08060003031403240c0b0907800d07215000110510620442d504009141c2061329200fa2032481110131a040051070809a540000d054000000311700c01300342c0740c0e400a04201c50a648041c40a80d040384d03450704000d441036081c00c6469000807010000c403841900708180c0680207220014042941c0c01c00310702410001c1d070f016900350317464103080001c140e0700c2241c0034040c0c0a075a90030880b00042e050b0030b06152003688001341900001002003004004003c018509240c0103c04a03100d0803c0a82415140d1880d0705 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 578659622 1250 578658372 578658389
    0xd170d0b121c0905090c0901020109020a0303030b1810120f051014090a030e090601050d0204080106060e030f0a02060304060b1f02100b1f05040b12010504150303171f03060204 77
    0x125542c40103409041e0150560b0b02c000e1654045968201103d051600103440c018110342d00e0b801d50320b0151300c5804805016501942d00842e500903142d0030710100c41900741c2c901071110326200c1000215142110410181d40a40405084200441c240007042e40d0000c40080e1460141082120004009c2d80c00340d0301c0d030002180d145480c2d9842d0502c003515061007040250206543c01032201c0d8611b800c010302640848141803aa090080400d082e50490f0450b030080022695a18011300c039050708030a0100c000301c001c80c010103894601d10701c00340d22441001c0c0002d0043d123011020404218043d0031034014180d0140c03c0317038551103c01c1824004100c00e5174203034001d03000f82d0301c0101114030103000705000c02d5070146c41008a1f40605404e9244980000c000f001044004e00c0049006c8526000a002d440088140001a03504003800c004c1280c184807906007070707c0c40d103500800002e50403000000c1d0b4141103501c41a01c9580c2d0810001c3c04145c151140051140c0f0350501004110440d0701030000e840071503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 578660872 1250 578659622 578659663
    0xf16170a02010f022104140106181b0f03020703120c0c061a1c06060e090a031106071d0a0b0c0a060f0924110f090f0d170d0b12 56
    0x1203003000c100d1068000ea00440640200345d4100280c416810503000b42c4078214041c418100140310500b1111960807007508c4200d90b030031000300400c860003003a0007803500d0514500d80c40c01c1c11002500c10390821b2a50024150045201c0701814041d54410411494202d401c2c4a4407045540c02000c0903c40340c0c003219a1481c0900079090844e00403807501d6904006030003041d0300e0034080a9981e2004080f02c085030020345810012a0306c45000340d04601483e086030040001300d1651602414107100140843d032550300040030011000e901c2a44400821a00d40c21084042c8080300171500c00c1007140c00000443d000054003800707810703000484a425a00402c403c00c20314100c43c4060098a00c00ca80c00b070b007220352409210a4401303e0785401030b0045110342c000160034044204016458100d115845c00000b4089280301150a01e000340d20b0014804586a03031640300607659411248100300d00b0200b02d0100800c05891947d1558000c4201e0000100210350034034a41410507075554100c0800ca2800106 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 578662122 1250 578660872 578660891
    0x1051804050706110a020d0b0103050d1107050f042004090b0d050618030409140103120f08040809040f0f0902190602150601270806010602120f16170a0201 68
    0x6401886009a0340308014068142c0303491811201400f001c0010720702c50045025590050707940c840d20344601441051501055850360a0041c101401700c1071460501000c1e20b030080c518600450301d501505c50440e943e168803040b072008140141110740148a03030300e400c48032030540500040c01270030407220709042c1400301d149144240300d018121000300804030303072002010030000f0345447e414040001d065011a03040070390303d409030f00c20740e02c0340c1611001100b580c900500922003d1900c02d6580f250301d040c22542030444450082680f07100410192428401080c001420354030350700722a01c0340d03180070818010741d1070303490300d10b4018680d00300101d00c50803403a002505141a41540d40c1d0407521503030003a0402c000d081903003483e0180001c000a040080f07201c04000703152210650244000040792034940c1e1035003131507619483c018040e0088415903014050302100800c40200711001c6100c01004107846418010350020b03886c0103610014440ba11400c45400d5495030a4090000c07181564000e1005544 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 578663372 1250 578662122 578662159
    0x1031505030d180b090a03060f180602120703060e04030c02011e08010f08062a160308061219150f0203131b051c260403111005030117010219080105 65
    0x300805175803c0010750300c041011072501e5100b40b0324410404804141c49840c0c1d5200d418101800300e040711070729404140420300142e110400ca03441691802c0402c035440c2001e04204008030010401020000c04d804130f101164411300c078015544002c00d074603080c0c1c011132800141c1820381c02d018154500044920010310101b002940034083e41580c0c0d03001d80072260500000c90300d14120102c24008d12010864003a00c0031051184041250080e034503c50507007088410003c0d0b08416109001480d408802d440c0a2020000015481c00e80d00080c01003000480d5012100a031142c181880a62480842004482d11804007114120380c4205450b8404031641a03400c0c00b5400345008090b08002d5141128030216204144800347d2401807100b00c0c80300c0f216507a140701220380b1803078030707403a5440106041041045607541403a00e00000c440b5050b400c3c0100c280108a030005205141c41d462000703000d624030400a504440b1840d20b00b41d203200700c4441d098405041d0003002e109040c02000b48045039000c002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 578664622 1250 578663372 578663377
    0xf05150913031e171314010b010e04091103060c0714030f04050103021c09111e030606010c0201110f160501030207020f04020a02031b0609120f030601031505030d180b 73
    0x2989070700e40301d010781007807a20068044080e0103182c0c1402024000040c009540000441c4607104241c96000c5c24021482c141c51b0590500c5c0407125103a040515040380c503038010403042c120100642e0f00103002809810013071a200462190b058050103440103020150aa0720000c000e00c90140b442a0300c52000030904c0341e903910a40020505010303091005010030f42c0300e9002011440c440762404541d01800b150a03000312f588d10801229504103070b44e044030660030101241c1d00040005008001010050303804039890f1700000b010903041107055452002103a000d81d0580e00340e0f0711860202d800c065140006566207072014800c0c45820201c4080020320f66102c1c3c001c0b117406a13800782c030b15030201e00b90009100194204500c96015400180128075903200386205445920a10800900d414105400440c0c00d050100c0344100c880101004460080c03244030b02241c0d0010002e19000030101c00da416010405110707600202d6040c010321050401e516842006102c60507080e10413040704980e60002c2c0d0343c241c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 578665872 1250 578664622 578664661
    0x103120e0a030f080318010e0615010212070b04080403050a05010c170115031a0409080d1b27090921020c0307030605130c080601231c02040f051509 65
    0x2d258042003c0000c1d02c40300030b140c12940900031500c02450300110703a82922140b55400925600c92410044021100700c4105210642070004c1c02d44120b09115448652184500c0540360f0300c00080420f042128500481d0000d5400c00190f5480c00c0e054581107018040e14008180007136801203d41c0c2d030641e12410a075040318036040c503400c48040c81000581c05449201d4280551018454240c0c8443d11a4068000024803400240d82e80b2810000f0003400c890795064000e1060f8000200001c0b201e80100034291004007440e200244000301c19200603031604a0740208110604284040c0108030340d001940880e40c0b01003800e101180c010000481c1e440d1349030002d0640c99880703040e041022912a62102e500061100b2064006414945807944010400d50020105502907001040f0f00c49008010454107030144948024130255080024145400b800c1500c21241c1780340030340e01c02c542d0303194080d15855000910a00c810700d024560044e44040340d46045000e14030034400101d001440c01d800d000c90 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 578667122 1250 578665872 578665883
    0xa12140c010f031d06072114010b0d0e07031505070e06031906030203031207021c0f050c0c0a090501050a060206090d11031605010f06081902150f030103120e0a03 71
    0x180e0051001c00c801901e800043e49134054600c00c001c2d800c40350144190b0744228800c3e2580ca20018448146089406420851a00440c50058981c105100381d80c5542e0456078860030307242d1030f40029480b401c024010000300032114840c000000040101c200c441e0308446221b1070f0200845d42e240c41081d503240d00c0910003943c4c001c10400008100c01005000b115002032503542c009692500e0b0b501003855030f403080c03032040801d0001200b000070040d81000310303541d84100c0c0d070b008880b05451010043d02998040780e42405202c0e0100d41115080010444407015560040001000da5601e04c4141c00803c800c0c00f0340c42c0112044140421032500001d0031f240100065001800c00c1c858050084962080700030340c08140380001c002141c1604c4507803040b8561a40161b000281040c1c244855000b1507400d070744050b01035041070110004544114140d00841e64056540302404e03244255144a140300759a00b18100b088040000700c00d03c110007000544154858a492a1000d00d0030f0400a04982501c8020034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 578668372 1250 578667122 578667137
    0x30601020705150903030c03190f0903200d030c020102010615080a02070809030f01050115090b1903020c010606080f0105060f0d090305071e03090506030702070b0c0c0a12140c01 78
    0x981001503e62034521140f1400381d00b850b500e000002e0955015100074070342a4404103c007141c90200c0c0c9110b8210580c64205034902c01034008016294010034480a0006a0403289504007104c0c0c803070321000c0091000304000080d00c00d0345000f4003940e4940109900541c6080804135150b500c0098802c2c050025481325220369946810886c00395012040469204c2e07806d000040c859101005802d43c0400e503000045000d6040c000004219500c016282007005031880040100864030401c032292400300c40203d400d45802400d081e006480b03803901010b069803800200140b06c1e5401500c0a00a81e118042040981d0381c9004000942c00360038004000207801704403400e5030703a40550010805c00e1003070922034100150360700c5500010108030f42c40c10702d600150002004160344807031a04043c0400f1100c442c21800d00301802580d9413514040c01020101c00034910032101002c0041c480201c2c401014000c07221f45924250645104e400c008030b40f04801d50660101004000ca80005034800c103951303889 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 578669622 1250 578668372 578668379
    0x307171504021803010507110f060118020315030f1b091510020a20031507200a0212070515042421020a111c0e0307081b04110306010207 60
    0x4002d511003056026540005080348001341c07020300605210f40e500340c071108140c2e810200790900300505000201d150360000b1005200000b0500381e2818040f92444005817a942d1341141905156007541101e40e143c0320f0081d485607803400005d840e81103179020341014442c0c43c80040500004810664103003000c1211003a8801c3c250420b508002104d0400d441260703075a4901b43c88a003ca50301400c00c0070241404074914002a0a081061619143c0c00807400c0d42e0500e44000c2c01010440076402c0502801d50b01943e202c1d40e0602007211a005a0700148580e0b22149508041036503071095114090195856595881c000b940c1c810944e011070305501c60100903c0c0301c0c0424070f114484510030724014840d603403450502c4c800034003140100e07006900d400107986410010000e4800820604250016800100a4626020141090407a031003050402e4500743d54130800190038a560ba0700020b186100d004125624411515505138800c40252400c10103210303042003c182d90711049581e540507030710025040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 578670872 1250 578669622 578669629
    0x90709020a0512090d091d0103060b0a05060f030a05060102070e04080d090f24061a03071b030c0213020309031b030409021c0f0203010f0306020a1b050303071715 71
    0x500e07080c5128500356241c907142c0c00f040c64402c1002d40e50000c00e503025146850403250000f42c450003800700c28254041e0313190454403c3c0c80b81801400000e0080d900c510b00c0c4c8043c1c0e15649900070141ca001048240c45400107800c412054204680c0114003a040c030300814815400410010103071001401200e105994613241c40400ba803003d00c550010f42d5a0b6440d820202d10100c141c0441e0b83d00c80d16420580501840d19020204804900e041245143c8141008103c04410a89400c403e44040301c588136500d070501660704021107003da46007030600180000070154408480020f641c821164030017030441e10020034040340001c540031402c2d40c0c1304000301d015980d512494030b80e2240703654080364941030b212089441683c000314001504038070f81e0010340c888902c4134042c4d40040751100c3c00460840d0f1600c604200054401d10010317020036800a651100359109564922001c4d040c80c810b003150301c802d450420780c0c0354021500b410010722524082e101d801c1195004600072104008450441e41242003003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 578672122 1250 578670872 578670877
    0xe04080d0c18060c12050405030312100302040914010e0a020a0e04051f021206030a02010504050d0f08030112020f01230d02040801110a021606120b03010905010f1b020609070902 78
    0x100018449041080c000d00b14a0b044400d0252089645119581015140c2070000000c07140034041440b606000601c816140042a1102c0e1820440199807a03200c0c2d4000d81010714441e000650081d0510b260f5205018003c00c9038002c20321120000c104882d03038200091345503120100001d602088602003049289003188401c0d80082c018400d44030031215001564000d00031065845810603008650212a10004010300b41c1c0094194050180e1000941c0002c005128034014207109110350302302c1109122000400101141e07001d014166296116a007034003c1c0d0304109022440b031002e0700c0c003400b01c0394031603c01c01151034800e0700324a90441e030030800c00d03036640c2201b00000c0c0e005a09000000f4404824010116450552003545075110f42c08000242040d4006e449900b40700c24900c010000d6561002c40c0085040c0c04940c005645c60041000a0241c006064080c02944c02c044520b8511111a4029045800360240d0311420740c0c0d15044c02c1e038807400d080303480b080203400800d010070a11400303400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 578673372 1250 578672122 578672141
    0x609090506040e0604050601050411131a07080c030403020f042c0321011d0403171e0f0a0e010e03030a020918070e150408030a11011104140a0e04080d 66
    0x80883c501d0006486075180c414102c40641302c642c001c80040005040501c04c54050940442c1143d18000001000d90300c0c050851003004811500400300d0340c0c031525050282c5e20020f903c04440b550310414851131540e660460300059204041d5455801e0807440e1600c105031400300100d01d1b0035001d0340008241c401c0310841102c408451300041040302540e500480c40c0714409070401102c0c801d00d50504600350300380180525006025118542804040b1380c10213003801981000002d41d003519a10031054400c0c111038200c40034040100d400a110390702c50000c0082d80304400c0f02404004000005469600744c810845012500d9013040010802d50007042c3c0040103107a601809001440407940054126034100700d81c1100050000e21109030306d85010560106400b140c41455420542041061030716803080e00c4100051003010138541d80e08070703000e420120000c480016015180d41e40ea01c07031509182c05031b40505101e01241c80c40802c80d075040c158118015a00004060b080c54240320346000142030015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 578674622 1250 578673372 578673379
    0x40203030417010204150c081e070c0602010c0e1c0209060f0907021b030610170a060e010e0f010c022119110c0f1f1103040308220609090506 62
    0x2020a684080741a80501200b01400050703840e880c2003030200c000007a03080f80604001d01c16426401145070381c410b070364407015000740101d210034210300107042c2842400401840161868000a0301a80640c00400c08900c1350720746c0c407101c580500401920b000c0144030501111074045101d405402c004d03003001e51180001d800f80c802050f0b40c800160401d10201c2e416001640045840d100110440000e100d800c601034008040c50705128805080d400380601a10404001200c2d003c410200c0070807480c00c0560700a4410003002d0444064540030707000c1d91180040354031a2490592011405104d50b00f03131a0546d40c00f8000d6442075641d200e141075004503910f4901c10051001ca40c942c8214084a0030900440d115070002000b01c1383e0842c1442c0029803801c0c840c907400c42000e40340f42c0f50302c015240f1460440c3d000c1d1007140f4030030100b45d42c07a1032032141c00007031340c400403402008118580c001046004146403d540d14950a41c00d9008006000e000300000a010b090382040f000216410032034101c036004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 578675872 1250 578674622 578674627
    0x9030201120b130e0303060307170309090601020a06090b0907050a0e0601030203071e020610140f011206090912140c0703060b040905010504030309020a33020c18102103030504020303 80
    0xc10399102600e01d161100c604c5a0000800d100643c941006600c000702000507a400013001c8140c1c4603512070007041800e0707010b440600c000aa4580c400d01c111320078130f030303000800300054070a90074040c10300c2500300e40106140c4141c2102086d90f00c0c1c0150424110307164902620503035904d11004502942002d888171051018010100e00c4c42e060001500444840310781c0100814a0802058942100194000c10554401c20081241c58440c1c000f142c45a003070a0811816000e06020504000c0c042c0da40084811454281081c081140c013100d6000280c0040d51907050b4000e1400c1e0a03600f03441088000c016942c0540710410000307030180c0194085580007071000030580250b480e924292241201c04400090b500c4d400340342117281c9096000d000e001d05010701c145600800d00002003950b071501c18000710b10404418256140c0c0f00300900030005202a020041d80100d801c51040160301c00c1e541298000c1ea42031010884c1c90643e00040d0b29842c076078004503101c0442d84c409400500340a002681c160104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 578677122 1250 578675872 578675899
    0xb091305070b120702011107080d09030e0a030b0a0e060106021506060f0301180f02030606071b09060803030406053d0f060504050114030c0403080f120708061009030201120b 76
    0x142d800741c0710900c4400d205003550b1412040082c21a14001441c0310407120600c41600401d204400b50b40041c01002000034001c2186d0030161094420031101640c002c10f451404820403080c02c104a000302c980c1c80c4180883c00b80b940b0340b9602c07500240608001640884074115882030140109070304400003400711494450001400002980241c10a8540c0c043c80316403481034010b20310030111442101c0000718103600b444000520f80d88034901c005049201e040844042c1400c5510601d00140300003031040080c2c036a99800d040c0c507031304100c1d82668424903281c0003078803120340a0300349034440c54106440324069201045400c030510200c02c15000a07817480c1c201064001954501c034011304102d85a81d5111480c0c940010704904030301c1031241c4252428414408204103107819501030720350284501d5103a00328a0a11a1640160150034900e00d60b018188241c0c1034102254501601c000d0700c0d035189a04000c201505d100c070084c40b00a0000705041c1c00000e440b081540440ca441000400700b003080742d007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 578678372 1250 578677122 578677139
    0x6030d050715050f0115171906050307080a020a08070321020a050708060a0c0518040c0c0623010605160209100302030a06150e01081c030908070f03080a0b09130507 72
    0xf04a0740c03400c41200b80f00051094180c0c504a5881c001014a86140004010040c0840d20700c80900130030b01c1a05032540180d02081d403a0001b1028100140c1100c18595550302c41075515811044283e0160100c001e020601071400b24018040c0c0f6040740e01e04450f04403034110001c409805003034070004c41c041c0000020002e00709101d0f40c001040c04100030052414003a482c2c0045031401c95203c01405002c22100e075542c2195071502d80205400c07100010300c003c40d41825240c81c3e1520a00814a5180c980f03103424141941755081c0000010b1060307103a0f6a0380760001a0751520032075000e80c41d03d401c00044100145804501254001045800040e11696a601183ca001f40380142110520b0301c0784d100d0345000764581000c41c010051aa0191402c2d450700b50080d8640340c05840c8640504c0b43e1176a1080c01ca40a504004203a42d840013440b03507500f01605200300ca144002d00101c002908207404690105000c0c000c241c020540102103038000d0b00e42088480000e0b0309030108803128080c05070000380760030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 578679622 1250 578678372 578678381
    0x303072f0d1112010207023d03020703090504050c030417090409052401030206070f0320100e03030c090d0c12051c09030f061d10091a06030d050715 65
    0x380326100d0403103241c100804101418124080f050381503841802501c000d0b0f603480b6420004d02004504030401c009078500410888101c505041031001c2e8940703104940030b03601d680100b114500170360ba10101961210204070a40d0416140c98144090070300103e00400c0c0c4208000c4e41c1c00c1500480b0901d4142ca0340081019200328200c01e40e8150030000c1c00c02101c40c920390b410001000040c5014000d903046d580044c0160150800140c444d075200f4450004040c0a1003008803d00d20201d1001c000f0b20b4480312080c0d6039800711207070154481c1403140b174108070034001066900522100040a041210302c00034059089000c80050740d85030718003800054213256940c40f881d041409040607000a500362400c007d508030b031000b4404200068500100046008400020807165004401246103140c54480351001c660741001080e4034007a09181080680080e0b1086003290f11540c941c6004511080044039140c008a0f815074041d04640031301007030148142d004012440c85400c010b458441003103000801c0383c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 578680872 1250 578679622 578679649
    0x10f060801170f1605130c02061303020c030610030201030c0f090b07030e0a030c030212031207030c0e1207141507080703090f031109010839040516030b0303072f 71
    0x980303004401d00071806c1103c0c0b51010710b100c181080c4400c101960000703550b243c00500310310340302801002550406109002030100000c0c0101222400d0900d030002c00a00e90542c40124086890303c421214082e000f0365032854114640d07110591054540501c00c1070796805800d044081090500c4400c80607603503c1800e80203103000740c409451180c25071040c0201c4541b246030700c008d150f0007848600a84130074404001d90200c41c070b2801162509004100ba02d0320000101c0c4654030182500404c10082d50020314582100d41c1d250380100c89203803078001d005c13152142d0009000c04040030420000031030b60410007030103020710031718010044c035a81c0d145200c1e807420345400071900840d00103250105840c0c6488a24050714119014200151a6407020050071a1030818a004080702c0302c4000d00c25500050740011101014000b0301091074007641840304103084c808201d0110b8941081c0314600c3c10000300b81d4010342e501803040a9803000321000c1910b19005d42800fa415422509102206d80d1107103200202071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 578682122 1250 578680872 578680903
    0x5120f0d1404050f030c070506160206030405061504060302090a0504050328093227160809030a12111c0c03020c0c01080a11031806010f060801170f 65
    0x14107243c41d1260409500e220040040d900038008008451000304003242207880c11a1030035503800c400c615100c1e10120791030010f94040004420403050180114816201d40d901d10b03011000e05180000f004221800d0707000c0a5004035003403000a0a0b07852a80c03003160441d00900849080107031140c44800e0300105e0f4040118039507041e500340d0261a030408440c2e030140568102521140b0200b140c00300b0005942c40c21a00b04607011464604c040d1200c1c16841002d11110591611004d8800044000c13540113440e0b00c001c02d4540740003c100076120350803135805014084061881d042114004541710840c642c1840364a03580c80c0c45500c29005100300078280754084500404403141c01c0c14a01e07084130501036004060500410992031046008240100101000d0800458540740e40344400010106804403113030002001080c07040200420768030a403d91210000c03102c0580c0c0701c10701000c9001c443d00c00c072004980e001c0010700090300d49400784c2c2801114107080343c40d085800c40c0c13414544400784480401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 578683372 1250 578682122 578682161
    0x120618050a24021905091f0507050f030702030c2806030501060e0d0c1505042c01061b020f03151501091a031f0b04240c05120f0d 57
    0x499000d0202d14a9901501411800e107424039141c101141c051552960030020700089002c005daa0300b440c400700c041c071740d5842c2018034500014054403540c03240304c0944591080c40151111950000200c941803030740500a00b0744000714006000403040c40c1d0144540750441100101940f03103241c001c2c1d04c01002d8940d4003051552500d00c0192000c803015106500450b07105048402141e030074103129040b21910000c4031076211040c4002c03111030041e500480707090301c00d04100d203c0c100c01012100c9000c000307800290405076030360017056500541c1c507010b841904802000b204058a08100510240c000241c00c1c2c92005c1d0800405602800341224100440540b5104038440d550780142540c0240c030f140d00c0c4408030020013203441c0415000c000c107841203040c2c41000403000041c040b0307190300040452500c5280c55a84561804ca600001c8004e0392401e41c0440003140d021605c210101c00c45103400a02600400f55a243c0c4100a503001c00004500c0329070070400000507003182d105206000649052214 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 578684622 1250 578683372 578683403
    0x1e071a01170a080309071e050109120b1612051006030e030a050706050601050c0f010f0c09150309020102010b060724060e070318020d080306040e0304120618050a 71
    0x1001610181c0208030203103001d001948841c20006010010250009181c6031640e4417580c19924020044d0001c840220407030800090300024500e800c1d040e560240c0395111100e0303c07071219460000c80e044002e0588108a0003042d5414607400c1c441482e0110f610340200c0d103001021800c4261007064031090110fa4450204010322a4544a112013501040340070f1840c0200c070100082c40390180c00030140140f0f6981001c910fa90b0300074001c4500706036114058070081009188081d00818500714404150740c01c1c2034440070f00b14881c450b000192081e2409004018241c0c8804800811410004905666941004603044c1d56220080d0618030b10441c2c102c2c0002d00e000e4855000d200341c005001483c0c0b4200182481507540c42080150302407079a16001078030800c4c5650f4000503030040c0d02c3c003940200c40503141205000c1d42000461068900362818013040007056015541c9218902c16140c507034070703e88003190028009800100c40b00e01c0e4820041381c000f040d80c43d01d131f0910440d41e10881d041000300c03500c50f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 578685872 1250 578684622 578684663
    0xf080d1d032a0922020915030607020d0f0c03090b0705280c15020d08040c050904110906192114030415030209210a060e0c0102070509060a030204021e07 67
    0x156131105407500c000c1c160541e031401050314040c0f100ba000303100b101d000d80020481c96180410780c0c0c007ea4010100c5209040c0400d012b5101c1c040030403144006044c506040c0303a200e0041c2c5808207403941c9640c03000d1f48103151a005c4a029080500f048070340c7d0084001100d005030703601102420075a840b11088a0303111307241c42c20a4200c80b03160300141da41e010301070130040b14640200343c0450031842400c14010581e1185080803840303200e600b009a000b00355400b0300007800402480d0f0501c2000070390300c2c244192503003400c220040d100c0e4480840401d0080e9000e00400c0d0700034072244141803520340d41e403070b030700416580307100c828940c072a40a98554004502080250301c000005401005a41021494801c2e62004101d012100d50854403080e003052814912481e8100603180c000c07074005004000240a88202e40d84038000d1808450061180444c049002e203440b010044c020400140440c0900d07141d603007800003075007001095000e0707030030524076450203602c0380001083d0030740c0b20700d0152040b0440003465 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 578687122 1250 578685872 578685889
    0x40c0e030f07030c090e1509010605010813020a03030513050d0506060301240e13080c070314011a0f04090803130605160c0b04050f0a08040f080d1d032a 67
    0x1c8000350388110b408002080a810001c015145d0448010500c1075800c001e207450f0800c1e0f1288030018a0702c04040204000040d40035134160781d02603840540649440030091140c0340c081c44069070024403c0e0742000001e0140d0000c08200c09a43e50314040395940e900000d00305030761088203035113541040d001c00c012407078284500385c0055401e52b1600384055500000002100c1c042c0228482014080c000c2000241e10b9080694101e901124185e510380114039003d45843d0300380b20403221203030104280c00074401d040c0516805004992264409104003038100010742003c075410030381103580e84403e040840d43c41c1e030055110742c030302031103d0111000600c0d088040721b800500c0c00551903102800b4241d6140c1c0700d403001840e95001411140326850b54104513040141207429980c103031040c3e0025004202c0760b48050004c5413030303202000d07030101d41d26800151070780d0765402e00301300041c0314070042508009444860001c0c064058100c4104100d44040d0f501030031808641070542104c220711800d0146802d82c0d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 578688372 1250 578687122 578687143
    0x10b03060c0a030b0f120a02010f031e18020603090f210706150801020d0f0e03040312050a090f0b03060f18072001050c0a120b0d030815040c0e03 64
    0xc21051801440118150050800c070104054580c10000c2c0c5503540c2c401400d120480041905441a0390b04108a03540e000500c81207002c50400380540c03007824060b104140c40501c0b01103840c40e100c10a9014200140881103902500700702c12070001c0c1c0980c50b030070051803041240760b000300300340c2c09200c4001c1d1400d800d81420780d14101d0490b0318400107503001002d07202c0c0564040c0c40454440c071445030b06010b0b000c054000d00950362020a603600441da440d0405801c0400104082158405020401e80c80303200303900025064144ca550f06800301440ac000a10a401c4140341551106c1c1d103c00800c005030a05e5400506414008824050300380f4040d090600c2034842115501440071060741181d00d1200014050801c1c0b2001d01030100025040305141c070080c1c501341008001500c4c00d030400b104290003c0e8a400c0000d40300400c402c0c4400c1092040713007201d50000f000307d242c0a0850b076040ba00741d54020701c040a00000d10041d6006919503004900b04c4444644501c01c6081800d42410314041c0d1154 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 578689622 1250 578688372 578688379
    0x13080a051203093405061638070e0108040314160602040f030b010510050304060203040206041706391612030e010c0801151d03030c01020408010b 64
    0x14001030000580030764504840a400c40e01c2e0343d1116102800c0c00d11003910b8551903009200001c440703850803040860107250203401d5099140e02e84061007494090080d90703540d05000c00011101241042d2001c5540031641602041126a824655400f070030051004500d000164414031805903008180e0000168082c42d18021a00c3d1a8400400c817603000d0b50780e690001000181402181004006004940d422100070340d0340d1a51103860200210903031100f9541000c0100002c60307586018055004804455a1031600303540392910b80c1c0f8000d501c060000c9a0019040200043e018031044800880c0400f080281c1002d01e8210031400d85609964607000d40d076050000e50621412a04032044241e00440c0401da4440ca0540e40b90a02c0410306600a0002003a411903403e1040c1e260700603044202c0d00b10000d10040310080c0381502c1d055400c1c013451400144d0040c5c000c21152003a03604071150709098440c0c4000204200103e4215070142005038030076500054207111507042401003404108055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 578690872 1250 578689622 578689633
    0x9091e010c1d0d060903021c2102070503030f060d15020d0b0307081906020409051003050d0c0c0303180e07110615030705100e03100e011b0e0d0510020f1308 69
    0x1c1e000601c0980f0320450013407000c0e55036081802072510801c0900d503090394040c2c680240b090502c902504810425414030002080c05a101401140c6d40c001c0d2408581e11100850440c2c40f050400404980020060380c1c0065500341c104000c00d8092400d10f12800035902c00680c1d6400074400982074515064015009900004003000711403000141c055085480702c086c0c200c0c0e030010740b4249002e40700701e502c1902081e080405100280600046401c00c60f840380e01161041c11035040d0170750342d44020440c0039028640c0300f1802c2000c00e01078a000c130b03010300c00e9021030560705403078404003400d80006440103070005a82114011800d04100512134010718407001e807821a17141e000010350b1700e43c5335000e014080c68002002c00703002401504007111440d0001d050390b1051084040940081181520024141d0700b440310984d000e02440d495040344007050741c0e8240060003d1024400140c0b4072090840303503071140180b943c40ea28003501c040c1c60800c52107896956100052023441d403075a00e150700294050f4012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 578692122 1250 578690872 578690927
    0xf03200712080c0d0902150316090f0e0a0903050912100605030102040503030f0c0f07030f02040c051804020a0e0627090702030a2a050f010c02071409091e010c 70
    0x1c0c0d41a207131500380c100c001007014191407002c501118111002c0e40c20003c0040240158909410450010051155500d40c403d55a601583d1070380d204621580703207860300d00c00125040f52010380254072560b000b03091180c0b0b000310003004120100040c0850907d241c1105a001c4118a8140150002090210f00039800d060604002940b20b11a044030050200000642030003103040c00e010320f2652030503d10646220301c1d40c03802c3c008203120391100c04912461401480c11000f5001d00c0640d004002615406d40c0d10611403824480258890f001180030b2040f81c40066105554160003007020306001c81400e03100500000421000d0481c40c0b16140c0315418020401180e141e00000b5076000e002c9a00e0681b0300b24400c1d203914410052006000c0e030301060740a0242c81404400070742644803030f0140d4020031003407440075000c0303803144244d004011904000000f603000918001400d40e130411a444141c8c0c00c0a1490103810a01045804940384981d4403159aa0011600b010b03001852a5000b101120310101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 578693372 1250 578692122 578692141
    0x50f0603060409060e0319020607080f06130f0e030c0708060601050d051005120d11010b180408040f170705040603080d0e0a052401080307120f0320071208 68
    0xc01031000340103a65900b48441840800d400090000401000342c90b51081c50142c40401004048a41d80242c13081c040400c00141c03250010f41e1043c00400c1c0e1448054648208012445c22a009050000780e11505030100f5560148183d0049900c800c0c011940d8203030f018070302414900e59500c204060740002c0100001640c200b400c503a440c2042500006043c0c0c0c408001d0f41640c0c1c03d5030010368002003a5940414019000110503039541c489807103c00321180203000355804e8035401d0302842d401001885096114205001d680b64101c0d2150300c4c00b60901703445074102d103680d2189900102411401e006c0d00380c02400c00b480010041d000036501440114117548440034a8030030600001101555240c4a50140349d041c41038803d119442000c2d20030306a032000400e03030049c50311100e42801a114400004109400100b00c507002a8401940c0176215083c0009580201400c01e0391414952615820070008402c2d51305010001a83c030100c03502d644150800400e030500e030304405014400001e040c0100ca26 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 578694622 1250 578693372 578693377
    0x15101115041109130804090c0e04091e0204020904090c1505030108120a050c0d09090c08091e120a0c0b070507020a0308090a0e0c041502150609070e030303040516050f06 74
    0x301c090f1825286919a424138a40040c41032001070070300580801c01242982c0560840c80401000d940e907039240200d0003007000226210050000d0640c0c10152500340c001000741d940900c0907000800050030b10744120007103400c0d5441c800041798032045102c0b080c02040360361034040c41c419250b460701d1401c40d07041a010701d544a00b40082c0b001100b2000c5103e1802c1880b40e030483d41001a100103403035003400b0b10348001d46903c030b090180702105420005041072280c0300b0a0b03030704c1c40b6102000041024003000c6282c0d81c066840c201c8040000d00a2400700c680ca2000038008048d40c035059990101c2c030791814200b1466404001c4c2c400803c0180401c0303150096503c1c8038503801680d410014150752805541c00145156509a02c20074940c107030403041003041c2d034100001d08102e07485030b07010405222007654103c0e1035401010b03c0ca8043c62a08001c1100d03030808030720440c0c0c4103000e801c0c80e42c14681c4001c0000d1441e04101d40451b802d601c4052403022404044604500409040d200c0c5104507604600007056030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 578695872 1250 578694622 578694653
    0x70b010b03010519080a3f020709090b06040e0307050a080307091410120b0409051f0507051605010b1e031e030703030f0b1c0b060f06040e1510111504 66
    0x800c0b058004058802c2c0d403404035a801e1085001801d1250707047c03404140e810704c00e003651307000d1b0190540024031080903026135004c9541c000811030312a5503c20421004040314228450036201c28002c1e43c00080c2c00b0003180407140c1c01031012036224a00040b005041d86215002046050b01031070b850b82c0d1644a429100c510781c003450510402071080320514100624a01104c1c0350304c070742000001e2081c840c0200f921161020040c45d00881314100c40b4070b10091b504240c038020300165041044268150100300c07104001441480085099411030300050100c040c0d140b450541141d11410b95149454100b0031000f0140030022a4040701184d011400e482c0e000d10340001d000e041d2509000d0381c0401e0103901640c2c0c044030003414074000030b4482c45420441c0c58881070451b8592440300125110785410a002d84942d10024091031031705080100703901c00560068010000795545402d40c2c449561a06103400e400000c0b0b54440081010340d9a00d60b1038900e0070803403d041e09505c0810f00c804540c4000300140e40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 578697122 1250 578695872 578695883
    0x15010c030c02040f11042c010510030608100f0507020a0b0c0702040615080f0c040807030f11040501151709060115140a170601020c01020d0f0302070b010b03010519080a 74
    0x140081d400410080c0c012100030160541c84d0568400594507040b0140044e00c0d6228070485c020740380c1f0300d100c0060184031079016643e00800c000410413450300a8402e00c8048142c900031805998681840e03152110145480700e126486200c412035110944c400c1550050480c40149001e4095403142c00180401400c03008040313000243c2c0e18195160f64000200030013000c0c00c185e081c40302066005082401c03c0e901071601e03260b0400458014000101a1400da94158018004031499540c0307880342c0c0201084100c03500b4840c103640900940c3c40f1300c1094001d0618041c41d06c180e441e8070714001e126491901c80c0c42c1400041a060000c0e8500004409065038a607440e00084102408016a5500070403144000c003880c0005400d20042c0c0e0041d0981c2c1c04424103248141030351107000c016611101603203403940c0164460410304180c0c1d485a00e8100607032001d0700300145002d10700c2d160000f0b064000d03000724a161100100422442c107145540e0986026038038962459107040c2447c080e1550081c0101510 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 578698372 1250 578697122 578697137
    0x108070c061505130506090108150c07141902130207080f09031207060c031808070b070905040f090516030803040f081303060b12010618021c0e070e15010c03 69
    0x3514924142d010b00401449146040a00ca200030003601c000c5412a0260402c040001140d440c0002e081c4102c00845101d211150740708154120f264005e910161101080c0700a81002100d007400380007400400343d01110070190b014010702404168070403150310b01c1c500c100a4030001c20003000948108c540310000da81e40c0c0d9400c81c0d001030719100800c0b802440c2d400c0b00041000412900380d01024610074103850901c43c00d20f0304007c1c68001c140c41030015218000802542001416000855902409a04196074103c1d1941f002c00c044400042040c0e00043e511459041805010072903820070107840c014015400b4155510407e4070700000d8030007003000641c042d1100030000c9003016520130b19040c58200c0f8034143c3d28104540645450403200303000e8410103d910360885d1041c0500343c25180e807210764550741c03103544016000039401204119207600700304288116114940c090422100102001000c60505115421301e440740098002c441324030001031200100d03600284107103003050300360030401c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 578699622 1250 578698372 578698391
    0xc040e0109060519050105010305040201050706150803040b04060e090103030c0209040c0e0a02090907111b1309050102090a1401020d050a031e06061101180f030c1704050f0108070c06 80
    0x38094554800010519410b100412a0700f18000d020b040151607100740c140b100341d03039607001501142d4054034042d000404c20010714001c1001a00966500000c3c4031074480b0703480d40c0707601d4641982c019401412a000c00020b04000d0950b111100c40c440c454102c1e943e4601e9407440c0d5010b071112003411002401114548005401d00c50340340381d00401840480360313102c460700d800301c090002580701c8080e01e0710441000d400724404c184509000300e0b4040032100181040344a00c4018202c046240c1050355120b48400b000035503414460044800c0369201d1400540c641307111600b0005403078840d400420718202121442d044980e030002e0451103d03107a07400c0030350b5110103c0b4400c80141200701e80700c813000d580903010401044030a60140044501956a8548074040c03800c001e400c0c4d0322081d1420f0030101102d19414042180440c003a2441d030312030b00306441030140641d1040340c0781d0000e00302c4c1e40104101040401c460f05005500c102244002d02c0c1480c0b2900e40000040c18800910502901080e0360360180c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 578700872 1250 578699622 578699651
    0x618010e071a040b0c0106060f030c1409041112010806060d0c1a040503010207152921060f0411010309051005041b1e0b07080a11010b120c090115020c04 67
    0x2500a408a04c0b0410b540d01c91740100507001c1d1895105420024a00c0100c1c00d404500c64407c2090076507030359641c0c0f040080c4443d1038042d01e0300202c441e2640a55a01c060310480e4412030014640c0500c00003030a4403940c501861141071071001409070380503a210300d5042c00000e8100f12481c081e110080070084607501090140503a81c05543c0159416601c00112042408003a9446c040e010103091002c1c021150041d203003d01040c0e540084400d01e8001d2041000c251030000c42610050b4072800703c030200b44002d898414504001a03030022035000d80b903001e000034003105210f4076115040a00b028051210036a40340342e5118002011000c8d402e90b9400414100b1030080181441c0b4a20251140e0030580c54241c0d14002c0c0f4041e031b5008448610490000900c901f012041e0b924403a008000c050a110b51240207460000040d00ca40c4415581e0341c011900300c0c1e860f04590009582c0e21001080001400c1e4203000c240c0c40180c0041840c102050350310181d96500145210441d542030f58086601e481ca034490 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 578702122 1250 578700872 578700877
    0x11030312040b041e03050c0709060b0a39060c0f1d0102150a0204060806030d05030c070c051f112821030507020d090308030103060504020d12020618010e071a 69
    0x116944e03040340d03072082e8185540940900040540941948c0200340d549600100f06c1d2020310a14243c000b080c40206801c50140075256030300b040c03a0b4400c2c080c50840c1d034a5203000c81c500c1080030413005000c5008809000c00740c0301d1a242d101042c1031030010310615101c06455138507904041c010090f12189484079a910a011025020000c603074980c0c5103052580421010750458014a400104440f001030031a24000403100d07140312140c1c0340c5902e5a1548100d03014241e0017030034151980c50000d0400035450310350520709038490000c0500600e1000400c1402001d03c011030804510a80c40f003200c0e81c00c11105200c0050a10f4082d030b085d8647c46d412403a00c0c42e020001d8607400648001800c50401c112501600003a108841c0303a070a070342c1109290b01c81a1500300840c00043c014820074030051002030290341c409600070303000400300e645112161b55000c0b030310001c4140c2800160010424070489091032025022a0007240e402408075009c40140d450f91000140310b424030400300041083d44503080e5004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 578703372 1250 578702122 578702153
    0xb01200c0d12110319030216050a0c090c0809060601031a0406150f0c0b070c0320012c0c09040303060e010f030b160804030f0207050a1211030312040b04 67
    0x30341d008540d09814100d800d0b90028a45001144500065422000012088621440c07480c10401172942080004034000e400011161034084258a01140071520412081c2d200c1c1c1c2c442c0b00001c1c0d00500f0a184541901da10b03e144900340b001b003500f48a4040ca02181056001e40203280002c1e6500c1c60390145021300c1031b815030b1107401c2450900049800106070030032802d400f4490322803100801c004142150b03159400e2401421954482000c2051144a1004a4a664001d2506c0000e014400b0060740c5910803000103001a60b555240c0f0048a054442d0340c101000a41c282d15211030800d240340389e0f01d03009580d1883e84100007120026040500a91045016120084205079a90b03110320f44c03480016241d004c150350420101000800b81000d042140440038440d44d100c8007a03484660b0162a0b52141010340c001354010714030041000d454402c03200c8014082038a502c4400141807c182c10207201c1c400405010360030800c0103820f40b00301c0c091030603080756200503206c016583d40e0034130004040c40c0d0034 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 578704622 1250 578703372 578703379
    0x402090f0405280506040e0f0d0315230909010c0903060207080c0601080303010e0c030402010903082a030418140103021e03070b03040201020c01091a0f12070507150b01200c 76
    0x380c40043c1c1400075403081e0710410341560201301805920b4030b2070f5940d034100f500c1050160b0002400d400810721136013100c8200c00300c0c3c42e0300c000c11a4580101d003040d4500c0303441c04003450700c0302504506189003e02c81b81e03400460038002044650b0401c1d40061a141041c00003034484d940020340c1e0380401800d41d0450360342000340001d8845958441c240207881e980203124040011250b0800b01d07400341032900840c0c1c045c0354140c60b0800c24030324550354040940c0244001c02240d170030030305a08a8020340201c04d81500d41d01c450155035524280049001d400340f41000c00a5401e2814122014007020406490b0641c1d404940158041050090f2101c1545c0501c614540602411000184441e540000f07140103500c02d8095032024500d110046408203010300c0b90b0309a404081c2d42d180e0108861000a0508130140c01c83c80f460560101c5c20f14211031002d0392907600299000030300c0360074014150741c5081c0d0044644420b00c80102d0b884c000a09100c0390941c0c1c0798003071141002c3d000000e0310401c00d0414400000c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 578705872 1250 578704622 578704681
    0x10c020a0312120b0d02040c02010e01090c0f0e01080705040504050f01060902041d1009021b0a0b1e0118020d020415080103060b0301060b030c030709050d12030b0402090f0405 77
    0x900d010000c2030a051039100214400183da01000c0d201030199074545a400350596045184a070204030142041003d6282075550300c00b50045204d400707008210701503008440c00341e1303800d1804c42e2401c104052039106640c1170414900501000501060140c02c46000300e401082c55102c509017581402d020b89042c02c002e6182c400300050b0303041c607a000340044130051362424155000150322003001e4207049440513031403440740c0024010781d8201e6000d084840e0202c1c040c1c204071003903140c105140100c1541c0980c0d050b10a070042103004a0f0301020202c204050010b40000c5500d411240700c800e8010712085180c668020440c00281003203031341590010111249e00c3e18030044400c1c0080c180070400e000071b444aa04080006505080502821080b9540034240900d0740d41d032440245107a40002c0d01c010f0406c41c0d100d20009040d903a000018803054000c0702c048405922100c8040c00320f401004240d406a4010301a0003540c0d660b100c60400542c00640300440c0c55070f1407a00504a024000d540c0301c1d0b00d401d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 578707122 1250 578705872 578705879
    0x1090b061909150906050904050c1b0307060b1002190807150515010e0607020402160b01061805010206060d0201030e0c0907020a06050606031b0c07090231081b010c020a 74
    0x2007500740481d11642180c0b14003c0c49010110790845507806654046001040010602d041035401540e0020a409910303042030000701072503481800c60380c14422035032300208103081881128820040b0440e0121995024a44a10b0f4040d490340e540ca420900301401a0760944240400e20081b03503d101c0c0d01c84a602201a44001c4000080406490131405512599820801940510600b40200100824003410800e01e942040f0207980a8080314580c0690032410200180c84480100e0281a0075100d12004840e803106031120350b26103501c258111742c0f10205100f0b00d82c5401d02800c0f03101e41c080c40c0c080b6850b00090100303450308090040080d0403410342c00401c222141e000c00c0000300b0b10710951080c80381ea03d40c070040000314002915001141d0283e4604084403682200060030902007020585540641c5d400c180400c80e00a035040020842d421500d0b0003003801c01d0904440c075000c2503181c02003c681000b86095403100c180e000c0c0b0700d06c80e2410192190680c003540012001d140e0040c1656a20387c0c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 578708372 1250 578707122 578707127
    0x90a060c110c241e041d220605060d170a1d030c040b011205010902030f070f20010617010e01140c1602180a05070906020f030301090b0619 61
    0x1c0c0d810380e890034080c110602205107003c2d0360515100c00c144464480c910581c150308a455400840c5004c03000480d82000b940381c14100d03000c0c000400c00c02c4102ca810700c07280d400002c0501402080c4190081070030102071f0103400740400088005400c0080000c1540c0d4040116210042e00c6074054201046500120041000c440081001075929907400a0030321810400ca041e03040002c00c0c90342d16030415072000c01103052a9000d01c42d43c4005241001c107245035018a04120341081c1c0101c5215a00081000360300c00f00d00e883c4c180c00c030105180018800c207032142d00410b180001e181c03501c40712001c00c000314684007094000c0c1000d00f46401c6500c5001d034061302403a009021210b0b620744203500f4105000c8009074034007103280c070406502a01c04e24241104181629040e40c0100885e80681046610341c4191450060684035100c00034000866042c807850150080c540355102d0070440d07102240c000305840e0040141e90454507611004182c826005000030401c1c00381403c4444064a803080389140c880c4e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 578709622 1250 578708372 578708387
    0x160b03070c020a181a06090108040f1a190c08060303090f0a080d0305061806100302130e190b030705181b0703050a030509030403023706050a0305060a120b090a060c 72
    0x176680c44030788070004104184040b90180d1a009404100711500090100d02c5100031544c250344618401c0c184140c80740e00d00c89403800c040e00e80701010b00100d43c1c0d080c4143c50754071a410340340e030300da00b17101c0c07070510305240000c2d40c0340305416041e0b0181074902c42c1640c55031200d0640038058448801540d0151b504084018000d0a00f01c0b0a00c4c490b0003105000b00c007584080c00340700e01450019050703d20692044809401941c0800a5030718030010203100011101000b00c4050b00a904900c48200d51080d405001020f640f02c00e005640303e5081000c042049035030784018200c09084800400149546000c2c12485000103900907000e540d5002a14004041d4824018800074a042c0c0b82040281c40310880c80e41c0e00d01650200a400c038282903144490f100300360204404026880c888103c415590f200220031825096000402048001c940703c2201c5415000c0c0d180d101303805a0b800c01141c1d1030284031284070580c2e05c4c0301500880072000420702c0300405000303445606800c11010700c030a400ca841c000304441c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 578710872 1250 578709622 578709641
    0x40603021210031a100e0412030c0806060301170c1e0916020604060504111f03180f032102130f05090402032503050a06050702160b03070c020a18 64
    0x60318071000100500001d5110070207494001403044003241d22032207424499003001d04425840040c840300015800e140920301031146d8070803020b000c0c00d0110060050262150100d48005100b40503040103815196103060707074111407018140445090391802e6260406001400ba03e0300103a1790400c44121014000c040828440c065030700300300d5a070782c200e604201d040d0901d82d03600060300704d1008200841d005402c196003140c0a48240d540420301c4c040054050301560036400c0040003000358050040c0c1d018864480d0b01c50003200307050898005541c944100c18400074005040c820350107840c48404803c046624003214103038004540c0d402040c00481148000d91183c081c6040e450840400c0c1420008021409240c0c0034000b031081218060f400c100a20180a20031181100400c0002c08208108030030f60006001300f00c00100b41c10403280090904c4800d000210800c0007028081250611200841e0750008240c50511080041880040c20071b02044d4850070342c44000086d041c3c0c0c800c1107a80010f691 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 578712122 1250 578710872 578710897
    0x150c0307170f0922090609031b031202130506070c0911040302130e01180b060f0a0e010605031506070501290a0303030b030c300109080a121104060302 66
    0x1040c004003503600251080001603078002405000c3c0303004609082200107078070f036800025001e9041e03030300da003040480710f41d0795090f5040c0b41c542c02210145500f02d20a0540c90071000c2079007504110588004d008074401203420070703403c0c6d40011240c220300e05081e01100038041c010215507481000d0306010020140c0f030700609400c0c500d401108003405407000d00f00c40440b81e0103064802e040c81120342e104028031601151120954903241442d00c03115854a1407408079200e44800c1119007050000d00980203881e09149000c1c0c0e807091828891844010300c210304460803440c16954942d22810903103010301418054540000000c203c1c90104581904001e10f031101100140c82c807816102001c2507580c40c40b08081d03400030410703030062010034130941003824020f001800311156110742c0b0300411006000c941000080300844085c0300044050440c3c03007284000600020f0000d1420743e11401018811128860180040e140240090b8101500300348000301103100b0303ca46550307490001034081c1d401942190507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 578713372 1250 578712122 578712143
    0x12050d0f0506150a03090b070302120604060620011b11010c0201091e020a0f030b22030f0e1201140615040806040b1305030711040513030c020f150c0307 67
    0x30a20003442800e00c25003008140824000500b80b000001c2d901403088401015203540743d4074003198801120364060740c100c0c0d800580e100a021210b107000200502040d00c200d04105040043d243d1190070245080d010740c0d0500f11680c1c40b00310321070042c116200880d200044426080500e071b070b0003140f40d4895413140381c000c0c8401c40300110100d088500c0241f0007007800031640e0600c440c0000440d40c0e00b081c50f00c0949103800c5503442e888070110201e0b559000310f0303809211004003d1403240034604007042e4a824204444110015a030190041c91b1207110038080103003112040308556541c2101910710300103c1d00030001c0d41d5103107056005500c800c403011801410001507140b4501e540c44110740032241c1c04000703844651a103699200c00e4500c007608140700b4060b09120840410024001030052600c100070350006801e2410a000603503030020201d9414a0592080704042600200101c1c20300f5411a0441500b0892100251002030203c6a030b094916020961110346080003004000d03880c080c002060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 578714622 1250 578713372 578713391
    0x40803220f06120509061605030a0b0429030a030804060906020d02070b06030f0a03020715090816050a0504020403050c1201020c011a190b0f09010e150a0e10170604060312050d 77
    0x303658a80542d42180110800e841f00d1000910038406940c11100800000c148044004005820307170b400403506014016040c40505d0035504921031100c1754031029005401003840d00d440140c081d48000700701518950301c2c1c4148a0400081d81d04561400c1c0040c0800c40d00c4000030708160b29038440c11202280240308007000000c69036800a001035695506a00812003141040a03524410010040c17031024000c2814001c600c07480103001e0303014410151010b45907194942010015049031b2980300130301961041100b070012840215040c82c10000c152042440c03412503840309402031040c40c548001039460141020100c18841e142900c4001c01107a170001d452459440440c2a00c000e07200e550708002c01000708103100c1500e013001c0d1512440c141881c0c0021800e00303002c1915000c04843c404102c1000052240e0404c0d046486104080029543c0c4c01201304a2903024140581702e00c004104080c0c00d000054003036586030800c10140d5800b00c400c02d098803425401030182e4202a41c4040090b003801c0201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 578715872 1250 578714622 578714641
    0xe040608011a041802030a050f0c2209050a0b1602061f1e0306090803180a02010504060e0607060204080a050d0f08040b0c0706141b040803220f061205 66
    0x7051860b4004889040e00e000d52000c0000a240300c00140d00d100308543d00040140e50305020f640e400038020310103829046004d007035082c28052400b000520541000c1c5201401034280500300d413040d40c01c000001402c80c0a030502603d4968030b010014056140542044845e41c0e407000c02e8134045440d0740888000f502d4880e070341100416105102c01e808080c40c0810444108102c1c014021601103000c2942c409032280c4544065880650064820510002c107001141e110610801d10081c41e10000d0442c40e40c103030780020304a02c251312400c401c028030380604081599558040300c0e045035005c0f00840d80c0750355400b40c56496405825082d00c1501601c1e440c0780320742d802075444a072240d4080c0d035183c406176990740d00d65151147c06044946080e006000c02c000041c114400c02000d1002e01d07149a140e450a955540102e20190060001c1c14206000c204284000041a14401d603002404522540641242d0030181d641f242d110610305d10150000042258010000a1062500d0b600521a942d980c10b5903 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 578717122 1250 578715872 578715881
    0x14010504051e0d0f0f0317040b0a020901181e050a0821070203100905070803071a06060906040902030a052401111c050409050906070c20100e04060801 66
    0x18507800840a52040d10b0b5082c10300d201054280780140031140d5480c1680341c4151696200108075074885999659406140c0c2000104903500614800d00c0c8061400b036580d403e101101a002104803900825110302583c0141c0c100c245800e00c2200f03284045903a0101e201400d6840c10301228041d81d003880c04545400c0c1441603006640d0b0303a00040018008000c41b030500140e403a00c1c240c0d0b520b070050083d8070060343c06000348140380c0b4150034080743c0710790780723041032410700c03e0690203260340754400c0000d5800100c6250404114070704680d80c1c060240c0d60344000c1445031054a00c003e50045000030040350050b015405103000380312003c020030159944008628040c46c030b401c940d030112103201e12041015032040341721510580c07a400541e82102c006075000305408040d001d107000866004141480500e402d845000d41c800b003040b00130a400e080401c3c2c090080308000d50060210400381039980c445014290442681e2040581113180580303414800034240c4071401e0a507403045080a400050f2200c05005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 578718372 1250 578717122 578717129
    0xe010515070809040f05010806090f030310030b091c080a05090304062a050f01090213020304470103050c01090506180301060815100f06020a080a0e130614010504 71
    0x1a0700c0e00e800c64940d101550080310a480e80262107002003010341c40240a164000c00c98140104a030b414142074041c140740581014030450f500601c00c00801060000c411011203400800042c3e0a8651054003818100d044101025031042201d8610a0300c1e4007003003035031240095080070440c9403a800b510f079849100e9407040c0303800110b07014650b90320b54401c842640080b4070003601c1390128070020764440b0f050074410501c12010f0b9641d10303d0042941480e82c030840704034003038040440c510300e031907500c00c01f0640c2c10a51b40820080310001a00b020011281901741072030f01c4040480c0300319803d100942c0414024041111f43e40201d40c50394400d54000c07051203082e00d100400c03880c10080d00302d0340e0140c0d1301a40182c0952643d00d0b81c0000407481c50601141003070708821042e21500346092026001000d803190b01c00300f071010708010204030060740401d0900d60140d001001c0c50b034600400c101120100c880e0031440f58084203242812411b00385550054086401444008001e49074140044d40c550182d8032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 578719622 1250 578718372 578718409
    0xa0201020615010f110309041a030114040f03031107050f0106140123030910090602040e06221a090f0403080a0c09090c02030f030a0204030b010e01120201080a0b03030f03010e0105 79
    0x202d010070138a000702a8184050320b504226400d080300305000406a030540001a01c400541802c00c2805040030300039001101d03c180e0064280f8100741e5900c00c040d160441c8042c2c1003523030f00c40030415a98046803c03a0704294000c0b00704c400c8450303207510300d074024100da109030303142280441c1074035280c2d5018244052441c0036040703081042440f00c00045100307a0005250790020300074032400301c040b40b4640c420104c105029540050300c440c00c24558058048002c0e0241c1c0c4141c0d96a03100300c504029080414406602c0320101080555642c0c00308050000726018256100080c1801c0003d00100d030106584074034000d5550b900e9076201c1b54003105c2140c1c40d5904103000548181020300c2418155000120204c00c1881100c1c60020a07804611250b00103840c0f042c2165000a401c00900404190442c0907285c015522001545410030b15942101c0d01300e4000e0600150600048030000c2c039504c070b54440f21018007941d5940101182034580d0780c0c0240a401454402c40340086610b042602d0340d5001c0c202d008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 578720872 1250 578719622 578719637
    0x32d04080d082809081b0303011404090b010603090c05040f05040201122702060d021b0c0a0506040909020a050303030718080d050f0f2a01050f25020304170a020102061501 75
    0xb4020f03c0290480c1e01c0252a08881008810721078108280020f50002104002d1500c2c0d5040403e46020780c045400d0f898817907414200088040341c510881c8504452a070304000520600c2494010080c0256601140d4044e00e04480d540c00c0751580d03000940b140c1c2c800d0f642c182038140291032107012600d03001c0125400a90a0000c001410001c203141c000c1c01d40010411818003801c480900d099134407010303049161844102d4203444800040160080500301120b080d05624245404034485000e50700c134030b1545944403c0c1d8036041d5200e20020001412016050b01d0b81da140000c0c003e0300c01c444c0d04100c504240140d110001c0c840e00d021a48507060440c9913035140c0f8141071501c83c08000e03000f58200d03480d01141040701c0d4101035030380324254003070b0300c0b608941d641c01030140542070b421100001c1c40203103007410034420040341d0428665103114450941d905c58100d11441d01c0c02324618069a004170303104402180034000c0d01132000440148081c800d03801c5440940d04e010728a0524400100841d021484a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 578722122 1250 578720872 578720941
    0x3060a1406010c0206071202010e06070c1505060d02030604030e011803020a150908060405150f06030601290f090a1a030601080411100c0c0b0408032d04080d08 70
    0xb40201c030300d1480c00100b941d401c1006a071208050347d1060020003025030341d80e900e8200c0066090101c40c6e4803081c213041012100d201a15664001000c2200c00085c45603100002035550303507815483c0034815000360844030340b45002e103030203005078240d090480e010030401940850000404841d4005130303036000e40600380c400d01d030032024407451000d070380b122041c000208030210303c07a0010403503588607500030f100501c49020301442000360800003901441d03a03004040200065510b0001d089411522442254040301034102c41038403001d00110300c1000302d24000a012401d5240b0b20010700040d0204542c9890040c0e500c0281904815444240802000c01880010394560007003080580c8103000c2d654520100200d040003e152002e1250914080303241a0184424400c101034035101500b04003250624044c145007146a41c0c0c06000400003400f690f07446d0002140f240c00c0d802500701c030312005010b5113842e00c500040e40c80c0d0f86407807207000005010200054a20408001880f43c0c20804101c0660800a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 578723372 1250 578722122 578722127
    0x7090b180403090e0702280302151f06020709060504020405090106031a151902120417070812070b091501030206090d0b0a0b010905030d08181c0e03060a140601 70
    0xd01c194107004488800250b4050851240f6208601c6a0302508031540100d03a81c0c06a014620a070341c4510400e182c080d8002a000603880b20921030944001d59079070350740d610f1010041d50b141441c048084072804009012a000550001500d200300010b00c100350325842484103e028a20800768048a150010400301d8040d511030002219001d01070981e1750040d4010400010381610002d061040c000317403230f660700701da4406905000740d070b24400307003100040e0000209110301950044200c01c5907140784c400700d00441001054010412141034500349a41c281d0314401582105100307840030651280041c0b0040e10214a0f01c03440c04007004217035003603425270b02032004a4000c2490385070400d16900150b4042102c043c5200e10030701c44507501040120704a4001051140141c2c4414000d5003c5d0440769616600040c4082d0700c25219102c0310b00071451100b421b441c195425070301035081c50300401c07011009984180b0f8841619420b83c100d0340c83d03849400c02001104d6000400307040191035000811199031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 578724622 1250 578723372 578723419
    0x6140c1f020f030f071e02100209060702090907030c0906080a030e0f0301110306040c1e05030601140703170106020303090d0f020321070801051807030c170a050907090b 74
    0x500e84801810200803000a1602d07a000307982c0c00f50810b80c4c150800c407905a21840d243d1004c008242c0b40340005150b818003039a00c0b040c40704681d80468000c100256035446d140d083d110040d03002042c484480c100712200a0f120706d814001031f6802000702002040011050040750116506c0000030045000785490484078203a41100080d07102031085003d0310a41d90034010003255180480d841031340c07802c0c80d20400c001c44103180051002d00c98030385080740020081c1d00c88154080100e0908540e2a55500012682c00198122401320800003181d000103141d480780340e43c3d01081a6805004481c2d07214581a0307907e01044400270515030000408411040c41080700d07a64201d1341d801200c2c100000c404900344400c224071488000803203048100180702c1ea00c07000c26801010700f541e2140454418000280d19014014070f1042072584940081c00304501c00e10703844034441120700c1940d00304d00f0143d042002034602611001d003588240788c130100d94000f85108116600c080244cc03000c2c600003106074180f080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 578725872 1250 578724622 578724673
    0x108060d060c08071107080a11150d1a15091005040b0403030e100503101712030a0f0605090601210906090b041e020f1c120906140c 58
    0xa0105555000010714a0040a02100894481010600d080d22000704800462140002e0a5004000c2001092030100b4020441e6800038072400c00c9070228000b2600341c8841005516002c00000350f00c1d204a0841c0d800030308900d180980258100000d60100410f0507010400083c980e1002c02c43c1445525045d4504020341c4403504040741007a40c2c690040d8000c2d00285d0003030b00824a0011b10500f180303400311f082e4080310f0950415505500740142502c2c2424868050842d002e01030359210603009108000c01244880315860342c0d903807841c041070311300c0c0170342a03200107449150f081040100d040d10306001d07058402c94060b552020700001d03c85007000401044003101000c43d5946200c0745c00326a0354000d0000107401041100c003142004d00c1c14401004a02011806540460100d0b00040e03a4405141075116011100c1030700443e143c40e00c4101e001c95184004141d1907402000603005a0002c21050071a9000c0e19040c540154080c0f428025110721040790b041c540081d404003440c000c0702c05000102c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 578727122 1250 578725872 578725879
    0x1050f040b0a06121104080706120f05070507140c01080604020a260403020f0a0c05041e140702071d040f030c0b01030c14011d060904020f040f0e16020c010806 70
    0x207000c181d000708055403a90b40008000640e0410102201a458020322400d804809480c500e0f02c0d242ca110b40d519868036014001c1049501741440c0014141034100c20350b010320110f810000c0e0700742524060201da0001400300d88100031381d040036000500110b070600105406031546549561030504100c001d40c00518420203104176541440075416080503a14440e0079415698101403c043c00d000e0300e049800c05c42c4910725404002e0407400580002401c1085030750030b58020805594500e800101e140b13480e075103032000502e1700c80d801034501114010507000300042d03000d40b4002038a0b200d0252540d80340c2c5900721401010000410009840b80184180a50003440c1840190240e642d400201400c00e0f841900d100c0042c0320203000311000103440c0c003e0380c042402d0407242d40603240200e03010341c002103c0042c0b10791004100040a500d5580440e1514070807144242d548a44511181540c2d002ca8000e031512281000c00240c10712441c8401c0e0b10f0040d16079002003003c105070100442d102c1c003000b00043d40 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 578728372 1250 578727122 578727131
    0xf0210111b0c090907290c010e010c1e0813060902090c07051c02060a0b0a18050901150803030a02030c090409050c03121c02030c12040b1909020901050f04 68
    0x203105418800400c01c004501c000e000929401c000b00030610001034107101454004803001c02000c2200c031644003001c240c1d0b5011840480e4603d4030021709001d82881700c1215420441c03550b0107140194001640d024032500e0b284a600700c1c20401c0c5090002c0d506480001c5801c40d8082200c0018041160104074801d2401240507201c540c01315080da6801d44041d0030300200400d0f4a810444140003a24000d80c002410020f0b0000c6010300030f540300006051410301c00d40d19206081c0d107032212a1080050180001c54907040400a0011002007004850301050740d4600b003a0800c8111451044000311075406005504646074103d00704002e50000d070000c0c0814100700800036080c1c4a501810345443e0042006e40342c1c0140410070306050030110741300c030310007040104100740301d0740920030743c02440c080d00c0140140c0342d81c0d070009451454401c14428149504281d410042040490803400e4400d183c1e0f0700203003011107101c00e0844142d54000f10b00075806107802c0018003840c00c2484e1b0f180d007402002000840c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 578729622 1250 578728372 578728387
    0x50103020c0106030f0c0f080a0305030c130807081b0f0a060809101505101110090f05070f06020f0a0c0506071e06050a0c020601140607020a080303010603020a0f0f021011 75
    0x30001c205100482d80d4002d1b5940800a101102c3c5092005040840141291414640d0300420a00c8001c0c1262240d0ba4003090300009050428017103009440010100c0701d00c161140d03482540e503000d501c1d00910680d0f0301020300c00c0900700008941118180500740403504c0d07082032815136240d03d000f417040a10b0f200c0d01c08008400c030700d1802007100220801080c0340509060205014030740001075040003e00c4620007a0301274103040000d642c50300c170b0040e40001404048500c0c11403d210b40f9010050306601c907084012420440800300d0742c08031071482e000c8649044140d0252f54413100040006412020300e05c074100960b0400c60014054107108054002e001c404c281d046803040c0071840015604540d48000300085005c55102d9042d040b40d4900007000b040d0300d00321141ca921101801914001c41e0082280c60031521900c64a1000d004a01c0075039484e981c540d01b004000b50400030311140000e054510300f20016002d602201c4040071181e014100c402441c410000190502c1400b80c00700d008100401d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 578730872 1250 578729622 578729633
    0x20924032a1801030b09040c05090a0608120306041404080d0518010e0709051e0604020a0c0c1d06060f0a0c050f0307060b090105030d0c060e1e0a03021015050103020c010603 76
    0x410020ba00901c1e81480600107400040444d028410340320b0150900000344004a12982100812150110f039001e0b400d03501d00c15100042e0402e5400700140344941c4018072a620012800f035849808103a600b00800b981000b000030b0403001c151030140c4200c20800c1100d02c568210740185034802190607800c1d4034a22802c405c0c2d400c440c541600903400c4e03040380ca014490005180516604080b001403251402c0d03111440142d0140030140c1110b2040e030380001e560440c1c900500d8030101c0a5000b000b140d141c25078442c1c2d0801071110700407501d4200d03583c6800107a560300d001d04c19261100701c0c500c2020308042c0764000c2900d4401c0300100c10754552142c0c025154904000f080141101c0b0311130003000ca8005d1300c54040c0f01d031403801030f00014840d2300180300303070301d040c0c0e0780951411070075504020701081601e13008005504000c60855040d02a07040480491480100095130103c042c0c801d81c00c982d0900d026058510440b4a0800c20140000801800300080d40c0300c0d4020740804030f4a03d000007840c2c0e55a5032207 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 578732122 1250 578730872 578730877
    0x304050f193c05010c0305063a08030106030507020105070c0204050711071805060406080316140601060c1a06090105130e06090706090906080c09090a050a06020924032a 74
    0x901c106802c140c9003a410400c081c0100310603030a4505080c00241014000108144021030a400d034a40700818044000a00c881c80c85e8035201c0c65000d16602641d080c2000f8010342c3c000d00070320b40420305000c0070904941c41440b0b003e10800d2159030b40b854266641e401c10020b004090b00400c00c0251460f280f00802c10140071440040c480c1900f01c100900c1030080701c500743d540c01041075200300d00c0c10004003d009404002c4420428030184001e81c03c0a01c0d103440498002010503600791441410004211306030000d0040c000c03603014500e134402d100d071a046030314006c1d902140c1c440d4000c0e80e2680100200d0900314aa0214054010000300d4405d82500305a480c0c143c0c220361070500c50340324050402140760001043c5014007000d12091120314180340c0c003541c0d40c2e99004003150082c40b503200026035641c028080002480d81c044180c8460700c2903410088080c1d000010710741e100702c2c1500e5208019001c1d80c00c0f40119501075141560459031851006400107603c5811038889002c91244510001ea01000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 578733372 1250 578732122 578732213
    0x5060703110d020c1e06030718090c0302070c09150504020d0e01090b010608010501080702120901050f0d14100305070e040804120c09113108030703050304050f19 71
    0xa2010702552030804c40c1c0d4170728a480d010b12452150101c000c440d2141011240c0c05641410480c1c030044039103502488645caa64000000c5601d045410707074500d90701d03400600000e03026007000000300c2d031100540350444858005210800c90111010866803c02d07402030102c90105500024400d03030070140103400d461400700b041710910318260052015542142200340500002e18201c806441d10b031901a50350b1004581d005034036030010402c19900c2e8031640486020701e10710320380151a801405440800b070320a023052504100f90320000121035190210350901141c2e04200204012847c0810258120b00058404d50301300b00100302c08076038034079060b1204800901c912002140c90345083c10f020229405030210700307041141080489041e9a103114062804030540014108003800c0d08248040b142d0190b0004401e800003003a0700702415000390195105600504c10741301040c281c1d01c501c9840d01004200602444401c0e0b03610008500786c1803420f241403c1060640800c4011000000702040c5002c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 578734622 1250 578733372 578733377
    0x3131b0b0d0b0a060215040f1b140a060e030c01051c05040f030f18030209101a09030c061e16150b0102150f0612011b0519140405060703110d 62
    0x45812030b1400d006200302c0c020002440545071151686144140001c030142000d0020100601d101083c40310f1034058500f4885481700b44812a0350b01c0c1c80b042ca40d40d0402618600c1104c80e0040081e8250150407041403d16004001e04002c0c0300c080015038541c0c002e201540d1401c20303815407040c90f80f01e20707101381c1d0302076805072005005d00251807074000d103c150b0000c2c0704000c202c0002c0d5042c030844201da20003400c0d030f0390403181c036800303695080e182d603141c83c3e0a0303400360310002c0d072a44044603d0700954004005a400c00d41c141e0b03035514101f03424424030348100180501c59145000c0e02c3c2e140d8018800c05412481c65004182d201a102525034000d85020691045406c030382c4c07144804a079680400056003440304a04603e0540d280c15500d08042d1030f00102414040ea2110701041d9403402c1c29400031003a0700030300d0302940b80200340c003000400903000100c41c02c900c00c0406800f90f0209000d0596916402c1104030b50300c0c6810f0918041c00a50b0300322120890612001020101c580c1d001030112400c0c903c4a40e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 578735872 1250 578734622 578734631
    0x3030121050f01022706030c0a0309060501030605010f0b1e0318060412090e070e0405060a080724080f061905100c0507120206161106070503070b01090203131b0b0d 72
    0xf000b00045004242117002404c00902c0c290350f41300d0720781c4419664020701c080510354581011841c160054448407100610461a01c4008400c0014a9000c80d050704c0300f0001e07151409440d1110f03c0c40074800c407003080000078503210050303405882d0320b001107520048019100b0000150031740ca480c6071a2054801b15a086141540f240341c90740d108988900804001e8801c240f103091a0700058004001500d0450085c0d48a900187c40c940350203c40d80000c00c0ca10303080f5030205d40d0b1a21103002c500d030056455000c41010314824a15503205462041c0110040c51441d01d440c0c446230f00300108002020344120042d04d6180700003815548400d10f0441c00404c40d200e0494212003482d015003040001d07041480781641a00356070002d80c031003000360382c420b104039003071403021441d0713420000d004a000141a42d0b01c0300001030b00d0400c014020000c0c1c100c29105640030710807641c803484450140c0c042121651a243d80103001003000c940700d40204011140407845820820703032180c1880300594450340d03111000c148c49 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 578737122 1250 578735872 578735887
    0xd0b0108060705180d1e080c0c03010209180a0626010f0216110303130b18090118150b0a0203070b0c0906031b0d02030a0f140903030121050f0102 64
    0x107112455000029141551900180c20036a01c1070300c0f41c03e040c090141035440c070070004000c4041c0402224144a4062841501052806035811f1340711225a0481f80a20001e5008500b414007c0d2000b24600400e14030040c4445059940c0d440d800820062020f07448500000307903840c554054013540341c0345100e60310030404200301c01401d46000c4000803140c42e104100c0e256070240c040d40810103aa0784040d07036a0b01d40880d400080d1960007001150150494016000074401d13007440300900c0c07007068641e008590305400c2c000b080f41121007403060030b1010206a000c035032050a554040d4900c80200c1c00003940403500c952140e006500405400380240e48001064001d00c02a000180c1c1c1c85aa829003962400e8800d5021400500014102c4150311301c000f03100d0074445a450701a9003015044000c21912490030401d20b1019040089000d540c2074500100003401154540d40c491081c10040300a5146900c1c044201007010050980080000b00c840c2010000a800b1300c0740c01c030300c086000c00268880c1c5a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 578738372 1250 578737122 578737139
    0x6150302010809070b0904090c09020a02030a2316030c0b041529010e010207030501020a09090f050402031f1503080711010503090a0602030c0702090a051005031203061903020d0b01 79
    0x70040d03c6400703d54402d280802801780c0e42012107949420540b0080780c1e100d50707031821030385618958210034007050004c41d100c0320071a800405030101c0d2100d50f0720380f040e0140300c51105403803800706c11580b011040d0400c19095044008000980103a12a00e020f002aa90369280d114003100c00f03403030446414480e00c100828140c014090049042c80a2040c00c101c12881028541006052901d0f5818040c2c100a0860141e00030701c80d200045820500955803140001c200400490f85405606401454102ca41d40200c000c0c2c0700c0c9074031965002d401480d07070742070b40d0021280740340202d445040e1490b1150142d8207081d116080070401180318601043c1c68012a1604040c10041c00d0345140c1000301c10f10400c40b900c800080e540b60000d820136401030faa61140d22560b01c461190700070181d080346618040c46030782c18955200c20310511513498103507281900c450030980c81303050b04011001002c0051011034603e160022404d40da046800000403010f5030b0340d0740860b8a81e20300c4881500c6485803440100030000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 578739622 1250 578738372 578738387
    0x7050f190c0620031306123b060910060b09011b0c050d05011b1e0804050c10020a05010f0513060e0102090d0f060501050303040506030718030c121506080304030308130615030201 78
    0x1f1982400b844244101074000401c44a02101c0c500d2512036a01c1d5071105a18540150340c0b403085000a0790000e1030100c00c803070754414800c100f074100a03241c0341c400202d80560606581076104140d40d165a1702059400c409003010346c103541030b40c280d04040c20001d001d0f5180e0101021461088002080301c40c1a1000c0914042d450174140040c001040b05d5100006840c604a100d584050b06040005894074101280350590618440740c2044500a40012858001400e6042544920000e001c004800e00c9000d06035502650360600d0784030003601450008410382c00c4801440900c2e0001803c01c00d101000400342d0f0404401900d100c1c5100308040140f00460040a0152205400541c1781503d00345c0410040e01c0b0007807c42040002000c2c400c01410b2030051407100850308203006100c03071502c0e0b103800035403070a2414003210042d10781c04004005440c80d003d28021070701110043c608140c03842d14191101c0b8001480c40f0340002052a60400184a038441c4540030001c1c1c042d07944403182148005010031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 578740872 1250 578739622 578739647
    0x80c0a080d1e0302091012050a150501030207020d06050720010903080a0902030a0b090105010f050f061914030406020a0905180a0c050d0207050f190c0620031306 71
    0x41e0018a0300210098100300807803003000c00c03051072180c500301486044009002e05070800303600070000f20b0617240880c1d00807a6014120900c0004110f6501d0b00102c250490b03280b00f030302440c40302010400b002650b000354045c0008a001514001c0040780caa90b0f48011030700200c03280320118002c0010101055201c540c81c485c1128084000c1104080d503460241070350341e00070303d044406a1102041d0f02103490910440340816400f5a2414490400d0400307180070380424040d92150034480b40000405140030440e032160440064071080ca02200c40341c0c441c40c500c46400c9000140032000b48288405030403003004501c07072401054016150500104000c02c10171403640314a1280c030300205201d044882801c2c11079000349184500040c0c04c2e44000c4181e9803401480d1103100324070b1011810805004001c1001c1d422000c0b0b4506494007981d00c1c0c00c10000d8659580409400411482810f109060146070300d0103100c0106901106030f0b20b16861001d1071940026a84105205079900c1040490303040500740041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 578742122 1250 578740872 578740889
    0x50301060207030f0f0b07031d0c0d06020a0e0901090b0301140609130221071d0903030406020a0903020a090902010212180607170a080915190e0f0106080c0a 69
    0x155450880025540d000501002e85101d10303019103c0f04014825100d00d500ca82e01011010b280c3ca00004007400501020818a40c1c2a1955507810400301010603080d0320045c000b0480c904010301c5807030354002500040040b0041c40b4144502c18025940d02400500030054032401080c446e501070241070a650450600d042d8864030001404241d41d10000800d900160315031409403241d809000207200b0004440d01417001c0130100030007441c1200d01103031030301c00c1e00d8001c181072101c0001d5041d00c1c2851001210a00140e810a2002c20002080ea4000b01042801072a10700006d941700c0e00001d0f08a0a140d03c89080c081d644c203040700440d601807100200c11700350401d680781010040c12514500c0b0079031038035192140500091060030031807449907034a14207010380142c1c0c0e100d00c452740c3c02070700d083d50545812101e0311580444106100011010a110320b4481c0c004080d404861000f00c80a05582d50b410584c0380280010090594824440c100042071010020007018021405002f0001e00d50b8000010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 578743372 1250 578742122 578742127
    0x106060905010905060c0a0605012c070806010c060605060412060e01050613270827131122090c021b0918030c01050403080f090d05090117010f031205 66
    0x28580c1c00c0142c03001164005d0f01c91070f030745608105015040124a5074010410b0b46000008245100700c0d40001e070f8000c9101d448401c00d1507000c01400801301080f0784ea01c1c000740d1000002140d0794420301002c144944940c1d400300302141c80300700007945600302d500003240c2005113043c040f06000b051b0142612800843c0001c121324244240401e400084c520b0f0300016882d02c0c1c0c08500a030041c560701d01e9401c0bc81d1040301382901d089614107030480b98401c903000746214560113000302c8a86107940b110640b06c0c2d4020500b00c0074080d140c0684014002c0419581541c050074000c020604000c400364040d82c030505e107a40e100090a002201d0300721403003c0788a00440d8005c1d90b004807049050b0159031390001c0c046070403032001c0d5180d452046140c1c202d00000101c80c040458654050302c0150007241c0903070301c00e07105c0b082a40e5941340b0109100c1d030116541c41e0030b40e201c2e81420746510300920007403003120010316000804030300c0841c40e4040c1e403d003a0320045050920070300c10030a001c490341e01c40c112280240b41151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 578744622 1250 578743372 578743379
    0x2040b03030d1415100c03050a0509030102040b180a0e0f070c06020d0609050117120f040807080109110f131a12160f030804060516170a080a230406060801060305030c01060609 77
    0x1800c2c2c90403900007c1c1800b07400200c17a0340060080042c1d88a00070010001e55030345807a0300c0c60401d56000986c1030706c00800c2064001c509458095800402d403280b000e9000300c103035a0b400089000c034402401a13001d00a17103400c030002003800350004190b144104c1c0c002240c0c451501070070300c0456130142d1103906085c0000400807580e007404909184000080000c0c185c940d0381000442d919407060b40c1c0003403240c0c03091a41c0000e400d8410b4100d40388040c0518420b5680740c65240511800c00701c01c1c0083e69002500f40d102e1082f00049070310003181542c0f49800750105a0000340402c02080c2483c1c010030f600e41c460722600c8100e18030300c49994060028110400c1030a4a15500c005590280780100c1050240110328450091100d8101c00d080c15001032004114901100d00318045610829a480005451034009220031803680140c034158884840082c030544607070356240c280444080d00c01c464803a02c41c00c0025550703400740961000386004a01556484000000040c00c556995101506202a900080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 578745872 1250 578744622 578744627
    0x601090506090609120d0206070f0507080a030c09091e05060303070206041512021902010b010207052206030b040c080d08090a0f02191511030403050a02040b03030d141510 75
    0x1ca440941c180d81e100e4440d840203000170203000c0c01c0e000791080c1d80314510503c0046640091010700900c566200c00c2d12900c040f05084600303100c1c0610151480200300880080a4400da2110075441c0042c40e01d18050390f04c0b6290740d015076400e1482c0d80d0b0080c24a16100c407581600c3e205464010600700d00461620036954046034180c0520b110341ca024484541e0f400540c1340c0503400c0c80b411400403003011035a6900c2000200031082000b4210700040d842c2c00c0700c0100c10350002640302c09407034009040f0001c1c02000174859607140d13445040d0000705500c07000c0010000d00a5800b45000303500c0f49503141c3c005800c0c03003081c0f803034503029080b00e108202c0c5040a102080c40003240d4150b19075000180d40304101418004221414910340b08030b03007c5c03074032510006528100720707100d01e4681c100342e038030340c1001000c2540c55a9203005a00020f042d03900603040490040c40c05d41d0014003031100c0503054a0400c1c1085103100121115500d00c4071080450b1000c10040140b9801d4003440f216084400c0d011640400c00c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 578747122 1250 578745872 578745877
    0x2a0106080f07060e210a0605130b130b0103060b010210060e2211091b0307170a0227040e060906070e0a14010c0606150504090501090c021b060409020301031a0601090506 74
    0x3044603807001c441140c0c1e1509001d205c0381d1b842035007000090105080c0a030840f4008a00300409445442c840f9002c1142c3c01240c40e02403949c944c2103110750413240d0941c1c54000040c12900401c0d07055101d240103000c0b0880072406400e00a09003091105070034602684c03031160034042c44401070980d080e08840c400c0010403801700d1507c40c81090398105203656442c10080d1010f1000b01c034603410f4410200400041a91203031254a1400043d8105103803500d880003800240e000e000a1141c40c1c0c08411403c0000c4100c1003050402103500800c041490a04484100d06040003541c7c8441c1681000d82040320362504000150305944090340c840c4030300340c038245210b110450003845003030401128640907410702100b0f0b00004081e00102c4501c058161a220000d00164418490305c80814213217400000d144086102d100c0b420302182d00a40011500704007070289903a01144015070101e024000801c0d9002a031000d917002c1d6104414080b048401c00d045440c145000a00c03142c1040f0f07511005201c1360301d85400703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 578748372 1250 578747122 578747149
    0x5030d021e030405040e0a020a14012012030c03010e01120305030c0306150d0b011404061707020f070b03180a02010f030e010b040f09120e01052a0106080f07060e 71
    0x4503246540014100d05007580f0541c0c0c440b660080c10311042c20000030b0045031004410303100b19588210b041e5691501d01c1016664610a40400d0400b51455010303183d52007031b072500c00311141c29202c0c400b01d00106903040d500f0694807030203051004030041c031000404025a0b8090800c07428140003442003070740c000380148802400c0202c50071000c408108552264448042111850910540c0714810242200e00034031000d078846002641d080404030b0000c0203607040350145c1d007080c1e9604420030b965141e203460141c40600648110320030f4001c0e40502c4001031201e03a018103580303d0b000c3c1e500d003007004d5285070140e828030340c414041e04031482c2000142e801c000070f26003032501401c1c041b405030b20209501c1c0c01003020303500303aa8005041c0808103030a03031a1503000201e42440303002c0b044809095070303c003141c45201d2400c950307021074420848100752019000b008616516046000780010140c0341c0c1d9642540c2246e8030401256001c480c400d210700300140605400760a1a1426070504a2100d00041c1c10001c2800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 578749622 1250 578748372 578748403
    0xc0303030a0e0f0a0b1605040e060409030507050f06070e011805010e0f09040f0314031005010e0406031b0305070b13030f050f07180b0d1a060103270c05030d02 70
    0x82c003000141034140a00b00300d003c2d0300c0b030a581800c0c0c2117090503032403a101115410781c040100c00303503000054024000c0e5416200c1c680200f84242e0780d80b00902000f4490140150180a4184a0f03030f000140c041001d184130345000300207445103042800b4098022081c06220030305006032407100c200070421310b4120718201c3d40c00f4a03007000c0242c6200081099004d10090064020800d43c00300030500200c00000400399100b5900c1e1100c41d0144860030700240403e5030b5906e000d03403549030308001c41e47c820405c1100030714009000141c17496503941d03010f608809840500c04003296240040080c403000340301c1c00340244003c4c900c151030555240c827191040034a40c00020180e8004180c807400f0302c44104038041c1c86004400c1120f200644403400000c00b00303001031100c4111401c01750a0032182c00c0c0801594052680500102e10030221b06d80305003240d43d00245851304140d80d50107007281c02c80b09194520001005040340040d15000340c02c22201c050095004180290f020004480c642580000c800d80d10100b40c9 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 578750872 1250 578749622 578749631
    0xa0206060d110907111b120a0209040605100e0a090204050709050d02090406060816081006050d080306150d020705010f1104030f0611030a0e0d0201200d020405190e090c0303030a 78
    0x101060301c0404c5a4185010366205494000d650a19014040214070b1b400f02d945180440010380020356a03481a00000d42040542d0302180000c0c806422241d004040904402d80d13061301c030303403040440001c11100700104544804c100f6042d41814811990400c071306d45408007445081c0404a1001e4041c44402806a45010009800c1c000561300100281c60200c1c1070782c0d500702d05820f49020384a01c81c05104040d000320300d42c0e401041e0607885084100c41014085e640d1070300341500d031401c290700020940c0d83c200d01c03203010301c8440804450081c01c0f049005000140c41d040281000b900311440c144074103c10038a444804018114000c1c1070f2801c07aa444003040c010b400803481d003400508911940c484020307401000b07000b4040803680080c5800341c0d55404a548243c1c00000490070b8801c41049404c0c610554040b8030910703024a0024200c04a602002515143e40c03107010541c00c0ba110030032050488044203003030021094401500d50041c600c00010310000590000203601c0303100286c140a11580d56 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 578752122 1250 578750872 578750881
    0x90c0702040209060703090e010e042612040b011a0705100e0f0a0b0421090506091c0b06030d0c420509101107140c13020a0206060d1109 60
    0x1c0342c044803202c08000d4411615900070746405040c000b91809441c4042e2a42c100119640700c1c1304020912a03900107041c00c0001984c0b01c40070300e8000c0802c8000c001604100900d6991420003408640078a202d00c034800d00725894100540e440c28100c41e580c4100c00c400300300080110704006020b442a4000c3d8000003621990403411601c0e00308003410312002070190b4400201804038030001d19104502840c2ca5080e06421303800980107403a01ca4845101090f2001028402c1c0e00300381025125141c000350540700b1070b82c500280c0140c600325020040b604516000c0030820241000d01000b20011411b00300f20310300091690b41d2031001418100e91526034600030900030a88424044188111406083c0146007070500c074861701e001e0710084072245014410f44940f40d5850081c2d02c920350442c44c101d50280d0405481359907800102c1c1028a0084580c820403111501d16036800c807c01c150100090380040e0b5615907407a020b0700303081008143c01d01c0f5401142001000c900c2d284980500da00040303903a00740d19601c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 578753372 1250 578752122 578752129
    0x100f03020310051e090f1203090607110f0f07090b0402030c0301090209040207060509030c010501060e060403020d060219110c06040e0f1801180204050f060a23220f0b090c0702 77
    0x344c010702c000c188101d2400d000d4500ca01203042c40248058400703680694454048070701c42c5d8801a1084141540321000155a281c81900c40c101c80c03841c000305036082d1135141207001e032401c2da01d1000010b02c4e8100840801024405105071416000291015402d6140010a00134180414401c0c6c52000340c0008452046e541d0b9a0f04403800c00c2c0e4032610403c910308284c1c2c00140da0342c11504d1410801e40c64a030010502500840349141f030f5540007058075280600f0b50703082c822031442d4640101c411a8003413003003441c0d0381c0880507143c00f030600980d1844032040d0103445451a05521001503030041408200a000e00000c02040660141c0e440000e0001c544135072101c1854540b0341b40441115510b0010b011005001c20b40741e46110b24022503081c41240c540c0202c0712160101540c009512981040c010401e644011000d680031700b07421400b081c1078103544404210195203003e4260b280100368460a000c608181c03040806403000d00c2010040c0900c2007000c04c4407450050510800b041c00070440784115078 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 578754622 1250 578753372 578753401
    0x1a090f061c0c09020304031101110a050d141608070e09040f0f020910080c090c0702010e0a0305151e07020a030e03010b061b010b010206070504030b060a031208100f0302031005 77
    0xc0c0c2c041e01c020985555110007000075002070302c08500003843e074821079421040c140603400c110047c00ea131940c60641306840954940d80301041d45054291030701602e40b1002420a0400d105400381003a0f000d144085000c01000c0780001407544081c06440840c007610380d2213881301183d200e980400c0c126000c0445042104100301d8120303001f0b50000c035002c02c002e1550710740c01080040710740100840340700c094000f003009103c0c442120f98043c03203907007480f54502541c855200010b2840f40074220218250303d03500d4031803c0c4104071244441200b81c0109100d580d0007001c120b04490f4100c4c106545050500d00e0000b502c1c0d0260100140030454000100106550203501040c804000200b0041d41c5080070844002c0400207245902000c0d460441500d00b1035002083e440d00c01c1c82c0c42d035542441c181c1542c0d030b55030a8200161806401c40c100c20000700000d911050040e0341c040440d00c3e40c074800d00e0a030000d821012940c4e04000605403104c8400c100586001a01107448000c502d40426141da9030182459a1f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 578755872 1250 578754622 578754679
    0x10f0903120915020a0c230607020d0507030b04020a092c100c02010e0105092e0f050c0711031606270b0703020105060a0f090903020a050d031a090f06 66
    0x82002c004681d003407500000c505c3c0303010307100f40002c90b1241c1c6e03950110388003843c4401805c0111484c00010944ea4681134001b480018401000002c046003652030f558580001070b0012190641030805100a41c42c142d00000001c000d154024001d0480c1481e60f000ca500303078802c4443e12030902e0340c1c40034504003040c407880e0300045003201d08120440312000024040c0c41010ba03c0e510715413034900400c07811600441e4400890138100c00f5074050385100e903609840900c885804000c102e54907401408086043e000b02400340c401c01c0d02d140d40320045402c11074401c06886404511980c80041c1440c43c0d6403204a004c0700325013660411182d01c00410600f480c000180141a102000b0000c002046904045e405005054000d038001c2003a507680505001420606008a0144d202c165104022110203504603905451091058070312203150340d40c0d25454080c41e9582180804d40350015015528003940e0380710214803003104e6510381400c16202c207075030b2400301520b558004e864000b4860746203002c109a03500075 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 578757122 1250 578755872 578755889
    0x100e0606040b031003211e050a0c030504030812010503060603012903071d07080c040501090302060904020706050c0a030f020f030f090304080f1f02192a080414010f09031209 76
    0xaa086815150031040c0344440e188003c560b2801d036800b1fa5144a2203e8002c42c00140c840c280382022681043d02c00c1c03034000c4000c50030050104000320001717502002401243c4103a816089031541840101810440300a04190190389807410625804112000c20101c0841d00b001541f5640d940381d0100f410902c09410050383c80e18462240101240c0034001355218141a903550300803900c4080020505200b80d00c03409001a282ca1024000341c030b041802443d03142030050006142810b56a22a802d8503011154505079a201140490307419426000f04440258503200071031400e40381c039514200ca800064065410014894000340400104204a80c0688039031001c0395004044a07020f1030f5120f1314143d804143c52040d0400401d00380050007641c2c00d1401e2040e4440b031144ca401000c4801c0c4402041003085170000b1880c2c5020000014100c90300bc074000d00202e03075a941828104058030328540211030400c00300704c40c40c440f500d070321203d20010349900c200d0000040440401c2281c035011203400c800003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 578758372 1250 578757122 578757143
    0x21c150b13091409160621021b010f23040b0a110f0c0c01210b1306230105030105030a0f03020a0204020c010e16152001050c03100e0606040b031003 65
    0x120569400714184202d0814044925180e800f90300d04170748440364401c0ca004070311800408002154a80250844815040700040c20180c5402c10000d4201c4108a0000300f65540d540500d062611401400310700e650080851003012103525645408020051000d0181020040828070030111134102c030b8417464045c04070b9502c5044049c0d92900d00c1c4e00680202c5050711031405070400550040300c2988001c026000480c01e800c0158001c14080d0440108950340010385440c40e03020740a15100c2e10015180642149105c00071100c1260702660300180401c3c1800402d0004200c103590003d003101c00d0550201c0c0100c0203009514059140126440009600600109508003a060158000c0d0201003241044862a01e01c441000740381104900452262680001380e409095014201c84c50440d00440c1e0307000b480e004000c0115007181c0c01030392500b841032400000e02280700700940e40c95001e024800350481030f60601c41c0000e03402d8401c038415410403440c040b002410580300303a907041c0010740e0426450714 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 578759622 1250 578758372 578758391
    0x20a03170d06090c050a0c020102010603140a05010e0303100b0a2102120a09121808030406090806010617040b040807060c02030405011b0b0c0304081b01021c150b1309 73
    0x12010303000311540c072821618181000900c916607005100f0440416203500b8600034040b001140c1c1c101e0104130680c1950349400001000802c101c801c1003e2001681c09002461118500507080d540c1814082c2c819900c00d000307001d41103524030288c4003199181c1d51141e035100421042aaa100f58400100e800340d0b00c03040c1003864400d840e8004042083e19800403c1d025a601c081e140300b00e44412034050107030b650600000c00202c0c080c00030b00700b5071907078500b241082a0391081c85501d154000d4109000081101108000c4141e0401001e030142c5a10f0902800246d00e5140c1902150350042000c1c11404030030010400340031907a0212410550000001e00a1081a441c065540c5d44188211070000e481c08154121a02c0d10f50503c032039080c1d00c485120b0b140d0316400c4072401d49400140040c0e900700c01c104000b80b8240c4900d038111071442c0031030001503103a07280382c80380d03003c0c500d4002c58019400381001d214000340070081e0703404c80548030820043c1c0d49403040c540403010801042d17042055030614095141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 578760872 1250 578759622 578759663
    0x1f02030c0115360c021b0103021804020912100c02010606260705091009050f010c0203030304060507020309031006030b31030908010f020714010b030709050a18230610060c020a03 78
    0x104422500c46c2c001c2250b141c25280114103c0c803030948914005060301c08119114a0f01e030700180010400140044d103070b0900007015500b040c15000103505a43d98680b4a064039580a0003034030001c20450504220b81c0c10b000700294048445090403052310111000010032250244050325015a00503103c10030300441544090a85141c40c01894440c407101c0001e52007543c030588403080f06a5000d0061401c645a40d0303a4070b030140402818403419404203010054540e04d042003d441020716044c0e000c180038ec50750802c0414808080d102100c6801c9002c100f01c010b00c4c0c01d101c05c660300105014445079150381418100e50503003080c0c00c5905ea0b5400c20300017452103002500030741000c500400300341c0000700800c92081d00b200d4440d82c5140c0c15411000041001801d6a400705a03c0b4641c01d0010500c41004c0c40c3c50920400d1001c0d046544c3d4024080710017001d460344809030030380070201004000300d08028000460400d81e6106030030030850323800802c1045444650032617004640c400c0c140c5070703038000c8200b00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 578762122 1250 578760872 578760883
    0x50706050702070f09141602071211090f010312020102070812090a080d0e0105101a21040b011419120312020c0c030d08070801060507021f02030c0115360c02 69
    0x8400782d401a5400b147c00941840300700c42e5542440c0d00240f00c0640f070050201540c0641c1c6806842c00d1132242503104840d114240454829107404c10045990760541c90700c1003000400070ba0b00710440e841070103030f600000c00c50b0040700c0783c1103540c203400d500c00d40e1103401c07030ba00c1c0c0314050700020640c090200e0048440801c0d0742001000c038034400c000340090f90301c0c8416000c0d09459407040a0754022401590100700c66094020009500c119040014075a207199004c07149001c152401c84060b4411001085045020300034000410b00845102c0c141c4c15841d104081c090549005031001e50a192001ca0304050140400c00c2e01c0e82d200c0c0c102551500c1e2810003e0b51650030030311545001380a503820a0032894490201b60344108480d84079184603909065084400f6040824120b800c80314004a45007142e44820040c0b50390025039004550b1038146030445c07801d40c2c161040c0409145100d41003400029181140a01420f001e555183c207074280885080c03220b0900007044800c810b1a20510040050340800e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 578763372 1250 578762122 578762141
    0x150415090b12040816051e060c030103060510080703030f08070314191503060c020f0a030f030c170a09060f0606140a05130303020a0203010507051c0f1b030f0b03010b01050706050702070f09 83
    0x6800355461f01080c83c3e55110141214074504140f020801407000420340e84c007080d040b100d4400c01d0144035841d41c1c0524603080341034005038040364148030b04020081e8401e0f511355002e407040c070f414003500244480034215002c002c2d01441040150707808000c1d842e251176005604e0002076401c0000300540d00e08007200140900200303640140684001008242070008086d021264140d852404422210204030700900001400000b000941e281102424290500c420b000c3c400d02480012044031318a040002c60362800b4084616a0602d4070070044c0d01d0f048002440207103800c0c45450b81d507070b0000c602110107116481000e402503000386070100900d60300103034220302180f00741c000f004581c88442c01680d03207001d03080324002407201044201d00100702c10342040310180c8003810301207500071240c1c5190b081c0c0381c034840ca81d400203940d500704015071013121b0003a5105100250020440781d082c1400007005e610405401074040d0340c4560124548902c2041507100928030060080c4040c0d455400d068041c210066 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 578764622 1250 578763372 578763403
    0x61e060b0918090a120c0204091a0108070b070b0c040306050106120e06040c050d0512160302071d271b100f0219050705150415090b1204081605 63
    0x900644140b80d4000300341c0c0c068069500205403880700c03035075900300e5900d0003007040c001c0040313000c0f41c01e00686450060070107842c42105144000510341c6003104102405038801841c56001c5041002503402140c200c0b007009800c880b01c9150b5070f80b031545c0c40c00d4502c119880248028036041c000521a40d000b01a0902ea01015405010703e0188007140ca0341e4401c10b9034007a00b000315440d01008585001d0006081542c494030517240040092549001c050304010010026800b580010710700f0998140007200c00782c10281300840546044140d100b00074203004001941041e070703981c04611983c0f130711148290440c510000f100ca102c201f071700b5140d03030011b05010454001c01c010721a4244260245024400c01e11840e8024141140a424140d4400ba02c1c900141c50b94014030401040c652240710809a91008803100c1c1ea641d0b515220f21014400300f0ba204200800c82d40710020b000001c0304c3c0040703400001000445151545503400e1502c1240305280c0104952043c0f441c1e04010003070701140008040d400301 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 578765872 1250 578764622 578764639
    0x309030c090203160e27070f18090b03100603200612040b0c041703071704080c0103021c05250f0519020f0a0309080610030201020a061e060b09 63
    0x4004240c00c0c3d0000703076055046000c0c80c0c660410090b2048440b01600345009203200e4103000401a1440c40485654926180000070000c1056640e017045001c0001c000b245481c43c8010308515041134409205e00400c11000c9d211240710342c0c80d650070401004154440c0004010269030f030b1034801124080c8096040002d5a2020080d00b01e24001040e41c3c0d10b02c002c07a101d00096502c6a41d82c030003800005046076651501400040b0f180c00703454901c0a04039100c00d004680d22242030500c15170944c803066010035400300c200024820290003140744030003150300382000341c0c45501d4000d448a20410600c20061800d2800c2c0400104c0710b44030030003440c110b4079088030802201803131200710390425003103120768041a8100300c00020542e1842035100b10049510660745070304200d45000d803c0600300c4000781c0c0000c80407107091100c000d0600240d80c00a104d84070b85403856195a0010351998800e0102812096880686600b102c0c43c0c000c607082c0020714100104001c0707407103100011182d0450500700303020311b804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 578767122 1250 578765872 578765879
    0x120203040602100b0919020f070f17092101020d020a030207021504081203150306130507091b031e151404051b180612041a070807110102090d0309030c 66
    0x20b9118042c181360004c0c04041d026581c2e80654140d5803da11042d12491740e00f00000ca24449008000c2e19240d44136140782c0e00c040d543d42c1450803d00028064841c25000e040250301d00d50354400040418034000d032184002402604da00050080c025042100c0405000107031600d2199419030041840c030344211009502850b40885001c030b18000c070f004507003055008960300d02c62946110061a40045d400000001e01d912190100781480021344400c81d00880e080350760030400100384176442c09041140300403c400d1001c0301d01c01841c854514660428507a40700440424000324bd41c00d130601d280564030621052050711880f4440c2191031040a021008040000b900d5251034002c8500070140404620120307042d0f144000d046900001c1c1d0a0005043c03040300042a840d0b440c061305c0001811a0701c4055440d040c1041c1041d80d030446001000011404d0030848540e8101e0000c85c0c210041e403030400c03020b52030500d005009210b00000035503c544920240020103911404000540303100c0c940a14103c1d65 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 578768372 1250 578767122 578767153
    0xf0806131205070f0203160f080a020603191416110f0318132c0303190e0106030b13142b0e2d0f0a050f01020a120203040602 55
    0x1901100601d0051409898076010344250041c0c52040d01030030b03240c80c4028070399000038940304a600c0500000c006075202000807011304c46443d00100b41040141c154100e10f50300003040c6220040503411010700c2a100150b401800e40c1c843c20f1425410002b0000384d041c0600200c00b241c5905442c03d0000d01e840050b469840f4000c10404041c0e0707038010055041c25110000306d0040700712200180e4108075102104401000d2074040c1c100d1021000c10b800c2165890a00790100c0394a9181035042154010010b2011000c0c0310383d150700d9010180307140001c0031920700342c41e20701601003580007810b440c445400b0b1000d024819588940c465101d0480c4000c4010615200c80d1108561090030304d58428899020b2411014580d40d00300100c0c052400c1c0d030602c41000b000a03a462400000180300c91555044403034500001101d50359011402c5840f24010404c1c035001401802650081c540114032040740c1c60306d02c1c3d0003000b200846540c014a0500b00300315080d03000b59660824492031006201c0d007107005c0400da0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 578769622 1250 578768372 578768401
    0x402130504151415070515100506120f0a020906040e092b0c0c0e04051b0415050f031018060b0a0b040905060109090f020a02150f060108090c03070f0806 67
    0x1416012043c0c1c038420312100704904541d0300512803028130f01c100802000a5414060030f0b00c2112070580010240c1014420030a01d4200d54108600801c000c03c86041c00000141c01e82c1d0b440300d40703064070380b101e50380e030020200181c080e86040c1c80c0c004c40c0c0031601048059030f4a542500c01c121a0048a00d044502448125130086140d1150f40c10b030b202904290b0114401c00c80c01c1c0c441c1e03000d608800d548598944051812420031070381a60a50081010b90071148040400c01100410480b41480155420000425003504520072244124289042030700d494409101d29044501075a0007007203840b070004c101e444801480d000844605c7c1c50804250001e00c0c5c10855002640d01c00f500d92811300e42040d4400000304000f03007865042c0141c681e8002a210694004c202e4001d000020140e240c91007100d0291070700001800a42d0550151001c01840300308c19802a0b511100900e00030300075464440705241080c0c140303e00d0903058080d080020840c8149010210100d130f5190003120b000f50b44d0404d007618200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 578770872 1250 578769622 578769629
    0x30708030d0f05131e1a040b070f020319110a060501080f07030f030e18090106150801120611160c050f06030907050f010509040501030b1b040602150a0605040213050415 74
    0x1058a00d14040200d048000800c500290301d120303407100d09034107851b0802d103419003241451000c40100d041104111440d2036281c0c1107050750500761814000000007a403207005005941003004448001c11711914404c01c0501100c19114080c0d840c003224505014024181c24007d1885034425070740e90b80c0680c5000a5400c08581e0080c00c10410219183e0b42143c042406c450450ba00c42500810a40c600749540003d90280500000008800c0d00d000305500d81034894101250074801000c0c0108040790610b940010f000d0b900500c00503a00545015001060244412801c155443c0174270354002c02000c11240b009542c4125101080e485a000030849103100844010081d90480201040b8a0608084c1040b10b01030506025080140711000b08003100d000740d0054911541800500210528a2810301003401c80304040d0351a1901f0190007075500c01085600c0c4103135a00502c0001e2012a00f580520003605006105660714541d060850301c100a20340650742c4581e00e0444c81100d1514414040d1084 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 578772122 1250 578770872 578770891
    0x71701091407030506072001180b070f0203030402130219090501090b2104031b0501020904180503030c18040e03090f041a01050f1201080a1e030e0904020f030708030d0f05 75
    0x40c0c0e1000c0e0111647e007070384000140501c210b80c1d041c00c1e0041c400c0c040e11030b42c21001c1c5541c1c407161a49041070707034000340f0180c101000c0c4208014680012070b404800c0fa90f21940581d0b02c0101035605152a80083c0710b5402d20120301c1e209420721025131a030000e044c0044400907601c00c1c1d261901c900540c030f1a1310491452440c80485a8000b512032480c8807002540f05010381001e1320301c100d42903086407104c1d99106044846075400261203d05242c2486400c00c03411900304000e0246c40030b6031301e07d65288000350800d1145000801da201003840e41c103041e00c803030602c054024405440804010350340c94000c5002240b03e42c40100d0504d039107050511800041c00344910300c0c0d18080c100d075001500d1a601c0013020104164041040c181c81013000840d42c1d000702040c200a00315032080d070511041c10390f81425400041da4201844501207a03000001d6615610100c1c2d2180a079101c62000484e020904501c66425010b048030000c0c4104010000e0101003141a000340003e8000309809000c44808560b039541 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 578773372 1250 578772122 578772133
    0x607120b0315101d060f01051b0a14010b0d0804060e15040806060315071709190605151c0f02060f07060203061216030b0601020717010914070305 64
    0x210a650410320003504094103891072a802d2807610b00e20184100c034440600c545a407001c011410445500c501a0342d04000d958050381861000100e6125015010504111010801d03031b00e10701c54018100303142c641900884501c10028030306560f040e848243c01031015480c10000b40d2040c20706158000f0070701d83c0070000034a81400c00c0070540d1011940c00c0803a4011080054141c040e05441004102400d40100148528035001c0200740c94980c84032010f041000021051002d5190070130110b154054100e1458103182d0359012550b460100d404011020b854070081000003403144a502107030203030030b070580504655481d400c01e0108080b10229020442c0c00803001d49404205401216030318184000c181a180a000001c5101c440d0020a02a030340d49a0004c1070051a2409181090072102d04402500b181c0f509150706070085401440054560300400002414170380c4280542009032140c140c4401e62680210340c050300030011600d0403540b000c50110000491200024480c00b100d134132600518 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 578774622 1250 578773372 578773397
    0x108040206210405010617030f0d201902010b01090e1902040312090f0e041a0402060d0606020106030209010501230f1611010e0f030c12070317030a0606020607 70
    0xc80d4001a501c550b00b01c03080b5018891032101c2c40c00d460140e4002c83c00402c041c1c1c2004520742c1320b0300d18044414000c1d4010000b0a01c0c22581009443c0164021100060031290343c142c42c40040043c40720b010084000001c1c1c00c0c0300d20100340120f211180741d80e8001c208400d804001076401c41064050482c3c2e006000c2c001a80d070034120041008138081e03002e0090305141d03407940c5444520344003424a4011a03a01070082c4411180901704038001c00500c91803100350304080c1c40e8040e041c000d02c2e0054a80c0c02c02400010305541311541252400b229082007001101d5071154000d00820b03075030008038441c07580072000140c59131048500c81e0b4103041031030700b80700642508040440745a00c04108007034464018445802401008085030f42103c0c0690254500b080c020000108031290302e02145d8070915040100c2c02c11a100001c04140101054070361114a1500c41702403854807641c0c1c2d0000345410b4500c1c034030616524a03000590301800344070500303002c6140c4604099840351402c803100300008280c079200c41e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 578775872 1250 578774622 578774629
    0x11070b0c0a021c0c0b07120c0804180b060c070f240c050f0d030f05130b131a070e09131e210906120515091e0f0709050f01080402 57
    0x141810301540b83c02c09501540d5031803000680c1540300d612035240114444060220541d40c00107090714030300d0030058a11207039860307000c21301aa000f41c81c0c55520400c0c0108801030f40da072100c03104c2000204226150785083d4800d543d181c28074010002500c5040000107011200034003040369001d00d981c9195040070b500c13075044400c5141403400b80c880d4070610742d00f4240960140f0a1003c94403013641d01248580700d01403a0810b5442c06898a007400d041102c4850109c0d4a484007a40c0181d6082106030050600b0300b0700c000103802090001240f80081c1050103041d90300084116070803001070b07403444000e030380e0324201c2c5580c12541324000e0200941c80d041c20111035032036103a400c0c030548a0388120840e02c804034541c042c1000185071a0000c58030420091080700e810040030384072103480e68024402850712001001800404603c1a406400303100b004c50f42d40c1e45060450340002442c240303130f80540d28141c40a044450802d56119000c5520000b001c41c0d0b0b414000000900c864040e1581c8440d6111a0b092 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 578776978 1106 578775872 578775889
    0x6050c041511100518070b130e010f05100302270f032b0507051015050d030f080744060108011205010212010611070b0c0a02 55
    0x21a54490000b0310421000f852240814180c49a001d040000c900002458019000f90f5401250162483d0090200f507240501340c4603c1660780c803580c0f03000307190078021698820700e0b1201c103002c1030404807200c6101c1690b03403800600e0201d00a2152194044681c2174102e04d154004000b0704600d05000d08000200b4110042c0c86164040320020950341d11b8030b03030b50000401007480c0b590340282c00f800035175100e940c00000380c8880440c1c011400e8000c21a00f00c100c1401d40740100045000c0c18038501028600ea07142e00c0791740c0046140c6005075134804005162000300b1505111310b01c054a400d060501c40c0864880a0050028505407100ca188440d1410510b44142c0b600400c089030381d00c9424a411a509071000c080e1248150411501922680c28610f118009220000840c0c3d584880c6443c1074024000036030720505d44a0003160414800c2d004103a03126800500b0080240c03900454 = true := by decide +kernel

theorem cover : BRFrame.Cov 578597122 578776978 := by
  have h0 := BRFrame.cov_init 578597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 578597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 578597122 ≤ n) (h2 : n < 578776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
