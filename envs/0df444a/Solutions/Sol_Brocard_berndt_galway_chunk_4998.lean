-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4998
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:24:47.543911+00:00
-- url     : https://prove2.me/submissions/ba3de09b-1699-43d3-9dd8-f8f5db6bdc9a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898741007 ≤ n < 898920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898742257 1250 898741007 898741009
    0x90913110d051b040b0901120c0e090105160c050705100c0602280903030f031a0402070516080706023c030a08150d02040e0f03070311070501020a03020304030b150a060e 74
    0x3c00e40311510303407059040007202100c43e1940100341c0e05641c1c5a6040901400c00d03030420503a1600d55502000e02000c0001c20810147e1041d40514003411b4107042451031070200500885491090440280c16034121000410951410f03e0007001555014204000e070b54295032200303012a001551949940b0400c03559149400c2000e64a008290307905003860f00c0b100707085842c02441d503915110800c0601d42e448400c618054034041121082c080014400c4d9598a810301e8010784078a10680b1420380f807420201c01290b140804102c0308250740b4698001c0c54220410080b0100c20101d800300340f00340200010841c044851144075402030b00c0d0380100116551450010010045034004061031204072410b00a65296500d90504205441c0c04031404100002c82c0c2d4407250620303401c11001459840001441c01c10180c000a01c9a56080341034191903c8503512001640c842c0521100100141c00800013400016007884e809500b0450000500000b07104100c04600040720790f40000c008100019510403503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898743507 1250 898742257 898742293
    0x20118031a0708070203180d080c160f082a0301090507030314090607020f0301150f0e06120c060c0106050a24031a0d02031f020307080903090913110d05 67
    0x40030b11854101c40510b06448000d490b4082d44c01a038a80e0482600d13000c444d562030301d4512104981120003245e4030901000c03c0b40d40c0b0b0b90408140c0407000842140000c080112a00b660122a0710700003030100f1141e1000740c040c4540c07664a511410000700f1100c0340c40b0f0b4400b446000d400c01c0c40b4074001c10216045050282482c00c040110b402912000c12021045d602c402c41500d680581c103480c120321a41c80540005e01415400d90464208141a2400a00d0140c3c2e421040c0881300d1184a00d4025202e5000388550600001c00c80a81d070361080b20500c6584c200040181a80f0030008000030f0300a8488000030300c0c940c92030f40840b4504c40d4038104200b150000005c5d001070810725040801154080c619032144403d1140802c900c9400c0801a51065440a110442e00c41e0b20007110681c8a02e41c0340803035002500203403074410002e6038220000d51520400000c036080d0283c01451810f8a55414511101c8450400340448880c10440040b00c850b446000941141610980242c4100c46a03400b0b0012 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898744757 1250 898743507 898743511
    0x50105041a010303231b100b12030702150d0212070f031406090a021204050f071a03041b03021008090606151215122103090d0c020118031a 61
    0x400319201004000194001701030480f4146451414804a00050003460041c00340302d041202c9070704011201007a40501060711172800781810410020900b0070b1080c003c00c500d14140d441c00640c0b00b0401580545071285100c81c02c2d603002d0548624109403109880180d8003c0c1106548a43d012010700150f80d0700481141084040c9150402510950001e032036115880940030070700803003212011840d01660303601210015200c00c82240303c0d40c02d1902e081d5948454060400d015401544004107401380f03030f4203008078800300d104000c5066484541303511941d000035110800d0110240034000005031a062444000c00340c0944426040c0c0c0f600a125074200b00d40140000d104890314007200054692800984085000c1c070182d2a50507954a001510440c6080c0c466580c042c1128840d000c49040000e800300c074125036424050100c08000c082c03c0b00500003505d0894103600800f0301c61499600c91041c4800300740c01454841c8170001c4590101400b01c219402c01d444010020103800348060746100300a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898746007 1250 898744757 898744793
    0x1b090d0510180b06040c050415020a0b07021f0b0d0c14040c0f1d0d02031903030f1503060506040f0501142701061412070f1d060414130905010504 64
    0x8420b02d0b10599480700c8150005080a01c140c0e5901c1103445090f00c82c400340d4020b0114003a4030303c180a0f001a0103950b03440c84803021200c0c040d0410029451b540301150440c0b03035000307046014a18403482140b5202030840b640740550400980b440040104411800000080c0440b504003000442c040f0288410748801080c03800501402015013410750742c2c410004464580880c2e400f49003041c181000420f1844405030103541841003141204031100005c0c4030a0f10750b4400e840070085460046c0d0301c401918404218011481541c0c0800c00106440360405d95114100401c001504400e00c1121011a4428bc0060b440d0b00329407040c844c941c0c18400810f400800000754148503043c82d00c021482c070703090140641403c000c1184c0c14585554003044c195030420b25030200c000c010303140c1030070010b08400e05403c400000031303000c0030113181c01020354401c0c0f0484034019204e01d2401d414403d07000e0300320050b00e4489030040740c000b61600c85c5200305d2007101d070a64030601c00450582094180060000c10b411000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898747257 1250 898746007 898746041
    0x91b0201140105010e130203070305090706093c0308090112020f04330e09130b040b07020322150503090a03030902010e060c1e03040602061b090d0510 66
    0x601c200c04440700c1524115030092801c000c40e00004804610000300e004c004804682c004010f00410399050340020748502d1800c821501f45030303a960400c5441500900c00c0103901500c9034600808019503003411184554048043c80c00d90980400c0700c0f40514060340166072850b00801c0c222010b6078402241c002c0600d00000541c20801010075280c818403ca108007403628182d0980c040f18603104412070545c45007120000b900c4851283c10151040030f001e12201d104003da0000a48440781c80c4481c507045640000e003080382c0d5a903569540324600005042e000640c4014001c0c0307400065000c40ca04a03001c002c80000407000c0c90042d40c048903640c4047c001c0107000c014010031140c05070000b03808109036007510780402c12032403900050300c1c00002104000d8020b040011984154800002d903208101c1a1100c51070b800703c2000d800079200e0089000391130040c0c0111001c20041100141c041e01940c90840003a440e2040110004110409941c02140c0310341282c0d268050f4003007140300f42c004070742e4941c0300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898748507 1250 898747257 898747271
    0x15030d09091a1c02010c080a0909060501173412050906070f0e18010b18150a0311040f03120809070501050a27093204120c060501091b0201 61
    0x90319110456641a00b0611500c100505580c4138100048080307030451b29041d919000d10400800102d00ae018071391849052882c002030340c4d489010700030040900084440310907100d4400341d141c1d099002024136106820b220317921168101900802111040c00e484000b9004122034070f032016039000401290840c1c006c41c040000103504135003002200600340c90142d80084c031060000e9015010401000c00982d074400c00442ea10702690020320801d03454103140d140c0301d2059820001003c0d001d8030300d007181400c10b1105109042c081c0d000508082c5035003140c0c50070207446030004a14000076600a88800004100220b030007038010fa12150085245400350072410304042c0060f19502c86c4250034400c00c0f00000d582c0034088081d0700c181c01100b0f010500c5410280d40c40116a02810664070103540d81a402c0005100c643c02c20074004070765214805108009036510703100c0317100b4031025845100600882c1120480010310a00c02c6074041c1c050303503030009055100e2440c480908404014a442176a14150f9 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898749757 1250 898748507 898748509
    0xc030a020616020c12190c05091b0f0a1704031e020d080c090316060e010f03020c0d080c07050105010303031506020a1a07020c09012d06080105040515030d09091a 71
    0x13950030003100055903180b01e114000c50146103880029550f544120340714444c15020009880220400c42e41e044400704800e880d8450501d091046001c504050b072001006503951480e07090014001024080c20492502038400c101140d40304421030702107000030b40c4940ca041c03609004180b08400d2884620042c43c0c02ea1116001814550700900140100b281c04a508103e540c0c5c204401050741000208125101d0340d0348802401d510340704007119011415140301c1540c1c252281c42a546045910f00051002d09403021050300c8034540900000305546003000032a000c00e40074018039008500c40e03a000509015000c4401ca00044940c00007011900951a0b41d00460300244042d0b4080c184101d01950700d4441361000c0e0b01c1c241c00c20a88031b070080110400011525418221680548003856000c0c4c007444a000104400c069103003c3c00010804040c01400700e070800b54003640e440090800140e0710764070781c3d1000901c0c0c0550402c041000445401051100d0030b00790040b204003503110383d184080b5011483c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898751007 1250 898749757 898749763
    0x18060503100e1c1202090a0b0c060703061703040b0c011805100605040e0c0f010e180a0c03060513090c0f1401020c120c01050c15091c1701060318080c030a02061602 72
    0x2080700701348640100303101203641d580d010614001c140e282031a5598441c030345d8050361200c0c401c58a000110345803500000381c20800050000c4007010600280d440c29003000d0b540c02a640002000480c20341da10941c1d0b001e5554201d10203019580240024400081c2c66141c54041e03e84035000b141c0624109003520744034030030000300f8940f5039808540004001c03000340012174850000108555220500c20854400103554900540c059540c020042c0850140d1020941c2911194420680c20035081103130002c1d54141a803021400720302c50b01301c0c4c21055554410040504043e9084502400e4040090703159560701044101c28140342039607031542103c2801c00352034960007454030140c1881400078014101c540203008061000c031049902208034103201501c1c2d5560302914000c0500c00340082c000c440c242c0d01400e01441c83e84080702508009a00f010001c9014010002c5c0200450451141810000d00040040c198110b41c0c200159103a20500c00000c5c5041d00c0039085101d0045074221650ba41f03a408 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898752257 1250 898751007 898751027
    0xc0a050d12030b19030611131e09020f120a0614060901020f0a1a0c040806130503070b070206071b051203070c0501050c130905060a18060503100e1c 65
    0x1d010708000d4800203100781d015100c0540c1d000da0005501c0c01c0d22964218a15100042d203008200030482807810742c101d0343e12072140ea1024a41441490790410071554003800030500c1c50b0810a45810b000d1341c41c491642a0f82060065003d001d0010031000744903442403270820360180c0701d10403c2c041c144c50883d648460164980c1107a004120000e843c0149900070000b8540100540045a0101e0506d0400c80c1d400d1a641b4460ba214102ca0408030341450030035415603080e00c0f070b100040d02003030304d41c401c420180f451030341011145400244008004107a140460038410511500541641e203400840200000d03042d580d2070821a04554800c004240005000566413080c0700b14645d49440f0742d00140c1d041499028010220760900c010482d00c0e80d0a1070290103001c41d540150b41f006074448014106880080f030f5031710780103081c1d41d504000c511801d500c42c50b42c4d00801c9074001080ba483d80013003400c1195034034105603119121040c000c000030003040314281c0e050891184143c00200181c3c0100342c510a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898753507 1250 898752257 898752263
    0x21810030503040f0e34090f080d02120307050901030b0d050319020c0117040204092a1508251e0804020a0b0f1209031c05040b060301050108070e0415020301080f0c0a050d 75
    0x5000420f071b15180100c283c1d002409490805040b1580d80c0c018840c3d0317441c8680103007801401404001c1c07848200000540f405603500ba216541451407a40044004080303411000b0b501a00c50b200b5070b000300f1000d01c01042504103611001041848019000c1c0c90480e082c0f885070304021513502c0c0d429008036011222a04168102e501184807085801d002803c500b03d41010446a901c1400d807036050309001c46070100326103640c803260165408505050300c860f20110b13080d800d2080c1404803c2130141412030840d19900306410000c424200025541c659088602c00d6038000c10402002e200540ca000814800144805030b0000d24050440440c1030381801002000c0110513007180120b05001414410348030280c140003a2200c034034000076607043c00b07090155001c0d9682111640441d075203040c10302a039416200048002c0a215150003629503040710001c20684014070340300240c0308040c0352030000b180207007640d100414145030070707481c0c01d4142201300b49454403d882201041000c0d0312030b0407000001c5a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898754757 1250 898753507 898753591
    0x90f0308090609150409050c04140405040311032b02070c120f0203100504030e090420040605031504020a140109450e0a021810030503040f0e 62
    0x142002189183c05641020b503800360881c0020300c07071110044080c0040702c1a2070700030322a9844000401d541449036000e51010144c50980d10101340c00c0540215030424424039140f00b86854142201d82590044149030140300c41c046541c0f180380c550340f01c8601841001500c218a4800250f5404280940504c02c00b1900ea200b411103005214500c2d00c07409990381c02609a400b44900e91003c00000d20085408038081082c44180395120708003400c03503a200719032015902c003208403a040100007003446c8200450703116071030380c2c0c010405032018402c00d800c1c00c030407000f00702a07030030640704101d003003501500650302203244883c0c0030b80c0c280ea00c4041c0c44219070304512865121a04d9603140840001e281781c2414242c80780c450300401c0035a642c10414a40010b0b09010001d8002d00015030752200701403d0080c2d84800591100805c050746103040917000340452700c20603000b907501e5803500e0441d002a4402160b0344600d403010041090311440b41c0307901c1014210b02c00140303a84040c2a64290059400868a60b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898756007 1250 898754757 898754767
    0x30f030a0818010606090e071d01080c090a030c1410170a09060c0207060323040627080a02010c0e01020a060509011e0231030816081216090f0308 64
    0xc401003161070312007142e500a04c4220346500d4040c0c061a6a41318a088142c004d00002c2c84442c407841c0032010207041000c0601d802d80c8940011912404080c1030314541580810900c08250345100714200110302c160800c0c50054030b02055040504d1074464014020058403500b140b400380c1c004203507400e400c01c0201c1c185958841400513002402c18200c010000c40ca0000d11540050b00050714000b01c030350300d0f6014400031038500d08041c96a1189041801e800700a0030200700065419004500c00000d540340300c510070031601e0904a802c410b40358090390071900001c0e003684d0540d42030140030b00c2000c0e01e04040380a040c0c0c50000035528a61a5400340000d0b40c0d40e004590780728003c1d040154001c10005101d03403001030010101d4025030190b094031240c808596406050b20b00e9601600590038022610030041a01d151504c5186501c001c542042c2d030750b1708800150026080700050701c110340c0034502142041c60f0044900940c200c4015900c000d20440c1d41c0304110010108a0704401d40307178080201c5c0c0d141c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898757257 1250 898756007 898756021
    0x6050403050d02030a0b090612070603090218160e04020a05030f060d14150f0610050703050f030c0c0d08091e280b01120f060e0316061a030f030a08 65
    0xa024000c00c541419000100740300005c40240c002c96040d14044403100f043d40c840c1c0c0200720951203e0800102e81e50003403c41040458000c1d48161034460000d003e60a114010004c40300d4550000c403251440c2342c4441c840e6480c0960322884801c81c0c0002030b201185003070074151020300035000c0200042d038002e08410020742d2686584544c60005035011024500c241c0c6103200440c1c940d0455084c034907641d00007030f0002e212a20100d85160003480003904034092951007000480e2241d014650940501000b0400c030003422314110000c51080000074042a192002881e0050920840030715013010440a41c052052084011807601d03110743d004407450100386a80400d00d42000701d40d0318030380545120203100087c81840c1c1c40b0034a03032552003104d01c1c045580c1c841c80c20b46a410720814020f8200c0001000f107900040055114036140841e80c1e08032814806101002c4804124085007152100d0316801c2181d240d54503801c0d62802e90310214041e118013a2558136040da41d0007407215000070801c2c1d24001c2014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898758507 1250 898757257 898757267
    0x1202060d0f09030905120601031709030f060a060f05091b09040e01020f0306090f10050907171303020706020a150504032102090a0b09030d030f020d090f06050f0f0406050403 76
    0x1400e150800c144490a0b60381800b52400740c8611810340503182c40c9509040860000c207516050366401702002c0f44520030316090040c160002000d068151140400c060000c1d41c8c1085010310440d000000440c9003401e11180f00203045041e4403c0b4001d1507802d003400b08100b2030011a1040041da450550b440f0400380740068003034030105a42c0b021a520004070042c41190f980c00842c816801a03540220944503016840c0901c101224481e17900d902001c802e0056160a0622a40020240c03900043c407000711040aa010042030b5840c1e450300b030750403c003041050307018450700c0c0041000b1f0018010f00841a00d9146090f04401d24510005d9900d000003000c04d80203958088944425080828032101104040d000940c0550f0f04240b02e0034514030300090070b440322400c442180201a0141081c0d01f001001036001c2c0c00c801c0034400205d50244880107604a180c0304400116000b003c409c180980c0f6400c00c6011030350090007c0300400300300c0c81003080028200b00d809402680c40390001030250b41c1c0d400c080316 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898759757 1250 898758507 898758521
    0x80d1e08060f040216021801050310020d0b100c121b14011103240f06180f030f0106060909020f040515040f0b030160031407091202060d 60
    0x50f00a1001c61410700307501040d50311400c42e910a640a070300d4074034410341c1c0d5062500240b00d41d5515501c5040c41000412454028005903c200f8101080300c420303403400180a0f4404d1104200062608101d0700140b10326107003a50300500740f50a040045444484184140c100c0110f4081d01f900c2a9042c100030a8200358802e280c0140d49074102c5480341040e00754041c01840c140000f00c0e0b40c82600b0a5400d1500d0100c00c4d6074021200284998078040c415401071203040100c0c404654002000c0c1c114508076103080c02172011001c04240000f442074100a00900304500680142209a20500a00210301e488504540a5640032201d2501c4060300251030313000c6100341c1d0001003504001e660000742203441000514140d03040c001000190481194143d0440061240e47c07840747c03001e007282c01d0038205402c54002201e4807810f144c40d00280801030680b854042c003989450000383d0f40c03103041160001000360b21790000300600d00024041d2501d648100c030120b12440207441014001103c80202540764000b007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898761007 1250 898759757 898759759
    0xb0f04030c060f090603051501030509010213030b0a06061e2f0307060b0102030310090c02100e06151f030b0103091209050108070908280803010906080d1e08060f 71
    0x1201580c0b11a002000c02465800343d40100e040158086412402401410b204659041003c001d428015004401814016094213a00d5501308014810f0000071450b460207075008443c1c0107842d0802090107c202d51300f0f68003010400030766402180d04004400d5100c00c0c000c14601e480c00304131700d03041f24040307030720040213032103c0601c5e0740c0a002200454040040c003c410700504080107040500001a070b160300c81150740070038000c0041c4003071144500d59171000008110900c1162034000301c0841c4041240d009002c007030f07901ea202c40c2c20013003000341500c83d0740076980060743c1c44e84d00300ea240c0c442c82d00d00340000d2110100f40340c1c0790300040300c01364425446078410fa41c20034082d0510904c0840d0150520b5003c1c05000d00180b9131200285440b806082007004540c0494002e1032401e424030580000a141700d5000400440143c81c140003103864000914040c0040c1480050741e00e16245030355241588414034203007840039105c000c00c0c4808070b000800f411204141490180e90b9504000115400c0a0703140d11 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898762257 1250 898761007 898761023
    0x1404060b0a0f0e060102060c0f0d0e1f0203010807150507031d0d0b160305091e15090313060f0e01080709030605010803180409020f061803010c0e1f08010b0f0403 71
    0x20500043c0b004240100f0003a026500e40762946280c0748010310428401408680d000c1084e9500c8510591082038052180415503180082000d550540351108a528500040c1c0100042c0410701051281000400040d50398191006480300058101c0c020908044c0600480f03201c1010074450703800280000c0d80f80141503924504452030b20501a40c01607480001c0344035082805400280a41b1566000d510600028800170318442d6403000b50b825080041040e41c0107403181801e2844000700c003540a0b5211501130340d10340c0007010b1b0081c11000307d0b520910070800d0f1040f078105034640044640c42025002c0c80d1418041d943c11000f0f88108040340c0c4010900762822000086013400440079014140c20a8100c01d42e0518107002c0105407110b800010354401c0c8400b040d0140c070f2508a00602c1c4411600080c02110510b640001e030840300c03009011030100300c21004041c500d192001d01c10b03800215002a011a490070182c0c01000100140104161180c5c0000c0d10508629140b046d14025507000b000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898763507 1250 898762257 898762259
    0x2010609230c0d14131a0403021c020f03040f060f020606061801110607050904061d0f061306080c092a0a0c08180109050916031802040c090e0a1404060b0a0f 69
    0x100101e40003c108081d41c100c44100e0003506c841328200c036210300458140d030003401803001040b0072404a400c5440c00c44e00307500c1005061210b42e201070010b00000c0c2244100526000c2c507000d800b0384188015103400d021508004104030f401d549243c02d07904103415181e0300071038403114040141c9040c0e00c0d40f462a421761240404002c07034281d12074020280c40805031014400256607000c2402d000702c1c0c140c0c074000c0030301c81c290000c0d5195207010541a03020000038008d408440b0f4928070601269540e0308024001c2e001807a1040107030801000f860b4101d040b04511243d503d8801d40304014044454800807540000010500503091140c900b080c0001e1b04044410382c2c0d06055483c1204461301d5400250100c1c281c50000a0189001d0780c100740320341c00d2400704400304031191101301e000b000200395842d05c3c2010540f0410150701c69206003800b000c0d460300c981e00e015041600c00c10002200501c01d00ca205d081091030b440e0704441c40032850b00136600c00d00100b8541c4611000884010950f000b4032681001008 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898764757 1250 898763507 898763521
    0x7081009031422350114010b0a08070c021c0606051201020403060b0d03020d1b0c3302070e0604090206160b0a1b0509010c0b0702010609230c0d14 64
    0x2407440c903c044918068110383d03440b403c80c041c0c0440700c0c06130300e600c80340184180d0032100d99034980d0034030f103110600018482220001228030320400703810000b0204800300d0456900b981042e002608220681041e600c00384656000483d4031070f48100e400c160b074120081101c100b00e501c1e044500540300042c84a100504948505070013500144030940e0101e080101e50061410030741c10740c01071a078044c1d01800600e003600009507281018005098440b8007141d00b00004107000008200c06271039a0007201103480003181490745441155410040000c0300c0f05460042190006011000c454846450b840140e80f444001002401d0000303001c0c0d00100b000465491500b00340d441640450f100e64040074603511058000c0c030454807100b081f518044103900d0300c039101500a001034010b00030145020300c140e440395560140004000d44444025039101d01c0f0074420000e05010310100c264003848036104500302140054a140317000717070030100704031000203001c04c00c55007030b0300201c8200500030050445030070000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898766007 1250 898764757 898764787
    0x1002010905120307081f05040207210207230a0b040801150f0302031506040b1206090c010503040b06040b180c1c05040b010519050d08070203010c02070810090314 71
    0x3031421507030740c016031401110040d04030003079902500c0035995541d01c50b581c001080c1070b20620030080e000c2c041140c400024282c2c0e640c0c001840700d070b445a15100503c00c0c400070308244001d83d01c0280001c1d904840c405000303d00401d0043e0841440a000e508001381c480317030100348a24070a4001010383d1070001000b0800c03040540040c0c40380031504c84a082c44956880554581c0b01103400000d40c1504003020b40340400070010b2800703030000e6004000107003401100c00000c14cc040d2840b14000240c0054040102080c07040c003d1703d00349002030905501e149450740c1c407940b0750000201002c1c400c42c1d65000090035034503154400f06482d220800101405d00304060204415000340204c07000504c00080d034844401024001c40f070040354403100740c0025900f41010082c1a0003035a00341c550044c49140009040e86c0c864032124915802041d000b56030f2110b0b4014142507480703408031501590312031f5000304003104000070011074000c1c1001c00080c01c1034562800315401d0010003071040c83d4030000f04108200c2c49070b030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898767257 1250 898766007 898766021
    0xd0207030f020d0504120201031d010603020f010e01080f0405030f030103262704020c07140301050717010312170106030b0f0f1e060403060207030c0b0f10060f0e100201 74
    0x65101d000500c41d200c00100d83e80c50703060b4400c0c40007410510040101880c03000c8200d5000d481410045221908003060340c20b000491401405107a4503100200198149002a000240828600340c02413030703440800a4510003010300140d06a0141e280000c06100d400d00940d01c42e4640c010a1907070b40e50f5a81082e00c0d08260700507c0c0002345845440280c5820103076021106141410042c04050180803040101e14150b55404150040d4080040402d510004e001240140060702d07603c01540c45110103040c01c40e01d000b0421400e011508142c00c80d51900018624116035100c451001d1880707410304100c804140780441d0007034007480c010000c03940c1034064020b0f0104910580d211200114103e0402a81d221310004a07070f005081401464070340003407148015403161000d0007031032801c2d9480e030b1910704030b0303120362000d40025000c50001b4003084800441584c002e4001080450b681c285441a07410422a9210300c2081c42040105031400c035004000040200400800c001c80000c0580c1d030181c040c2c41e00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898768507 1250 898767257 898767263
    0x6061606140c0315031504230f010e10110306060304030e0a1d071718030c0303040b0609090a0c14030a1a0702010c020105190b011103071a06030316110a05060d0207 72
    0x300800601c4c450900040342d022a0004e1107907641d0380d440710746030401c9400c1c01c1a100740c102c556414051034841703800c00a04030303128052400040e038240021421406c00ca480101401c2250410f0b20b01055503000c03205507a000202215959982d845c4c1d881d040c1c429180c005e130740c960803d400c400000741c06556102c0c1c2e0034402c6103448450340c3c10350300c554044405c0b01842600e81d00000b2003c000c20300c0c4031003926041424060b020110391820140c45140c40c43c58004071400c48488051000f000030500381001c406420101e000c0090054001035600d17502d2503492401540c25140e80481407090582c0c0406c00e400c0440e400000303146206103e0500e1106014003220500d0143d03003004a104002441441000d01c01c2821400c1d8048001e00a50001c0243c143c001d207482c1080000c04a428000d0018001014120310038910001031040c94098442900001042107200b5001800509010700748080c042600c1c1da400581c500c0100914000603030a500a600070580050020616044280c0b00740e00814007140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898769757 1250 898768507 898768531
    0x607060f0b13020703021b0d06111e0a0f080a180302011b090e010513200304110d0302191403041403010f0b03030a140d09060f0f0506061606140c03 65
    0x150803039804050340f013207450050061703002c1900301080700702c06151032010080061905012200d291a240c06545040503080d555074000034005600b58450020005d1280308103121a08003650701502422000603c200802808038031000526a000c480c1d105c5040b0600c801c401420040b01400d0090007082c554401c0c502034100390200c156001e014980203401c840c1c1e1078040c18460782c200300902600c2c600011009a25030345130041000c8402107801a8560703000e0303009400381c40e03203000e052030f208401140500324003070104940d04501283d0301150380c1c40c500720031645e05002c008441c6004060340d104400e00c04d400d408007160119401d80241c02a00c1d40300c0d01200280b10204501100f0011110132030001981035204000c1152614003c100003c2c5050b0405103480c24442450b039a8002d94610541c201c400c03d40c0d83e00c0880c520070140c480e0400845032034004211170724007203010034002c0c0b207441210407002a250041008100c0940c00040030040c01910411450924100e01d0700990001c1e41e40ca000700c1c0b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898771007 1250 898769757 898769779
    0x207031809020c031606110406021c03050f130c080d030c0809032802071d0910110a2001140f150f060703180f091a1305060607060f0b 59
    0x40440c002c2d80d40343d003180d402031840d0211440103802c1d1342c048010100d40c450780300c02c40e0340043d101400c00781005003100d8018103800840390b80307090700c1481c0208205092500e40000e010b5075514201d0401d9110010781041c40c40680ba40c1020a032040c0140d002d51007500c28030858a0406d54036800071044040181c54040c1c0580b243c05c00c0719203034082c400100c40b030895401402c0c6609074108a0443c801310180c015202c00360b0f00ea000c40d03400500e1140307544030450a804244008260100403000010501240c01c11a049500342254100d1150401503401c020704600c0150341c00307503044078105101103080b00070400854009044840746c017045940082c04200400090302d4020807100c0760000c0d0324010141102030004008120494100384401c0e0200000d280b035881031441e5000007034014240482c40e80584514202d12a0241c80c0740e0003007051069000441190035484000002c612a411000045040e03541c08000c180640103440e0080c10310342c20012080c101050b160f0010300c280905444d440408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898772257 1250 898771007 898771019
    0x203091306051008100b0c0a0b0901050f0105100306090f0b120a05030a18030506070e12010c0c02120114100f0b0322050c030f03040801143702070318 66
    0x1107106108041d04122261032000400e40310340d02c0c02d0740c81904606540c20322074039140f008900d0f40100d1103102050340844c10401c144032165403044c1d80540590001e0116180400a2070074448040c402c40c2d01031092080c11200290191704241c0c0076040710182009404000d8a0f0302d00940304600c101c07402000c0b1408c464921100100d1584e45064104004500e045005082240d000012880808924034000000b000040d014080e407809100265a80442e00c1120b204000c81e81001244551203a031411566011458200b10020100c40e0102c4512040309060002c4501414440408945151a28081203035111002854800791340070000110740c1103440701044101071000791504e804080301a01c0b845915024485054425441a02a204500688004240341c01088074034036886400200c1c0910010b44240b281c880703000700030582011941491a08180e8241054031040303882d5402c7ca101c40281c0d003a1390041d411008100000b15555651820028111004100d42d01d03210700e01d0160008803 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898773507 1250 898772257 898772261
    0x2010e1027030f1d0a03060b1f12051003021203040e090114011e0f090608010b041a2716170702030d020c01090804080f0d0804050d0c030c0b010602030913 68
    0x41503905846520101c40f2114041d1018400c24403200c82d24480501441070545802c100d40c001103101e0480130030841031003401c00464825500c41c0420903901001d440f442103a110700b800a014051500c0010b01361140308104030001c42c25000070b0340180003000c2807a02944000300030401c03280d040c1c4000e07100361550001503091340c1042216901a0a04100505c01074503140b03030b0701f130351840012200e0045070703a600c0d10061070040030790044e180a43d8406040202c41028010342c0281e140445007040754159461000c0c42100e03c040e100e6000d5062641c0c080310902d806440451452410010384800d071a01c2500da40415041407a000002440703000030051840340c01c801c1d0b078024112a000f840c204001c50301c0d050000e4201c078800101c81d40d00c4000ca1408560614000c0c400307842e000010b044540310034034101d0b02e4030f001c0c07030317122410030140070100404500d001c03c01860b000c10924003109400130742d040403a0031401200c0f0280c10300041e9030000614580000080070038150035104051600032030b81e00c40c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898774757 1250 898773507 898773581
    0xd03050108060138030601090618031e0501050115090501030c020703080c030f071208011d06061c0c030c0e1203070b180a03030b04141501030c02010e10 67
    0x807603610000c01804483c8620004200e4881c0c2c990103108800d42524050400010310707011000100030010a200c20303541c0c0005490003408160a24150002107001d0741c840b910800c0c440500910482e0000031840070f5080c4d10a02031503000002400a07513199852003050500d521545000300c1c11141000074194068043c02100b2061a0080c1c04903514684580080d6403088250706050b0008100c41010101000064500c440c0507901c082181c00e5202005084080180c006054810040b9044a10400307145c1c050381d4041e03400d8440d2515840d518a4000e040d0150442140c1c1441c1451140344265a240d4400071903100c90360344100c100c3c80c00303a040c88010695000d1904460700108100d00c04100e0b80300d60071350040040c40f40d030445040c03001003180c18407200c0c00080b00000e88070051295286407900030552084450680e40b500c50070030610901d0b0108403121010b040c0b50f15049904c01e402c4c001e500c021030344100034041d10480d09214590b900103144000e600c1c90f036003080780b904000940411031060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898776007 1250 898774757 898774769
    0xa1a040b04180c0906240f050c0f0609070b0c070b0a090e0103060902040b060c0a061a0d030807020106060f0f0f0c021e0111060c0a18050612010e0714090616170c0d030501 75
    0x443d81d51055182213a28150702c030148000d1090270418001c44070170800c031003e42ca6236850050005400c00446c10790400009074050808c828041c484100c0740c81010400740120740c419844583c0c1c8002c164009d86010b001c580c08801406002000042031103200c1c0c0000d500fa82c0308542c07c000c844250300c104109801120f80260140c0e000c1002c001c0040c4c001d500030341c004c0d032418000303180c2d00c914400019800c80342104110001034411080c031141540900075040508100e04108091045001005110781942d1b030001c000c020050403413045441c003800c1c800040c55000f902d0500d941c01100420300300680080402c600041000d07403408810030020500b00d0044074204421413500c401d241c8201c600d181c10b5015580c0d04032402200040030365504004120201070003c42900700c0d8507007080803001c0040104008244034034410400a003070030031821513240c0c682c100e80e075546800c184c541c019030110000e04003d101102c1000d001c03104507008030141613452002411103409642e1500c048003034450a11800c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898777257 1250 898776007 898776059
    0x1815061808152e061d0405270d051e0d0f0213060212070b1e040309091d0d0302132310180501030c03020f18090a1a040b04180c0906 58
    0x511284d80300703a0343c070103050348243e200d00340580039200084c08a030380540d008640090380003419441c80d1106101d0900c5210b145018103094403142c50007605a1080804c90401c2d030400707000502341c4101c900e0642c1c4840c60780500c20440c00c0904c00810000394012a5201c000a00a603c00220a4800034046014005c40f520143c140259650396045c04074010700a14240040482b02d011080501402948202d010303640e40c02050345003803645002c0360300d441c0c0424034030140c08041c1286108009030b0107030364903294500165a0100c80d01003100340c8105800c00700e02c002c07518031203c1000a09240c0785070452411503001e000721800c02070030b662001400003500405914820100080d41c026031000003900c01c00e003405071410a4228141c6a80e500400640d58058100e40d01c0f16140e0038070307000391a4481d290a0b03040000d0b030703100c107481044000320805042c070540d1584d07404031181d1255007094605144210a07005101c0795886e010442a55500980420a00c0c140300000c0c101c0f590308030751210000086070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898778507 1250 898777257 898777259
    0x50109090903090b0307051c09050d1d0d0302010504110a05031b040b0409050a03090605211b2805160209040f0209010902041815061808152e 62
    0x40308081c11400c1400d03014840d500c0000100c0301081d40065109150984e909990b0b440e05001044e40b5144500410441c0c600e041101030000d400015001035459060811580555589400f103120006802050703820003110f106900815805410650040b44105045005805100c0c1480040c105610482d5416400102008850301c29104100104000900081458034072080418240c40942c00304569940c4440041c7c0e0034154060f241102a10b424075009240c4540070101460516150740303055a54800c40020440f40c1449481c12204081c10000c0b403070301c40110b1038141521b0b01d112000d06140809010103c0e85542c4500c0c01ca541001c081e05258500311916020301400e1400103100710788462403881b141001da914561450300800a0410150b07a880c240903d54507241b003425070140f1071500701600403440c200d90002c02c03026503c00e0f18090040c56000e01d2500111141648000c81c0350161141a5002c0140710385444d10500b0300030079000f00c1c1102150391408008140b00340034246201024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898779757 1250 898778507 898778519
    0x3010b0d02150c070f050301050a1518020702090702030c070f0303050a0f0c020d05061509011d041e060c0f111c05040b1206010905060f0306040c031812031104050109 73
    0x81c28034080c035210803403c0c20708202c2c100c800c1c50301c9400e400c031600c00024035004000900d0240a41903100095200c20303c0b1104c0741d55154544210341c0d010380704801100342c00c0304462620b1681a50850350b001090f00c40c00c0d0030302a0307019440350302256018030b841c000d03581c02181003c40f07a40408100ca0b410b94600e8501100362004541d5041040e00b201c0c10441080004e00140c1c0e80d182844404900400241c10207062881451201c15010044107004d51140801080020320f905041c100700000d0301440400d5555501e030628084422082c82d1140050140034202800740c0d0307070b212480e111007036102c4c05400c0c0c401c00c509503141607100d8548401c43d44040801440518540903401465960b41055400c15842c0c5150340f0041c7c2020045c1d100860288041041540c2e00840c010000c4c00d060f034249240c1000160141c1d00ea10009040314011920303000c00308000c40c441d0340310903a00c1420050070f001000762440c02c040d041008084c0c080000e07040c0070701c6002032105c0d603049501721a4143c48195a15242c05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898781007 1250 898779757 898779769
    0x906040519060617070f061b0215070209010b090906150313080c12030a05011205100203040f0b150f03190209130b0f0106020d0203040b0f220b0c0c03010b0d02 70
    0x704100c8000361105800240040400b01c1880480315070ba0140004034104928030022140c1d0360702035010481049004220a0030040004d2319040d010b607508016508041a40c41c218842e04800a40225481c0e000044001f540c0c0064080000201c0300901e42c0d48031071040041c1164289021800d01000b00081802c2c1100001500800b520907072885082268400c107aa04000b190074464116402c00401c00a000e0b103503101d028050400011034459524041c3ca803070f03640d600b88031007035008241e0010110741401349840e800224594480384420072860110047c500001c2050a010300480001255090a2801180d4102c0b540c2c102c8202100400c2c0c69003c010342800c002e440e900354401008030601c00300c0e4a401c000303071240316200e40c034040325450024000e00d0000101114801c540007480103000e43c2c2d480c40b04071088070003100a89905e8030200e2404001c0c201d0f00c0200064041411800010b105416030054500505850140c61100329490149800d1301c0c4108802a0b01011170300214005107442 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898782257 1250 898781007 898781053
    0x6010e0c0a0c06020c070504060f0b0a050c010e1e19120e0402070503070b010302090a0203040507090506120a05071a12070305071727010b0d060b0f210609060405 71
    0xd0b240c09604020142c541c00202e03030066103400076039040400180281e0815014120041403025411000e41c0d181c0600c1003218000d401c1c0c50020000002103100b5094425082000b80c01d001c00c080d290b00070303690f94031a65822402c2101d40c016004400700015132801e261351400c14141c00060a6040b0140088101c540c0350b1543c000e80c1c3e000d40e01b4424000030600c20805131030b07241d100d0302120f0150b505500400c031850400911420714203004004100002d8000b061003012103c20076000f0a00e0740f0703407800080c00c66440c0462000700e0310980d0070400034400000340a00884401500842201002c4600305e140c5105800e60320b944130303001c41c0205881c14070942c0090350080d00380c908080890000b074120309441c07001340c40c00f415032403441c0c6001804100358040026280c000718000c000d129180b0020998000766200040e24150740c2d03004202298031029040c044a01005004071103001131070100000b0441d00812100f098402e42000502c0b005c00042c041b0b001c1e540040051000750490000010350081c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898783507 1250 898782257 898782277
    0x3010921050d150807170304050f01050c0607090f05190308031b070309060216030f030e04060f06110c10120f0f0606020c031c090b1b070f08010c0206010e0c 69
    0x400c810464140b8074400c00003030380d050061403003d01c0c0c6401051403422065800010040c2100c24240043c081e0000c2200c04469096411500c10303110000142c403a400386440c801c2845c040c1904100d04a5402810042175801c0a442400320648440900041d4800740309010ba000007414801e0000c14401d001544d8064010811124440d000503a809101d400864088000c0f4a0300f41d03050081940521500d05d03400ca610030390b419228038545809540e415512005010300114095200c074507115a0800e80191141d114100c26032076890f00001d0120305000f0118030b0b94080e201a40c4001e02d0040c0403404bc220751517856150341d50340c07143d03514002c00581c003210000301d81c0d07400f0004422816004060060005170041d014607445241803500b0152400e00715142c500b200d840940b48030b0b030084043c0060320300c2865001c1d1100407020ad00306002e48411400a211b03c113080000425441e11850702058847d12002400a0136443c0c1041e40e4910003030090042c0d846407400021102d00800015041140e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898784757 1250 898783507 898783517
    0x203031207170705030c610c0504090515090f0c0a03050d080a0f0f1d0111030a1104120c0f0911030402010f1701142407290a0c080603010921 62
    0xb410704c285c00440840c1c444560304e0224528031015286941c100b141406c80007403151f0320700105590b0b8030359890070480c3c02002e2040350794001c0709090090801200d14814401400c60100b414404503403544c9032034034041c00e01e41e44504030b070900d4075040110079182102d91100081528090400c41601c140718010603111141e6929040d10030a84003900540203869600c041c00101c4003034442941c19001d8003c801c48610760306010403a104503044500b00d0340d10011034040001c05410714406a001449583d200341c81c24a2410342c0c040030b006044d14004c04480310001640100c1303564a10408c15100c05d030703801d40c054100500008015501800340410250444e141840b80301c0a40340c44000d50140c00e803c403005440340c09040200d1410b001c10070304449010071207800c042900e810301803241c5100d030000c02081c1ca04170000c00c86481ca9031240b0196031950980a1980d5860074a120380d00500b0b0000d5030f44006481d10021810a06040c810310840f82e0300035011040c1000c0071078801c00320540382101002004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898786007 1250 898784757 898784827
    0xa1e090c091d120405121b0103150305071401110a0309140a0b0313050705030106050906040f0219080a0c031a09090712030306030506060a050603010e040203031207170705030c 77
    0x1060030f01003407122042c09034a0a488038104020b0211000140081400076482034511080c5680c0312112010004d809203404280c00d4ac0060225002480c4c0b507100800358429698003007101d40c030500900c404507900f80e0310040c2c4c100703101300465503908003007002901141000c0f10074001031502d0a5102680700025014183c01a507492400320980e200b10f42d840040b0748003031058400c020060114100428045000307008039410000002c10034000603107118070444c0d40701c2070807001c07803405e8054038080c0005258103c130440c2d0707852000d880c0c4034044448004030340c5000c10072190a8003911481030075500c80b440c0200d03802844000c3c0881050042d050407054418042c00141d011a208406041c0901c070f0794021840b945549401442c049016080601c181034201007404181c4440050303c0c1140c0e2054050070440c6c5550020038118802d60391a1042c001020303040004503504842c0e28004c03005854081292551002c3c81115540419201c1d0503030fa440030455060f00303203111206032100c10946000c40c1ca500b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898787257 1250 898786007 898786061
    0x10b0a0b0f090d1e021002010c0509061c15030c0e010f09050910060b131406161118190e06180c0604090c021501030c0911120a1e090c09 60
    0x8019044d214000c2860071004400842c18022007020003562140002d200e1807282c084050481e009a0b80c0040c000c15010070780d00550070034059501e10707000b9a04420001c8860311560110071b19894001070f0341e00c00421394001450a0352071720f614100e44000201070079407801c04120b00c0c09401e004e00820a644581c1a4841040c00076105060051000784020b0380d48505a4881c51200c2c482548080d65102014003180b255454800c1114442150400d0313030b102c0c2600a241001c00821541e0b200d41c1c00c0704100b08400031001542080031701400ca58040c0040c00c495141000d0152403440c01c100c0e4240d0403d00c01b0039514280c100350801c40a8101c41075510101040c400b040003a0440d601071070305580c49052565160b901131055412011000c9620782181d81580c172a00110703a2188a2400c9003036403484120340b032184090556100703809000c91014981000c421030000f81810a02d0803011008540c510703074403d107251040200b141e900828420050345456187c80c010b1403441000d01004803400d22007109 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898788507 1250 898787257 898787273
    0x112030e030f0d0e010503060d23030a0e040b030c152a01020a090807080c0d03030f090609020f0303070c14040603120908061303020a0b07050c0a06020309010b0a0b0f090d 75
    0x2040b2a200249441c229240000744a204410441030501c002042401a80d490701c6000c0308902e500041003100c00d60070b50b00d00301d1f0070211962460005000201c1c04610035544290040308241045500703014500240003003640752a80c00780c62a03884420318012003032843d84040505091828181d041d000c400710160b201484113524014140c0076540000e51254075600203c039000502079480c020200b4a00740694140c1c0c9655140d10a4440c42c09800c00508241c0700340c000c00052a000c8000b441881903501e400b03006482c1c0424120301c149600d007140d890601300003090760742158000d03c030000301501e0311a4401100704203600440e0041d44038800800820001005c280103100d070f695648122902c5d010440c3c4c01c001c00a80010014103800040c440801c0d0300140000c800c0342c110400720030f9522103603c162268440c001100485018015400050012983c0518450014a0024445540c0c402c0c1042441895400766102504040c4900c401400707202000d04ac0c80344014044890a483c2c030380300c2d144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898789757 1250 898788507 898788523
    0xf0c13030302013e0f07060e06060436050102131e0506031302010f020f1c02070801051006110a0b0c0c19080301090e0c09070207050a060f0203030112030e03 69
    0xb40c1c1d110391081016400c00600b21031401c0301d841c0d00c11503510440305010310b00318266071640d19854000c10003003510026082110840c9a00201c00c012040b11440d000e52100381c102d0f4211f01c42e9103000402e4030310307100c1056510f110003040c80c1e5124400140c0410300038042c46038841070303501c1e650a02c41d0f4440c1101d4000100c024000c0f17811021450303400700038000040c0c0c460b43c0005006003002d20911280464400d4810301070391742420490030030040c855003280703064541c0e10441c0030742c85405420030043c480e12032118072400c8142c1c00d9868281e00c03a040c0d05d007616401e4541c40051103460400304443d9114112801c00f0709560340c161454440755441c3c00190031b8041d1065040d24500240c14204886c0800014048040b1134034040c4011143e9111546030b40414840d201c1826203955403480440c40134020b100c0c5200b00140924058100100c000396502180c0c01220701070343e90301d070780880c00758051500b0182c80030681c2c0c011440d503801d182c010584c00341c0701e00b0120240041c4600010859500f40710b040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898791007 1250 898789757 898789763
    0x20f0601081c1e090315020c060c070602271c05150c0d1b09050108040201090b0f0c010203040b010905010f080d030c0905100e0103050a021e09180a0507140a080f0c1303 74
    0x40c4c4a60841c00c0005034400c0d520b001c00d002034810003070b1381103400f000304270380c2c2e840110300e040d1548500c050300700400a44915010040607081102e0742410011019018200fa59410744a401004a104012401040c2060f802401940c480d403148040305c58003480032640714401001503400c01c0058805481503e00407c803840c0c00c1c2c4002045140d00c0341e400b5807100002c01092802401d0b074103140d00082c1c580c54150203104001070f4000346002005200c4c4085075a15000c0600855480c40d00782030100b2560300a0140c2c1c00f41300e007080e00006907240d15101c0c0c00c050350040c1d40038100e03541002c0c80581c0104081e484401c10320150380400600c83d40c0c2c2041ca1420340d803281d00e0700203c0030320001c00101140c0c4001c1140719014814030050040a10101e50301e0007081c200308000d9070b00c1c0001000600c04100e19400701c00c20b0300610080000807401a08814001c03070702500c8680321804803980c5015a805800300c0d1400040b4030070300050303845c0501d41d131464100f0b046205140c80c20002e502000b01c1d212107030f041030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898792257 1250 898791007 898791017
    0x120706050405132d1506030b030d0302120c07020d0f060e010b100905010503190e0f0606030d080f04022e08060307050a1e0503010204090c020f0601081c1e 68
    0x41205060180303480f103412104940c100300d908060750050031141400381e0401c41080100071081020416a80421051007603040f00800d8a640c901c40200074244454800e4068001c01c01503203a05030290007911030b002040800c000d4a596001070f08031103604044c20990f4003504201045000c05ea0010304807442c0341c001c034804200340c0b000d030640a080d1401011643d01540036841c0c01b680c150307444001c0d03805480091802903a43d80711400240141020703c0d0b0a0300086242c0301002c0c00b40341300020180e5110603684192503040d035441c010182c84d02ca09038112404a60000f0020b4a4105034a507031076403184c8001d01c44181001c00242e02c2e02c48265180600c0c1150180d4a096240300c0c1c1c0202d44071783d115501324002c1031200d047c8004034601079094030610b04d0005c001c00294440200303102c80700340900310143c000c6485a603280d0a038009003800d070380300320094001c2e486803416600c1c6c04641e090503510220010100b400c0c1317104020f100c41d0324400d909003c2000480f040403070900c0b2003003d08205a140c2d594 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898793507 1250 898792257 898792259
    0x18061805091b0604090c171303020f0d0e2707110705030708120f1e09011209020904031b051c090b210408090303130303030605030304120209061207060504 68
    0xa080c80e1208803004a800d03480802c450b40e4882c0d5a40040341d056401d45c400100c1c010b940310340c4c00e403449940800504129244a400c000b030101041325054100d501030380c200d44052004880c40c9444022201c01ba10000d05045822440c50070000140c0540203803512031245a055642144410b100381507880c040002d0411155050003101007008101030300040b80507080385c1d03142070410f5680303e0741892440c001e80804540010035031044011b680300302c3c00000360004596684e0387e009a495200b1044a408600e550000c0c0041c2e441622030b56403501d6000e0312000c25612140c80682e42c0940000300040034031055018240010014821424040c0f04c1c030300c4030f904e422286100a00354030100d40200400c2603084c4480c0c0d01441c414070418108076681050b8500713649540c10700751468800e5540d00c5405102c002045482d01c0110581c0d0012680655000c000c160388038030030543c9a05c5640f0850000c54403401c0c000b405031414088003070b0400c0e001080c250781da031225248582016940d500c420007160001c90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898794757 1250 898793507 898793521
    0x70308091e032203020a240306080a06051504021305040b040c050a0e01090e0f251413080a0f3e040e1006060306080609060118061805 59
    0xc00a010301503048200003070402a0241c1c2070b40c0c0d010348078100142c89000008078900c840c0c3c0b6451080030719005403641c184181c46240c0c0c40030050801202c20013801c2c032425008030311440391242c5801d42d81002c014002403130603900d8050141001404000b0b0581a0030703500300311a0703128402407441d061a12845551240b40004100031a1465801395001c0c1d420100c070103003075a0784942100e0310806a428515401c0384c00c903004860103581508005030407181c074030034003076650410040c4500c42c055078112068440655262800c484203421351036000320320b0039107401482c155110054040415086040144103985880d10751030329012003001d03a080d26801c2c1d0b9010500881c85a071040081c2c4000e1041301034022094103c074912409500440c6501d80f03180c0310001c0d40d4840d00000103000b401012102c402111000040040102d0310500020034903146c40003561000200e580c604c01c80346500a0f0225078a0010034840080600e0002500140e80381c41c04600480d4034562006040045080000c251030014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898796007 1250 898794757 898794763
    0x2011205071e0c05160f21020301050a06081b010519030b0303041508070e060307030e100504061b020604110405040318090903031d0c0436030831080c0307030809 71
    0x440000c0028002a105100032500d240c030307040883e15240c034102c141d40c4a0b03035807d010140c06040001c0d4076500380800e008802c00140c020b00140c0300b903082903988081c0b0015030b40101c00c41c80c03003040d4085070003840481e007a44030501c034160100f0551700f00850380c0303407000c0000b034150f40c090340140003511102035816044552007441241d01046504280c0a09140c0e64000750040c00002c0010042580310320011030340d00390030f10110403d812145024802070a140c984600a0b00c0204a24007402c003214042003c6a407000610500590700000108035040e03100003440064400148250148036800d0f001c8080d110b0541c4512009200c40d40c4001010745640c94010700307440ca01032003c3c04c2c240503041700130b00000e00811007400201084a0000c0d42e0744003c60520580c3c01044e825401140c480d607501e40180c0e01400b11844210311955402e40d0b5030f902c031401811900b80d200050f914413035031080b105159102545014800500420186040401d0300c09254690751115404500181400091100200c1c0030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898797257 1250 898796007 898796023
    0x1508070207030314161e02010807030c080103110f0607060b0310020405030c040f181a0c071208092b0f080615090402070b0c1804060302011205071e0c05 67
    0x5440070300030252443d2001005941103400d40b035840c4100140e0344041c01140d118130440340741d01092a019401003c02420500345100364143c0c085010300001418144c031900c20840d2600c0c0c1a20b8203182642542c54050078820b01080194014045000c0c9624030750302e40000e08902840b488010580c50740080606040c007030342400f0b40405070700601090046036400308510040340020303540011195255081d80c00a40018030321807000380350032035502040c07040340300140140c582c0041d0740d4a1a6150380f8181040c611540c0700c0682400301003100c1c800303d0352040780d980d40c00201e0b440c101c900c2402c0c6490707001c000c00c09a400048070344042d14020003482d600190703d1007400d0507a0030401d20310324000300403034846521030f07080e03140c0101c0014030f09855944540c159000c080d001010301000345041c40d590600c560014004101401d00788101d02c0403440c09015034020707254107940d040307490a464400302e4098240541580e051040d41d00b00703600c15814151903d00240c01a55920003551503509001e4240196 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898798507 1250 898797257 898797271
    0x6030a21030b0a0e0c1303060f0c08010506040b070803090f060f010503060f01140409060f060b04050909010c020a081b010504030819050906150303040b0f031504091205180a1508 78
    0x44001002404c0d075840c18954018038050302d085d664202030002c1c0ca005801a08000c00e0f41d4a88010b0071010581503001900b5190562900391450762500c003004010700072031160800001040080700001103ca101468004025000b101c46c00c9000c03541d42d40c2844030840d8280d00810240c0d004001074070341000743c81d41042c40301208907d554100340e14207003804000d0b44228000d640b240000c038208001a44964080c40031b40000b00095915440c480180303038032903c03d04e0310030b031000300110b0701080c4107115034010a04250005e00140880c0d41e11251690010b114030540c01c0e030708400e000d00b210401e00820b44960302c82d0307440b5201807030120040725481000f5008041e9061428003000320544001a4090b0000351100034200171b6401c503c000780c81c603c0f070798000c2c00401e140480d8040d021207601001d140614084100b2600f843c40f60303400d01c0b0881d0a5854041c0c0010038840450300558064130040450100302c0c45070350000034a0314041042105164044010082c1d501a010605c650104440c1c1d08061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898799757 1250 898798507 898798519
    0xd050a0623040b060c010e100c0908060601030506180a200405010912020619020606210a030c140a08190903170a09090507050703320306030a21030b 65
    0x214441e85014140c00d680c180e0750080b50380fa280c02449030b68580035a00d071007101c00000d0102030440441e054036100207400c0b040d00c86080c03141f06410f81c1c0c083c02c411400e440b4610014141c0359141d40044000c0e20f40903141e60740020310030119483c1c0c410501250740c85403e00d0000851125000e0b20041c400c3c0e0014403c1c000044018401800307141e82c852005001c0720404088440440340742d0001800706d01ca03800100601642d01d01411241c00d801190452240104a401500c0c1c2061000d070103c10b0304600c401145207811540030000040d000d10315401483d40125070351081c5191a903119072801c250a141603417040e1000c1228042003942c050500c0c03540c0c1540c908400514030319602c1c070303a10807940d2250307031040013020038003a10f1030744103d242600401c040c41052080e0b00f000c1c200900140e000030019030010f031803041c0401c00d0164490580b40e11740301c100c08080007280d000c00740341402d400252844e0f915029440300a40407900884202c5800d03101e407403d401040c450581c000c2d0448990141c0030740652 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898801007 1250 898799757 898799789
    0x327030b0f07440105180417210a1b08040609080412060b040209091303030b030a030e010f02072106020705070e010e0a1e180c08070f0503010203091902060706020d050a06 75
    0x1e1102201c44502100380d4608420310b45a070b01d4135151810311006604061000482c0c035043c052500607270703004e0424019800c0403a64440200c80e005691104c00d6450500c2c80940d03024880521484815030b1040c007905000507841c2e95540d412007260300a03400010141004041c007014007204d486001d01011044400b1440d015402c0c0103d80f02c1f10700105003038480d07190440c140701418001e401c21504600f00809442030843d407850701900a005080d90f050000700d0072040040406d000003015825a410100744400c100184040c2d521040203001084920301d03000d2002000240741081000301402103000c59071020340c1401c80602269030020004030030386040184c0342034030411611010500107881d0317401054000302403048178000700c00214010b046030382c4403400003080400842c0038402d9031004400d0304411541d0f042098282e0009440b801c01e5908086403840702c030400043e010f165140b0140a03a0708282c0e1589440342203800c00c0c1c044038011078903001041440300d254801c0c80050128109142210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898802257 1250 898801007 898801009
    0xc090f10050d05101e02030103080a0806030102310b1917040b0c0f0702031b100207050112020309070e01080705010e041103060f01110a0327030b0f07440105 69
    0x810703005440c800130320b59901441686402499240e0300d240c5a05d442035680b940d480c0b600c0c04150341300c003003641f0000e5156004a00c1a10341070080303c01c100c02d0180788401d150300f060645000c0c0740382c16064070380c450401c407400180f40d404e0320003400d02e9108482d0502d03642525600d01420650303090562000030819082044000380c50421503540282e071984400c0d45a41507000b0000f4103104142010b5854840e00001108820513000d80020a40701620078800460640701d00360fa44556501a05010070444207680f00d4494660b40a1980300c0c1c030032012036501507039541d0209061042a0030404c0181c0218030240a40e58012000006c068030565041204e00301d91500d00c0c0c0b076030201808140c828a20780d011250303541c1c0705801e0034000c00402c205035140703100702d4507028000d01003e0502413922800c0d03000c285800e0001d8a01c000840c1d4103c03e41244903601e00f2890900594010485424000e20540380111204072900340071448a492001e0402c1c6907003050000c3c2c9031107929507680901121000140b000e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898803507 1250 898802257 898802263
    0x1110030207051908040314030307090506030610110a060e0a050f03121303030905011508010b0a06080c0705120a11100b150703120212071e0215090c090f10050d05 71
    0x49111541e51030242580e8038941302205210760b91020302000c040301c528280002010004600442e400c0c1c0341c1003c3c0907035403810300807640403c032821507016601c500004501380c05055840c41940d41103040e9600c031314040d5140b00484e0705603004a02c8030351114032900c080005c00c01c110164056020300071402c4c000031801040880750000c04100b23002d424401e11b401014040c0e048240d259a00400910040340020081d5121038200d1189040d80d6080440328807103401c002910f0425581036541d00c20940e9100da03004140c66010790411112849041c603241c0b104010800a00f50502c0c0d160380f00040c210748980003e00e40383c0741c90703070005000d86040070395401c50b42c44031400202c5d0603040300700740c0c4c550009040c00da0789042c0068030300d20060f00014900c0ea141001c0d18050f8801c00c200c2d102d400268a80d0500c00071340b040d070700340d034040983c1c80700942002c41500300300e1680d80f0a0320340d02160541405100400c200920a641c1000340d0641002031055141e50b080400c005868140c80800851030a91507030f41c0d03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898804757 1250 898803507 898803523
    0xd080a0e0615011107090506040b06031009150b070614090f1c120f02070c08150406020f0405060c0109060b0102030a021507020111070507030c210209180a111003020705 74
    0x2c0e0307118003020403000c69014111425030703e02c0d0881520050b0313540340240d102404040301c1491196183c0481d4503050302d0101c0c1a2401012000c0c04c070030016040400307900c01000082a03950142d12041000a80d00f44000d006101c02032040ca0302040400c0f40610103a9403010280203100aa00400300c80c400b00003000849044032140000040c00800b4a090b045e07407aa00480700c0b00f009203003807540f9403001c42e07074a40003018150321824424849a980707015654852503644ca000d24014900808903001c14420b4000e04142c1e0700c50b04440c3d140c2503541002501035807090418003591303516200d444080c8070322441a070281c503100b03002451a2814000c002510307000180074010342d5140c64000300315002d00c01d510000b11001c1c10180646e841020303081883d940c160034401122160305104001c204203150600c1c405c1552142612514511095401c004044e03d0060000040c0300d01e0702840c05c81c2c0c0c42c00304550804030b80200c2a000400d280a000e0240c03103940c0b43d080c44181401000100300268001401c64 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898806007 1250 898804757 898804771
    0x91206021e03070f030f0e0f0610060e09071233080304051c060e0712060b01030c17092d060a090206160503040b07060519110d24080d080a0e06 63
    0x2140e082c440c88503402403015004070002c0f23109403002054440c0c00087c06500610700d1407841102d8030b9540008985110f00480340d5600314244c1000300f20b500c4d010b260100c1c40c01e43d1080b004941c45002c1c4842c03186403c0b44001c1c4000021075205040281c81e4400044c0020702000c0b8003452400d4188404160142c1009421160003140e04010b50140603050b40200880600b80d13050717a00b6566205030105060280e01401e42d0581e14003180441258042d101c1e01700400302d035484800c000380940d1325031940d101004010345180d01034200c52591508060002650b0910340703022078030f4003111524a80c0d14148006120309009881c01d42d0b03030005a5900c0082e541c200101c81c5a215035040383d8940b40e41540520b5000070110300300420840b0412186800c028421804042151f10241007000c902d4140e1340c0b848030104980d0020421b504543d003441e04007140c9840000b8400d200c51400c403075070f900301040e20303840081303541c110411914002d9845a21a500035440b60024001c09a8158036280c403100b010b4540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898807257 1250 898806007 898806011
    0x1118030d05030c0c070806090c0a0f06140a1e02160b040b040e040228030212150109020d02070c0b1305091e060f0d030306030b060d08030a020901091206021e03070f03 73
    0xa034085801000010302034440101620b03403034107003103800301d0380d5103405c2428500c035200034003020500e0130701d41c0400c00444109540740c111019014070307401400da00651144ec10040c0208140644403889400c000340d4841540c02440281301c8101d600f00d001c0d0035504000d41c1c160040008004a650803401da9068a01241c40318103d40c5907480081c074001d400105c3c0d0729a1242c104140c030081050405490101c80c001d40e600c1180e45922407203a9200c0044034204940303944c01500501143e4000c0d40900080303258040700501d488001d4079580a91400c581c000010580c0001c1c002c0c010768444070851000f0300c030581d062001e904000140c0c0c1454030038044000076840c507030f20001d881d0784c1c0c40720303013500c0c1080010384501c03481002414010058400303030009a43c0007150f4400b0030202c3c02c2010540800b04e41000301181191114101180650301034600c181c100b04040c4004030391203155034030b0381ca80d0b5131182400503030380d51881d20150b424008014101c3e00c40c01c014003c028034190040e42d54101c10442d0701d80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898808507 1250 898807257 898807267
    0x3020618120d0c031b0810171b03070503070803190f021504081201150206160f111011190e0a0306050601110d121b0212031008011118030d05030c 64
    0x70480081442003d03e520f05c0c1da03042105010390390403d210354010407141940c100200c0e1140c800c11f00d060070000014850f9480791011219040d1840ca9400a400000301518006580c402c0068a4161756400c55803254200083c01141c00c107408202001482047c249103141000b26040691107c10a69100d450070460740000380800040900f1501001c00c088a0109030b540c5800008543c068241ca880e070241c0f044201183c55510320240c0712200110039030b03071710102800600044800340c0c0c500080c0b0f003180c490280002c02101c82c6010702040d0315001c10856071180e1706007050310707000c0210519a1017031012890001c1c0d00c5442c0d0403203100c10361342c1095000c500c513106e140c0100d507d84015850380c210f81c0161100e481e041648401c401100e046c02510038400040c0e1501701400e08144005c100c809030b0b100044820108c240c1801865110242807801d04003299995880760a5035071481c411100c582c1c0c0081c4485048020615017000c0010a0740284039400e07501c94060b00b80d10024240c24462180410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898809757 1250 898808507 898808531
    0x220303110a050405130519421413020a050d09030201020c24010918050102070302060601090602060702070501270b09011b0c030b0411040903020618120d 67
    0x400031501056039000d559810864000604540050140700e10441040840c10202000c5000360f50094074a02004940340075076800301001010601d0800b0000c280922500361100c5415801c3d4403800828071880c82c2d60000480c1145900209030800d94000510191015007078a602d811000680020030f0016911f41c10320308160703046c2c002d610800030094184a1010200b6a040d001340c01d08552010840345515040e1000c8000340100c624006440b00510303004100a0206070030640952207800c400b130002c003c1e2611041e0a9034032901d025805030303201406220fa80d50f8000b03c0000100b001d4406400c1c54100b8200007074a40b407085c030a050400ca50080c0001140e130041008807500341896150302e801c81e9407000900f60f65000302c40c401c1c5c0441c5601c0c0049040d407801110352a011130b40003502c58483d40c00c40e500c003910503001506c1036890000306406400c0c2e6803070710320400c23014500a40051000d480c100c2a006174940f4060403100070342d0003c8912146044142040c0d40d0310708014400442d03501d442078 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898811007 1250 898809757 898809761
    0xb040f0b03070e1905060304140d0c020d0f0215040803030f0606030403021c020c061c050108010e0604060f1b0305090f072105030705030301230a0b0403030507020301060506031e090105220303 84
    0x20304140d40c880c1c0d00002344001c000c0300b07801c80310900b2400000d542165403034030300031f0f100c40c1d03401180650842501c0e406000020302d01041e03040300d544024804500d0910800380004e058210f40c10100b0b05c2d134400800c3c000030900d0702e0507182e4040c00454010b851840c255800035110f001c1a48102c410006120000c0e01741d030700034010030701c0103040a0010798850600070380e4144418101918561201c0c03070b160000c00d0810041c000d2003c000140b41c0103108540f13580d51120002d00e560003803002c0b01c955404002a4490b00c82d04035001d0030a0b50359021540e410045203c0342000d0040c440703050140d0108808200100c41c02008010344e20354002490001d14050602c9825171080100c0140613010000004c64404080da040300b00303140040c090103d6a1400c00144500100c8601a1400010080c0320800c0028824001094024030180010a41716584c40108034581c0013a45c3c218800c03503000000d501c1c90b0f41801c44d000d622030b0402e00203010070304100480300020f00b02c2400e43d4044011800c00340c01414065 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898812257 1250 898811007 898811009
    0x1104031b0512152a13030602070c0602060a1a210604050a121427040501080105011a03060d0201080405150906180c150a17010b040f0b03070e19 63
    0x10784000ca80c6400d142950741c942481051000207140d0b0340f00400e00444c0c00b01e40707440000301130240e12030041410008080d4190080c5520020700c198003c4040000b400900107002e40600c80d0784c44040c02418610064103104e0000c040810a600d05030400c00b0341511040616091801a05d5003205604d64540f55038410900c03451001c214840c001c00d000406c0750000b0944030281c091244501c00c00e20401088640000100c005480ea036001c0c0300c42c00485002800040c02c807800000c0c0906280000030100e4240e49090340144000d946d603d004000395004050500360051399550101d25629200340001c440c03050822010b41000303000d07070000703040100c1000300900c10071a00444c0789241c60059600e41d13441c1f0044032a0030410b0261040c62071442000603c0c00070600d00240042e24008a150702400d054105c400843d0070020503034003c007101211034070103d000e400d0303a1000c0f551b50350911200707000e045419440942a190304000b00480300da400aa00410072804075000748c038500588030040d210300c0c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898813507 1250 898812257 898812259
    0xb18070311040e04060c020d0203250b0f060108010605040b040e06010302040815090c0604140d02060d0f09020a051f0815130f050105010315030206130e1303080a1104031b05 76
    0x100081c0403d003500007000c294403a0303114250500c10b000b40408200c0e00d80c1c0c170050f076503000b5030b006018081c1d4040451851225a9003130407965000c0540079151490640c20541d0016109005070301403020b5568002c0c40c01d805416181082c501c5c052030054100076910440c42080440000790002c950346a02c01d070101d600030506030044849150106403a050b15105c292054880c2d44211200600242090410b48003205c112060041c400940d1030180618840407010403030340040204030080700a07201e882003404440c500680010380003040e105001240c80c070749d04002c0c0300d440d0031581c1034020220701c00c0411000c1c08502c4c0c49003031520b403426440050081e20303400e640d001401004000c0c502046034044018a0340010741070260742d0713a800040d0119018141c0070011184000818400341c200320000b07008c404001282c40d10040d80d940202400084141c640b45025441c1030688404d15030712280054110051450422000c046205030840b00e1245e403000030f05081e0030100080511082010030002440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898814757 1250 898813507 898813541
    0x5130c0e010623040510020a050708070602060c0327072103030f0b032d0d0203040e091612080c120d060801020708030609040c0b07050102120a0b180703 67
    0x140310003920402010034014100001c0c0a540c12100c950034003600040d0014108081e02e1405040a0034002d106000320518015845848004800039800b0040301005000031400f5009242c02e0110003400d12001414030384001c0018018040c4903659a511036821486443e8180c0e070076810382040d141407112503848500600c010005140c0c48050240f0a40105071180d9801c00201c00424122011560f07802d289a4042c0d01101c0100405440d44034062140321032038401c40700141c0d0035021580f8110200103a100142c001180c200440c14010b000342d500a00020060100003146580f21400900944601440e09801d107101d00d09210740a0700311a9450103020030303941d012400802c1c5401c1a40400001c200d050720b400c00c00103404806109461995500800e0f461541d10b407001007090001010b003041c2e5079420710000010300c842010009080252003240003603251a1000e0083c060620000c141e01410390078400362020940d2402e5000c412803400c0e0480d41d4441d2a00c0e4001c400800300112040c003808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898816007 1250 898814757 898814759
    0x6041203051f090b010f031a130212090705040b1c02060f0c0d09050f010212031306020f0307030e07060c1211160f050a06230306031903110114011805130c 68
    0x1130b40109401c0c620a884a000c0310041a904a080791500d00000b1440e0059010705112442c05036803140040d000030300301505141e034580440369450b4060f02c00c9081039000038030400030381c2028040e48400c0c3d20122643c8509804880e500d64825041e81c400034400c400000300032100c144c00d1010b49144549100031903032840d00798a0060050001d5011f45e40c0b003400007400c1c440c903662000800000b0b22081e8402c1a0075034580980a03041c039000424211f54407902400070103804036030340020758030819841c0e5003c80e0600d2107652590602e5025000407041040c400300d448003050f170a03940f10101404900e005c10003204117900d00e0b81001521444584c1c8029250f40015803100081c11802c00d03108110780c3d032200c443d680c4000307994801e00c00d0984030345518a12489a00218450055540040c001c0c0a0380c046039406900d2075640d80212100324007291450048a145031000d114104403c1028000364545504000c03000ba28900c0e402c10034a00c003601c8200190b0004402206882840d41c000e070114442 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898817257 1250 898816007 898816019
    0x804090507121d07150f140c0a051501090c0e090a20070203010e0f07060c110303070602072022110a031d01060b18010e210f06041203051f 61
    0x1d003c0c0800c2c0c0904502c141c034070120701c1201611140c07030180029110030303961035450704060740c4803c001107442c907d42c082881141000c44040c401c0c0603007140300d100034003001085035141d11150007060b0000800d1600e054081040107030801e00c403030034004c000c4440980b40d81e550301d4034202800740c00b00246000481110f428080960b054080d0551910807070080c031144881d6043d060f44ca040107100c202032540051000c00c441401142d00d2483c1601070403002c5480c0340c8000c04640340d82d01c421030403218241d000034442c09008107500300600f040580448080040c0030030740040c02481c494070085031021400305510321400309903441b14401c00c00c2041c1d02612400005805030040c030044c4900214180401d480b142003010610800080d141d52000890800c4080c0074000b20701900146100d0600c07180810003d00c035a1070003d2550441100c0b81c0c000413402400c81c0f0a13040c0400d4080c21392640e40084103000015540d84500d6154101030301d0002002e507901c100c4400300f4824a0290034010304403100100308 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898818507 1250 898817257 898817291
    0xc0d112409040e06100e0c190906170f07030e03070203070e0a150b19090504050421180308070f0b070906090e010312141e03010f060c080409050712 65
    0x18060080b0350400030780c005030000d80d4844000300e81201c10035000b4139003440417004000c64107030480c2c030103500c0074144240c1031642c4240c0420400000042a40c90030104400340c1e0001c11800244010301500b519070400270144c400c3c110004d04404145500c8078801a81d00070304105941810742c005080301c03082c80d581d1940b0600864190b032441005401c0c00c640d1603030045010380c007034110341600020a141203085004520240c2131580c6007402c10084410025860740c0c1e0740141e5008a0240050150340012a688207201d0540400024140b04540c900c2443c3c4104184a4004aa800040351f44d40d07080503203081d13441c100340c61000500e0452120280817135143c2c000c03042400d544e026150349a190391500c40140c0504400d1000401001c28401c4208110380b1801c029072075a00000d10650804d00d440320009108502501038184407840440100030f40401001010002d2100d030074560b03d0020740e5210700c00f1174031aa00400e4005030301c502c0800e4120b8814043c0c12400c005c6c1c0c18027003240200010344604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898819757 1250 898818507 898818517
    0x90d1e0606050f030303010605180a1d07080f1605070c030f0b010f060507020f040e0a05060a02130e100b0a0903020402031e0604050601020303070e0102120f090907020c0d1124 77
    0x1000f80c481c00300341022410000216810303504a902c840342000100f03071441d42400000e4998503003003040d4a00028031600b11031080d031140000f11601c61030500d04101d0040086900408040405603518240914180c04841000040c1d070f171860a41c2d40c6000d14246521481c05540c0010f0060b00b001080b0024801c00c154050b041e901525244041142d41307200441d4103004401c8042e5100c0c41041d0090800d250aa20601024036100d003600c0e6031700d03a5511907a00304042128001c11007600004d0382d04002260000035009082e151152000c2410502c0b010420355007140039201d40210005807100c4407d0103910709000441c2d0050080d550381c500310f01d46e00c0105204026180302d182c00d6002242e01490a40541c0c2c0c4144410303401141180d8481c0801c681142162425a044d0b008121a0030a410507402c0100317071442810003e107960704010003d0003003402c0000d10352400c5410200c8010302c983d41f009125882c094002d80191900101000003c580c295940d1045d407240409051608600300081d010380 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 898821007 1250 898819757 898819759
    0x120a120905012c091510021b45040317010801020a0e040f02091302030403020c0925031d010608061003020d02060c03120a05041b0308090d1e060605 65
    0x10729612000ea64101c03c80c9004003100441d29a80f000310100b9080000c0d041c2e500c1380d00d40c00d15a16416000780400c4030040e480318000016084082200c0f81d0160408000f00c0303088040d1940b202d041020752000394100c990003c0040d007481382c0c80c440035074001035607144201c804061101100ca41001c1c80d0240500318986840098400d00c00d000045a11061081d9850920316407180c0d441c4c440e000b004c0000602c0303400b010b01c02c855400c5c0706151041e109c7d1034440342e40c200d28081c0147c0e80c0c1081d0070044d00d408041c0910511417540c3c1070030003020301a0310f05062041d2154107081c00400940d100e06070040d05800d4008181d80d244008001060001500140e00311001c0740c0540c3c5103a01c2d80402c903034001446000194112000007081c40050070441c00401c08801c24600352402c0204010110094040558400138141e8441d403c0c0010311000c0ba06151100c1055202545007a2560765040000d0141d045243c2c4540c0740061181e00784070301c00700c0020500011500807100c0700340a141841c002c0020340541 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 898822257 1250 898821007 898821017
    0x6090406080601290a0507110a081902040b0906061c14090115060221030c0d020f0705070803070b0a200c0127030e100504050901060309110f010905120a12090501 71
    0x40308076102601c0c1140c005e5149035480b0383c074050b016100c403003001650a918039000301c05004d00103101c000c203000c01c4007072841c80300d2a001241c040e4010442500d844822982c40754100400f44405940c0301c02c220750071080500705100f101495420a031004181c03062a0074584002d600420180c01019840044440c505100203d10349403914002c0b83d40d44068000030300340b0b0059402c0021410040c00185922604221250345404410143e02c1c0607038100c2004a1050344c004a007941c20000b050001c0d801a000c06401103041a042e034882c14880c19014007000450756450030110010041e5034500d0169290083c8860f03a260480c0c130115009021100000f02070000f4981e44103511481f82d2400880660196106860b2511080421000307098040440051040800c000186d80e2603044c5c10f54020905a14001820040c4e802c001d40c1415652450500c14901000e1200c12030380c02119600a84105550702050403a0f061203003441c050510001812040c030040104006c0c551068031501070f40c0c001c1e030b11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 898823507 1250 898822257 898822319
    0x312021c0507170606040611030904180308011a12060d170a02012301061b06090803060f040b09070305130503070c080c010f020c09101205071e050901030206090406080601 75
    0x140101c074103941d03166100c48100401c000c151b100300b0218484c0391003101271300d02d000307074500009003203d000e108101c1002540b250110103240d04664400e004060208144680340b403107030550340e250312075a00303100c02a080200c0810301c2c42e00d88200384401030750300a490720513803070700042c1040d201d4000103540c80056081c120700c00180c00c20149402c0030b0300c400e1150060305c1e900300041038070048602c00d01815148040c120348008252140168885680917000203541c03402c4c404103120b480040b61441600031410554601d00c0c43c0c84104400d6407054003403900040382d03213031045c4507241d907680a0005822440301251007400d2000d81d804100c11511100b017100c296101110040d40d04000d0000500d0158000000c03d500e41d0800b013110603407081001311007513421074640c40c0d5444c444031420000e46583d4080101844048001c000b281030b4802080102681c080c588400a10001c80500009000350701c0030412958075110313904070a014014203000e4034515a181e8000442001d0203001803210308521740c0c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 898824757 1250 898823507 898823537
    0x2031e06010f1410030b03101e02030103050c0405040c0f0b04080105010e060a330e01030e0f1009020a09021b160f06080613180512160312021c0507 65
    0x200740c00845010503030940000010300c082080244d40c815020003070507260001803036280d50600c0b00307085200300d10380002034500003101c03401d1030010350744010b5a01c20310420040c00032a07000140848610b00403075020906907103d00e0880c0002c449648822003a0300d4012000c103007000500040c1c019525a100204156039860b00e01345002002914015003040c0819802d001d450104580310019025240242e80802d24043d440c140c9a240b12218500044402144c4200c80da0b050252107000d40203031006210041d02c400101f51250314050a41101503515061401191181002c89004043c1c01c4011502c4504921040200601c004965001806031040d40c1401c02c0d4004184410f80301041150045141040d40581d41d5007005130405a000100100d10f91000c0010b009030050b43c20496981ca50b4811245011031900310340703a51030700d00b00030305002d03511846444c186003112958141c40c1c141841445511554000e00c22082250f00780c01804c410a00745280c240c000724003481c0266600e6000f001026 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 898826007 1250 898824757 898824779
    0x10f020909040206131520060f160909060e040201080a0203010e0a0504023d0c0b06010521091b0919050712060f0608070503010b0703050f0702031e0601 67
    0x3081107607000c4142408a000742c1088406407404d0308138040e10000d60780c2c5070105035880712054008080020000d03011401b500303040054415010046000510403030401300390030b4003c400000d281c0c00c1611180c54801a030ba134407616080009007907100d0704011850b19101c1c802c04070013084505130b011508030300c040394645149108aa04031002c2c0b0000001e1600c0f1000c805001c0c080280023030b03034004240710300250280041403054609178410000c0344140600110000840e024181040051005a0b03240401207040d002800e03910007400d02c0c2460345c0703e40343d9214245005d14034801c8000751724400200a01c4050000b156044111501505910312203d0000c2000001085544001103e0b40c88000c6ca071212107070b0007081d082140b508003c411514021014000c17280258440405015600070030061950010030054110409282c45859907040421082d00b51148840081c204500022a45d40070a402c07400e650065078004c00380c2e0f555440741e101d800c144000820819086028150000070504610 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 898827257 1250 898826007 898826017
    0x40905010e060d030e040c05210108010b0f0f040e0a14060718081005060604080d0203091002010c02120309010f0204181a0d02040b03010e01060b0c06090d1718030c010905010f02 78
    0x40ea20020703684089001e2001900c10110340311f040c880c0c1800810682d00703040c100c0e03d10703443c4014025030140d0f1414a48a0950302c04542103800360f594285c00c12496250007090030103444041e680070035166960f408242c682504c142025040078082c40c0c10700300e20000030401c140200c44075030303a4401c810362403030001c40f94428034030a44489034070502150907500c2490704510b9000c000109054101a60380d140c540c140300d1020507010040c1c000080c450700c54500030f0b082e07489100151008000c070700401000070790745a0034841402104040403002400f50312094020180850401109540719680c441603c00100e00e8006812101410006080340c101c4d603040d01c03032825002c000d00410b0807082c2d82d020f01c40180400e5020030303019522821150903e038424060600101014000c0e00c0c1e403a568512101e080c444017400b001e802d80c101e40721020f0b0040c4c2c020301400c042d1400300704904458035007488401d4404071856104009000108940c29112410342c800c0902d98003d00092207010301c101000000c038828 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 898828507 1250 898827257 898827263
    0x91e21061812030103140106030c06020304031a01080a260a031b081501120209090903040e0c0a02071a090a0e06040f05160f020a0f0b0414010506030a02060c0111040905010e060d 78
    0x2c14001000400d009a00362400d0400d02000019a15280d4032120240000c5402250150340300280c200100244000c0404202c8410a41b401207035051103200e640303030fa400c02406400d522603042086002c442c2070154410015140002c155074000c8004081d01a00301100084641c0340242c10348101c5c0c50044210b64441c805258030900b02d02c0180300159421203000d101032400c00d5084c845400140c4820b418540202c0703420000f10340356031500f00e02502d0340f0740c0104802e80c010ba0a0102400c07803500000c82a09542c685202400901405460110140910034002e0303804190170000144041940607100d000e403500ba1801e208003000f5800300c5050340c0054a0000340b4951402003075034200c0c412030a503024500e1038415590f100d00262914140e804000301d003a0740e001055018001000146c001c1c1300740c1c803180000240503d140c501d0009071284001e0a0290043c0d00004110341c84074030039440760b440041190356036a161b645807005503004040c24000c2207208a000c0020840e9807411083c6018a6a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 898829757 1250 898828507 898828543
    0x15041d010620061b04090515091b0909150402071202012906090d05100b01020d0e062704020408030304050d090e070c051011130b091e210618 62
    0x22080107a0700400c3c007044240c00b01644c244000b007021400c50094500032100b641a084000002e8401c00000d114082c2a020014404842170320102465005035210b55000301c1c0c46269640d00e5040e0303441070b035040301c5266500920000e0100100041a019011204100e074020040d0200c0c03402840e1641140c505843d9145c444c0d040380a0a524019004015010001e0000003c80f00d19076110703440c19019075820600c844e203460244900f540d0400c030034600e104443c82c04d181c11700014000b15405115101080c195450b00c030458103050000e4400c002e03020040503100319543d541d10300e4403c0c0c994000351070449880c02a0341e110821107103d44102010b6078201d914546a43d120300760261240700c0100f00890b180d0141080500078081e9900c00e40c00e8003c64003c0c01a07444442e1011040c00c040c007034001191480d0300340018861a11107104140500319081c52100400c0345910002d0300c024000b201c0b0108045070425403500341800480c41ca40035a03110b61200d804200e440800a031100c44544411030700703074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 898831007 1250 898829757 898829761
    0xa030c0801120204051b1b06160f080a090c080a110904020105160309090603080306030616020601061d040903051e03060607110d120807020c1207030215041d01062006 73
    0x302d803591003e40c03c0b03050a1980c5000000a103030306145604080b00720103580c0341d2024020720080e0140401d550110f02c009c451410014071501c050a4450f404e030320103081041000002e030b41c041407a80004c40054000b81601c801a98940c8450303580c8242131412a0800d02410345101181400c3d00c49a000341e40c161545400c0501d0f0140c02160001d50701e1003541009a221800602442a8420b03400a540180c0f072080e50703880e041043c1460000d0240813402d8104c41d40350600e90140d0b000c207465040d0303106443e00540c4505458a503900c0140200d03039490b881498120b030582016008002060004240d0481c0c0e80818103100b02000c241c04100c0d12281c00140400c9031000040d4080ca40d007014140c0240001101d0449885c0c10f07000349100079100001c5040c241c240310780141c0400c40704180d1103040300c00b0300c150310003900e040e51500101d1100900803843c9030300805428aa10080d2000351240c40449128031a0012003071300c001c0420311030350300411001e9070840150304021640b20500e52036540203040075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 898832257 1250 898831007 898831009
    0x20910060f1b03050a17010f03030809150c0904020f0301090207060e0f151003080a0e0310060302061b01060503030d0b01030507140304201809060106180e0a020f0a050a030c08011202 80
    0x15034402e400101c2041031765601d030882c42102020346d50103041c5503000007011509610b00a48240c10143c0b0301c1e141e590040c0c2403401e000c81418003855000f1211000365842c0c00d003c6d000301d0043d024a81045001000200c00825a91b075170751f0141c0715183c0540814030440e00c1080b04192240020849100250801c03114403814001c0780f40580c4d08010700401c48020590750703488a080341e4118070015030024098007030b070310028641000101c1c0310b410f81040400200c2c3ca150b0018049210301001003080002c40c118100c140714003075200744020040901520b075901c054508800081c070308280414082480d09000c02e02e0b951141920445800c3e105103c03a00c0e5072181e84903170342841c40c1c00890725011414640c8c40c41d0301c0d882d00e03c54505217042035000280c0070305128040a0900405030440c500b000b415102e00501035001b1407400e401c40301681032649550320f601c0344040107031144240c4001440310008400c24420b034098014007000c20666400c1101000001c2c0c00c4424140a00c0f88400c0c050b0006400c2000d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 898833507 1250 898832257 898832267
    0x12031c39032a14070503090f040b22230a050c09090703090609062412020312181c051501030201050d1a090408040315050402130513020910060f1b03 65
    0x458460350030040f04071400f0042d81c2006512182003140d00c0e800205401603207060110003095280e900719414051160705102180034140c054508080c0011080b4826061000d281c0c407001c080781e100d1080210b514052114108214001c3d10082e0b41d00d0b103020009600070b408030098031007112004007148550b448000d0101e019010504040c0c40d0300d0380d03620b89a070020315140f0807141b20040c0244100d602407032300c010408011038070358001e040304940411034400599010851482d800c801e4111640c84031864400c2c3e030702d0103501103000c80d0464890100601c040c03c55071822140140f2420071601400707404588144400c00030304c0000d002c1081400300c5104654150002d402181001d02110740101c08000000e915000c2980c0c182d40d4660002824014032906c0045803000e068025400d0245050650200d103198003800e444000823503a80300070030080340c0d501c03290150454004140042078148269450003060030b5120300c1001c100003400c80820075000d1040014a60481c43c1c442d840c042854909880d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 898834757 1250 898833507 898833581
    0x1812031b0307110601180f0b0a1703040b0d020306120f0a120215040c0905060a0f0927200a0e0126160801050612031c3903 54
    0x140075441c3c3c0442c0c2444010440c0b03500070300048228000055000b00590300301c486000380c00603400d0901e4189030054507151030101c00c4072b502c007a114218100d1401d0050a5020715040310082c20780018041c00c0004d0150040c42c021102202d442d0103441a15240a40e41c401164905503a90000448117003c101c400070901c0203560b150054030151a400350718006030a200f120101d0300c0385007441d401d102e510b6803840b82607401142525403a14141c181645038a400e14280300b40400b8540300c4149029040c8404421683c0c1301300450399100c0240c0c5481d100074003406907070301c02032600d0200011004a00d0300c004408226500410340ea5000d900308611810310100c5108804003190030181e524a906004015811052100000e4010f1080c01c010005c0d00b500c00250003507214034400c030b1400d5030005001c0201c0d110314102100a6507074a0114a8980107042d5814070701710000070304484a0340c80c40720001e00c00400c02c140c84042640300001c1b1010b50803035800c10310000254440d850b030312100b141000340100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 898836007 1250 898834757 898834771
    0x9030e090114191d011d09190206120c07060f18060e120a2a02061206010201140c0c011107050a121107030804051f020607030c171812031b03 62
    0x2443d0035203403900b01c1c102c10b200c03440c0d513000e80b80c07603400402501c4180c03d003103400145102c0c3d080039941410345407d5540c12011440000c04a00300740c2990855a580044404003125a12510f8492a140c00c60807040c0d04891003d582003400c10400700f500312801e100d40303190b480c07010004079000d41c41c80e11044001d000c0c1c0310120307016105413511108200e0030040503080d0705501d070790b03004100301608059480b01400344e0608420300c08110000c00060351004160b60020b00740072801101d56440c040103d02419161251500340751000c810301c85003903041401400490300c444001d02c020640300300d0151192082e40c601519540101e0b5803800050080220b500c802c10f82840d108107800c003444d0000b400c00c1002d90040340c034604001004c00080c100744001d860f1401e10382c400e2940c20080990040c1d1640c00080842c41015034038000b885d140c030301485036074500540c104070401251403c00429100b03103140c1800d40e10740d8402da900c2c6200c000440800c5920401d000d0605142d200c3c0e900c413081d8a540c1024202d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 898837257 1250 898836007 898836049
    0x3070c0809041b1101090c0303050309012415090311090907031728020d0e0607150204050910080a03080403140c1f020717090a05030f0109030e090114 66
    0x4803180c1c0e0b07483c051075030b1002800b801000202c83c0f03481d0280a10542400d05842641482e50b03020106d4280003040341100d400d42050ba64950b00c4030442070040c00243e800403402c03007160181d903a405800c0c1c41070b101510b0310b0311421000220b2982003a10116014400140800803150340c180640c1400b07182240c2140329074003207d02150f2a981e0300000f070040c0d504030900f0500e0120720401d101c142d002e0b61445450070701d04151645062800001c0d12010700c00e5102050148500d071031610b980301d54003154036207504400d2180d040d0f441c13002d840d00654800c1c032507540b064806c3c5d4003241c0420300164054044a20020050440320070a0398140c1e94640001d00a600744407900c0d081184c0802d02030020000b244030781000d00350381c41032040610030044400d10701840340b510601c01040021514034240e0300d04560180034030740743c401d041c4c00a40c20409a800c05500740c040c0d1002016121415003045d071300c140c82a112003041d40415012310000c2182481030801d550032110003103070503042c00d0380349540c410342040c00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 898838507 1250 898837257 898837267
    0x20c030304142d070b070f0b06013f0203091c051201090504050114060a23030d0504060306080d08040f020d02220e0604171303050714040c090b03070c08 67
    0x11402400ca0f0b8148511041c92a500f070315021081444001c01815400c0f800504000407511081c1e18511000c100400d00c89108010400342da0240342c46030550000b0588405481708001c0e4400c0420b0741410f042e20600304116150442d060307541c000daa01c1007185c1c400070803081008000b19003889000d80240b5061000402c804507170904038138400e5000c1d080404002c02c1c1803c1ca850154212040e80c2d0b04240c0ba40c02110a108840d83c8001e41da0040300c0004030150600500001882804804071586580c0344c804c2c0004d8200194004000d8012920750761030800130f17183c0e210354140d01e64030b40d81700c0540015122000100010b440628019a090024145c0400a141603010846244083e00840c080380403074420540300121078010f0340d0200741c0040c00362041d030034030303540720040d003140c1034413800d0321000108900742c2112000454000440d0420300311007501c0d690f424810180c5446e040011300480c02c1400d10b9800d18014190102299104c4400524645d140001110361198400c000c48014500b000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 898839757 1250 898838507 898838533
    0x190e0307030905100c03230c06090703030f0203072d0501060b030a1109031903021f05041202151503070b1206010305010e0f0c07021f0c060609020c03030414 69
    0x40d000d400d00c65200c100d9624248410002000101c030140000c00000c22819000698800ca52048070500020120743d48120170105403c0c50140b94003440c1588280d10030004107140010303404044034002d4903010b0503d82440d1041b0b0312846100300c003421100e01c2c045c0719000144096a000c40d03016000c40c6901c110201c940c1d80e40c0c2951811b6018103012507002c4288219101130b88a0030803114107504e01545460000404251214541062481d002100b00e55420500d4000c0c03140e07150700052a0941c4810210461032040180340030361b01641c1425448040c0710800e0f00005105e01d203c0d58805034000030ba510b0850142c10b0400c0c09082c00d8040c0075042d40050074a620101405140c1d6002d104280e17946031600004044540580c07198101420032024030181c042c43c03150864000c403a9000181d07071041c0320300114a4079100346900d80300c3c201d06580103000c3d10364440744651100d0f200d0030003408850b40d174070304103c180d005002921400750010404a400035420440304085810440103443c5007601c80c40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 898841007 1250 898839757 898839763
    0x9010e0319030f09081011040308131811090405061c06050f130206040303030c0309020a0303080a0f1a0603091204262805070306110702090105090f190e 67
    0x40d018401c40c0e1014151904043c0c100442c21080302062800480403460407410b6555018150581c4e031803150789811220003d24004122400346800400c10395456050785007040c2c074900107114051000a10784003001108006004a8807411485012141440c1090b4204002042c3c040c2c01d040d8006d024003004c00681c0d003a103d800e94007174080e10000615181c03210544414900040c100841844d05906840050303491400b95001e480d007510740003c503c080d0340002e0300248403a18000e54810141d070f800000701540030a04030b220b1700504c60f042c411241c81c1c1c240b4000340c03a1021144070117070500000b80704c01801d207080510b80c440c91102c1221032004c4c140203001d40c1c550203508a010030b060010b21005c0da840f4039822801011700079000030700045840011440703480340d070003c40c2004100c16288090911a00304845409181c03c0320341005404500607a4025640c004041213010700c242c00000242d520780344c00310701e221b100c450070000c40a954540d143e491000d050048240e40903581da2000b200c4410030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 898842257 1250 898841007 898841023
    0x130203010c03090201020f03130e09030403021305270303070e01030f0609060e011a12150301051611030c0d03180506090a020901141f020c030a08090f031504030509010e03 75
    0x1d0344001075a02a03a0000a003454480400e030070055200304010103076054107880c1e40049a00c000500310450311280522411841180c1c0040d5201e02904000580040a0f92000e405005207400c03e5407000103041c0c0c442c03c10141c0955420564001307100003040640100da00b11442681458001007400078a0446000c5803d00c2d001010b107203640f1141400004030781081a409080c130508221384000501c06140c040d44604c607005510102d40d60003050181d0401c0603048034282c0000c0c02030100740b82664100030084811000d0703c0003d108034403180c1454130080b0480301c010000801074600482c0c400000d4020b0921210a0304003030b9510304c0042c0c08160140b04040c010341c0054050541045c40d8010044c8481e0306812171103681003990404180c03980d83c400801c20300036086195010080040c10140c0c2008203021845425024080e210803c200740c441c0240040c101c1100d50b900c0358500c00342455581e8410219125070010441c0c0440c01080c0180040d10300040145423245c403401101e400f00e03003000c0d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 898843507 1250 898842257 898842281
    0x30604060b161403030c162301051501050a023a090302031216030e0a170606270a0917041203090509100e040c0801110a03060b1204020913020301 64
    0x5040001400c1100c460f41100c100f440100c011410340c20075202c2c48905105000d001c00c00c414403400c100f8100030b8907400800d142e160030220000b400c418090414040c0200700c51a60b540000c0c0003080c20150302450070788007a04034907030040c281d02584000311030010b105908031540034031142c400c40c1260081e1034102250b041c850b540e43c1c5110391540c418189484080b003101100110180000e503a1242010070301078074160585001003100c1c200d000410070100c00340c1c01110300c0310b5101d4680e00340c161000402c0e0380160300076140311855001d00382150161110080c040e44031440d000e0045130401c0916080b842ea40350040d601121002a40e0341402e025500c598081e039007101d107014806080c950018480b800070242070320a000c00c0c2c50800d1001400c10341d2801600048011400030805010a8090a5020300841802080072030a001aa08081d1f08001c0b03900f40001d00b810404a0b810150606507801c42e00083c14180540d122075013044600b500090031541c6204414116030302582c1c0c01d01403003910b40c00e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 898844757 1250 898843507 898843537
    0x5060c030a0e0103110a1b12030c11060103030503011703132d0302030309010f0201140f010314010605030307020d05010b04060f080706090e18190303020d0501150212030604060b 78
    0x18800c01c007510081003070301140d061500d0110116115008202128030406561030100103c1844050300050303008a01005007043c10078100c101c00c030742e400d64480140c0da0750a403103441113452804545a41ca00c000d01006000510a00040000000c801950640b52045070300341c030b0420040703141e110004449984035900c0305405440010a40c000001a10782526402c03810707409050441c1c0120760f40e81720f50f0f00511304009040b491404001d02c00c1d032150003101e1981e202100941084c2e40c0b11090840d007800140d0380c50f514808550234100c030520500080b00c101602031414250300c0d40800610001322402620103548a02030300b4100e581d107220382c7c8086c2480e41e145845050500784100d2608090741c0209061010b4000c05000b4024003090b665402418101110745034000c520815041000100020f00100b501031801e10406826401924042040140c20465603070f8030003900304400c1460807520003580160300d004242c181c42600940d40500b000d48080380490b51782c51145603c1e0b00c802e007107111a407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 898846007 1250 898844757 898844767
    0x62c1e0702010605090108010207022d0301050405030d0507171317030702010906180f08070c05030a1101020105150f130209030a06150501090f1710020d02211e1005060c03 75
    0x12074054261750140c442900218106040c9502080180d651010100d60f50180352041050444952a030310f010312030050001d01240c01d051400c03690340d0f040201c100c1c603800c0c01d15000a0300c45100d0101c0d03030740150210800c50b85d00c2d100c03011082d0340d010403980700350b43c64a5102020380204056500842c010740b503e0340009072010480c1000b8045031407070080c02c019080c50400c44808180b48141e0600300b1900030707540c02d580312061f103080c0c004084544d1089030107004102425080c80100c4c5d00305c0201e0202a00244441e03554441254000d103c1c000d54207a005841d884280030f02e0418504880030543c10302001481e250309040068a030000b03100d412900c540e100c5111164181081c1d842d40e00900081c2440c0d003125013000081d4a10b44014090820280d0310300e0a04641a0010840440c40d49203a40307007155200040300740000a5480089000301c05801d08030004e940030480c030803962060341e01c41c5510a49100a5a186107580c1c0090103641c14151941c1b00400c40c2c0c2d80d10710007800080c900000566942e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 898847257 1250 898846007 898846009
    0x9010213240207063501030f060e120d05101e05180601140a03140c09121f020a09030206040b120a0621030201141009062c1e0702010605 60
    0x120008207600c00864000c40300412946800015420882281c01c00440f25401c80500748404200c03d11000400410b01034000818000c10f003041015041c000e0000748028952041e8041e1b440c00f2400545026100c200000d54410b1900c0e40055005460b82600110b5255210300e448203c0e560005007610040c4d906004200e1032400204c03c44001c41e084030503d102d40b6007040003a0442d55a05000c61040c07100242201c50b040c4203510501d42c07060380c100c0c0468075081407465211160003209400c1d004000070130841110120001c1c40d11810141000078081840003080c0120180d000015881c0034451210000f2005945080180c0060182d0340416522a0b0117070344405609100138240010039441c0030801e1114801c11803c0ca1040c100e1030402d09034491162030124010462204020380505000052048507118030500408440c41010148405915170800019200001d070000600c14203903000d00b52202c880300c140c00d5011800d038010004280381c03201500c8240000300c4c1d001d00180d554071024021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 898848507 1250 898847257 898847309
    0x618091315050a020702150d0b032803050705030f190203070b060f21061f03080304170d0903110c0301063813150813151d0606150705031209010213 65
    0x308040c02c80c000e05812070090bc156469a00d04401001c4200c2c4044041040c903000b00c04803010150b001d002c5030b07035411215042c00d602d07420541035101d480001b0000c7c01021440003042e82c0246800000c2e100c0281c5a9600300030032050415801500500141d41c1d82030051b02e0030040c601c1c14103105015024900d02180708515002c8a01810000c40c031000794248040751403c0103403507210380e00282400101007101c600c111a0701503c01c1c06080b03e42020b220f14101a40900c003102ca02e20741c0000c681d07550303030340508041c240c4072580030b120542e4100040c0f400e2200904e4100300600d40d100e001841d000c1c803408645450641c00a40d4040300158520000c0065404425941c06022003918154466050004544e42490f45000018040e2510a091500001c0c0c0580c4a1604400449900190a030348030352415214030003181c80c41d00c40e280e2000b0040c9682210400c48494541c0240038524001148100804420b00a801c2c403a4940d428060b0b00784040f04030300302401920000c0c0743c2180d0201d28410481ca = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 898849757 1250 898848507 898848521
    0x10e0102100c0224090a0609022b06060806130215090603011e06030c050d020306041d0d080f070e011b0b0f011403010c020309010c110618091315050a020702150d 71
    0x2001d0044c10040040246011441c5076010382d1210700031840380518000940365180707442804910b104030f840b51030042d04080c0d110140043c45140103214165640304402c0e01e520b0200c4160307040304032a4482c580103117000c0c00200d811340c0c2c4490701c2c2030a0024000100340650026040a08003070480d0040d08085089601d4200080540d0f107400d11140043d228020400c1c010007420621403900440840e11031395454000b585990360300c0c1e0100c501d4080c035402290f034a10180200c030000c40c1d0b0003001b09000c001d131011003904c51440c5465491200c2a000c00440305ca00b802039580c03c90956160603e0000ba100c601004d0090440d41903554940d41895002e140105180842c04d10030380c036210704000d601d50040140c0324000801d01f0000c3c1420301505001c1c8584200700c060071350103100015680c0c003040c220207030041c40181c25155800c241d03441118000314004484800f81c60304006000911b1002915000b00341d0164403002c015013070100c1e070303404255001034000514010140c08125001511002c0c80b03518 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 898851007 1250 898849757 898849813
    0x30402130501050d02010c050f01050f0601090609080a141005091605030606011215090e0f0f030408100218040c08011806240c020a0906031e0809010e0102100c02 71
    0x1072945000002003421060721002418030105030528424090244811705c1039148420003131000386084e20051100d01800c4540c1400b00b000c82c0404a0050b00c682889026141c1c002c00030008000c1948620380503d44420305074600744501102d00c0701528803800f8240c09041400004e008520300885103102c0b1030340175003009010354007540803c0700f140e900101036141501503103c00220540780c41820b0401e4685a013002201c1c80c14051015403030400010103c0c2c1e02840c850030307100608400844145c403407240d8455107845070f02000b00213900e500740c7c1d03005008074401e8005a80d01d51400d0b40205003030b0741e828016440802c21050042000d103007012041c0c179080071354080c20407245040c1900009401078014010480b4042005180b200394010f8018010b10750b00104050b0601e5900c007000809440743d80000c9882010110800c10340c2143c04600c1e44030240d21220150408070381d440115402a24290f03a18110720509911b2007050100d48200e205e5094198081d0050a100300a00b04102c3e42c01d212403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 898852257 1250 898851007 898851011
    0x61502210903060601200102210f010e0a180c06030e0705101b0507051903122c031c1101181205030a02040902030f011706010302010f0f14030a0203040213 68
    0x255003070b5540450020707071254013400e221508240011228508100d17844011010790700c0084c010b8000c1102c031031f2100c0c6071400700601a12650780d00315440d621a4003842070401c1c16a00c0408502c0744504c5800c544281e1402c2c00134000003004a4540e0100741d91940c2c0203402280d59029101030301e0f041440f080d00545029114154610010704005150b403880328641c1c4440e507201d40c3c0c150104403040c031602d00148801010705504c840e13070204009829907184400c0310b1000400b03403d00c150900803440034420101085040c502803482400021803a690480703650f5050041051201d0403281448441303681764502d6441400c9144011105400c441042a4480c4440d03c20960788002070080c03881d00480c2e200c47c0c0381c420b40f00e803145211103010b0302486c4c0000100d140080100500f40b141010b006040381c0d0113a0000d091031040c0084181c44000a0101a0000d40443ca204507601e0194030403164042c1107190060b0505500b40398007107607130000e550140c0c60315000014407003507280c1503000e02c4085447d0101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 898853507 1250 898852257 898852267
    0xf0e01090203030d0e074101050306221a0312070f1707051009031205060a03060b0d29060907090e04081921090203030f0d06150221 58
    0x3507503030141d41d10701302245407a1048103210a1040c0000801000c0d518200d124083d58503140210b12080c050610144101e1034891142d1443c3e95000f030100541d06071100c910f182c5920041c40740000703a1401107961031903030b1001d02144200c1e512a508000304e4410815030201c000504142c1803080c804002074441c0c00500c100008a02041c0c0400c00740c90340040c000000385a10031140405004001c3d015101c0d000d0f00c4c00701a5880c1a94210400c110b00c03075030b104000c0d110303c0c50041080f0b03441a1542500100443d0050000850a52140f40340c00002041e90300601c4940d6503480e40350300700c4007401d010004000b03d0307800d681d800c51140135004401296036240e58540701600401e074060b207100700f1403401c1c850030108040c0020142120038420f0401c1f003c000c00e050078140078003800c1c0402a4001000030f10a07031030901d030800e0703c110f61096034001c001d9450002c4401004415420001c100140907603102000249003000b10b010045020094000c0d00c40d84a201039015004400c01c3c0d19141c140c4004c100d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 898854757 1250 898853507 898853509
    0x50a1103070f05031009020406031406010f0b030c120a0209120304080f010504021008150a1409060102030405030307110a0e0702101503020f2107140406090905151302130f0e010902 79
    0x1120382005405d6140080c6412032400094060034180d031016101031540040070304a02c90200745075040c0e40807034448183c40c49d0b948030810380501c4115810501c0c01e0b024000d0b040100f400c0c00c0e5054010030558000b5040c8003603c0000340031000d1510f19144117134800242080036440c00d02c0f8055400940c80c0080101d4a01a004200d02c070903070f071441030200144400001d103c5a0b10880e5a541d0aa01410265030070752070302011901000b41000c0b00384a010080e00048066200100f290145d42001c0e000e07504200860380c81c0b0300020030000601e94000c140002c04600a00b0496800d8480c01c1294014a1003042a0203400c1c1110369000391013090500315541130015848001e06d4076031030502070b242144001803011620720314035046006451a4050841d000079481c040130359494948c1c80440b410490140c0d0b404180044410003000203086070021a180b03040100402304065020754941c11041c0740d030020b81e0000d010006d40a2240c00303115075541c031004041e0400d2203111aa41e108078000c100c1690550 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 898856007 1250 898854757 898854763
    0xe06011a12071209080306010215040c06110a050d17010902181203360103090c050409031106040623060d02040f020d06080a0203010c02071a090d050a1103070f0503 72
    0x440040d064806000441c2503035114848988403160700070804c00c1500741c0c901c0d10096561041d9426801882581c1074008034880d42d404440c0900d51180e80680300b40e20b800030a441040f403a403150355850084003081c0000c20f0081c801403e00c0078640c1e458200c40300c0207480c1c0161a00040e00310081709403041c40302d04c143c040000510b503d03c2200712074100a2040c0c01044074514480c45246c034042100500443d501c10b80e00c1d44006455030000802c46840301d401c1e200440c1240d068400280401d8410142004542025804469414020701d004801880800381d030360300d002016101160070076a64a004a000c0400c610b59905025880c1441c486074241b800000307204d0440d01c40080e10460f80c404248403920140c0d8100d41c50840b02c400203004440d070b00d10b0b9207612241e140a06034001e509001003410454030100c0c002050364030701102103640320800780c40ca90180d08020501030700500035407280c0c40458020018031200610500c2100300c0a0781000c24142042c1c0c940d4842011803192100511940d0740c08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 898857257 1250 898856007 898856017
    0x605160215060a05181005010309081e12010f06020d0f052205100c050c030c09041509150902011e021f150312020705030c0927030a030e06011a 63
    0x20164640c036612402c00180d03c041c55a48030581c4a051566039050312a00707051094801d15114040140766a65a4010f4054801c4204020866a81000480301036000c0385803001801e505120041d04080c0d44030000e081001003a000344041c07040740c80c0300301b1a10350b040046070f20741e03800c5d454101101c048218001c1c3c0b81d4007402400208421080c00613244041d503015001e002400010021a5034002e81040a001c29442e0b05040c0e82a0184680481c92401c1c0001c0000c0a4071019007001415911520f0300803200102d403141c00400e585600e04240450038694035424240410403002401d10081e01c005000c900c0c0209000c1040282079854012464001c914640600320400f0421094095008440000c103140d841d00380c15046c2c10f140c0030050107044044403404012607000c03200500c1e1107900305070351520305d4441540d002c0801070000b081140003500c2c9145886e203584200c07207074182861906d4203607000302c1080000a9515040703030300d00300400c00c0302500415040891034a031200f52980b1804601c24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 898858507 1250 898857257 898857283
    0xb01020703081c090c151b1211150411030c09011a0a090f030b18030708180f04060e090d18030609031701030308010515031e10051c06051602 62
    0x4407100791103800d81504100794541e40302c07981c59400d90710b40c444440764085070294500011f10307048482e08600e1007505c1000d6a00e0300001600c05c0034620070f00880d6040010080000d042c040d41c0c55071030b1b10094603c0c0e20345c09a0b00c913417140595020b0000034980b40c04420306145d4070036042c0c0001000070216007400403401e0100d480400c0d85d1810203500558600646500035100007099903000000d0000101c00980500f03035030998940c500742c80030081c41d44c2c0e00a0303d401070014202006075032051401d02050001e1058050001c007007094100d0001030488401e6444113038584058804c01c071000c8811301a2001241203424041c20711032030340e0120b074884a19804000c02480da00e100751414103004010301c181403180d1355005642913071280303402000c01d03a081c0308080c010841c0b62031b105100c065283c00ea074403a40101c1c110151009075900241c0f03010b080900540c400002d04040030070143c03245903000d000031015003206115000140b4044046860003000300e11052a0341c1c01d060300c3c05a010680c180071201c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 898859757 1250 898858507 898858537
    0x1c06151b12110304091506020318130f090c05011103040e0f040f08130305010b0913060504060f0e0102131d1303021c030902010f0503060a1e03120207090b0102070308 73
    0x14805106852404000c890794042c0d101c041000240c4201c0d03500014018031024105c1d20306035030b03110026030740c9014440340c010001103010328030307152400d100850024003884c914004c281c4000303007051402220504041030368000d481340d03818451540c0110036070300e0b0225440001c610f00381c9014521540b008014260305200c065440c081800d01844401d00050907411000d065500c05c0200ca0288c0d041a0030707c0100c4243d42090b1100125140c040070b0241300704c032004220300c190303031866594000070140100120b0712151360382e40000000c0c005101c1c200b10b00c91228001651031030705586610a804856009046003801d030b224058805070760b000c2082d0004008001c0410f565680d2505a007800d41400000303a580b50310320708030800c1e5641034020324401e6000781c07100e01c1c0d42da54004084400f0f100883d111750300b100740300750100305507000f014000f0300c0f1038a03040480380754649980d1540c00c04074013050148010380c00510b05002d64451071240b9886410700340010100c080c0b030355070f40411601a040313a00e0340003c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 898861007 1250 898859757 898859783
    0x5010804081323060f18150d1505030307020a06110109062a020705061b07030209040303090c080c031c0c0b18070503240c1c06151b 58
    0x1151800070364060b058044407500c0030a441d0518804082050003006006100103070040c0050b050240403107140003012050207140c0645081110700380f104585100390402c281c05109106010b044014122000d42c0c1400030602c1084820171150000c2c4580000e88290010011100140d9401142c0b4080b0340c0c0b1820000440300c42004510300411141c40042c03c0030307091498242c82401c03180e0350305007044d00e91420100092200c00040340e8904080c015a41c000d0820414501da8141b5854028070601540e422242400d8503540812503030b010580b009c8000c01d40f519002010440c1038039089018089200007031144444810010380d5502d9070704943e21011038801400302c62907101d14243d01200303030010024001030030959448a20303080142030b10903a5002d989008241407a0101c2c456201e0404110b018a10166922103100409006440406080b9040050307024542d201c200900c01200508070014006280c10040060303501b038006910704000f001003001200c81030320044404899000aa1070b0101c0b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 898862257 1250 898861007 898861013
    0x603050402061e03041e02010206010e1f121110080106140c030315040b0111070e25030606090b03041e02011b05161403060c03070e041109031b060405010804 69
    0x80c403d0702e0143d800c2c5031880300142c0200d00c025000750b00451041018400900c440d54030005a8174103458000e005800034401007120701c511989240d080a10141c070b143c440104c040c0030241c4d00403d42e00444500d80e81003c14424808074074940c07911424103179000500250841e800810b118014060003090010300680600091101c0342601c0a00201001720380d90b904008058038483e00c0c001ca0054440c038144190282c581d4424880c6c00301780302c0880e00820303045041080008603100010400c8441d40240f210a00c0d0b2410326060a000c12012074a000800c5828094000c0104d10903820004100707008205200c0010711100c01603100c1409441070072003078155440101c42800c80b80040f0301c1c0346000c80c81d5007400c0c440c012542000d48002a0310086007107960751030036009100c01d00201d40e40340c1c001070000ba072405483c0303009582c800010704c0c02d6850300070004001400ca03a00c0395044496100c0104615000342402c1100e180c03140d02e05850118254445030020328103105501906040141c01c801107010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 898863507 1250 898862257 898862269
    0x201021c1805040e030f210405010f0b06190806060706090b0703060b09060714010b060409063f050a08030a0c120b2b0812060307171903020c03161a0c070603050402 72
    0x1981c22107001c9887e050810741041400ba08401c800b802160f85013134012030b12841c0c42c804481141c0c0e04441e904038028401041075450b030030010003d98105008010800003d4130500c100c079a0103206243c3e40155040404008085515079041100c410804008601c450f54868081c1ca01c03090388149103401400c08519018050085004010707000003010902145c2440ba0781c000c41c040d221085603080f05100c109120300c1c8402503450701c041c0440400d00c0c0101e14041c0101c06200c00d10702640072100350640c0d41d40d42c483d8991049440e030b52095a9000c6a00c0700c1030b44001c1c1a290868145028454150702e403001400580b84140300450b0424034032035007950050b40800d1032200d01c1c1c00c0320020342c46000040319000260b9003100c1a81c8240a014408118100c8402c072a0350032011000080c0715603501203044050aa011260903000e40c030610807001242e0740c00308116004607c030b481940da116403a140078414840c180d130382e9030300e603407841803000b001c2c0608001044021900f02d40760204d2551a1400450302c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 898864757 1250 898863507 898863547
    0x4051c06090c0f051305010e0f04080705030304050615040905060604020c070506040909140a150c03020405030102270d0b1b040b0c03070227130201021c1805040e030f 73
    0x542140c0d244001086a140c50f001d6048035000d8805040080d8401000012100240214251f001224001c40e203c82100003031198042e10940069240120540310640303560002c4601311a20b0b4010420888800740c8400341450300a401d0b6028006c07c0d8807039460584840000300002c0c011640424603121030031081024400509011b0240b503652a103941c0500007400304024156604040c1002c425000d07600001c000c0d2007942c0240c1c1240c00340c3d0707180310080c02400741e01940004054007400301160a079000c1c8001c250104068803202c801114000540980c12188100345106503054072002d0003003410724001ca036015490b000e09506010059040c40788601954000d05080040840c5004c10343c42c00100510300f03d802120400861038459150784050302040144115452145010440d4060900040308260303105005641904403411a90b01500c0c0c55041008001a242d40d402c1c6d039009a01e51100c4060b11050340c007400140240124a0340d03a100d024015551500000303041440041101c003c0d10f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 898866007 1250 898864757 898864763
    0x6240f121a031c080a090c05090a14061f0305130803070206040b0907030f06020304020f090a090605060d0b1f1a0309061014010c0f1a07110304051c0609 67
    0x10324209400c810560006260040c000c0c490003070351031030f80f0091084400c3d0b01a00d90343d402071959a94003100d000740082400403610745401000c0800c00c1d5a56101042c400d10b401203000a0f80001c072120500c5c011006032450740030303024040f554200740d00303c001d00d01000030050401107940c3e00c400720011040e004440c00a05442e80220038442d80c158003042c4980560b00440308041c96850f001940c5441f0711040c400103201c404440c48800006000c0d03000b8650150004001c0d4081c0c0126a0104440344412140d0456080c1d0b207124103400c0007503e11945030410826140d60310804819a604844c280c3e024201451240b0340c0b07111807001101500e4800041e00741001360964401c00840c81e41001e4100740c078038031b0701c9010707103000510030805c00300c1804110384e4841c101000c200885401034450301402c1c00142c800c0340da41d009500c0410261202d000d0140d404140007805803031701980080c2550301101000d42c443c0c20400c410070580e0f07188102d0146a002000c14a6190304441c508880200300c000001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 898867257 1250 898866007 898866011
    0x310021b0105010308071b0609181418070b211801091b0509040302070e0c0f130503250905060607120906020f030a091503230a06240f12 60
    0x7000300243e21700030304107141c840c0c803011040614440f080c400d19030150040c0000a8181102003145c3d000c401c0c02c586400a82c07410004200400815540c000c00c1c048030054038100b100c6031080c030001000c120070030003050b00c280d00c079061410601d1322410320700002410418400c005004150b142d204694120210a01513000b0084a42c040c64801100101d20280300302007018010000f0f41d03030030450071407841a42c0c1603010707007402c90030070340c1c155944e910143c8000c20741002444001d80300f0b22108024102010b241c03074030040340f070300d0041054079040b5003500400100710321b480032081c415030604001081ea004207801081c00e07541c42010900902032440f0242401031585c201203180c40e0403c00480c1035940750782c241c1d1400341c41600015901e01c00c2a5001d4001450000f04010f026401c0d8581842d2070070302d20300850a100c1141000d40c100301e102e00140c1c4503481030000c3c400e801e580c910882005100320075051800901c0550906d400c5d050800c140000d00c600c16140c14880c0788500d4000003601000c0c0d40c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 898868507 1250 898867257 898867259
    0x1d061603020f0303070e130b03030319060b040816050102010b0312070312022205121b06300a06030b010308070314130315050135390310021b010501 65
    0xb004084d100380c446c1c2e06000d031070007030764205200c50070b4050701d040f0060140c000d502e541c840f50705003060040e00b110740080043e0b072440045016280440100001c01220700100004000700e070380e0070a0720b15035500c01e5055a14000b8000d01c2c2c1d443c0402e1003103040c02d500c100c06031100392038207041d20810b82800d000c543c0f00d8400a0300050380a40034039405035104038000d5000e403c0c1e450344248810038031070083c042d5040d03100c03152515a1101c0d0000540c842180a40800e0800c0301190703000014030703801d440f071101220590020510030341102e0004d0380d00110201c02442010720b541c458004446040c000640002d20000b140410315008284403112000316260050b65400302c41e500080e4401980030440f4039003108099409a00f44a009050696808050504003030344000340303403403d540010203544114101038000200500e800c0c0400204401501c100e01f002c042001005007100000c182c00d9031a44046002002c1c054030005468249030744410001a9078824040036501140d906c454641069070030280 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 898869757 1250 898868507 898868521
    0x504020f0a1e140901050d050903040e0c040b030705090418061505150f1605060403020604020108070c030e1306090f020915040614090a1e061d061603020f0303 70
    0x4000c08016520703035507038410b1442120b100c0214551401d5607000040840c100310314828100c000410711a44141045460310a5103500e070016a4012100b00d01e0f03503040400c00700003110035840d6035544891401d04480c509820076942003594000980040d0400001040720003541e2140d0380107050341e582219611b4482041351504001400c2ca41800040920b039006000689040031889400303064803100d15181080c070002c244801035048402d08646030703542c040c40700001c0303202801078601640c002d6000c1c00480c03500307000160111b4030240c00441003040e0a01070901080c1d00c00c83c200d076011421140000b1484400c0301c2c01c80500a6500b2280c0d1042ca030010358130b4100559030090080c81d4091340d02280c0000b4040c07581c0601e0085100d0385000c6000b115000c111000d99100420046400801180c0c00d1500ca009159440c068842c1c0840d080c402e01900b8045160401c68030345e9400340280000545891920200b21140580580780f00f4186014404004240c001e0040c0c110309400305044a40301d241c401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 898871007 1250 898869757 898869787
    0x11a0a0f140705100f0b130c0e120f0622060b03030f130e07170406150306020a0f030509061e1008010213170a0b070c0219080309040b0a060c0219050402 67
    0x203440091864503c81400c841502d0103600c401c202e000f0440d411f030140844140010f0409642c1e50f02c10402401036402c40d940e188645840d000c80c042008204442100d0645440c081015180c4034408400c2c200f41d942418944011071042544007802088040954000c07078030398054428070509000d0045050740950520750400d80440300c03509400192a1038010042d02e101e00c1c01d02d00721843c5520300b40054041202a000300c2844c034403440c406140c0b0395407621034100300e0300300c81c480c2800103403118040443c003a40b40c054503410840c004003400050a03c1d4031840d40d81d03401410300025200840c40004c805d848003041001c0280600d0009660310600ca411283c03a00c011400740d00b15144107103041000080c000602407223029803061510480d519109002c0d01e002d074900d1400c03680070f1552022140012640e20240c002000c60100035529400e0f418200016561007864203030007449030280070810b15030700000f4452600e80550700113501240e01049075a0a924541119411600016428003418450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 898872257 1250 898871007 898871023
    0x3020d05010605150c070e060a0b1305040c030911120309040f0b06031f08010c05121302121e1c0f1209230c0306180106180203010905011a0a0f140705 66
    0x2010641e560952141c098041c0c5802c1034800744c1c2c100000a006001c00c0c0d13882b1000b024024224040b102102c0c0da40c400007000d40c0c90040f1130400090b00c5481d030f070003044242001155510350494900740281c47d5000c58565a01800c240248110381740e0b16a000c50726100ea0007000814800b40c1943c0e40c916107101400c0051b10030300020075080f04500c0300081c015106119012088034150b40d001c0c548180d282c15a00c0349a009400080d0b213003080d600c000700503601c40c21f541c14401490740242c440084062141c2805041410300e0410303542100302c414805082c0002141002080d50800083c0c0700b041310000c480c41d043d03c0d25241c41441c07070b0402010510003515040d00d020f80c030024880d0400000410320079228109034645a4069011201156903001d810300d42040f91315600000040e00c0d40c1d64105121100d0042c0a900212039001005020301e503103038025540984402d40c0d50820340810104c500002c0d2103040300032010084000741e21030103071303100d09003404601c0c1548420a0b100c0d0003d0810580b121a5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 898873507 1250 898872257 898872277
    0xd0605070c020d1b0b12040204050c210f060402040803030606130510030509010f0b100c080d021201141008010b03090102041502010b030706081501030914030721030b0a03020d0501060515 82
    0xe04040003501e417141000301d50101503008402c1c103207500c49609101c040d05010f45200840f290034003038a04c6640c80f008038201c01c041da4412242041c18902c00c1c49102440203410359025a00400040c010902e0000c21290403030415242e175070792058004030840340c5125940040c9d0740100310307201c070031401941500024000da4680c1c008100b80301035420f0144c126030495501c0c6802000c100f4072074803c680941d4440c483d06005500c0e0515060004081030f00b01d138808086918001c941c50b005101c10150030002c03020180041e6440e02044100b00ca000d08200303414400c1c4902148000001808240e0a40640c0c00405004800c28152072407010041d020302072810034503000e807040341707000075420348200071341401001e100d0b5414042c1d1a1880044015018056007035030300b0002100c0c002040f07802040203042039400346055810100600304400403901d900b101d4001054144410201c00d5528100c48004499048440002c20840c5244c00c502500e0260b0003190f104443d0b8001c8403504d00784100038400c0c218 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 898874757 1250 898873507 898873553
    0x8010501091e09060f0c020f06010906080601180204120c090509060121020d3e03100b0d0213020c010e0106120807031110090308060f0d0605070c020d 66
    0x280310358a080456805821090800b4207016140280a5882d8400a00c842c01940e0120b00401a043c00303005544111450100581c0600c0008502c032100b4040b85000d070030400c2e41409110f25205080e40ea40c03a060090f603680f0358a100c02d11102c0f6a107607040310300a00b48000760040034441410035840300f175424810f01c4e40ca40c0c00d04001888030540420074905032103866160a010307008620248400c0c0d82d01d003400301d811074801c1c0281700100c0d103140311106020f40740e101840782141c102d07641074140c20000030411030794501d50301c6040016600840c000c080400c68a000240794060200041d001c410b00d002c0c065001103031035000034031100b040d030010910707102e01c18006e00042070b0903c01542201c0b15031040e1502e8801c82c0d001080011402c01c010803043d8081d240554030002441101410081c9429501441543e2581070b44201078225500547c811000c4441c014000c05560210f400300003126401010f0641d62000074050500403c3e01c0ca0307200703402070048031810b015231408260a441807042484144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 898876007 1250 898874757 898874759
    0xf0319030e0a41010807030c1710050312030907050d0c03060e0f07050f01091802040806010e0402040b011d09100b0a0903060522110a0e04050606010e10050f09030a060e0708010501 79
    0xf0380c20b481100c1d034010182c0d6402959034401d0342c00c030300030710b102050901007050200e4075010800c2513140b06405802c10410035542c1c18a080b00b0585020140d21004c5c030416000c0c070410050250100b4143c04940d030035101040703507540600e4065007440541c1c10050100e45090341100103058001185200c0104442c1102c05c400d495408011030706038034240b40d43c001240c0100c00c1c08880b0030702e01d0304076101c80003400160401782c8800001e82001c400360855076000700c0002c104000e43c9054050740340d88000030b0034035028001c07003c90703070103c00c084001c0d0301406030400700040344d900008c40364120014880208410348441e03040344000e2a0603075500c41501c095040c0700205c2c92800c01c40549164948840000198a188039a00c0b00f85500b00c01c0c0600742d100c8100034000950707445003002140704d103200b1000380c507052800c01d00162507542600034241c043c0801d0980c005006400c2803c5904100000c1c0c00c4a481e05c1c4c440c2c0019240100e003600040a5900300b0303024503249200042c05405440a60300280131603 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 898877257 1250 898876007 898876109
    0x109051501110d031e060308031b03070c060207050a02190509100605030103020d0807050d0309140705010f0e15210c13062703110f0319030e0a 63
    0x100d520042c0315807a0703003281d400c840841c2d000341d000380300c040300c5541e124022218114031007044904607803080d10009030000800079120080400503410341c41ea100050304500300b0110081043c0b107207080080650b5030010341c007028840c04002101205a0042c00504aa507007003165202d036000c1c40c410b8038040e208640200e16801011000201900c40760b944070340c20740e803a540800c4210724041c50141c40c114801c1000901064040c088245007881c1c585007c2001800c1d4580a03602e41488a0050100c7d00303d0303a4240041daa02c04030b603407031140f51460f081801105403000640c042034103800184c0c950400040a0782180c80e41100c0b2a1101043e50b0f000000d070b600c05c006e080841c8200341d803440032100c045206019640c01a603204004800c50a081254466a00ca8000c120000c80e0420344981d51003403d00c070414500600d80c55070180c016805171036121000034a000c0d40c21003500d002030a00203400c4d6000442c0e21030542084c0104501c840120038030001c60810a40c5040400380c440c0c0030f914104402c219 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 898878507 1250 898877257 898877267
    0x90506010311011218080a0521010f091b1805090a0912090f060c2132040317090d0c030507120323090604090e16030c0306050403030f02030109051501 66
    0x194560005d06a600001c46603168010741e444403080406011050003c50743c48001204046880e940085100e0165410074055500821551f070122084a085ca116059070440301d1151084011403424209840c1da20b101901400310040c1d08500d030026002c008000d051029500030043c0c15000b00841c0351223271944001142e180c284c2c3c0c054070005480b41c603801c01c5a00d01c904a0044111f00a414600074424009071046d48098990f11100016615415561506926450792943c00c201c118007490719810400c0011080d010340c0c0310162003005c04228400c401400743e4110740340c17208024030f0042c4142ca54901000c1c41d103601d00003034486104007400803511550100140209503051f855820520880040303c3e101c002c200380c80c4003080e40c0207100002c9540c460401800180024920100d801110f801a043c036040d0812451541100003042c100003203000a0610010742e50402c0001c01e041e80c49040660140c091190082c005610001c00051001181e52007640102400b0880b04818a41c910045074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 898879757 1250 898878507 898878521
    0x9061815090e16050a080622020901080c03070b0901020705040b030a05011e05090303010e040813030507080d0e03060618220602090450040321180204090201030905060103110112 78
    0x121b030764013007408070f19079a405003001210b0f0f5070b00002540013200306501203607000c0401e03806001c0c030703a10a569015180c0b03400d00c103610242c03a034030102600341181880003d540307050b10702c14140a10ba8961200110762001d10088c80550340140c000c0c012006404064582483c05200d46106030b8946030200b5a48107012007164120b900740c8a00d0040c58a690303d8160856008900700c0750b03400200c400000010304240400802000c481024102c60065000007a18a0921b101510b101e50015001c004296540070503d50994081d518042200c0e510880c0300d5000f2003c0d10103144d25a42884048400c0042e660020a036a4200380c1d0b090051280b603400b4141180e0441c40000c90240398086001c2c00f00400000d00c2c00d0200307000080d403c04400d0b003100450911000d83d4140c0009a0524052012040240e01c92180c00040101000003440804040f60300300c8400301c00074070554650600c4000d6a100350060708256800006852081d6503c2c03504890300008030422601256a0141c08403241441c1d100b006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 898881007 1250 898879757 898879769
    0x2030105010c0b06060d06170d02060103020928060f140d0c050f03011112010302090106080403090e072a0b1503030d0506041e090b0109061815090e16050a 68
    0x60b034000300964594554103801010b86810540501100d10051103d019840c000c00070b83c10302480748042c1740700340d500f071100c101105001d6520a9004200684031740200b580e00180300c0041520800d115040402100700c1c5108044201c0d040c107a0100b04e8045440501c411200b030600c01e5011014814203100c1c100d038070120058455181b100b001c20907420840740800401100800009540800001c2c0340115003190000e058060010700050007127042c50208ac82c00340c0348a042c0342c5014601540d00500c04c4002c0c1c000d903e0102040000700340c00d031f4020310880030003041b04414040710046c40b041c9010f400750a12003e03905500d80b070010401c44d8004000c41c80c030720a00034001d98544004100c00d1805404080d14254209035908808003c50700d445540010440d00c800300420030303481701c0c10120740025068000e98855032030b00320204000781c001d010b000b80d0f44070f0104000c94000d41c00c6901c9101e001340340d030000d44c6550804440f0304a0881c0401e1400c929414140b8040c0581c2d120002d002c5481641c0c0100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 898882257 1250 898881007 898881017
    0x30f1806060114041815081932030a080105040501060c0f020f09190506060306331306090b040815041b031127130303060e13150203010501 61
    0x104016500c240c3d2200d4101102584061506589641c03451015114054610308596540d60064480f403604445074001c002c0b81c0018070180388000503c80c0d9417140442c00030651781c0700c0c09203801c1101000c10f00d81d502c2000b00320710100c020400c0001946a6016170003000c0040c02010001c61035203850f2040b03c3c140c40d29942c4010740300340c60780d4501003c041e4491042c0c0e4000e00290010001c3d513a0601e000703108070583c0c801c036015a44103661500c02d0f6880030741190322070041481044000e403a00080096400c4514140550401300794001004800000e44140c41420000500b0303040c0e42c4101c5071100442c0c01a030f80d54a2080c1d6689a005428040d9004140058101e450140703a116040b14200c0c2c3c1003400303811404a40c03007414200b04000d01481d070045405003003501c0e80034281e10f008010f84000d030b2000c0c1e5440b20340315075451225000402c014030340040791031024000824144a58014005066260300b500071505000c2c2c6d00010b1a032800e441145e40282d5a0343e040c1c0d00105600980c0e040701d4043c0c5030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 898883507 1250 898882257 898882261
    0x1205061b040524040609180b01050909220501020c0c010c12031d070305010b011d03060c0c0c180f0115090513290a1e1203020c0d08030f1806 62
    0x40240e000500d400d01e6102c240e45144100000c0c000e4401080205051b494140801d490604061440b403800c0001e8070740180b801e41101c007240d0b0400121058040111340810b029912454600e010000070041c03001d05101aa81c000c042000550041001c556901e00305d80c2d20203045001100d41d02c04481005140800001203803d860b4041d0300003151840912405090754139200e040b45144c842254020b440390781d19a042404296001255800001c0a282113443e801003039501203540c854001d0700c0d4a20308000000e003212404400e22001e0455100244a039400071100914100c0e0b080080d6001c1c0700d540d440034000194110b208988130014949074844500d1f49180c40c00b08041c244084080303a49187e2902142c0414000c0400f580f50007555801203110b1071941c032800d21410540603000085090503402401031404400388a03c01122080594140c2081c030313500c1c0403410450b00b600c010b0380295000e100c403402c204d562340203140f28146d000c81c0c0f030420b903036994080c00003580083d07011300681e000100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 898884757 1250 898883507 898883509
    0x3030902130e10020702030f06040303090b0708090a03140904020d090b010b0702031903020c0a09050901200418060510020d2c0f030a0b0106030608011506020303070c0512041205061b0405 82
    0x540751943c0001d048d184090100603600b070070300800b10f43c11000280d5031010b010400282d4008580c100c645441d14003007074941040d4071079641c1c02c0c02d00040c060004142f40203504040240071100c0c1804c0c054019034444c60822800005441c40041c200c808100100010030044212800d64039219001401030041c82d2805d1003964440a1039807058045001e2081d4034100b507142c00d14854010b0984030070000344c0303161900f101403c442d01c03000c2492440b02640c02e45007000320101c0569059600031001e442c0c0911844240e04014240c03580501e400c14010101c01c44200e0b004075016180f0401600c40000030401100d5001840c0c030b40300d000300215024103031028414207240c9802034a050700130307089810003c481c1d01c2e081c0b0b500d076099004000090301d035401417141d1032003801401500030428255000150803d0300107034a03400024031407401c0100080c46a01804030410941071586030000300340d9030f26512003110641c5600c0303002c4150341502c240740124004018126500340070320080c420150500e0701b014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 898886007 1250 898884757 898884761
    0x13050f0115020a08180f150a030b0102010e010f0c09060c170a050c15010807120809010f05071509140f151008010e031b0706050a0302090409080703030902130e10 71
    0x4214011840360303415a81c0061140c400034600d100e511040f807810100010104812103206c0d1800070702450348020300c0350041d500e80c01070f50b4008125090200e83d100043d00100d0060800501c840425800e0445d079a018807880d61000c4400201d40c0d441c402425102d81c42074801c202e0500c0020107021090f040140e03a00310700c10143c01051154034002d45040030b210004d601c1c02050980c0368545844201c01041508070802c2000020941191100c15144460f1101283e500070702c10003e050154074561018080d22500c00c071071103254000c040c200c0b500c015508220003052551011a45240700c1711841c4001d01c0c0000f0a003444002200c010b20646042c101c01150340403002c2c0c90480340b8400c100c0701040c0c0b14001e0103022070f201404e13002191a040c1c460705000d80844020303501050754000e1102802515440130869400850300c3c00c3c0540e59a90b1034011030000c0c412500040c2103501c011030450105680742d080002154000c460118654105200c12000c0701c0c1085095003403a4403600c0340a094014503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 898887257 1250 898886007 898886039
    0x50a18150f090605160906020a0b0417040e09030c0d1b02010e132904140106081911030703150b072006040602030d060609120609150204090b13050f01 66
    0x301c0442c19110b196694010381300241d8a02035040610180c02c0c002c01d81c0054240010401d5100921040b44542c135900c9ca500701c040c00280c64002c00c11066004c5880c060b041f10700800c04402c0343c0110781361520029461360004541c0c0c162600078070a10994142c46504004501104c0c03c49614a20300c0b11b900655031440c00d0030106411071280c0c50303010340000ba98440d1962114012019500a9001d40484070200145030000d0f48900c0c94140701603100340d0903e1040e415528241482052501c0e015114003604030034900c400229030810000c400b401f00040040c50244802d0b0300c06010818214000000c99880c90041c4000003000380300e03c502003000c05142d000040c1e01004540c9414002c140465a10380c060b4005001603840004e11002145480c400d000c003d003224a003004041c0d081c410140c0e1b13522000103014148503180e81c039a80600c6545100d180c03044540d600e0856440e503980304528068084988503a2184034142403050b8400264000c4501c02c0607000e244c41c0c42c687c20040160005085 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 898888507 1250 898887257 898887281
    0x6030c141c0e030a0210050105150a05210123040e120a090b040816140904020105070203010209331204080a050717040905061c02040b0d15050a1815 65
    0x607408041c010080501c02132184002d0755010700250045559030606555060b4072981c01a208044d01c801840e801506407100002549005640d45500c2c5901d43e00070403030000ca5110141e40b240c00002c000d03007803108444c00c80c1900c940c8a01c070510780b18100012188c0da0b00c00786030b0315008021f80554019091005140c994040d0420700c11881c0c4a001c0000c0340e4000341c02c001034503446100340da026100d001006100800b0120118080710392b64401290744c0040160000b414000040740e4101107643c20b4050300c5409402504032804601c110151010301b42c0d801000d194117620782178580d02102110401c403480c100c101043c13400079803555610030005a112103132140c100141841a200004c903c4151060461070342c0403001d8442d801c107440308040755406013000d40f03e11042a20700d10017942d040744503404260100d40c0011003007101c101203a101200da48004040501440729a0f1403416180d100c60b0040000210801110704984a6544120500d11014240210740495202d4003240b0340c00250354460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 898889757 1250 898888507 898888511
    0x41503170f07080d110711150d0516030507031a0616080309010203010531090c320d082710020a02010806091314010216080406030c141c 60
    0x3140548000340c100440445050000084400350003140307014014400003800e01710351404004c0d584181004070428056802002c20070b038488640c807014000d9400c4400858401e0001e45455010031451002e100c04000229140c00f002c00c0300b1070310910030304011420022038551702c0b180078401c1220980108407081400b040030402c440000740b80c103001e035000e115142d00168981d410081000303100d001d441300b0071280881254500e0601e10400446050300200c0f060005480c002c2c6007403020091280d5080060214001d19945084241d50015a446480d490002d90071221102040050b0f00701199005032401c50f060040c20320701c0074180084000d00050714011200000340a01044200401402c05000768200ca00380d6000e41d600b148000d94044012121418985003001e82280c089030810300c0a02424140702644a000000750304a41450070003041219010391070f0703c2c20420070b43c094000c2100180c10011108162401001031b20a9205a403030010f041815103800e005201d910750441c600c0e415 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 898891007 1250 898889757 898889767
    0x120402030a0203010c090627231e041505030d05030901060f030b090f01110f0c01021c1b0e010f2d050d15050a290301080d08010504150317 61
    0x80d80910895904407403a850300b0341b00c00c0c80c1100140020401607002490940c0c150f40c1d00c03404071018440c803810b548015003c51880c14015507142c900d08480c1080503044542003a90300c0c80c0c9490020190181d41c41150280044055003d03c4036117500786110b031a8150740111094000300b40210080c5070f111000100005805542c0ca0310160400350381e5205031107400d107400a10850b03440c00d002d017118940c1500000d2001811009044c0c2c2c00d4400c3c0070110130741c07803c04070700702c89102800e404495065040c000e01c1c0321200d07000b0749982e0040403220655201740721f138003045021060003811034031400030050b1114201040b40d40400d403002c0c0c04064982c60a02c05105000e2052840c80011450317801040e628140c84850621840701220b5034254405030240241e541000180d8800600b0710903602d41e00d003c00341e00c034180301c461050407200c0011000740d5030001c80003084c0700c040040e844100713181c1d07542c901072240d03654800d00049802d815010f01e42e00c03500b44001d00101d1b0700303401070310310b02c00c4040a210b2030300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 898892257 1250 898891007 898891009
    0x40b0d051e07120e150c0307090b032d0405030307050d09080a1805011b080c0f0601080102070516030f11010e030d200303010e0708061c031806090b120402030a02 71
    0x9504030b030281d0100e09408560f07100710240d03100e4000c101c81c60324014014100101c1003820700b101c0c0101b4040c03940c800080014582485001d130540109181107440d0348900304038110303000d141c0c60701e00102d400c00d0400b12034035020701c1c0310741c426409030390820091443c50b103c801040700d0551100c54035090a035250841da000041c010001848190f5103980c840001c8e58102459044d0403940f40d1045041216000140f06224841001c1c5040030f5031000f0250b0751104c000010720300341a5251040316140c0900c1000107002034040d00100b9110b4826001c1d40c6040300001c00900f00c003103450201419542c08100303007400140e01e015241a82010505124089100020000303203815180411000000e850480000c00c1c020442900b048182000025500359810f0200485407480000c15039020480c80c42c02064070342c0c681e03502d0466440405410007820090742e090151900b806c00c408010704540886c000030716207120392802c00c2994540c4109510303110303105004070710340f0b4406881079902d405050010381c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 898893507 1250 898892257 898892311
    0x131a0703090b010e060a0905010605301821030a2f0706060b04050f0607030e03030d33060302070c0f0816080102160b090c0d061b0203040b0d05 63
    0x20300c4d075009514024540382040c01120340c0c44e60701000460b42000014026541c2180a03510041c200c000d84020f103800f00b580401c0301404041540109403410000d01003245c46405840c04110602c000f03e40307080c2407404408a5082701c00c480b1010300001070001c41d001c5003003030304504015842540600d099103c8000114000011442c0c050303034081c0002042c0c003c1200c00e0040c0740c010034011010724101850880852640000762503458450100040c5203020580502040d120100300a4100c90f1907074020540c4c10300528040001d015200c4401142d041c00480c04400a100c030402c2103480c980345c51400d04d06401a40010030200d4100b400d00d103001c070b1b2040307440c40380030001c0030070700b0082c40e44003c441800000f81c0d60a400101c03259004111000002044a80454880f9403201a403041035454411050400910348910340d80041865918000c3c0461031700405040410b800c44000c41c0b40000d10180c0e640d100b603125032401d04406019144050041d07030300c215400142d421082c0100000800810b0f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 898894757 1250 898893507 898893509
    0x60f0c0908010f0908180307031a0414060402010905041a061305040608160b1608160507050a0f14010c140102121b0304110f04060602060f131a0703090b01 68
    0x2002500303048041150350300900600c20a882a039804204c4e00c0c14a4a42d4049845812015503400c680c541441140d030b2410859400150b4200c103e0f401245242407140308045420380f02560001d90711241405952004203216003e02c1d4161500c1c544a8603050500000d0080401402c180005220140c107503501c8010051038841d0a500200b108581032001300000c030b80c2cbd0b40c3c2250084d40c3c080861441c3c0100c891010005807002190b09030b880b201700201000d0005400c60000b894803c003c1040c40c2c10f0032040440800745803042094403c3c9503200e80034085040c0d41031244c00e0b0400b64840b01082074110031540c8561810043c0341a96148966450300c0c03030040d403030041184082c0ccd4009080144450441c40081d04000480c0e480112800c1c0d80da1010030f81d01000d44098000d02a0706a01e42c0e040e0707161020307800110005841402500e9036030001940fa402d007111100e4101c040000082c50751500b0000c0e040c69281d024002c52802d40086240120400c402080d14061540d660303440700200b07502c076103024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 898896007 1250 898894757 898894781
    0xd0c0503061806030d05071106041205070806221b061808010b0a05130b090a0902090a0c02300d020301060e01020a020906060708130603021b06011d04060f 68
    0x25690342040c41c01d1141200d601c900c810b407400000010b003d425a00840e0403248800c5520313203642c850402d03061440d0183c00080019a10140000b00000c3c1407040700340009005005030152944aa07445882c0d948694045030303070080c2d04401009100e010031355134083c016482d0040003014492402001120740607401900202c6c00b1500c0e5510440100c120b10024070054650348000340111003a0002040c140c07480d43c002d00d4428900007600c1e00b5100c0e000d1303200070203600004004000a0500c0c2c00c550000301400c8806a00a80e0ba40e40041d50142c128080d03e416005076500500e1020442d140350001102010b203040031002144d41c800790820b079581e0103055418a2074400590740c0d41b4049002d0808091254094150341081c0064800b41e501c0c0007020703501c08400c0d20025502e080500c0c042005200300004240d03c0c02d011070021a4580d855809070400348034105e060342410104010355070341d401003445030007048840b40540d005507420b02d090032034009100300b2001c609010454030303581c240c40b03082e021a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 898897257 1250 898896007 898896017
    0x1209050c0306040b1006020106050a180b030607051306090b0403060203040f05010509010515011121090a08070e0c030c030a180204050f041b030503030a0c050408030a02031e18010c0204020d0c 84
    0x171100b5502c490000800402450000f000011b19010100714104e269100700c0e590720700703c10303c0000d03280916000b0420552005099824038546444041d006801c51b9030b050040b400648030200310140500f0915044e2203070310130440c0c06c0a01e165116130195000a00c1106c14911613406000024000d00a06000b00707985000407c0901c0c0080310b6003241085a0031141c1001203010700c03550b22690101d8092401e01024000403030712404500f8014061050b600e003150013070303641040014028400314105050361103c000c191079940701c2662600d406d000a9821040d18041007002c181000c94550108461542c5030000c12040c007015000030b022038100325030042c046889002080104404494124103c0b400540524203040c255260b140e520f020040480b01c2490703468065032040b42c0100709403801440c0d19000c890790303103036210b400079100e4001400780c8121000150084c006000390005840d00079411202e01c5c1d20404c41e501c0119888010303c2c0c030581e0015800c0090384051001c6e03024008243c0304a80321 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 898898507 1250 898897257 898897261
    0xa0503070b04050c0a0e190e03040611010606021c1809110702120f0a03140f03010305030a230d020d0e07060903110f09070f050d020a0c051c1209050c0306040b 70
    0x1049003400c40c11882e01d44078082c601c00c144030b40070b5241c01c6c0e56004071310240d1340060740e6101c50303c1c80b00404001c44a01100d1102040c002070b6152300113601080300c82507500a0003801c8d6039080c02e036581c050420b10f9581e1b50900304584032007603105d000c040c80c0b03513403038904490045a502c40105e0200e070120000b8403410080000c03954190300305012500c0d548242c00b0003d01203c1031400900761282581500101080f4034a00d0b4400301c509440180c0f1000781190820070303500c2d6035070300e0007682e00e0384400350840c0822401d0007400c3c1407540d00401442241e01030350580d440d2603001240716000b5401842c04603030850340c1d111030100900c002c000324409000c498031981e01c543d0a50908046000d000380541e0710641c400c0c014160b00c1e0701e0756042150045a141082851584a250191001d0103000c2c080120144086442680a640207002c5030703001d4000c005440360a5074068240702d0800e00b80c00c400d0082090b00e502d01c0141605544000b503240d00800c01d942c1c3c1e0801800020b408d208007036400791103104074801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898899757 1250 898898507 898898513
    0xa12141902010b010c260405150408061003023703061a0916080603030c06040c060f020a05150901060b04030b0411060c0c060315030d080f0c0a0915020a0503070b04 72
    0x840c140c0d0803142400c1000b0000f001c1c0e42d411070a0718031044101c040401e5100b089250790406e8003a50041c010050039511b5511a0007036101194010b84141c04c00b0b0b1080340003107000b541200440a040c2e80c0c01810308aa0302ca10b150386840c58180010702c100f440c4c2c121403010702e4038a01096024000d10b105040c0442c0d030f00044950075040c1220041814801e070b2000c02480303e080c1314207210314400c2d0b40e00d090175001607844a00003815801103620f481c4850083c1e008101c00c1000803001c101c19240d1945511000f01d031070613003c0ba5a81801d2000a04941c048085440d03511203040c005075120b2032070b0f0300120355561104160701741c40d001540100e4100a40c0ca00f44010003d111000c82402d038011b943c50360504848104140e581d2b40c0107644240120000000b0608049002e06000c0001c0d001500f10742061440a41c010706448080310507040c096151008607071a40080d804941040410b581c402440d01e017010825052a5100c030070490561190031070f110005407090000d052461300946e20014949042c1c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898901007 1250 898899757 898899761
    0x80f0a060c180e040f0c091b05030f06011107082e09020303031605130b0304060b01030614012007150207050a0302090a0b03011409030a17010501020a1214190201 71
    0x1d00e090080c0680c041a12507403141e5580100100e075584001040035071035508101c102c0c2201c8030000b03002c1e900f01000100390340d00345400609020600141082c0c8086040d81e040301c99000a848031b10b12a07040e180402d042d58421710740f041c510204d00c0c05440c2801d550b0041c041ca4225810030f000381c240c08001a1036005504182800d039900303481403050142d0350080e0b0000b5120b210040800d1a4010002180508a8854803e4075550b6101800092416803266802c0e0041d030411181100d24508107034060805521902480c400c64241c0070052406100001c0151344140308910f6403c2140410444100c501c081009490000c0100003410078842070403440090501c4440c3c2c00c202d0180003029410001610380702540c0303503c911441800512680000000707030140a082c0c0ca03123031810041308140210004007100500110b15903071502e0004810350b0342c3d0404203c2013445030901680003a2031050104d840920619090741c5a850120744045851480d07005503003100e4a480e41c000000c090080e0455024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898902257 1250 898901007 898901021
    0xf0b0109080307050d050a0e1525120e0d0f0c030c090c050d021c0e0c01170912091807020a062d1d06150907110c06070c080f0a06 57
    0x214042d40c074005254a68076607131000d165010301001700009180301e500d44100031104040200518400c000617484410380c51a0b007007112102c030702482e1a58102d8030394000c6000c100400d0340c00614403004643e044400d850310510704014540144104182c040014808240c001009100300185040d590541c145000c070b8082d2034200e104480d14042101000d144c00c201030f07a06a51100c200075944d4201141c4400121002d10504610282000c00c0303480d401c0008112404110f500b0303079849010210085041400190944d05d400b00340e003103135492780058070322880102072960020704125044503d0740611182080111600c030010b821100c2180b00304843d6002ea010344c01d801c00c4055000307040000c4415850b80d00c080c4010101d0b0307620800d610001c840d000c801040030b20560700341d540b40e2030105040c0320300c1100c5090b4a8421190100002c81c00341c00b9812402d2001d40392001001c0e18109501400103a5001110036240f04a5100001822201c2003100031004d03100f101c003402d100c0b01c9515100060380c1d00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898903507 1250 898902257 898902269
    0x10305010f110a0c061109040213060e0102010902180402010c02030312041a0421120f0b0a0504060b160501060308180a06230304080409050112030f0806060714070503010f0b0109 78
    0x10860454065070001d9050340140c1c0180d40065071060000c2046c1143c800c040c180390b0094008600e03041e14000c1c0b00c51103404c80b0b600e626405d40c0c00d030544004a00b21200110025849081c400e04080740c0285805000d034003078418100004003000a0b00080c0c41d5800010080d1881d40c0070004002c204070070149001584001f01201c4101820320356544082007000c00300c1003c60902d0704440162040c401c205c184040c07070214108002d00a00c035011a0081c04100c1445030040100c0d240000e02030515120b0401143c000450349810040e0600e50001d01c011010807d690070b640701c0101001195070000140760720343c07007903080c100e01450301070030f00c01d040640e68031584c20b000b41041d50f042c0031121140c1c240400e442051400b0b03902c0d074903803070b100b012801a41c00030640c403840d02c000030844843c07401c0a2082c1c1801b03925017545105030700b1400c03564844100c1c2d2a60304090180036480000d640591520401303940e03402511006c40e03c030030110f4211251020a020241c2d240e243c01d040550704041c0610190035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898904757 1250 898903507 898903541
    0xa0c030810030f3818100606030e0c120d1b050709050613050f06191a0a08330f151b0a12180e01030308010e06030d020a1203090209010305010f 63
    0xc4c054080c14002c0002845501100008040c00301c50141c00d00c105005911101401c2003078944686000b0f0061840c0c00c148189403080b00c40c4141d0602e06100c0b0740a00030084001441a2480b40004443c09500301d10456078081c60b070070384440010024424200a00311403100080d203072a001c0d00700851801c80040c1420301d1440d00e420300140c08503083c2c2550744080b05858140d01d54070354003014501100e40347d01000d1a00045450242c1071035440008002c03484c840e94074001907841d584501400010b0400b026141d01c5a119200d6070520a501d8901c4940c603001400303042c0c0c0518410101c4c642062031031030116850780015000c807010022552440020490354002e08520300e8969846d2131031210403c105007403160705c3c405260004000c0100201401038251603056a594070314019002c04000c1c05200d0058094034002112401c001070544c66440300c5030300400940c2016210640080d5900c6011000c0540304d40c0e840000d80c03241003621b0700031403050000160707018500a0345401c0720246880720340040d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898906007 1250 898904757 898904843
    0x40b04091e021309020a1107030506040615060804110103110a030506030f01090b0a1517010225030f030507020c0d050f1009030909110904091a06060a0c030810030f 72
    0x44400f22550184e9088120040c2d491211950aa800c030b240c89100c0122072084201c044104000810154000c91080c0e805010103147d9920192002c03e9038000d0720005940440000d01151100c64841074044060400080700c0100c0941d030807003640300c8003105e27002c01d072100306000140c1010410100000302110081141501c20354900c905d01d04003900d41c0030003030b807580c03c00030480208550303040042029605100e6419018a0300c1d034040d4114509402400071404075002d4074806100c102c003410390b13065035220082e20321580103800501c1c0240041c0214801c0071031038102a11040388201c50f60b8094001026a00540030400303103044102040500028140b00e1543d000035000034042c003d440da0f20320003040e40c1042500e040484c2c0100015958424105812030081c0003a9000719550742c844e82e4100d9009aa4410074090540305242e1000d000a0036110100b02087c400c1e0802c54000703020310038042e8401c1e13407070721040ca042c81c0903c4151094103c00e0030168441c0103804020403c2006400d1502030750f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898907257 1250 898906007 898906027
    0x1404170d08090c0108041103030301230901030309052e2d020d26040308010503010b010c0503090f120a0c26070312030b0d0c0620070317040b04091e02 66
    0x910050181c9134103100b6400c000c10204802000035200c0b070030b006011661207695415181840340040d800c0400f8aa24a0108032282c2c2043c0c1e500138103807038264480e00c010300d2600042c000d00c1802c0c2c648006000b04806130a420701c0038201c00307210001d2215901c943c4c0b490111142181e4811507450741c907000d91400680200c0168001c00c01c44964441c5080030071070401200c2c203440d004002c1e210503840f9180c1400c04c02081680041c0824180d800940080100e291080d006491030464484064074642c000c0c840c2d1285894560700f000610400580070294078140045800e142c8410703c00120b404603030911042c072001e480141d04241420604080d082400d4100c1d010719180c0c0d6543c0009009020b03135180310011a80290030464500c0700280c40b101001c4028100301c0000d00c114015200042c12141ea584110724a20341c0503a108400e03000580001071031b5a54403e040c100c030542d1100c002c0070a200000389904000b0250008200d81e08001c43c0c03c0030203046003906280c83c0c0240040c0c141c814407261800b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898908507 1250 898907257 898907263
    0x20309030f03190e03120406031b1701031b08030c030910090b19090503060a0b01030507022404020411030a02030412080702060412050c0a141002190f1404170d0809 72
    0x7164031500f00413500f124110302180c14141000506446288002000036046030303d58050451400000211108a948440200d55514000d120010800e66040c0188081111381e031401360800c80c80d403031700c1134960b40d00c9203040d04503004a525180309e50000b24503881c1c00e080c821202c108180076403170002c19250508280c030456025440000300c2001000021401c0c56001d62489005000300400b203504915001000c40d010384640550703540001e0810002c40c220030300000b66880080c4690910019001e00616103101c170b11001001a82d0041e102c9107285400708419000f1800b03230544000c056501e140c0340c18007861551000e040c0c0c0003000910720802c1000d590115200d900154040502010701d401d405040351a40101076002485018481e59501001607481d02001200010340a4440e116117119120040b801000761211084800e0072200300c1c0d96101f40c0c841040d032409400c2480c08140d01c4145c0c440940c1064100c544403a44c003003c40d00300000100f010002640c541d00d0405240c1c40c1182ca0252 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898909757 1250 898908507 898908547
    0x6030c070303021c060308030a060e060a0311190e0906010e0412050d09140f070506090f01080c21090c192102191a070503070227010303020309030f03 66
    0x108250303020950b130b41d11003402c1d501010361148051040c410240c0300c0c1420f0380c3c03560041d940d0303040aa103090400103031420155001072240ea0001d1204500750700d90749a0b8440303a854490081da001c1246c40344031745070b0064540008003404090611402914208021601d04001a0040102c038250501007000240002d4001c4c1c18166a625156031941049481d1001800204000500d10864a01e8007a201032000550850040006040b5501103586505100103031142c1d41c0f503543c0061120109512035402210555007001c000c80b800c40c605000203c015440842c02c1c05080240081c40080c4000702c0c034100700601059034200c4540c040f4820405005440300c2e0345100e40502c5c541c0301001030480e61201c0f901c001001e80c025284510900d003c0108641c4070b036817801407001250542c40030074000354001c01a2110715900000552501c3c1c115020400c403000d518003400300070b841203410103143e03a00756400c09000318842c0d0000c54590000200b014182000f100001841f42d0003441146a00201c140c0400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898911007 1250 898909757 898909763
    0x207120c0603020d0906060e1614030a1509090602360f03030c12030406060614030a1a03011506030c0e0f040e030f1602030d26090309120a0c0506030c07 67
    0x1030391150b5001301c51010700a401c82c0904283d25041d40051503000700044544500c41d409262030202510369025101d048981500310384901041c40080c507500701c55441010000948201c12000540d200e01e500141c0746480400c40750282c0100c2c0c0341c46104c485d2060002030700403904d50010010030340b69400c0c03403400c2c18404042c455100c5011066154030305100f282d02c1c02c0d01150940320724481c582d849030303c41e600941d0304480c21450b144000030aa4030461a003071091180f0110113180d501d801d064036000d080300d00f00e8849606070b094060080c0d65000d1060141d0300e00a10422500c1038a40000a01164203440291083c8035034484507101543e20a032010801040403140051306055508d10b56103076000e005ea01e5400050009201142c0302c0d031720001142820f01c200c04032083e204220100711594a05004c071010045907828100a030300000c4450964060071800403203050501420004003000403000d040c407440c1c0c10102c01441480b6000c6140c8000e4042039a9951950a1103104d5040d11b11443c0005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898912257 1250 898911007 898911011
    0x601020a0219050604090603050c0a0302030312072a120e06090105030429090c04090b0402010819111c06031703070c08030103140609010c080114060d020301060206070207120c0603 79
    0x46034031040c030800d0380b40039000c050038060300d41d525101010000d005d00d00080e140d920903880c031266245801020314043d658040c0155050220211008555460103480d00f0203102c2451003800000f005945c1116004d441005a03a0104495080c140d0404000d9210f010070810782c0001d174a002d40311902150018602843d003240e07030703580b030741001c03130340703410b004c0c10210182101c03601c2a00600303e0494414082c8030f010013584c0340c5e5095042040700311a0364103402031402102600283c0590f0043d00c0d03041d803045807400000f81e0101010b01300d80450b14110034802c8522404a0f846200c88510703070401c1410b02c00c101c0100285829503e400000b0943c0d4055014400b0000000032540c5202e0025000204d60040b0305c030780c580d40c50b45032449408149070591072081c803d2000152885105000d85090840e05480e68031260b420026016440001e100d901508803d003000003000f00c0b80c040c07006500900071079015010f503040c030490090811001d50b008500c5008548070410100c1d48000c140c404480644c00c4c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898913507 1250 898912257 898912279
    0xc03090303190809011b2628140c070f0b0f0709080c06182704110603061020060108010501030507120c1806080f0115090c08010e250203210601020a02 66
    0x2400281004c0310740c0302c049a10341901032148070a05202300d4050118040300c0b1502e801080700020046580000e1543c1d4600c2d400c10216600040d000000c00c0128050083d5811010700c90301ca40410700005da448283c0131140d4000c00c118250300001d014040c0144201070310300d414000c00010075a0051300110580d20074105150b0ba050f81c1c030700541240143c1144d07582c8045503410301e1141c0c9030310f0303003120280c03002132580791128075038038007802140d208030001442504880543d0100b191000304501d004100660b0b4041c0100f00c0e6007080000038001c1450740000f007015811454100d007403809980c085d4500c5001159004000744045412074252070300c003440c0003884d281c0c02c00001c020f40455403108520340500c88440d6071707488040d044540022002000300c4a89a500c0407464200c45c3c50103034038800a030542006010068010010303a400a500c050a908003650500c000514140041c1a01300964000150f101c80103034043c05548800c100200362085500d1300f000041d44a070480c910091003104c102c41 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898914757 1250 898913507 898913537
    0x9080a080a090503100221010312030e030d020c030702040b010c1e15020c010b1f0f05090609030d0504090c0203090a0e040213020c0106081509070b0c03090303190809011b 75
    0x480b0b2401400028203d40f4050740361906030f0001e601c0002ea48545200c0b2005540c0d000324000c1031107040b41e0303000d91620341e07120404408070002c100618040c8000e01007005680410300903030018280e01444807010315030350303049441000101c0d20300806450512501080c46804100c1c2d200c001c480c0611302e02c801414040c0c3c0d61a010800d00801401c80719a81c0c408a903d4501120560104502100994081c4078104200307444c49580f498174807541e0b0001c0ca130864144820352080c0040c010341c0801034200c41c148041d000020381003409400280303000941c0407400700300042890051002d5454240051440c0c0f04111000c00c8506000d405050b0f081d0500d400441c5c215100c0014010310194003000454850404c0811103000e440c4501c03c03100d0601c241c0c0307840350b07086131024640c0d4002c009081c010010349180055028243c2c00c0303134002c207102d8001401113200d662014001000415031a120245d6000c00b061000b400e0101c0203030030741406a01d060400d2030320003441446041050240e003002440e98441315 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898916007 1250 898914757 898914767
    0x51e0702070305013602060a030b0409020a060e0102160305060412020a05010905010b030c1e01030b1c06091e02030d05090307050d050d170c190903020405040b041209080a080a 77
    0x2600082c40d80d880c0c980300c61700b14903002c0798031035024100c952480000a80000c200c0e44854010b500a54419000c00280812500a0b40030403a0a40058004145500c21fa0001400c1c43c0b41940060003203103500d10000b1256905000150204e4041c0344c5807402d071030440d00e0311070303a6400081000b8800d03a5080c036505501c5000300224281c6a5003d0024440c107802850902e018108103400b60b07009225030b040c04825886c0000c0058a0088841c61800c11000c0010044028090080030650001680010342030090745031aa040030030b41c029117012a0040682c074194a111540180105100309184d00500041c0c1c1c012a491800181030b10f001c0e07841b035148400007420001903900c01c03584001c2c00d940c501c040040200c0c25000c460b00036250350b241c60390708102c107145002048540e010380300d400b00101d40740c00158400c0c04102402501d0405c598907141c0d800b140481c1e034192030580b2107180384000c200400021a40b04d1054410034902400d405140c24489035403840d040100412016020440c882d00300d00c58 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898917257 1250 898916007 898916009
    0xc04050d08121003060e03121609030f030e010219020105030402090415060f081902010f0c050102040e010612060f0f0e040204020c0601062c181f0603020c07050301051e070207 77
    0x94280610941442440344200c000d11340710403201c0c2400c0c88414501d0200100580c0c07ca520384002d4008160f40b50744840a1064070807403032405100f144040440410b0380181d01c1c080070303442522054180c240d1113002901c0c1c1180300401c00d03840c000385e049100050743e01000b03070703a0050341c1504c0320b004c60f444600d082d1101402244c0307062409403a24100103900048120214101e07003042003581c1241c84800000b04a10344031820183c046001e0025105031726108004c10f01d12540140e000505041e1a11000d032030011007039200c807002a81e4490304480c050402d201c1c4000070000003c1c0c41900c00d1a1081d01404a44503118034160206200d0000c0c00f03545507501100c110152030029184990f03125600544a880e192500a51103005140e843e0681442c0004e18140d02c100201700903651580c0c4040c054018078000c1507072501090b0400c190300401030030072003007000e468544ca0143c0c0303071449007054502d4000103030f122038820381c10b000c24403204001c005640703450700c008402d00035450ba80f90b00d0142d1038424a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898918507 1250 898917257 898917277
    0x30806010c12050d0b1903020907120f0c020d090e0c16050a0c0f080f0a060506030a0c0312121406040c050f0f180d0b150411070c0806010b030c04050d08 67
    0x49540201c10b095442402400b10909030f850410440700100284495000c1d010300c02c0039000c400c84405d03c050b01d012540c0301d50041180c1b41851820403040c200c039058810b401050040c403901c459002921030b405002840803060146840c42d00d844c9014441000b006026013488000b040001d0b66528142da0644c0030b0454a400c9411200310791110310f04124090502d21518100c1900000040b07800c3c1f001041503039030702050342c0c02400850465244c06008040203400302d40e0600c0b58015100c00298801c0241c001180034010f02c0c849505070304400741c0404001c401c0700c140c051034810201a0074018110311500514107590015001d10401d0040d5118031071540c220054510128100200c0b58102000380790350300704014503040100341d820500c10303a1840310100a2541d036480c400070b0783c0540e2814004800c0b4400034400f1880503011881c1c5441c40c1e222035010b413082e1b1034902003403282030803c001c541d005080c045056851890001490442e6004502910f031203aa512400b0f0018855038900355881422 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898919757 1250 898918507 898918523
    0x1e0709050a290705030a08060109120609060b0d020102331312030902030d030b0a092301060206071205090c0604060c06141306020d060306050906010e01150c030806010c 74
    0x7888501c100c50000040708280d020072811450108022100000d542d0102c1c4c0c010025410410422070558428000824260400c80340328400a13840024070790300342c0000c4c041c1000040d04c040d24200441911618000c2a004009a405031030050f603000841c0c0b0031a10802c002641c00102c42c40d103880d0306003030040c05030f04e1000c0204240606400c07005c9641d02c0082c0703d20302c01c445c0b1001c1d4078001c0c0c0c26610150006507043d01301d0018500d001d03001c0c0e003103140c8071a0002c102c91140c0da2a400760204490702e89144042007440d125042d1102c014403899035001d07102c140002d2109140080c00103000103185485140c0c895102d07008035900307003810048a140c4440c010f1280d6151030f100c41e0001c10303007040024241c1d0058100780150070b12484000d029401140c0c44050381e00003050944518000c0e5000d0300f08000740e51307582c1d0f00000c00b2441c80d2048a00840084010300131135490006080e01085041c2c111140c0a0b40c6107200c1e02c0e4080e00309071411115503041c10034910031344e91000140c484001d1048060b000320 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898920863 1106 898919757 898919759
    0x1917091507081003020303030a09030905090907171603150f1103240607030c02090106020d050720220c0206040f0609020303070606080601031a1e0709050a 68
    0x3c060030900c4144141da07540820b2540d44101d40035020345540d100752008060344218002d00801f81201c60b41400e082481c80580c5808007441940442e0020041c6500036440c10f202183d40c1046078002c00f280c01e070352400d0408020900c0c01500d100d00e803400080c640740c02807608c9480782d8200307601c12150035a6510300311034221400d0104c00c0e4038070f10100714075000d440d681d0000a001c821320a50340c140d10055144107010321000103070002402d5422210004000e01d90040c00d40d00d0003a000301e070b81040501c040129000032010aa038080e0000da0181800d458024090003503264201c1a1904000c0c070805014101d032240340075a0001c1140a9103507031000450704607000300b509140010f0961b498038507035944070000c4a95650114505411150042041c0400414400036410a200b058049803400703070991420ba517038402280e0882040d0f040850301140c42070708101d01a05002d0300080000d = true := by decide +kernel

theorem cover : BRFrame.Cov 898741007 898920863 := by
  have h0 := BRFrame.cov_init 898741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898741007 ≤ n) (h2 : n < 898920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
