-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:36:52.951436+00:00
-- url     : https://prove2.me/submissions/75ca4307-6c6b-4ff9-bf4b-4444d85509b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 615107913 ≤ n < 615287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 615109163 1250 615107913 615107917
    0xd02160218090f030a02060a090201120501031203180203030a180906180e030c300c010504050f160e040830090a0b0408031e0a020c0606091524 63
    0x861000c09200c41000114102031000f884030079140d2002e14a40760b002007000b0340340d220090018140640c1c070044e500940e40f051280250410414608115650312824903400740c022051002000034141549000c40c110540c0300c080315560702800440c2005642407065032152105441980b110405400000d40301c00c06010f01c60040440400d038252071110711044c2e5040d00c041800c5880d096004011042001c1c1c00052540941c000c080c05240400c1d611b1780000d1450710650a00c00b09188c00452000303007445066008a0041e07104000315280c00c40800002e58403112b55108240c0310b24050081000350342d580d0103101d41e00903c40e03403825141040142000b08217504200d0a150700003004441c0e80c8586d00c40d4605142c03c0010040181701a181075175944403030700801000140f5005000c0082140814030b1503030701c81c0c4080080e4080390580352140e5020000c0d0001c5184015520445c00032403035605060410b1030294540810030120100c1d45000d10150140159600d04800904039901c03a0703c10080d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 615110413 1250 615109163 615109189
    0xc0807060e012a0807120c180608090d0804021305091506060c0d0318050133050603040f0c03060c090504050606040815180604080d150b0d021602 64
    0x840094074592200d1400d0849080050980500c400c3d40d0000e619000c42a00e8445019104d00d0202d12a5540080407507244140140410b4594180350908400326000200e048404007003d400280e22035541c0302c100c41c02002660f2860203500404901d11301940b15442003907100c0d001408440b1603100080c00c2c07008030b80c0102d13030400494205604400490308905030041d000001104c146040010b400b40c0503864091280c0c0807001d1542c0c03540101080c2d002036900e241d04981000081204d2000305600145002044152007481c504503042c40030050b0399a000c41047d208013230041401c595459481c2e080502410030252055003514800100095081c010008a00303855560360782c01a103040144801d590001d0303d0140314400a000600503c80c000031040c080a0010b02d026034951500b06c2c03194604140e441c1d24801501801e0104020b00c03000c00000c048103003894070704003d50b0310803414100c2801c002d030082c040c02e06010400303c0e02171140d580142c500c4003001c0803115003070529a8006018048000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 615111663 1250 615110413 615110423
    0x705120423070308090418080a0504060f1b02100c1b05010215011404110d050406020310050d0c051509030708070503210421080d051f0e0406020a0c0807 67
    0x840e0012803034a402018481d800d411000400c151800d60783c40c1c0345140038028086000b95921825001107103a00d040da21082900480c00c16510524104014a0341e4094011040450540c402d5031081d2441050380ca020100b008000c20b507024a2a401c10000c0700030300e010030041010700342c0c02101146219207503250302400640f03541192441e0800180c10f1075100e8070304001c0b00007050010004907000c12000d0001650071280011000600005102030b0700841c1d9003411428a01410441003149540c0190700404444031b0444000340e0303c00403c94500c20300000200a4a0000410840c50030221482001304040a800030b040a440401107441c0042e03c1c0e001c4e08075540604c1003000582010b015420301080400400d009102c00281480307441d118034400c0410100390080201301041c1c2000760300030740d1507100051954880741c0504510281409a0700d00001d102a0014220b030210b09a0504040311001c1010002590b02c94840000039008200c810702800000f454040c00600781d01c0040a4040c410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 615112913 1250 615111663 615111683
    0x50a09030207050103020c25030b040f060f0504030e0f0325030606092009030309150d0606051e0702030a0c06090f0e060109140a05060408010b030120090907051204 72
    0x1030400030b28051080e440b06040c18130401406021007004502880c160251108046080012800ca100d4401c2d01da48003500340c00d502400d21040108170002c1c0780c80c1d1800f440701842912030740300b0782c0001c0750b00584006001ca420030321610740906009501c00c1d00000010300b5500140c14031587e2000156414000950b40d01a08905004020203407150708094420b0070010040340c2d0b00c400010039040c80c803440f1b0380a111404034440c4040c0e5000c10132600021005401d07180600181c06803407040340c110314000020315041490200d02e480c4158103480b46064074003041c6594103540d55092041c3d5212401c00c0c0c4e09805003141c1003010861020340c2d040100320035540c451155241900e5420060510b0700807000fa05030704c07414404140c1c2d114107200d007510100d4600024a131860700000d0f900c4400c0368040e503003003040460001021101948103050440e010340003480903084104d4040311001c0400100690787d8000e02901d42c40341004030300c882d800111800d2071741c54071005001d81010242d00f200e08031409125 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 615114163 1250 615112913 615112931
    0xb041406090c0411041a130305030d060305010f0c0504120503040b030f0906070201110706020a0203161101030b06092110050c030a0c022a010c0f0615050604030803040303090213050a 80
    0x40c1c81013814040100b0807140c1802d0a1500c01d00700c19440d00304815103c000420303035882440c04000d4180066a01904482d682d611042c00500900101d210a1381c45520300528000b02010602400b01c040842e540c5280c60b04c0d0030005080300d0007650010648072884140004905550040015805901005414455864440074181c50244001d101d1001c40e4108150296845420300985040c140e207c1009a114040c102c022171860080c6982111111000010340043c403032640c465015820302a64103028504569060180740e00c54018103a4000da078901d9030b03da0390030b806094103e05158160a030744491800c0e1151400395041030f00d41590626000041c001c212304c441c400c2c44810700d420b00252045c40c42c01c26101c844480c0c11420b000a8400300c001100540e8800d14250000c1503000103000761410a504202d00240310301c0c141e1004000c1400c074045410f14041c410345003101e0b40803646500d142c0e2641e8040303002d00305d8410101d80201d902c44450601c01c00c1401900d210710300a0000003400f000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 615115413 1250 615114163 615114169
    0x105010e1f0501080403120c120c0318110a0b040e0a0f1103070f0207120305040e0a1503060f0605060403060e0c060309070e0c0702030a0b0a0510050d0b041406090c 72
    0x20080c10349201c1c140c0010724201c0000007140c080c002c5072024200b41074541e035541020b403a000001c0f004980300c18946003441c4c0c681da4211140080301c2e10030741c000b0861001c0282c41a0101c0300d07804000401c142c4034070050400100c181004402c12a0080d004584042e60789010489a4000350080740c1d04030b031902c0800c4150580c500c9040c00c0a114448140031031510130702c410b1540e02c4040e180204000300341400da90b40c1ca0081000a0040690110104115030740b41070061268120b4041c0d8482c0c8107450000c182100620301070184910540c1180b02038151669440380c0050060344031425031503440740000100d99031740c0c0d0b01900040d40201da0104a9505200700f042c10100186100c62160205105000e2030320000030701d410a0323448106240c101d945640465801ba80100d41c0029814402d81000808015550002030f001d8642034005100036250301c1d034940d001441d94003074107070015000c04049000c901403041d80c5e504107001d0143c0210010244208604200d0111140d038140d51013101c5580c0c043c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 615116663 1250 615115413 615115439
    0xa0f2105070318030804030209040c080f010e010e010606050a05030a140720060708161209030504030311030702062b1b0207050604030203060402041d0601032303031e070507080c010501 81
    0x30410350240e400c03e034155507800c60f50340200d02002c1d020390f000c0d9001408200da00c404040c042c150760b41c203c42c92500750715441c0d8081c000d8492a0344035542400e801040c40c02050240701b05460154440500b80300010b10111542c2d0001040385104945030106280b13011462105075015079499034840d00007600c0702e0342484080800c80c120a040e544a1001c1100440e03100c001c090f00900303614005110f52007000c3d0b0444001880d02c0140084600d0900b5034000c1541010040c8100c0c0d1185c0c0342c045141c40201e085640300e0040001c080d4110074104400103005400154034004c680b944240c1c0c001200103c0901b03400c840024820610100720380700030766080d030f80403c500c000401003144d81074903060460307011903142c19024100901841d19150f8a1000310f400215035582400c41c2c0003160030715a503905001c4000c10700c0c4030480840d15120b0740d0b000210310020040301c2c4503c1d80d010400001d1050f24440312031101c1d00900036000c000091000c0070005030420010036410005400106180d41030040f0307800300c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 615117913 1250 615116663 615116687
    0x5040507050306030a030e030709110909070212030609060103381e040906110315010909020304050613080d090615090b010207090f020f040801021c0203090a0f21050703 74
    0xc8201803080200b543d6001440501803a03040c601f1454102800000c28502102508000c1c1e0550070300b40b803541c1601d41e560142241c0c00c8110341d00000b40d10740807020b91f02d4446600380300309a0b001c1080005e48508101990035009241850001a0010280301d040b4070014002004062a00826001c8181c0b500c0c80c10703100034680e03046a8100c0030940f05c0148140f01680d4207807a40c0035541320500101031000d180d03ca00c07c0c0d896820050b0781e8908e01000c4038259a040b8200c0f040c04690302c40c1c0c0c081150340040c0309403442503620000605d840d850b40400400e0480c1e003c101140c1c483c00c204500362100c21b050082031141446240040740c100d403a10350340c0d11054010741110903414604041ca00742681e0010b08a41200d0f64044001120740000f980800644524070b00341d40070b01400900001c402c4c405600074201074240b20046000742407600e90a80917444241c540c2e0b0000e612240030080402c02c04050009180c0c85000700e4440c210303801c980c1c11a80c4108801010224401041070010b00d500200e01c4085 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 615119163 1250 615117913 615117917
    0x14070b150f03070b0702151e0a02070614090904020d02030f07032d03050c1015151e03240f1d010b030109020d020909010902031b13030308090a060e0705040507 70
    0x40c1e0f50800105209500809402a100c0c0c2c2c45c0c0002040701c00382040460b110341528101e02c8040301300b80c8012070142d82c000d19072000144207010002402a101d070b60019802c42c003c2c01103c0c40c1040302d100300f0030443d0001e44160703480500d0040d01c40042ea01005003c0303d5030b2024018000382481c1d41030000042400401000400c10618141c401c05260207400c5400c565050500c11746400380d00c01100e2402e85022081c1082c5032900b2031507040200d8520a030b0007155035240d2454402d00d1030150446181182e44101e40f0307400c8400e00504803040c040e41140002007001710f9000c40c0023250b502071001c09405030703209200541c0014828452180160741c4c02c8564014441840740fa0352501d01c0d10800c0307200c14452581000c0d40170a008024a01d0754040340e030b030000e0040116505d941c5a0b220107000707600580301e05540800e00e00048008888400588501040d0130341030754402e82c03450f01c046e95504401040c0c00d0722400b8408115001030300500c00c06800c1c00e5010001c1120b1400c240610003161005021202 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 615120413 1250 615119163 615119173
    0x16050403050309100c15050f0606130608130602070c0311190e060d0f05011d191106070b07081e01051f1806020102071209120314070b150f03 62
    0xc00714900008940e0964026105440391203590ba82c110f030301e1440c03045e00501403480f00c1c1d4050303c80403041d00405c1c01004840058011501e0b00c0d41044401d01c00c040528000f10744080080051034000d000307440e8440d192858880700d600c05503032583d0403607000d050110751800c003e040070703c103001c4071040820101405480c00100710040031021112000188601211030400ea4001195911844801000194001d203030f00310002813490418041c1458441100740c440c0c2c90b140c5a0030996000a180c8100042010310704104802d60b1500f80c0c4190080380102c0e001035041010000145030300e4043d43c810b003456030300c01016042c2000740c07101d8074004e441c00444903c2c001d40144126a1440700d000d9806050350120500092100819a005007610a401020b403c0683d000903284c1d07010b4006003980da01c035184554540b120840107949120b45405505440020301100b000002c2c09103200c40e040c0104031612504095881e03a41309030b60102143c01d00000c013080d030400c108a0070403030b010701e00040c000c80c0609 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 615121663 1250 615120413 615120419
    0x60a050103030815010302040b0a0806040c0f14090312190f08060a090c0c060f0618020705030f0d060b0a1706030a020f1c0209040c03030816020c06090414010e160504 73
    0x600064010781380c0c00c415005013060b0b869581c001e90444008090301014140c8810600c200070302400c00464074640254103141303070881450f02c6500342c20326030310540d01c5681070701804aa00c82801c0e00300d412400d406100e01c2c0c03402078190014070301400d00501180708184d022499010000e04a0a610100d1810b000540040c402599203078030b039090a42c4c46481000038001a00b5004a40241c4464405801c5030f10f409081c1009061a41201003039944002d4403155840d84082013100f217200b560000f070b10941044c02a0003004108400900c0002c070f03d1071002c00c03c503803640040b500b180d02c040d51442c08a400c03540022007a41c944900607906c84411000303003000a00e25004180c0030501c65122620078480c0881c01c24000c840380848510840c0c0142c81034507a403a0619140b5146144c90000350040781481c40040c800340c0e10318101c102004c116034040c00552040e030082c0141d030307000001c0007540152601e110150291014440500a000d190140c628034140007802031058411128800100300d000c0000f8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 615122913 1250 615121663 615121667
    0x21f151a0301170a0507060c0f0f08030907050d1109060102120409060e13030c02041d010e0a2d080306060d181b0e0135030702010e0a030203060f070504150c05060a05010303 76
    0xc51b04588103420000303610b500038988080c010121003401020000e964843ca001e002103200a03602c58401c40e41200ca20030303107800070800301d42108a002442c408490b0140341c0103060041c3c0d00c580060b0180100c0d040391410032001c0d00560490740150200f6540c0707403002c0081e0340d031107000345405c482a680030182030348050f1402840f20bc01120040e0050392951114414040c01c111089071001d400002040002c0300740940039203a00002d40c0c03d889600385840d15000c080d18030101d030301032482511222403290503590703207404003900006d103001d0384170f1824060607050b140035000f2494060384d210b180b442038041c1460600700c1150924525062051404400d0001003c0364400301d054a0b8810700b98010747c08814040030410980c0500d00d200601800316814111800002038046079200340c0311828400d0303005003406090507851002941c55400000442c200303010710308034a50052014600545013a0703d4401075a00708001021400c0000d400c1032401e0180003041c840345421000f41c0c0c405104c0c951443d140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 615124163 1250 615122913 615122923
    0x240c09060503070e01050f0c060412050f0720060a0c02090a0e15130807081c05060619200a0605090f030a050d02090a0905090d021f151a0301170a05 65
    0x15600a0040202941406a0246c07003950070100812002c0c3d030759080c0c01c01035207403526403d90341165000705801002401c50b00800a444250f840d0700c120505203034164848a888640042c02001880b0410b4200c06030b68890f04010311601803286c40d04500c003034403071041c08607010004140c1401075143c0000b807a04d01c0d0340400c0b44500542d10000036041a1180c0d400810911501c08c0020300039100050000104111034014007a815041100d586951000c4a50f0038151441209c0c01e0364450410000702c01c45e449041c455000c00c2c840c40c0340c807940b508004c0d00a5480d00c0e03c0c0f540301200e035a110100c60810400c03240101588031503580084c0c5071030502020804d03680d02642e543d070000c0c4030f00494103c03008049039060f01d216000007041009001da07104c1c008801400300340d0700038510f809100000c42c1c0040c00008e06010301c030b204240041e060500310708003000421020311a0350b10280400400910100100c180c0c400c480301c00d0003002d6480d40740c4949160120380c070042555040e00700c01506000301d140894 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 615125413 1250 615124163 615124171
    0x3020d0309030215010906051c05060c160609080417010608060c09180708070e030609060a0f0908030c190f02060c03100801020c07030203010f0603020f040b060403240c09060503 78
    0x103001c20a40030520b02a03080c18054050304100026200c0000742140f03076030b0080c3e1300b11403081d0381441c0e04408040d80308807649260b61024010381d21135400f003078550801c00010151142c40c0d0030304400d6030341075545900a445a5030425584404082014030415400354901c4244045500007003001d94a880d000b1a00c0d200c008100b00b100120100380c0c45440d84620300044000d2004046100d12031a0039032001d0181d02e005c6d2102000110100d060700782c0e40c24009100c902031090070000b000265a50308804015148142d410102e00e519040c0c1640041c0ca500040c1d80039115408105032143e00c030190302c000164280c11840200104bd0165414140c0c000c155542c0141080481e80d64075650000004105162540076155540c40010104503460000c00c2090549100320000d00c00d55260009040a442d100d02010b0b50042d08040007a11514240d8070101404001038051820640e4944803200c26401c0c0481c00c0088204074540c15204002c42d2007211440e001d070b402d11404003810f0050041c02404018 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 615126663 1250 615125413 615125417
    0x60c090807140f0402030a02190305222003010b10030609150605040b1303121e02010c09050d140607080a0b06031e06150f04090b030c013615120903020d 67
    0x5c2059401f03a81c044400c0c1c402588401c00414a110400500802041f1041d2503000440300344442d01c0c00000c61030f07501580e007000084034007030500703da44081e00082d00101945907585010202041d151f01550303069001c607070745002454504c0c0504007000d46009075545440c0d4204840144102500f0100b03540940700ca80c0ea00e181c9a081c590203202620300c030ba40000d000703141c01540c205446030b0b0241c510310a06a00084134030181d400030000780e00743e40c8040401c00c042107110b80b05020908103001e10341040c074040c40102c0c5065403a12415400c041040d05c01070300107001802003103034cd2402801107580c1480251141031852400288046900180c401102d044941c1903010407071a035124504000303201d5220b0007a40d51740c4015624404541d10030b200d2809540d080101c011b003d0b15022800c00600c14041e191a482a0f0100e0072005000248020810240d582081d859940c80154004203005e042c0076006103440020b5100b02a10007050112510f000030304081c0341c440081d42c003041e6401c5581040c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 615127913 1250 615126663 615126667
    0x21040312050d020c0304030809040b04090201021c170a2306030a0201031a09190605010306050d06020f0c01020a020717190b0a09150911060f0421060c090807140f0402 73
    0x740b003400a4400c120311141c61707102c04240030051180d8600203124000d4202c40801c2050841c070203210954858000190258001c40740c0700302c003d1803d002c0c1251501082ca00f001c10030848840a248400c0f05035143c8c2d4a441d0303920b04045903104820305c1000c583c070b0f45240300801450400b000030345da030000e0180203040548034200c034150482600c03070a140810b002403501c3c110303150900c2c141c04140c4006200c0c41500742440300004803540688281c0051340d00251803045042c4807a1a0900a0351000d1040c0038441020041003d082d5828806014a03030380643c050b0240519205194501c1e650404a00203941c00440e424050544100660342c0450740c00076460f01d56644000f0031100800b0400c10203006031803c81220341541180f07900242c4c55900c00c1e2400d03135110b00c200003844028010301483e608100c2c81080300303120342d86038883c0b50100100100c3d10310b481306040d580d401013540d20b0b0f12a000082140f4820a11404106001d19801342000e510405001e5040000003404580314203600360040d540 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 615129163 1250 615127913 615127927
    0xc03041a0403080d1505121e0f0d05070606060f050702040f0e0307110415030b0c0309010b060c1501061110020f090909100e0d080f10172104031205 65
    0x15902a01c006580181e00390382ca410b1100000c00140c0341d0744110a8942111050200f140d00e4245540040e40484c40020f050b413031142030800442100b00c0c2c070002542c1c0704080301182d00c40b0301040341001c60003d03503a80d2a12101d10340703014010395509030480b070140141e00d107401c031500b07603c0019680c034a6011500488c5030445055403000600c20000d203940d25000020f41d86049c070245110f144d00380d80b41a282040b062912110100b20300d40b250100801d01e00c07401d404a130105008101542d00080140300001e05074402000003840ca500007801007540d0303003004001542e16502000742e06d00400301401e02158155481381000e4a8000c5290044105940840c01c01040d016400c1914218000506500b005007408820695900454420020b10b00d0400001903000e050108401807003038441d131651811915081400415944018101e010b90303024424000b985840020b048850280c05402600c0382e80803a0f4580000040750089802000740100030400c0002c1c800035284844000c103190030f030b8848078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 615130413 1250 615129163 615129209
    0x1c0f0c0b04020a03120507030e0a060e06030a0b060a08071815051b190c0b0a0c1101031820010801030b18071d010e0a0b0d0b0a0f02030f0f0601050c0304 67
    0x2113904080c04403c11190003280a80e00301c4000d001c5d0a011740c44090303400c030044080101d15400340c080d2000243c0407240d0000381c1e0400c0c0b00a540c0142807001c000c02c1070f0840e50b001c110b240c2c0004040d0300004e84c2d00004c0c041495001992011007020420000c10500c1c00d014000001880041c44401000800500440340381400c58440220300d200c402a942c0c0c406010b244c031510300000c202c040c0c880000151000941c0c1110b04110703203e500c800d8840c141c580c28945c8802260707820040000781031584448030907011031280604040303d0b07840744404009010240007102c2000729020a05030500505900501c0403814501420743d008504001c1012485070b46628903080c29115409502040d640c0d0555100241d0000c2d4114142c80c89000a903843c3d9942488070001d43d0540d9613081e4200d00403003141c0000c698000001d503840614000301141c409414000d1000300d900841d0300481c41c030516014002c11087d4240c560750009000d05c1c100b800c065144964549a102d1480f0710741010f03da0284c8002160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 615131663 1250 615130413 615130429
    0x50414120c100315030804030c150c0807060204080303100e01050411030c0705010b0a0e011d010501170702190507050406060201050906150a03080703111c020a080f040b07051c0f0c0b0402 82
    0x1010407162140d940350761b450300008a401601080740d40b00d002030310204e440030080304501410415076480c0c030000892602c0c0c10308142d00c55030f015281a9000c200100d0140d5080000314040d403150701d014443d291030100031084104041c0c0100b40304034101908041c2c0320f0070100c1501d400240300b04d4000e50b00c55841c540280100f641c400034a810098011000500f8084040424100c60911200e40356020308144441401e9009020700ca01081e03014841c0c480b40c03000c10301800d0b440421401250180024081425441c20402d0b0044a82d940007020511850a0501403c40207045c0c0e40000d005500300440003a0703c0f4403004040120303002d0320f41d59000240d9038621020000b1a00100f00540e00d09150a00a0644040f082d079004c076440740f10340c903071050403c0b0038690b400d140d4244c0c0138040c404a80d03614542d05900203001180140000e100c003194011980c4002e00400c0d1081c0c0081120703001d2a5450140340c1c140e14010820b00c112043c020060740d81103074400c90710310b5001e0485240d95885200188001c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 615132913 1250 615131663 615131681
    0x140304050406060206040309120c0303180e150109080109020906061309020d02040311460e0708010f0f0b16051005180708030d0213080d050414120c1003 67
    0x90400c58006500c60f008205140a45d00944d40c10b48e5103901c0340b2112848818103100100400e00101041020a04c940c0c2e4a1710301c0d0000350051080265900203442d0100342c02d071030420080d58034003103042e1503680080c00c070001043c12000034008600c05400144442a00410301401880c0019000e19070201c8140480050031334a242103444241c0192910001d41043c041126412032540000506150a00303110b103845250200c3d49039a48d008520525600308050403a00c03035101c1440d47c544000b0728000201e000303445070500d031490601c3c02a80080c500041a400580f6600c8407a5051004160400c950015180c074010311560780d071251000c589020754001d4019040b4040c40078912035043c19078001500941c2c0c900c07003401c0228003c0512584a43c2035101e4000260320030480c01c0e483c402641c01500d84468001074261001d0fa0303403100113007000481c40c08540001e400240611a401460991403660182501c00d50900b100740042d00d40d94600040300c0d10311402041c5072403501c043c07081d0400000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 615134163 1250 615132913 615132919
    0x14030403050c070e0109200319021813020c060f10060507230615030c18040f0f141c0f030b13020406090e07020f07060f121d0111040f0314030405 64
    0xd40d13a4030300260000340f00c4e843c005a401c1204039141e04581007c0780039203000d140c000184842000d95030301c260b0000c1d032044406140d0207542c82d079080c2190340c1714501c0f100c4100c0e50748409070fa00c00824041c40d0910320300130a0380715003240031030900100d81c00c112503560a0f00d106003486550b410f224140b5051044084e9101c0030f090a089035660210000811924010311003080f803903002002080405885c0d198003030310a074010319400810f20449003d07001880c1c000c1e019806400382e5a805071103420340000300440a542c03000580540e12488501000b10b87e40602a00c85941100d0501d01e100038240c1c41811404c0c41015242c950300301150307803007400120460200c0f200842d6190fa407010050140d03401807251248c0d0010a03000035880c14004a000b8115410a201420650f42800da081c0c0d494610440203000300300360a81014050070040c41744440c10700120100c80d4400005003a00c50a5441c13181046d00000d4003444108141c08030b10581c0020340c0e600400c01284c403510b0f15001481c6004c2c680c00994 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 615135413 1250 615134163 615134189
    0x70614011205071413020f0d02132102150c070f0f050405061203091203130f180905031801030b04020a03050613050f011512111914030403050c07 64
    0x621680980819070307010711600580303910607565101804000709142000d90411400c0c0d0213020300140e01d80c0280b0700454040442803e110840e01d4840890f0800348050003000c4c0e041c0018002c1c140c8901044024803640070104865410f580d011403500041540004602c0001007428103c40c0e00c140110009454200304c0d80b4440c039661060a000310b412841140d008a14041c04500d643c00c2501e814003861165000031441d042d00101030100d110404080c1140500050200080c040e805032414001451031100c0c0c0f14040d810460038038074142c1c0198610040f0f034502480800056008010341d075094072500d40402241c0e503482c0060b8081d15010031400ea0061000800d01e031810341550040b4094001610541e54020442188408640c81a00d01c005540d907a1801000212415035008a10040c03d20b4801c4001070a0002d040603242e000c00b142c01c43c0600802e5600060140542d00c040c0d00007070b07141c14081000031400440c1b86c0c0c07102034405000c10200240c6640030800c104030f94001841405a009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 615136663 1250 615135413 615135419
    0x51c0f0f171015090503030405090907090603050d0806010c020102060105010e03030412080a0f09030809060d02120721180f020a0b0c0f070f06080622020c0c0a0602060403050f07061401 81
    0x40400241d004440d56003000c2c3c444894003501c2a9801030503690003400440c5080c2c144003c20001040081c000242c9209071301c4007052440160084d0b00c000e51040c4002c142c0b10224046c050110310009001d80d04006841180c2c00260b1790001c2d04a04443e4203007810100d200ca0100424203503c03890700012450b01c03175a18900100280c000007031415080541e280100c0c15841c02c800c80b42d801c1d0510025140c80380a0200440d03c0c60464000c10003003907070700001031404044c01c400303801081003110910041107c004004075003402450344141e40281c00780c01000080c0c40415015503008980a01600c5081c1100009046490b10702c240e0002c4d11480c9146a00c1f540c24000d203590b0303140c4201c2440403c0c0036901000940a085000b14010761b003498441d4a1607139114010301102080603241294000841152031940c440303280b0050160f000180c002c0c0651010b10828001580d83d554010341c2151710000400c008280d000050303c45511000b080d0569503001402c1920140280ca11a14066600c81d4000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 615137913 1250 615136663 615136681
    0x60515061309052d06010521040c0e06130b03012307090b0a0917071a071b06020d110c041b0305090105070e06070503041208030103051c0f0f17 63
    0x242040300e0091030700380002d54401c1444050071310804007042d480200c41c90744034a541e56900340b4950000c0c0602d0468100030190811080c2c00008010742d8101d1004030301400188040d06074080d018140062800000b03041110108a600e84041c1d405c07586607a1354a065a101c0d90203400400d04810000108a480d81c29485403d10801e810358080c00424030a00b00000c0e0b203801386007a60f062820710788070000720300d01d4210958088541302900c48203a005044000c10104541907090700d210050b440348039141d55292421844041702070300b4041d90148449400c0020f9980055624103003060f601d811201c0726803542441d882e010303816242c10340c0701d800c20086606010500001c0250384082d41d5007405181c6490425500b01d41050b120380c80051883c5400e40141d080000003854650704c01e070701f200e150581d1240356804071520704404680320f031400401002840410040e0030021001c240343d403c3c41c074041000150140b0a942011810b2200e04e940b41d42c0d8090043d030265401e48480d42d0700000e5481c04400b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 615139163 1250 615137913 615137947
    0x6090c130902060c150a050903030402151209030c0705030304030512070c0e07170c07110f12060a0b010e10020d0e0a0305010c030525050715020408030705030403020301110f030406051506 82
    0x4006480402c400090701d51b50a07005482c064882c0d60091441d540712034090090196054083d500b840500704030002c240c1300000b02d050305c5036510354003a50b100c102c191074035400d02410354001171280c1d006000601c0800c034080b4642050b191402e91140e994517041c5010b11400019500160022102d10308114420b600515116401a01103450b12000d0740d0341200c0041601541ea4060705409603c940100d42e400c14a40e441c2250307400804050300080025480c0d4940001250179005454035440400e0842d60403058280341c01c1411102c0c44001000c49400139070310ba2010540300c040088200b01c1303d141da240c8464081c0550b801c203000740000d043d484000341c00303440c007569107941941e005442c01c240c1506000d0701000740b107001e1741d58a1511206840c0c045140c0b81903000c611207258200310005000008000818520b8800d44c05591160300e540100740c212040c43c106050124000c010035050540403108030b03076000d580202c0c0000d454907200c11950480040d803e906405c1440090208140144104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 615140413 1250 615139163 615139183
    0x50f2a010207030f0302040815150a12120207030b07050d090c030f0b0603010209010f1206080d021f140403030c030f0c09050a0510020307020904031106070f02060906090c130902060c 80
    0x485411100900000320101e1045100308e802c1038000c42e01d00034900c051818000d4001e1100c0324071800a00c01c000c0005c40b82da0072503206840d00441e84030603e0400121f5400a41800e0190019001d06403031502c600301032603401080f840410000064640c49a2056407011481c15040085012440c0d113910300118441c000d00e4007034640c5155a00081c1c1e00e8070701402114075544040e500c69a4002821105442c4c1e040c0003540442a41d0300c480380800c507040104202500084103500504100000b00000040601103094248405040602d0142401000c0344a245c20550620700060850040d00c0120004c00603001a140d07181d045c1485940f030742d039000400005540341218000c1d2041d84d103604020031034012000002c0036030000d01a01c00546081240158030a000c1e0508244050301c8401c1c035424103804075540c0380440d41800078102040d60400c02c039030340034140310700802c020f040c262400d680d1407c6100c521446100d41203035041c0f2503031494011840c4036601034030341a141c0c81c440c07045907101c000400d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 615141663 1250 615140413 615140417
    0x4050111011109060901031b17092e1e0b0a170d050c0a050a0b07080f1302041a03010510080105060108070912080c1905070b0703050f2a01020703 64
    0x80c8203064809418442c503810901124002c0345002c1c0c8040501c4101e81105aa80d070515603140381040c02d2a020401c0103501c4410342c2e50fa40c890068020000c50144405842046aa848503206070a520441c3e54414143c1030182940701a5529414121000d006964004c075840c0034078001d40f00c00420f40360030050000e1021162041001d880721020444d600c2c2c03141071031102e41d0102c2c4207100311030300400041c100c40c002c07042651070300c010985803c0d25082150034200d658070b5a1008001269078090790054020004024a5002d400c000142d22440b002900010f40f10340da0b1249403040c1d5542c0507004280109010f4003d0041c3c1c47c02c44510f050390085032007044815401d140c001040c40d0710528640303120749004c2c5c41c0e41d807109040003406a03c3d00c135219412502c41c1810031a9450142040180d400207038424400000103040624010382045201e81c00f4100301e40052000c4800a80c12506071003001110507203554480b84007020030b040c103c0712006004241800ba42e00034020321010b40050008500a0b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 615142913 1250 615141663 615141677
    0x2704063305010206090d0215150306010303051c02030c18060c0a050f011a03120a0504030803010e09010e030a0c060b0301060302091003030e010e100f020c132f1b070317040501 77
    0x3880c1150300e1b12242e004200058100407034048022503600440c1d81c0010700318241900b070107034400119140880c00c0e082030340070540c08a900b500701c60311000440f0f08861044825410350910740c44216150060302101c1080d014404400109138688400340c0e103220150200702c640e08103240c103140b61243e483d01410302c0554280748015100300c144008050411102900401c005c03034072001241003d800640a1034104030042100001180d440005540030b841c80318001500350615880b540e00b1903030b007546125525082407041e801c00035000001c10340e03100d40110001c203042110300b0009005042d583c01c025881000700d02480300154800d203d4000792442502c69a0000090000644080d00303035121030303640071001810045425104500030b11100d803081c0115048100b41c3d0700051054010380030000d50440e69650410305200b0151071044596804040e0b994205180c61040300c0c9500c02c100c41340602c0c6503003500d424401c203001c01840005580142e144e04000400100304102075205210f114009a04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 615144163 1250 615142913 615142921
    0x4031814120d1707020a050d0305180f10020f07020904030507021206040209070c050c0a14130908040b1b0313030b06010e030714040f020c0703022704063305010206 72
    0x1d0001d2090420f07440d00c020b00603100c800c0c2600820010302c1c0404500442c03000000051003000b00c15010202914042181c0c54507420711090507142c060400c00039400b41d00d10010300b10001c02d00c1c0940b21004500540d554402101c000303154400c040000713405c81c2075502000103255222026180c6544211207965521851102c0c01d03580307000645003e9445180000883c99490148000c80f8409100b0010b55040c60001c2d00022540501070f88841c0721300c0340030300c0c4a078401d103440354040103000b8000307a00708408041c41d1265100c03406230340584070710102c000400300c607a01180003014580c3c40d0803d00300c9564802da0011000305143c640300440e0012141c2c4046440b940c003441040c040704c0b0010b03004004c40c61400b0000c0c01c0c021440d03143d180d00b107551070100380b505400300d0000b003a01c1d0f040e14004102d454954418010590703140941408200ca4080da14150305076014407058000d5000880401c1c404002110380d9046160032540503000e503c2a100b80117400030f000003003c12107000760252500b580d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 615145413 1250 615144163 615144199
    0x1050a141b2517071e09090b090d09120807080c0304030c030b1503100b2b05070b0903030d020d2307030e160501030e0c0901170f070f0b0304031814 65
    0x251460f00e0184681040d0000d100710094034080c00c0303002e4000f00c0a0701410b0340c1c450002c012190008001d85404102c001001001842008080d261038518034001601d10700e0404224189519640010080c940006104007880405400d9461318042c50040d0317070740e5603600d1401403841c141d01e2000310307241c10403880051010300110780d048071048405130107008080e2111a0400090004041c4d07294001c1c11910140302c05e048102244030040b00385041c00340c280742d003810702c02c1c641007959104000d00c0c41c1c100180295500e010050340c018000301400540c45104a27a0254050074140308104210903040005458115011008070f0091a040d181000007d6a000e18039403280440700010403411100401041594840d5001c070300354007841429100c008001200044c2942420b90141900680c0700405101e03414080c00b403280e001c0e04c02d10050a21030301d40000c0d100001018800c002c0c0d141c4c070100000d000d0602a4111030224206a00d44c204000c1e19891840340b6450101034003809440e030508c50004043d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 615146663 1250 615145413 615145439
    0x3090d03150b0c120a0f02010e0a1a04050724081b0f0a090302091f0f15033207020c010306050d0611070602190e01050a141b25 56
    0x8000440901c1580c20200c10444581c02035032001c0c510701c28000d48400401d4003002504840f031256683ca00c3c004001000207094640c0028a0045600301492140000c0c01c03441d5100101410200c02294030750711401c0503404e00304154030405c0d6100d071456400c030406010010810a1603000d407501c11042e214004401c1606240c107490b03a04007641088202c0240850300054500e9040f1403501d4103d00e61241d004c41c4905d00e09403015489203200103409500b1912540200000d4504510621405490314001701c07000c0500c02404014199908e1000030285015070083ca003600c9203181c00402032440600c8540d4865080745c0e0000103008030180c1e50050340c03203030081a044900042000400d80030b80d445060041c080c121141c600c5500c100007580c002070507030028001d41c13a001600d181c1c51084c0d084000d0501c8491682c06410840208840710304103800c0444007501603205e180d255107403095119039400c1443c40c240700b0a454070480b9041902c5c86603c00020501005141c240e1602c40d5440c00c10403080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 615147913 1250 615146663 615146681
    0x80909160905040e10020d0902090f16080402120d020604110d170a0e0a030b01050301111207031e060905160c12050306010c0804030f022803020607020d05030a0503090d03 75
    0x5075607407401c00142c54582c00c804c030070900c0304082e070b00861a1907240c40200e901041d03008050a44890301c1500790b241454240740e0142e04556200c135a4581030040c20807091401400d102030015050218003552950701100014030710349011503e640565450180d1354507803c403401c9911242400150505013059030410105943c010820900084401b07482ca1058100198000400c5400c104040caa0b540e0300c3d400c00010340c001c1055100c1c070750500c0d041c5420b6401003008054002e0f0100101b0600b4a1204031b0079501240a00e000940384001030460300c0200c19000040c2619810081d01160303492031035100b140a14002440000c0b80400c0c070105941604100501602844e03002d64490074042c042c100440d840312051404d55165001583caa1503150040c0d081542ca817009107a0300300c21410b1424514001c11000b00100384034108240300c100300510540002402454089408400c644403203848081040e0302c2400d603030302e80c40002030080154004072140581c80c840c160204949500038800d0b0350b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 615149163 1250 615147913 615147917
    0x1305030c060a03020f2218020403021f1403090c0306010e040203060106080711030a030912030516031d0a12081311010305061c0615140d0b04080d060308090916 70
    0x10120000c0c01038000f034018583d4101c05905c00c1140b500703030107440300f201d403a441305000e9413a60207400d00c245910a181c0c02d40703e0031407280c4100818001740c0c0d614501c58066600c0380c2d00040362408140c504980034a4001c20b440d103c0b500100501160160118840030300300019803c4543d26a43c1d02d84881070445e098070040d4041d0031407401031000c9441600e5081d485141c0d420808420380b1502d401c1c40c611381c080366a07480060b0782d5480c2407082064140c9161000b401504d414807080c100607045042c007840000d0504141b6540d4501e004045503001808050b04040074240d40041e650340c10055040749006000c10300103050400029a0b4501d40c0c00c009240640040c0c0b041c40580e41c0000540003040050901540301d00e00d6800420319211759000340310624850701c0c02180441d5202c81038a50b041a03038101c07860001c070030002c5214031f460701602031100c142c01140080640d241c0303042811007403190a0688082a08004020090024460042c45040d000b5108600341d6a5141c1104070129006000080 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 615150413 1250 615149163 615149167
    0x6061706040b1602073201050a140307021608060117030c0a031808031803060604060302010c2a06020a021e0108060904050f0f100c0201051b03130213021305030c06 72
    0x1078000c00c10100d85012103014011216000e03201c441c41b082160341a412000c2d02c000e02211100c40c200d022120030380d101400c0c05d046007800da500d403028214481d03800110144d5440440080c1d11503100304130002030084032040c8a40c2c1d0b65291082561241024003d05000a82c403610350071643c2c100004803034001580b6009042e10000c5690100c030301ca103000005101010125101240c814410b100800380300c490700c01d40c910390501700c00c145410990003c040c14800e91503c002040540d130812079500841d980031141c010011000d00310a5007020176a00803071007260401c2404036006800181d045c0c003444c002c407003c0301421343d45040030120207030541c0c806001800d62000b0800a0500c280860780080c4a1001e442d0b040c000c24040d58509062400c00b81c4550788403404d42015071076a4490b21414249a100a00142c68140160406104140c0c494401804000000741c003201650070191401503000b424103ca03143c1030320818004e0341080300340101c6c3c6003070f00400103024500040e54501400016120034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 615151663 1250 615150413 615150421
    0x80d0c080d0b21010516090843030507050901031e0501090524010503010c0e010f050d0903030f0f0c020606011b0b040308040c090218040b130906061706040b 69
    0x2d0041480b4664110005950900d428101c00e014004001e1a24000080303d240c0b0b010010500e501c000801d40500c88203450038844140c0100d500b00388032401e6140c23002c4841510084445016502614002c5840040c444215014024440350f040301e01507400c40b044141c4920410400d20028440181400da0207103c080003071949082d5400114014800042c1001c1562561030800c5401c21404000902d0b0304030368500e40c080341503040e002d06810b4008118440580e0005009001200c4186042c048022a60f03014240319408407450404039007428003a6107154a0090050191410781a00d0306083c90050301c0d000d0b02078411844191b205900514076500d415005640c7c2d54150b80c5401010300b00310000801040f04551114061486641d64404502e01810b01c03090101c6540c00000031240104408483c0c404800108150280b08850002d28154004001140300700041e0721070200b00e0401342d18005105c940c1e13100c0300c2100c02e41c400c405000300310340349216141c9030304a90003400094614045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 615152913 1250 615151663 615151687
    0x301030b01082b02150a020d060e061c02134503030c1106101502030408120a030219030c1805060301090504050109080301170c040b030a060f0b06070606080d0c08 71
    0xf00d00305036014015644111540b0001407032031081283c0344060030f03400043c003080d221040d210b1a002032100400464090030072900003000004a240214200c01c10f20303224a041d5a54030200190344000000c0c200009008048403462500710461680c90300d9500e00518114038030100c2401482c0c0001150090580d4000d0307a05070000d0074440658001c101d02241c007091901c0c020850365014120040210001b1440d00c4120540c00d414001c2c441c085401c2400304100318880003d00b60601200030003440c0d250045038100b10002d0281d9a01c0c10301100b80c14005590107500340c1e010119500c11303681c1d00b5003009203c0c0f02c0c02c0c1280d6594443d00760400d1040004001101d103a9020503001482a800842c0d001800e413540b00f440c0c0c0082e00581000c0700101182d4520000802c038103c40c030740d02550240030203040c020000b0b440d200c02078800342c0441c0e19503458400b80c07185940400c502c800c0003402e40d902c451280c00c1580050246008032502d500c102c200385800e4900900c0c01c0300c509584184028a844207014030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 615154163 1250 615152913 615152983
    0x90601092d0c05040b040e240a06050a020a0f1109010603060f0902210103080d0608120405090916060e031e0c0d14010501030605061c02010813050f030c030301030b0108 74
    0x20b018108107040c48041a1008105e0041000301103821203002035003000078603074082070b607840d648015480e000e40c0032080c240c55200c1ca010071150642016503c4020a074000e030700704591090000d10b50f2030f10702c0240c0100064a400aa0061416604030b001eaa880745820780c1114510f000700000c46080c850104a1040990001c0c09907000500f02c0d282c2414100e43c140340c1c4031400307800480740301c40003003161023300d0a10b120780700040550390300030710184260510041c01803056000d80c40c005d00b1250000b03500950100400810100910300e9400040d9480300b0091441c00540744180c40303030240d14205001c0c4a42c101e400504207500c0406003038034814060822140c101c0400f0b08a9840381800844960340782c0030320981c0d0003075024100108480c07415004000740840101c00b038858940410f4502030250b603000d21095444600102c0c01c04405019083c018078000841c41c180c400ba00c0001035508a281c0040301441c100c81c0b182da441c02c02d41c3d88415007140c42d20301e4209025003400414825080403400458 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 615155413 1250 615154163 615154181
    0x3010b0105161b03110102061b09010e0609090a05070f020f0c0105090117012304200c01090206070f0b2a0a050904050901060303110d0e0d05011103090601092d 70
    0x8111102c3e200180304030a21929600986141c0c615103055000c0c3c0d41c0501980340c0c001065215030000e1444804207900500031441907070304104c0350f44100070580d00e8044c12208100402460540ca44c94054041005488116a010005030042449059040c00003a0100c04100c03000e010f4090402c0305c00044038207030021800c0904000c0c4102429403030307000f000a014060a40a00c443c280c404070941c000040d01c01c140540340c01203290112405140000e041780e00208041d420015550780e0322180c8075409020211006940654001030740000c0020180d41014110b2103280604429500c04d09964403000b02c000302c6000d51205002860404180c2500428120590b03003840d46c104101a8042803c440d81201c5821040e03644280c00e00c103064000e44440b01002211000380074412915000410401423582030718000e8041c0b0740b802c01003113000e410000151002201203a240e19115065039a40e1200b0710420400c2445c01c06400341e00c1ca0102c8001c505e07c255844003000c20b8120503041c10062076a04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 615156663 1250 615155413 615155423
    0x100512101a0d1a070c0b19021308030702040b0a0b04060c0503130b1b0105010506041202120a0813051c0f0c0506031e0a0c21020708032403010b010516 66
    0x1011041d030320b0052812045000f10050012910302da10b4600c034000010b403400060081010040340081d84040000b9402102a2405100d4820001f44100030f4000c04022504900c5d01c590041030038113001001d854800c6c001c4174140101c03032681081c80a01f00842c062010b001030104000e0084038010144003104901c104110303860507015110308110542c642c0c00004402200094901110b421003602c8076080b88540020425945860005081442140725814500190f01002401c0d550b9544c64034204110785c41c152000c43c1054074002c561607010000c102070307400105901064504001074200000c9205080703034640c0500f162120b01c0d07180c54440342241e4407811030703002062580307400003d140206203204800b8410000c03014104003210004007000303505c6242401110b503140e070000601c14880c0d8115003c80300c4801404100003e84030b0000042d2000400005205d0301c007691542840d60800144461091550000101030a8030b20340c0c3d80b07550010b041032000c03d00020086800b103580328420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 615157913 1250 615156663 615156701
    0x32a180f220b042f1201060b030108060601020f01060b120a0207170918040f02090c0409050403051e070209041112120714030c0a15111210051210 64
    0x1e01c206000d003038101d8002c40c1c00181032002d00c41000041c4401da0100c03002054004131412044039029000340719031044c941300d604110855240c0301e0080d4400c0001c4c1c00100182c13036036036031136143c0180e83e0a07060311070a0052058002c0400e41040c184106d03803d4402c9540c1c5d00d072516002c00d03802824060301601901c50181c0c00c2042c00c000604095845104420744aa540e4855030803408000e02185c4084000e07480240c0d80003000000750a038102c90481d10b078104d5040220392945e240c00d1449000315040007c5141c41c0c2000d00c0305154105000c0c021b401c01010300514900301d004410030307050141342d030000d420829010100300060030425030248103a0b0042c000c645000c001403149842c100c4a500f04001c040d10018544050109040c1761800c4460b0740c2c0002d40c038028101c410079617644040d02d4003400441028440a03880090342c0c108079003414100c0f002e55110f5075040c030800090303001500c074416400c0c040d031000070704d03810b1144180380c007008008060042030f0317504506600035140e154042c0403501c2d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 615159163 1250 615157913 615157951
    0x1c02030604020405100c110d08071e0b191b0516052802030c030f0d03230106021e06010b160c0b120103140a080304060b01020c032a180f 60
    0x40d0a810500303c14055a960070310301000d09049011201f000c034101c2c0902e0017100903802282c412411521419400745420642c50191000240d901e02d0006004050f040c214042c0031030740100c902c9100b4480380c070704410445010841c07048440c40d81007046c01d602042c0d0600107212070080306140c0c42019401402628490b0285000003040c3c0c20381454045400c0301d401d8000c1040d81003c01411183c0e0a09400034038004061880140c1d4403c01041d5403020541c4508200c4401d012800034200b580004600060055031661700294640207108940d03a01010003491210807041c1c0043c860341207030b0507a0b000a103022555407126000b1f40201c1402d482c2c114003904001070310008000103214007000580d00303520550451401c00001216620a14101c2e4425600007010580410840360816070164000400d13681e000b0040c1c1c1030822000d1440c2d418040c0310380361002660a0072f0713010068403180c500d51301420302c814100714031812404020322000141070001030300d11094010031500117890010b45110000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 615160413 1250 615159163 615159169
    0xe071b0218060121060609050a0602060112050312011401080703060509160e0603040c061101021309020c011b09060306050126060112020a030902010f0503060f01080a0902120a1103031c02030604020405 88
    0x14000401c0781301d196507020b0410032940d1241011010b420104e07060244e00f480c2c554000e517120810f00504100d02885446801005801c0048417024a01c130700741902c1543c3e40349441c0c0102400031200398041104c08000600c1c803403092003040240c0760010500309180d12025010540b100d10805500c05018007e01d024825545290240d0300c11f03031140d01c1c4040b05078100600103040200c031300d08404c6207038018040c140c098040380d140001640e0b043d8a0040e00c0700c00c595080d0703014000b161b011803610210190141c0e0115802103110041e0340c1152403e0007015507690044030765580f069a0500d4080c40314040802116155031890b802c514149090600d0b411401c2c0c6440c101c1c0c2c00140300c000425035038050002156008503203100700001f0350030b01a00358030f0070001140c52003203201100c41c1000140400a442c0c1119507200e02800c0307030045e0102c851020311510b0140e85900e58032042e10040d00400001e40705142c0002182d6012289400419158000142c101c1c040d410140c08164419000e00010506032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 615161663 1250 615160413 615160457
    0xb03040f0b091e210f090f040b0d0c0503060c0901020c041808160c060801210305040b0c0304090f050412030902031009120f020309060708220e071b02180601 69
    0x1400c0740260041080e000d00c0f5201c4d0310004000c00c01081d4050014260150754002a01c0c0d1495007558901c504054001c0054000e207001d0b401a50b20a042e040110140f041d0b960941007590403e40446815899400b42d20040740519207005005900440d1038030690305254222010030030758024583d06900491f80d0b614800d40069031004124a4030710300c0c8a0030f014140320000e00400950510060550411692503010381d0504615080e0615100310f030001c16108000301d4004200180d1201c2d1a0601d1400107034aa501511410084600f490008107010304248545405160301c00e0f1042090703403c004050740a068240b4069908d03015030704100d0349180080c003507104520322440c85000d50040c1c010703003d0a00c40843c011542150310501609200761030340750407142c00c1031300301d504152a15900d0321980c4104150040c2c9024011403c040000c0e1111690141d600441c020f496040c00113502c030101c05d43d90001c402c0702951108000724281004001c0c20b0380310f07405c881d061601c051401c1110042c12502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 615162913 1250 615161663 615161713
    0x603020d030f03050f01061403070216260303100302101205040c0806070e060a0311130303050415080613050a02070c030b100e0f0a0c1b08090a0b03040f0b09 69
    0x1158a00001101950f0f240c42102e0344001701d0520b034606075040510003000c1070340e0020302402c0780e10008040307000a4000c10603681c000c190051181c6100751901d03090348003552140e80441140044460810b0404004016203115000070001006018a96002c02074409075a99142c014800d16425940d2251190b025143c803c82c02040d203400440e152032186854480d00900b02070420885421b400c10307135a40c08048070010f020902d40801c1420000c2c82e0303a4828414112034030710224100740000201500180a001180d0300e191100d4000e0a0901c0240c44218048a0340c50748541c4400d54012008002c0d40039a4100c40f02520050502603203584803800001503030000e40c0c00c101c0c240d08008803010071880071000b5046803015206a401e000303249002d685009030010ba813450300c9101103000c0701d2042e0152004a01030f0030541440d4041801d110056520003d40c25020302c0b030898001c100d0440c0842104d0044d648a003420703c00100a84030b06100c0b01001d400d070a02802039440748503500b0450719141c581 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 615164163 1250 615162913 615162917
    0x1030923123a050f0f0a020a2f031614030f0d150909051c030209031e0c060d05010504050106050702030319033c06030c060c051c11010b01030e19060603020d03 70
    0x84c1e0030480319032581e003240100200481ca0040280034200b035030040007003251107010b104110030552110f4031881440f2400003603440c188004a4003055180c078072500035410600a0320a1b00030507803c03c00d02c0d900c9200d182e500b413042c62800c005801f1348040340d6000a03100801c02480714840c80e141e180c900b0545c1ca20401c180d849134003003400e80d040d0082e5420503483d044110b0034118034201c10800442c0d01c544072140883c844004000002070224800c0c03015603809200100031035503e403450003200009003028018240114a4800041780d0640501e003180c0502e034004009509101519126510402528509804168481340421443d540030400d0040d0480d6048003040f80300e001e14020350048030701c1224011481d003411802c0000c1007580c1c4c40c80046c0e44580c985101c2003045070422500d8803e005184841922030605070300f11041d8003100400e2000100c2d80244a00799440c40110141c881e08c031024401900886245c5000703c4466041d03026181c841c5001003913403640d80d000540d07102815201500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 615165413 1250 615164163 615164191
    0x10f060303110d2c030319050c010b01020303040b241f08060402040b03010303050a1707110c010815040b010c0c060e09011d010303080601030923123a05 67
    0x16200038481030ba00a1901c0c6003554804e50150403009000301c0c50148a070404002030030080d00b03503c0034011038483c105003120300c00884000c84002402c41d4000c0581400300e500c0c03d955146150700c080102c034080d0340c02601d000c020b61500081144010300c85100c104051b094085010030315102c4d04202184140c036203849110400c26418003034414440109202d100f07520400061055000c4a02034a055035090700d003042c4c40761215801070f1080d1111924a415002d82d00040020150344110b0f902c2c8000c0089041d2404039050700e0054443c0d8900b82c84102800c41900e018403075506240c0d101074041501450030920746981c6c0c2d160029416901e8101200003140644005c00380e06000014034014000c564080942c400c00c40e80f80380103510180802002c000803080070030080da101c9e4002904090300044c43c4000f00b0b40316a46840e0744c1c5454242d400c00c0740503021034224020080e4081c0ca9004070810300f100703948055480c161030848007000240404201c1483c00007e80d1819129080c4208903046c0214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 615166663 1250 615165413 615165437
    0x90109050a210207050315060a030c0807090c0314010306200d05010f12120e1203120117070503121b030c0303071812061d15060909070b0714010f060303 67
    0x309907241158056502c0f0b13070300410142d01c0008081102c200c05d005001075a0301d460000511400702544058140703200c002c0d0220b1000030114500f0115149100700300580d4003140415800d986191700c01c0210a0355400040010440b1a04507046440300c1500d0080c1c4040e440340d0039901500300314031a2a10669840043c460300f41c00b80ea100000c2c09003090280604801903441350904007500b05803500f041001c00b0f1700903040d1031702c00c85403076080700040503070313880d4410155a41c402420034807861030b05200c4c0340b50704c90204c0c8020520310141d0b140600581799681c83d00911019541c84090811403100d454004a100440d090016109230740702c84029503940c2c00c0c4204000c01c82002c3c02c1407103440e4090301c141044046a607581e40072242e58880b0010404004225401610500800e0651918014083c0c5502495102951144114030403240a20607480b02c03080c0c2c0340c1c0c5180c240590403582e0020401000400c1e158600010808aa20300202d182e8140e0b110840c15554035500403408140c8000100e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 615167913 1250 615166663 615166703
    0xc030b12010b15030f040825052103090c09060d050a051b01020105151c0b011203080f0f0402060c28030305070e03100b06070812090712030503040209090109050a 71
    0x45403040040321140f078114100075100c20626030b07001c0d00042044000040d8a80c090880c0c2c00316104080b079038810061200c40500b0996200c0b040000010000c583d8411a030301040f1640007500e0055101400400c00881c070700c020b20540201c0a044c080d8081e003207184a0000031420008444814407450180030700484d00b104448499035420f44007410342e4100f8040005040c1c1584000610b540121804152140740c0210706901d03602030032010703041c80d00180021402d003401c0c02c01005064442e903221405035032074099110880400740d8079011080703051070228025180c0300c005003c551900c1c0e130980703202c12075105050160145140d81d441c0c5070000e8540a00c141a014482c140c2c1c010980d0400980301d01032280004e80325040d10b0150842d00355070b41c100f080c003078031802d003a512041d5114001603510040c0640c5000d440d6801c55116500740715196020451605000b141201c0701d61546a450a5845650820040c0d00000300f0740c40d402c1d980c1d5107141000c50401c2018180d47da0062070509200800c00c101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 615169163 1250 615167913 615167929
    0xf0e0402070b1302030f01090b0703050402120a080a0207091103040215120a091103010209090c0310090609022a0304060e0429030606030d1205070e21010506010e0d02040c030b12010b 80
    0x342c0c1186c0e0b454414000c1c04200e2480f91194052080c4c503000510750754034070010380c48409000c030000c26481799203024020080140300800b5030742005d808840360140d40311a5002950004100100f00000601c042030040c20000300320004403030412150360400d05044815803204800b200c0e000c69103600c40315460309100409813110003030713174082d0000d52600140c94041540da030005000c0000034000000004c55205004619a0140040e440140aa942e40b060703000080e401c040400032051500240703010302440907080c40b05000c3c4544000d1820913160881c1910440140d40c60706e034200351910a100001d192815001480e880c641d404c1703a4054612000b458030305407009128170b00a50001e100d642603590814030711050000484408075131991264030440c0e1240312240c0864001c00c001c005410080f410394480c0c100500c400c030081040380c2c0c619004413056008400126044906125107038003505082d00018140c1010307003000300d40e4043c0100131071250b880000e1003580d180d560341c44007034036483c100310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 615170413 1250 615169163 615169183
    0x22081b0d03060303031109030628150807050307030b0c0315120a11040b01020307140114070f0807080f16180f05040609050114121609060602010b010804030f0e0402070b130203 77
    0x30f60500b0147e400001c2940da450162028003458102001d0301c40081c1d69030800c00e040180c5c1d080a000400c000c86101040c1717446405840000e0240380004191814000380d000220713500503110074899140c0c1000361205a0010f4a2a02c0b00c818003000c1010546400409035021210400101142002400c00440345248103140b241b09904150390820320340c0e0f0000949113196044200240701840340340441d801041400b54400014420300108100b2030f07003120a00305e0008003601d8030541503860100c115035401e07044664007401e91180f800301e0541e90004140c9a13000b4410300382440c031445200b03600c0d881d20165038080c0440c080e406d0001d01c0141001e004c1d540060010f030000f0302055042c80405403e8101c520b8040340105030400850300b640b00200304841e8030300789010240b2482c82e150709600c40075085500902e8003542c201412030801c0d5100b141181e103e41e03015030384d4224140c8196800c0301c9105440c2e5103a07511680030300991003c600540030181c001e645c2440500a036900d148103050070441004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 615171663 1250 615170413 615170441
    0x17180409030915030b030105090d0f0507020a03120c14030903010b030102040b09090606070c0605030403030c020a0506070503072007090b01020d05030f040305210103060522081b0d0306030303 84
    0x14010800282d08805000141c038442c0102008104801404400074940300891650660900003803010380c450128816001501d2561504100b007280d0f0740c150354610aa000094000d1682d0008001141d114400304140e4882c40c60260600d40003901e4851005001c3c0c50750070144d4100090a03100c130303e001d1140240c030320000e80c02581007500c1d25201d641070780990403416010700d460400007440760f41d444d0103d90034298019480141252951002050364100311401c81c080380c0703880000742c1e66500004460404030391110040ca2141e4804801b141d00741c1002d00301c0e1040c041d500c0c04692204100708542c4001c1e0090000404207207190400b01401d8403041c8038441e055401081400d06010342c0002200d030b1052400b0942800fa894600c1c0071140c41c0714410400c004510049140c00e000030004a00740d0490b80903d100f40810303114104e0301c034000a030507140c070717135101c0c041003900d90014030114003900b09850902e54640f945a1505011130030403090b81184c0740002d82d908014400c241c3c2600c179540c0080140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 615172913 1250 615171663 615171671
    0x52104050d0e12100c1107030602030601030b040b060703030f2003060306010e16030b182502010209060a0c0c051f02060907060509040b2e1b03080f090a171804 70
    0x408050301c1d01000c020544521351a400040112400b41080c10a00d1044078200c81fa030542d40d0900303400035041901c07880d00107400e0600d9460149810300a004090300c2c02003c40340340290b1030f078066000702010341824140c0f58035000d10030105003100410b400f085900f901c041c1ea036031409004041c145a01604400200c0ba035020902c026000790f24021081210315050010f002103e42e07002075142003400c1810100c1c054400104902903004820746041c00120803101c01c400c02d12607505901f03034020000e1142e0840c0e01440080c4465100f4804d180740349015545040c103454440c0c02251075120f002071000c1003450406034443d0980d03810400d40717a0080307903071024001560034500300a00700d200e200c03101441161251840d40b610f99681c2030340001c2d444441c401003c40000c144940c081c8000d60b0301c5c00310110700c5210b010658100040340407048158960344003201c0b9a12003d25004000014048500b2486110004d00008807040381540c401900544069164001521902e8000e031340003c0b1a0700842c18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 615174163 1250 615172913 615172939
    0x51b1c0e0610120c031221050727080303040f0b01060314060d05010e070305100c0201180f0326010906150909020a030e150103110109080d052104050d0e 67
    0x403a459030309a4203d040c00c1031240202c2c4c141040004c20503040604130007808142d40794107a4011605c00b25018030b08060780805044942d60004a41040702c444020409255194034403040301613010010f280044440072140d9140c4803041c0c40d64004035411201181c150003e581401080071f6418010405450188058150b040d041054250081d0485d0b00900365a0300704e404000c001e400102021020300115508682e40c1c2c10300d5661010044055084645440c1030700a11702e00c103002d1120b0410aa8444800b550550341d02ea81c02414144402e81c2000001c1170302c80b00782c90403030040c40d400301c58006840ca00c550610203820210ba4066010003014504104181600c07074120911030b0868030720b50b0700140c55200103603094010b0035408400c641d160051212103007800300d0b0028018182ea015862810f0b9554103007005441104050280d188558071421307400c0d00c02071003500141024601d03c02c101c41541d805400e0603002c4603054904440301e0300700b03084400003a90322003007003003c1402c100e80544051315 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 615175413 1250 615174163 615174181
    0x207020f15070303180b04151104080c0d05070f090b030d0e0f090417120406050603070308071209120f0212010b10081b03090d020609120d051b1c0e06 66
    0x8140b0708000d05041d01c2e9030704041c0c544030812448110039000500140d8a142030f10f0452180100c4202c59008949044810958414500160f60030b84906800a00c3c5061102d0300b0416030f803140310f208841314414042c01050741c2013050040c9000745503400012400a442e00d00f01b40c10164864a043d040000d140070610b81544c42e05800c41201d030050340e6455182c2c4890600d60711b514001c1c010b030391320001d0020f09544072005c40b01c40680300d61302600c010401a224071b020503440d014030307110250240006016080215204080e00d1205080c9810304a5080d42d90f141036200610260800b0385045071243c01460035030a10590406e072482d034441c02048910740e220001407241180d004410108407607100081c2ca045440c102c21075a501c00c401c80c16440e80303024000b590ba00c412580c045c03001800b0f04004200400400034100d007440e200c42e40c40d82e0030700910b407036044001d010091811012920004e64a1881181c14006012055602c042c90303000c3d2605480410544d640b40d210b2800303a0780300e0401c000e8456 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 615176663 1250 615175413 615175417
    0xe09070e07052703060133020a150b04090c06020105090d080114030f0f0307021005030f0117031b0c01170c040515070606140109170c0907050705010905010207020f15 73
    0x403e40040e10031802c15038030125002a42c200700c55038151161500220b241d11450744034503504ea002032401c2d403120411407416000c0301803407240c03c070260f8807484221002030000f80d16180c100000000024019038000000f13019502d40b18000d4400564040b820302c000d40e070a002d0380c0d44c0041090000c2c030031078242d400e00030b01c4c00c20140300780c04501b2010580000555024414031080b22000d00499194880f011801904c9900c1034100300d11800649200c100054040c030f00f0f9074400c0350107002c600d6040c1c0c83d110312200810340d50000d41100e03000400070342088604141002d40144044001003854103105400542209641045505544500010401051060001c0f1000c0e68410f82d504c41040d1422181e032421802140340c020801410040c0c08201100c02811084c0070b041e0990f16000c1c0c0d16076900303600c01e00a651505d200b445407c03400c0c8541c4076041000c0c010b504200c40c1c3c5840c0386812504d403913203070031100c03010411500d994000070000c4c154604561030703c0314190120340e010003589200ba5024218 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 615177913 1250 615176663 615176677
    0x60e1504060c030612060f060f0b16031403100906061409130617010203090106090516180f1e050f0603010608041a01090b01020f012904150e09070e0705 67
    0x1042c0c907800740e4820240310750000001481051345a403015501840c2c0342002d48448030004070300c107140100c000b1b030001d4840c6081c2d08980300b140703042d86024a0940109000c0c86051026014088800f0640748443d41c440d00440c03081c1507045164074081e0030410014161013440c1e1202003080343c00c00d0300c034040c1203c400403942d48003070442c2e41c98000100e4039103040280007140d001c00d08881540c11405110340c41034005501c0307142804020084103032250345400440d41c065a80c46500107080f0004010b4901424840c103454241c84481d00707400782e03204480c0030b00010981020128030802c4c41901040e00240003a01c000d0b010484010b60980ca5010104070103000504c28142081f00c1100418240144041c43c203803104910070015569685031407001c0041c0c003028403110300600c0343c9070a68040d074106100e005680041c02c4c00c0094400317044042210904070684085900c00c1c0c1d43c2d4910341125141c0c00c0380d800140318445901042d40380c0b400c241814040d03250f00080000000000300400a0b601100312008 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 615179163 1250 615177913 615177923
    0x5030309040203091c0c14010c051c06090c020102041a120403050313020301061d1003080a210501060c0b1f0b0d0f0f1508031e072607060e1504 63
    0x30f0380e6404686a207407080580010b460441c09070000c0000c907500500c1504454041d1034851240030450340203600701da02116107000058000d0200181d07840c120507014446683c0a240400c00e03503104c040e05800c4940e240b4019000d42c0d030028003008100c070000700da0095100c22680013410b00d07841403888502d41e500108014100800000001c134004a0282540c2c0020380203030082003911384440c9800c5030041c84004801d1181000c00001e0b1020765401007074010350303912a20b03450030301c54141002e031041701c800141d16019002d00f048450410f00d13284070313060090490356031b0303611050440d003480901c00e0000380200c2001c1120300d05030703030340e008500c0d82c00e4080702c1d207901360150743d000490028002094403480480300c480c1002105010303400190451600b00248011004003141d851040e56500c4c42081110510f44001000c10101d220314600901085030003000302c420368010f02d08411100203640301c4c90191508001c94003805000007031203402d070b0704094100100b42008050900c008008001000200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615180413 1250 615179163 615179167
    0xd020103180b04061413020112020322080a08090a031704020f04020307090501180e0f040f020310021207030207050604022e0509120a02090c0706060509010e06011206050303090402 79
    0xe145004401c061000540080d42006103003440d1078028080c288520003066039900b21130200741500902051545251b5058641d0143c05200e0b1215001039000104100e28560101c115214100d1080070b01c100302512034103091b640c60480b804040d045c0a00034203008c081e41c2c009058400026045286d05106240071072440702581e550348002100512313900c6805070440c0c004014003030141d4100c030b1400e055a40c04d0300d84a002d1305464441003e1404244078001500050201090240c0004681c664000307018030701c0680e10040307503000300e13207000d140361081d1400c43c0e40028904004041904400c0d04819945415441c00c0a243c540c1e03035880e0800351000e48240700c0002202d5611100a94140317140c60fa8044201d040104198040c001d0b810520b4464001c54051a12200d00600031510a100d42c0d4014002c5881d42c0b030b21b103040340003908aa401146c030350b0751311080810320b6626140382d40d000b010010113032401450b01e038000408980c88101030944d820b0601a00340502d55021003911901749044d2001030f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615181663 1250 615180413 615180431
    0x3021309020a0b030c0d0e030304020405060603060d15230a0b0406180f0905061003170705031b030906070b060103140423031207050c0601140109030f020105370c020d020103 76
    0x11217188181a950b802040ca400b880b4454400040055807165000320703820030903503a072081440350510044074a60784c03090f480302c1000001070030701180089400c24900002600c1c1032288100c021001600c0c2c20720a040315120030004c0740c0120340214002c500341038405014462400c0d6003205e61049140303010902d0303030301c3c0c2100c03141c5044a50301240c611a000404c440d00e500301100302c49480c09603808186c030544d0100000513149044401102c401070342c4500110301d44048484a0a28400300751008009400f04014501c280c2e50742d40302810f545030050400c2c02c42820490005002c960390303c0019203000c1007107010030000c944800134850b0105400f007521101e0f0b4421405050461088014042403100c40c4130600024646c000b0180c01c9003103a080c1243c01e03998860048810f000c82d00001e2a0014454640074000030707000b80e0030000401c0c0306040031804c014882d0500308403002451002007614084800703c012305500503000715620100b81c20700caa0f8822258002c24112241c02c0e00c040e0502d0340740ca50b01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615182913 1250 615181663 615181681
    0x15020c100c060f0f02030114010323061f03021804330807090e1509070308070c0305060708100605070b01050d050a020604090f0f270c180603021309020a0b03 69
    0x2101e8840034000d00300604d07840940040d000750428068050002e0418090701c0c05035009205a8086402800c2401203400700c08904041c00100103100c0c580080780b0400b510020381c1801c0d41d03501100b201d901c0c00750322215922914108160200c0b81144160300384110028a440c04401464198001030044200004030700b17050348001c680342e40003081501c01e5036000503034104668848107984c031041098036000d10744c481c80d86c215007500f0354214266811514080000408107001032250a01c0380d0520700c2010b0303507601c135141482d03800c585000120313000c2c0e020000d43d0307042c2c00148409031110703042a03030519446880f140103010050140f54000d0313511394211414880200310701c603084d0f5402409180d449031078401c5507025288060780848800e0070000303070f140944418000c0d05100d905013001040034441d44051420b84594607041661501c0c90124080b80b8919086c000e9203d00e040642e020540c0c0c2e00d144140981c5104904008121a2504403200016a500c00340700040305c21410b012512500c0c2d0300f2038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615184163 1250 615182913 615182921
    0x70504350a050109051b0a0909110d1b052202180301090302031b2e0b15090a08030307080105011d1009081905100216050609030415020c100c06 63
    0x5440d0480c440c0440c00c50402405401c42c0340c0117031048040d6801c80f08400c030301007400916000d2480d4841d040d40d000348461841d5030310440e006c50082145c050180c40c041c02041c07400c4201041030b40c0030042c000b000c02c5003c01a403000001400300342e40c50a42c4003103d000b402e02c400c0342d015040744403a400081d450f5010031082d14044002c1c9008008101d00025468003a65a6000001070700b64071b128045a56802e03d000300b0800d1491058200c00c1c1c60b010494448511b00402e1026028480382e9509501541512410030444010381c1100003203030f03124621001c02145c10710651000c003080d070040003000240e5901080c010b0468400782080186007000c50240c03080440008503054001044960445030540e21206070403c0f100700c5c0054403171100792690252500845c03600050326940c490a12108000d06980c0244036220b08106031102d4806035686480c20f242040c0e80d00080c80d48046010321078215204002c200c0405079000511040c3c0300040880c2000c49029261414481705a000505000d11504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615185413 1250 615184163 615184259
    0x9020f0307080708071d1611011d0c06031311060c121c05040210140c010e0105040b0106020a03121109060a0903030f05042709080309070608070504 65
    0x2507030310300da45800c050340e5120f015100350500b81c03055020000b000754240b100c680c0c001054040b030390a1035030b0310b0381d115540050500c142c000700900046c0706aa800703400c0c8100140122410f081204a8190090171440c0146000c1c04a200301410010b02440c0300300303040c020350225442070142c411181c1000000c0c089005a07003d0580345d010781c035140403c540010004050381d0041c3c17205003030001d030000c01100450b03004540003500701601218504000d0b0082c1e40020601c10748120862601078011600c034250307000380c0064a1903030f45031303004d00c0104150b42e47c0d0702d40944820301c01062540180d0301c0041094042000c2c00c44015544c0c111864108000d00449071728840c090540c039510184581c0007001803109100542c0000c0750b007a40c00c0503440c400c904440c2141c00141080d12000002610307018210501000b0a41156641d0345c41c0300001e02d140080c5204094241c007404400d8a0a140605040402440303102013000801007441140b0030f484d00304498824400010f40302c0540c010040c080400051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615186663 1250 615185413 615185419
    0x11040e06030a0f052d0d08060301020d060806060405060d0b01030611040e090307030906080702030901030f1418010f14070e0f03030c030a3e0a06020301030b040317041509020f 77
    0x103e580040c0000041c0201c400c00e40104140108504501d81020f00b000c00940a0400c0d001280e6402105e4403400c161b41c1c0020740140014a40304414007405c044507ca40d11040301c903000901000740603e424402c640e44001c069650380c00d4407201e41e070b03a140106014000182481d907a00350342950380c0c0d00c01040e980580840741028619081510000740d40780c2003102c0072000256019008203030a80b16041c100e0203030000ea002581024114001980507040100348840f503a81d840c5e08200607001c5030031029020f000a41c0c11544000c0342010200e007035420461b00e8000e518141014a441201110f04c460f0f4800d0b1545040d000c25010000080e02c000c550042103a4948400315803146480c00100c000c00300302c070b40d5880f81c0c02211307a0041042c911039000c0c0f294036011001e886c80d04200c034201c200c071001c1d00640701003503c0300d602e119500e070002c90f0420382058660b0308d1180100801c25070042e0b00b0052a00c0706003040445842c146e5600840540d40c079440c558000c1d22620f4140440d1110079440103d06001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615187913 1250 615186663 615186683
    0x6030809060a0513031109060a05031f0e060a060f08060405030a0c02030c0a140f01020106082112090307020406060c170a141c06050a18020a0c0602070c05040c0311040e06030a 77
    0x3c0c20a06c00000300241224450400c140c0440d45503d8520303541c50031110080c001d0300d10011030606421000d1070f1603500c43c415948904400241c1c60b0300303000300e0744244041800000d0150a00100001d00441c94102c00d00c9680070b5000d0001080d80007050321301107401442c202c004030f20f462011034204651881c0d5982c00460701800840c03000030100401110080c151629810200a40c2c012801d076421446280c1158011001c640801c0c442d00f00e000d00103400042c40c0f64a040701d0050b00c0f17402c8801c104e6103040036401c0030072044210b1a05001e07100080010b8070301020201d41d503440343e084c6183d514491402070300001070f40c074445074028003454000c81c0032080565218291001007160301e12010946045031850440301142502d461664402510b0624003611901900c407070b645802540301c4010701060244684007080010440c0c0010603003a0b2194244030380d22441c000900c41034409810180080c1410008040d848034000010307a011503403034200302c80390703a210700b40031904004444202034074440070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615189163 1250 615187913 615187919
    0x61c0507030b040e030703050301090b0604080a0b01080114150d03180303080a0e010525090f081005010905060d17090418051b01050405040507120e100605030106030809060a0513 78
    0x1540401d101901c280d0f41032000c0059240c0442c0c583c40f44485c01004110213200501c04010306074070a0f42200e02c00345c589403500c2c0e00d50500503d48030a000302118030b030810100501c0420801c2c003401c018048404407100050401d15031702c00c1540303442525240180304121a01301498811214044600c800d01011030396030b0345a0800505041c001c89910082c0c80c18043c1070811140140b14492088a030320310441303c1040c10300509101d0451008072070017088400c06001c120030750f82c214601e00400c0c10308028800d0f0f0076500100d0050303c5059101400b02c0b0310702001c02030b03281c4401c0749840c4810381c0407004084610307070303994024400e009042006400610f0040312500c041168840c1c050520b004004441d0920001a82001d5140c0903015903400101c0078801000307a400d168010790741001c040c0c10008002004a042e0800b11840f0182100c219808101c0303924803e1442c0c4500c80c0500310030380007408031900315251108244203946045010ba000040c40180042c458016540c64070422050090500e90b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615190413 1250 615189163 615189167
    0xf060307200a02190311190f0e18060105090c070c180b120d0c120c06090b0619080a2409051005060402070b0121051005010f06050315061c0507 63
    0xc150b0100700d0007050b2800040300100840c0000d4800c582d4004a038186d035420b282e0500c200049850401d46c8007071070f030342d8000c43d007640c3c4011180050300d1468100c00d01454189903108420310080c0540109421800042c0a29200c4040c0315078040741c1c2c8600d469a51600389000a005000741c0c0c002c002e045010a000015402d040d0082c4541c6641200c801c2c510541c1c8021250b03c030540480c2220203c0c85ca420a080050030b00001212900d102c0c2c01c0102c1640c04c15100c0320103440e40c0107030454941e030f41441004031a25145120b001c180400030303440c103142410074000039640c903403800000d06404182e1f800d03060319100c42e45500c4001681907401340b00d1103000f031601540d51061038000da590300e42020700042003810b0520031348200325001034641034540d103010002d000441d80b5200303070105544c1d40c0c80c1001c04038408102203400504d00b05c2d0300040c158541098001628140d800542c2044004c0051041031840f904115400d04c02c115030350355903003500120b5401880b01920400211030309101c2003000307160b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615191663 1250 615190413 615190423
    0x21021206011d2e02060f01060c030e0904030e0918031c15120507050603090c15091806030d030b030319020c0a080303090106150906270806011404050103020f06030720 73
    0xe0240348543d103035501190140e841d400201c5040c0061818030004014092040400300c1c000f85c02810b0188080542d50085103046e94202c4d000e40200390f03400d19503206030408031480303035010342c41e41d0110010250901c140d40d200d128200b000c00c0c1403241c40350703c0540b030300d00c2c0d134448034041411225010540d40c0c3c44218403d401c03000c99040e1110300491100242504200046a00c02c0c080c40015100c4907c25004006040209550340d201d81c440a000c02d100c2c90700d030f0144085c00203010342400c1100c3c2c03a00c1802c25141c804943c1040301010704100315550589c03800419180761004e80d6170002100005103030708918007813003000c940360321110780782c0001b48151001c80190f000d10f42800003030060b25141c21030510b03010692240300000650042c4c080001d148a44213030009140100040710b002031030210084103a01c0c03541c100102d1508107900400a44500e040000d0010304241c034144070b036624540028840154203403025002e51000000241018410301154403120340d4a86250561506400003e81ea1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615192913 1250 615191663 615191719
    0x3040c0e09100f0b090c0705010f02031e1f03021309020d08030601030c0f020706030e01020c070f0501120e12030402060d0509010c0e010504030c12021f21021206011d 73
    0x92454503c0c010000c4070140200c9800d00c8001d0301d04440343d200c246540f1465803040005035982c1d507031540030680d0034560740025805011202800c0004d1140c00b015640034001c0500360003040c15884240b00181a01131080400326074040700d0540f002400d1800d294054200f4036402503102d10646800410054a440554024582a6010041751202030001d50b1340c102210400405a0b108020030031405101c1d401c41f811140c900c500142c10701e41c20204c0f0520f0b26040c0c2c0c02c1241e03404032440c0140880d50b40003c00031200c0d20382420510a90828400c000d469520101c10504284400000203041d9211541142c480c41040c1c182080b040c079180c1c0469008000040d42040000d0b40c440801003158440e0080d6026282c000303400c00303249450a100700c801c40d05400300881e0401c4020800c4151400c031440300c21907400c01c5d5190304c9680080d51500d201e200b8400300758605841c0c810300001803040d80e200e00a0364440320030700b030102c8104407000d601c2c03622444204c1c51a030310880143d000c14441d100040042c40c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615194163 1250 615192913 615192943
    0x6030b010f05060a1d0103110f0c01270201180e0412021b0117090a0804080c01030b0103020f0706050c220e0a0504122106171203091203040c0e09 64
    0xc1c20740303880400000f8030850320b200c1c00040410401c82039800da0003180310321100e814100060302d00d4400b180b41c04540c001c4000c00d900150046003600c1c1001007030185000c2100c14501040b02da254550362401280401d206c00b83c1049100360950000030800645100a09a106e104900340c2c5800c1c0b401407a1002c0a11400c0d00601841d801c000e2607007000310fa07007103105505844d44041c00d8900e01c686008a10001d1102c5200e10414452001040c20a801031019107040005480c024542400160561740e0003102241014410040000c1a4202000f610101c980c4040302041e1500d0b80140c3e05641d0080140840303104085030800110039950380541000c980f00d2151042d010fa03034120b1340e0b004a50007110090020b40904154405a034031800591f0410895507400c040c51700100b005260441d83e29410920f0500070198441da289042044031144131084080010b155260001d441038580f0320030700c04030760b080e1802300c080360800c540480c80a02a208000f00c1035018503000c1e0503169a01e03a64500011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615195413 1250 615194163 615194189
    0x180313091a040b22020708030c130e01050d060e0a060606090f09052a0f190e0405040c0b0724140a0213030b1e0907260604060e1006030b01 61
    0x1018141402040600f0800a00c0c00c81106840810366080202c1c00042d4103500e41c3c2008070100246041003d14024980d81c400151114030780d142102c04c0310b000390040e208075810040100300302c0d41d418800b01007040d440f000208440c0001811a46402c00400c0028509410640040380340f5502c80f000000b02c514010001607650750710808032048402c10340700c018a940035020581103c0c18074003000c103045a038010301180703450418407140b4074503000581101d1f101d08958644411441e440a00b1001d40c600c100d504229034105651000b208148500c0b5003044602d01280d03074018400d010205004221b1803c0d17100407183e820600c43c900401e80301b1141c03200390041c1070201e20040311380d00c292900c508500d508071241504540ba90a0140c20041148c00c00e56120300d07034150549044900940224003000003803440c0e03800c08803112524500c0591440c03134030314842048a5a2100028505d420075004040040d0071800314030b035503080a141c1c5007003030b81003400c1c0340c0b0010402c200030030824101c401d0759110030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615196663 1250 615195413 615195461
    0x108010e1011040b031e0408120a0b09070e0f120f06070207030b060402090f1002010914210a0309080a090305070e0405030d0b030106051c021f020618031309 69
    0x108031030b0100c42240610000340400d010301800d032801140c010400c41c101080c6541710103800d45220000300d5044800340c00c0400da141c0c452030001910781e0030503204174051019403001008100400300040c8120104410809010110b4843e220300144403040078121226045941d01010740e6800b0080b1005030794859480041d01940c80400c110095960101400c02d4580700c1d41c6c20007010b50000c10905510403010400c944503aa00c03401099a052820b800100d0b02000504040c80b0408024004c892580c2121031504000384089030304662000d4071100c1c0a80714024000120010b212103040104002c5000898a42c440c0d003000402c0104d038441e40888529030344404102d80841005c2d50000c01c0360f84140800007951000e9000403011120280c00002c2d169900c2e000210b00c201014845242c13982044019019801e203606004242206130400716042c900e1800c00950f51140145002151520714004560301c02050040341c0804916052200c142a00c0d01703204002409034030708205d02c42c02070340000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615197913 1250 615196663 615196693
    0xf090c040914150303030907180b04020729010f0b031b220504061a1c06061d04021603050319060e0a1505060a0f090906030803060a0801050402091302010201140108010e 74
    0x120300c50147c0c4005001c0b56450328940454052440c01d035005030b661204440101510b03184040c101c441d0090308007101080c4910500c401d018103c20320620f8072450003006000000c100022101151030f002390040d42c940d66084503400a256051503000040300011300789555081c00c2d2910b40d0004004401d4454a03643d80c010001150306500c2424486281c1190394640000d01e0b101800c404046a2000350bd4035010041410880d40c09810a0000c50100d100722402e05030045581c1c0c00a4030207441c00c52500086a41032201c0d680000e90080400c100000000c83c007103104403100b07603201d108000511199444590b01001d502c01142c4841c107280c45d060501c3d40f81545131400000300c072005801140f500040785002c8581e00040c0c44490280600d0100000305d030f84007441100f0085018160154807818080208290001c143d40640d5080e8100024040540e54013807041e901b000c0c2d044d0500c1c00c494502d100603405404407a03509502c0c0441c803030001a201e038041d0401101040a00240d4822140700e03015 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615199163 1250 615197913 615197917
    0x9090406090c080f190f0b0f091b1813060f0504110301181103010e12090f120d0e0f030f06040b0901090c09022107090603050c07020f090c040914150303 67
    0x290b1542d00903005d05a000310340325002d140e03440c001e8802d0341c450b11a58440020000c401d440310700d10f0000340802c200190000340100201e26406d0040c2c2c94101d102000090f405901d180c3c82190880c41410204809420382d4440804030f56214209005602030b2001c400003c09003103c0a4500d00b445028030444c81ca0b042c8a410140c00048094a02d10380843d2107500e0551007542c0010303003545d80e5001d6101003c0303081080402c070010492810b5580c80c00383d1b05001550b04648203040c00350031003181109a21001092807840040c0c20326000451113078000010f440c180b00c0c0380c80c164142c041e010881d000d05501280350313403141d400341540103004d40b521586c29080f200b910030050154a03007004144030f8010660024921480c4406400c03540200768000840354030400d4a0120205a036007404010042d014040c5580c0110441710071810415039401082e600160701091611032510134001900440442003560701500c51020208444c051140044d04042803e49000b41c1c8441c141020720310529001003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615200413 1250 615199163 615199183
    0xf0609020102160b030a0b03030c0f0f0d050f0f18150924091201140f0f0f010f09020d27060b0406061b050c0303030408030a0b04050601050a1409090406090c08 70
    0x30341d615550380c0000140080000650681e414001004ad0320680041040384086056066020701321010b200c418092801d0020644c2c8018440c0034440c00255603e41c005032001b050700c80d02043da03508003900034158207080c50540d1591141c05605000c042c02c58003030191152501c280c40301a200c3c000c1c01b020340880345251015440742203007009511ba04c1e040c58161201640c0300c1c5800494000745a100075585413004a82c00210f06100b10f08210603944170101d4503800c60140000600760b541001252064034460303000d44c0c54110380026000c412135205600484c140c00700000c80d01c280c0580908041a407404200d41900d404c1d0501c03a80414030701d0144107120440e0307210b4880c42c49801c0b12404408a8410444058601380141426580c1c01d0f2400c2c801984200e1003251030b41c0e5031b8030700581034500310303429070305001d019a00d00400c010315031f42c1201c103c4141201d07138100361071140c40d44483e600780c03840380311040e036000131802060208200c11500007844051003020b00e04442900e07000b141d0f548880e003034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615201663 1250 615200413 615200429
    0x703080703050306091023010504150507120f021903050705010c020708010609022a07030f0813060309030f050f0405030106031109090a0b3115050105150403120c0f060902010216 78
    0x1f80b0300e00340a45440700016400018100300e82465a903040d00c60b40105510444404580300040040811601d41090508580c9608001c2c00e00c44961500940d5040c04081c1c6040c0e00784640206000d043c051003c0ea403420303030300000a020b001c144110081d1142003c2c801c50410303600300840800d640c0c00354001d13075200d011281180c400003041c1d200980a4203050001d5035030640550403000c000f00c2c900044030030001d0b004010803990b40f1207201c0148210404c0d0b501c0502054030704045800041c3c4d000d4901c5034204014540300f62181c1402110414a200c0c40e40029415841c2800c000200624020b10041c070000841d041849a56034246071501ca001c0e80000801c148500400103180d542c0e4000c07400740304031503070600c26034890303818030b03070074113440904805541049105010000c0300140f0301560703000d05010365083d5000102e43e00c00d4200d078000c0380401005070f481409880b1080e0b1080b803e0f0856160841c11020403181142131501c014209444240d005020710035000c100c4442604500302150702c10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615202913 1250 615201663 615201689
    0x50109080a03081306140c03040c12030e011d0406080a0b091c030c05160f02030c01050c0a0201052d0403050d090f0603050402042a02070e090307030c0507030807030503060910 77
    0xd40b408080181a241c00b205c91030358421000101000d580d034800e10640c0031700d403625500d06040c1440098034031598080f54240c1464407080002a82c800550f1959a01c207007000d81e80c030f9039101700704090208c807080c000e41c103d45441d40000c1c010b40001090451a401642c81040300d0300d81031500ea4a81412410240100c61400c28142855120361302200f80b10b40107250550901c1d03800a000030403c02c215600743c0f440d1070001958001d40c50280440302c0800d000f428580d14181d02810010388412a050019040c454045942c140b50904c603404400350100203418106841039642c0000b07031581250105840740d1065038420102e540c0903504c6142900c46901c2001d000a00d01b02c03044015020040040340c02c20340b9400140c1030104c0c103400440300c28000c1d604281240c003075040028503203411940700110544511040c0700c003880000c01200c41e22505807074042d81c071801a042c0076280034001c0d44020030302100064240f00307040d40000514015007040700e04182580f51810030406044150250f4802108c034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615204163 1250 615202913 615202921
    0x1b0b0105151c0203180606010914060f220909110d050f0d0e24181203070b0a110703080a0f0e0703060b03070605040b1204060902090907050109080a0308 67
    0x1c03904031014603a1001481c945812511100001400220385031140802d8001c003d03c090010a243c00e010440c0501c00103100c00d260140c002000f00e0240d10408103030303102030030810005803110350480340480fa004107126500c070129690081c65581c00c26400d15103241c8a5000705e40c9038124004d0500301504407503040c1c0304c000f07146c003088031056800d4011605803103036020300d040070003050000218901309501d602d6030810881d01800042d44420032740710f559034034801101c814100382009480c101130408481d184c03020300c9040450710308076400b42446070b203100c049a4481000a2080e11078412200320303a091002c850502e584420b80c0c020800b00034081610f5074006400d0708110f9019424400c2c2c12140419482d601030702050034955980c0081c0c0c0e440d9103803040e044080c1030412000300203202c07920300360b440c2038504401a81d0601444c0354080c100e40320310000ca428010150401d04103250010407114090030a850b501e60356107468450503000c51600400041c80300702c04114020211380684502e4881d542e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615205413 1250 615204163 615204169
    0x7090506070512031305150105030706030b01120c05040e04210801061205061c0c0e0f010b070609022709010c0f0207030215040305060903031f030c0504150302060c0d1b0b0105 77
    0x28000d8100e00740605e06400840c00421120752092412811421a5414407040c5410401113030000f409060030400500041d0340d202c6007421100030341d10400a410b1000b62405c55140c441e5078030040503140c94800788002d00c0350b108070030203402d00d03601c450041081c08404203403042c103024410078010a000504800d1088115040590f110714000d0861203150400e1010342130b8080f00c1e00d400d03030341c01106040030300c400c4c0d655207012508403940000100c103640c075217075a00160b445094002840680c440040c8411500c62007540442104680320b01e0800107003101c548117001ea402c4582905a43c28030441d5900e06020308800780c4050055405404814155020b1002c003002c1e107544490762603020040000803410902160380144242c40107103949041c0500043c40061012a960705142c10780c000c10000034074130350741110480364180e038007182c0c0c40410780000f4601d41c1e803540080d41001c2d0028440c80380d0700b0089201c1440111944445441510440e0782450100402000500403a962401400985 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615206663 1250 615205413 615205417
    0x91518060317030a060b0307020c0406090902030a080a0306050603011d0604090201080105060c0a120f021608070303030507050d09050304090f0203090c0d050f03160309090c08010e0919050607090506070512 90
    0x644e4544c0c0899410741e40e61950f081a881221000c006800c07480b008800da18040c010305000b000311395001d0043c00c00c82e40019440e41c3d10300c10024a091000070f160443c4d1802a08041c00030070b8001c0a00f9105d682d2040d0b2422403141e0724132441c0310344900350002040c520703051049510054041e5120000707603082105201d101d0740224020a40f0b44140007002c40010210464184c40c018142d4415030142c4406a01034500010381c02d503003c1a81401c0c80a10004400003001011250103103130200c1c45807038154003960039100d80b5080341d00c00e60811075032905120380040100210742d4a1901000340e14803006144c4201d00003a03d000289070414001500c2610300307000b402c0b646034018000d03203a8143d02c00380708914660016135043c4c200c0c0c07064003401042c182c00c010107034000c1c0004c00090016611401009285420501403090000300441c04916540020400804101c4950f070b10711003a0311550a245035140c004070744140010f00b0844001c1010f04250058a1042e54010010001c00d0b503a01d94a856035 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615207913 1250 615206663 615206671
    0x319050c0d05072c0a1814160c030e0d0b0907080c0d020a030b040611032a0c060a05040503040503070801021207030b0d081e0f0d0506030105131b09151806031703 71
    0x1011700c0340790100c1c0c9480e401400c5403282195050001d00c0304500c01c0c1c0d006030f94100501d0403400d0f002400007111110b0300b00503298400c07581450800710b81c00785a000a0300d001080e410250280c580c51007000a840300005e034003c02c2e038845500321001001028100100c070b40708828001d40003020708500700001061154070350b820038466403001c110100c203001a0103081e0021a00980c0218851034030381e241a000040b0502503000c00d450b11072a060002480b40d9550701c004e0031301000381d0b99030750008051003020f100395070182a0060130342d05126695072086020b50800462010003203006030115110714020f104001d070341000030300703141c03000c004a48550410790007100030b01031041d591a02c448049002c0c14001d040b500e0240c00c1d400d0712903040140080840381e00130026402a898041803204040c105091544060351050521800703d2140201c1258130050780d020001c2182454002c00d103842400e54220280e0701e10307810f5030100c0b20740c1c0704d640001c1e01d41034400540b42031403551884060903a920f000b5644 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615209163 1250 615207913 615207919
    0xa0f0e090721060e07180914041b030221060903030105150a030f1d010c11070909020f03030706060305060c041d0c130e100506040f05060319050c0d05072c 68
    0x880d5a084003039070002c4e040382c030100000d040c2602030011132907403d1040301405240c50100480e80f240d00c90702c005040003400180c0452114001d500102105030796a0001c2c59002d46805e143d580a203840442503804221007490500641e4001a034496000041da03040358001011950210b584900c40007003584203614001c10103482e001440303610b001c07501409171550441a1000580d002840c030517403c60707104007040d0041041d000c0e114000c80c080060400c058078169140024410504d100013040000c03248807250309804003003000d60901000d0340c020401c42e40a802a41d409a5651241241d640310302d02540d24414403260a0404d1025006455607004075494011450684000f907040c5403249540d114264000c090340401c000504070038003c000405064076981d04180c20101440e00ca803003140107048c0075000220015070100081c0281c90880c1d020f940702041142440b5071010700b00d601446505201500740808203040307034800c903981483c2d030b40313906c48003613180001006201c101c052031003003039078 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615210413 1250 615209163 615209171
    0x51c08090d05030a120b03061005010f020307020d0b0f070f05160309030f0507140f09151807050304060b010503060102061305010f0c0c0c05220b13020a0f0e090721 72
    0x700140c410802840700403903540750000d401603005501c1c425980c54034650384c002c1e00100140b020742ea80b0311000c07209454090800342c0e07400d2050101245980180c810107076000c4d28102c50b0a0905c5020440d0901480c01900c1d001c000380d07102c4109590700c901c2200c002d400074a04000720281d0000c100344150889111303140102c4410b03a00d455081d40d01c00441001e42c2d117034100b03a130100400701d180c0d2021108800e065400c0d08290304080001030a54800400c100c00003c02d44c0a200c03110364079002c0094558512241a05650409100090080c0c0044800720f034158988950382071150300071010740f441f4003070590043c0380d2a80d80c1800141b0483d00c03290704840315074841e9084140c003560b038040c040814809544442500c0e40c3c60408620313040302584440e0050403612442c00b01c4c2c050100302d60142110080021441e4a070046c04600510f0900010200c01d40c8049590300002c1d5000004010100c05960b9808058401600300312030183c041d04c208010030354003203149186100e038146002e030344400700360001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615211663 1250 615210413 615210439
    0xf040e1003140d021c120b13090b040308071818090c120b10080303070f05070614010302041b1d040b040e0d080f070f050c0c0a0e10051c0809 62
    0x4002e9002c60b0181030010380104400100181c1e040110100009036600c441800c04c0d21000c018084d2400074115801443d1039101035030040d180c3c002e03400704140003120104086900c1e4100100140e606841c1140064035400c0416a803d225043d00c11b9210316074201082820701d0b11400c25a142105003103911003c0e15289004080741c9960301810051803c90216030b0407801c0d5142503074a54000410010340582c00310340c1408640ca002050b03a80c41501820042c003003120060090b17035540206080100607905090362800280351120301c0781d040300d109690501200102060240341400d002401300001907030b5480140d4840c13441000c02c5000e402c043c00c0041c0d80813483c0042410345000003140e0425902035001c01c030405500283c1c0a0b4005030079008482d003410405001030022280a56000801102040b50451520248100b6007084001406010469501c4400f02d8908000721100801c04072204000960790070b104548280d82e040e69105907460625558455481d508410403046d04280d40034119 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615212913 1250 615211663 615211673
    0x90105090d0c0219080706020c181f15030b130e060606090402040b030f1b0a143001060f0e09010e0405010212191526030d060b070203070b0f040e1003 66
    0x2803001d0100c843c060050141062400307883c0986000500b402281094425400c0c46000540300307800146921360036594131070305404100d1400c1034cd003004014482480d885d00e100c5405520040c0c02da1303416110b080f000344041001000701c9540301065019a001138000602c00d280000041c8462140100014240f41d01c400b07107500f19400031659040102c0442040c81442c43d143d034210320000c09000c1440703107040f00840b001411041722807044c00c10000d02080304002e09083c2086400300a031580b502c400e00c2d4680282004040400303101e0b80000c03610043c60000070320300c5032900303044d05140500b10400176440d00306400062080104140c4083d542400074509840203024901d0241034031502c8060360191103450041140c1080101f00a007a54102c03040000410001010300114009417080140b494178118060441c03180d00c200300307111803030010085000b000c01009046030900a6044607003a03074403829000214841c4201d50004108144002c0148446881089170700441c813107003220503580c0d02d54070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615214163 1250 615212913 615212959
    0x702061909080a030215010b04051302030712020a080613060b250222110304020d02010806040e121c0209010816020106050307090f050907060e0d03030b1017090105090d0c02 76
    0x224011b03041860700802d00242c1c1e1391b0160151010310980c4d840c003464a030000d42000c0ea184070112506401000081317209005201d03c0940501c8200155512195540020100e040c02c40e0124840c10f01581005000c007980c0c4500c505649403801c0485c03a0400f0140064034903080c0d00040100c00d05540300400c01078941c041c03240c0c06010408200c03882044403134036603000c4e15192040da1191b10340c107004110241c0c0d034003d02c10300c0c15602802c02c81c881e0f44450011601514507910101c0d914829400b0700c560107461038004060441406034034900303009200d180760b0300340c2c4030780681280042c030090003043c0c00e81078401002c4ea502005000005980f80d88a0110b42848102d85c4048082d942c0c8104801c800150340c011580e2003502c8201901d1014140b40d0007070050441e0801050054100c1d00d25a001c0501940c043c5601c1c01000300382c11112100004010103144084003000881d03500c06010405605050044030b00071504100030b4000c6240d510000c507901107100e00140e81c068080c042842e9149842a0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615215413 1250 615214163 615214183
    0x1d13020d0e4e040608010b28170c0307170112031b170306130b0d0816140a0203070e070203040320121c0e0627030d0e090c070206190908 60
    0x160b59072980c0c40d081014140b200141d0184040c11800c2001c403121104043c1c042d1001c000d00c142c10382031082c40580c101c0710482c0030000420f8414400c0e0034003000c0840c20b4055449010107a03500b01541ca400c404540040000b84540014900440410400207001d5002e11540b401c1e465034403400300d03000307445504074020b1081c85620354040c00824016a0704000c810031644810181091100032444804281e8002c1c503c0b0024002c5200440c0700060031544050700d8240b250010a03402c1200f080c0b090301c5440b01c4820408070f1023071250030000141102d00c0c2c80200e21440c8203802031410701e40383d41c440010746111030310721a0310405040c0c50f86d21241c0c1c89850180c0c1640d40c2c0c030000e20100000b046076800310b030410003000040c0450100d507118540d80b0134085549011aa04040d4100030f029500c5c09400a85580c80e280d2600401c004180c007541e0026000700aa0400c070703041c40d4180c03280c05100c816845003900194000c1c0d000c00180b1040440308070030070318000032854450b216a42d16003202c0c0c10509024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615216663 1250 615215413 615215563
    0x120819171315110306041a030a08040f08010b180709050901030b0403021e0c010507060204080106120c140d0b0405070506041706010b0a020a031d13020d0e 68
    0x31003040706014072040b2911440010a07010060010390141000d15800b0052029103d2515451009008801090100f1844001404031900308403035107450402d540150162014000c000d81001440321014002c0500020b0007400342050300d001088603480c120001400007080c0100c03944001a2522400302060082d0300490b0240c2d0f090902c4d1800900700740300c43c9400700307143c02418481e00d200d40c0b000c140c3c00300d2100d003400c0991382c0d1000c80c0b0f0040081c1c0501d40c460005546007500024127a00241168418513214451031101c054480c1148040b06600c00350140c2c010100c020000000b81e012a00305800500070404ca510442e07460780061180e0303000740c004800300508841048090303401044a58050401d440d003072414990b50210080d44da80c245c90003e010050544071081c0200407420038203480304c070041c00c151482d8400b161a007020f54080e14401d10301c540340c4810301500213030104070000d220003c82902d80131450f411003a07c0988644c60201e01c54000c4010f00c200700303d1408144002641e40d44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615217913 1250 615216663 615216691
    0x703080c012f2d030403090f030309050411160809030c01090b030c0318030a0e1206060f040e0f01050a06090e120f161e0b0112081917 59
    0x550031050039603034410410300040340c5a0000b01a400e032015400c80819620901d02a11418a9401114182da20801e880703088501003540304142414500114441c81c0a5147d0040d115a00e4564843c40c0c080b038030002e80080c1030303444103015a1500c1d030001500d400c2c03810650ba08000b400381400c20000d08000d0102e0b00420005945115820180304510404a007401c210301c201e03181209446d51407100410303413402d040c40080014041015003405e110fa201040b4101c4e6110015003101500301c0d401e106205100d080d691aa48141d03840000b5594410000608400880800d0b1420300c40076002540c4184458001c0110312400340b03009124152040121250100745185010b5400e822606032245404c3c00740c22180504045009400440301c4456040c0721a40d0784854210058103a02003603640141085056000300c0c5524010340a85000c26006000c2051540da85280305969010713a041d0082916030140024620b800340801781c003c5903025410702541c2d8124a0310143c80b003010440b83c3d50a01d00d51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615219163 1250 615217913 615217927
    0xc07021f0e030304050d0807050307120801080610120f05033c07050307031b021011060108160e0901060f030b090c04090228170f0111070308011e030203070308 70
    0x4007025044000d00300b90b018503d01401c04003c5121304040c420040c04c00310000501e681004020801c03103822580050488a02403407901c0028080902031180e4181e900c03400740890030380c050307201002040b00e0a412240003250404e940301070382e401c544501604c0600051281101c2d90103d040e182c0c0b4881c0043d104c007883c0e000c81d1506070001681c0815440e8400e14144800400910008101e0b0010b071b070507080101c115180c103120a0295100010000c0d08203240462220b5480d8202c50303c5007144801009550860383c80e420410756945c1d4011034002030a20340c40c42080400c101c00041d81d0401c00503800410320689444200204803640d074000c948014552040003a08502402004500103040340e040c0003101007500060034129038802c0c02014002c8071031150030b0011405017103200602d0040041d9455450340b0700150b4032a07a10760340411155003000320240703607002c4160031a100203906455400540c2d090480f5003000101c080b0141940304023140010015039400c00c003100c010b51260040c1991020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615220413 1250 615219163 615219167
    0xe0a030618031403040201020d0c0c080a0f02010f0e0a090c02010f0509030705060a05130602031e0708010f171209060d0f0b040b01030209030a0212100609091704060f03050c07021f 79
    0x41044040003c3c80400e00c2840010323a404500140101050710f00f135448500c03181040c11121180344d10510480c0308440a81041200304400c0d840028003d0702c0d5005036514050341500d59001105581380c1c4a90b0066041c403025030785903c61103507041144000900d012250f80b0311000c070399041c1da01210b82d51020036528100041002829408004030074184140d08100500708103601c0c2c03012004002640201c009442010300106d01d8a501100d0444442242040d100c007801c0280280160400104601c3c40480c21406003103100b0810750744100185003465500d505654140c01c40500c26070f116608001c0729203850981e0068882405070703a4400900464210204000c4a480c070708070314185401031010b000940e0b4049900107030320b80c060722000c0c0c842c503a1040c46414011241c03035020134189090408a50700f44540d200000b4075124103004c0c00ca41c0956400100307240524410741e13000506154114119610a400542e00409082c0d8030390f0416045d5400120303605000100d540c1090540d543c01d604240d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615221663 1250 615220413 615220427
    0x90e040503030423033015031605060f03070c020303040306050f0a050402180c13030c03050c04050c1e040b030f0601031514010513080712061406010806010e0a03061803 74
    0x407628640c80545050120044d580328003580a000350388841360848090b141e11424a04940e00c404c4080700001e40c41c3c10054028582442c440300750003446595a10f612905030850100b0940c1e000411047c105403901d4098440f030b501c001d1034541000142191070b801030714100044c02c003a5228010110326440c01c0559040041001000c99482e1400c0800344000f42e1200c0e00c0c644440003240c9480503140e0342d1441c03800c00c4c42c8980d5000e01741c8a242c900c0b000092200518030002036034810010344070100c0265040100380c802c01c0d64800c44c02003003046039145d4005d0702105040020000104641030503950303445065141c104030740c1800c00d1b40b2228200100c5682c036100b20f000031000040d000c43c495040180c40c4081d140c2c52991031341400400601181c9032481502d5000007803c04104403603815403104003aa0260203203100c00c5800794204814003842081000c02d6520030441130356000700680e5441c00456a88252054054002e0030320b0802001040300c0d40a840c160a0041d500e101c00716950340b400900c40 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615222913 1250 615221663 615221693
    0x31f12110901030f0210140c102301050d0c0911030108010b030d120b0a0f03240e0309042a02010c1b12231909150e0103020307090e0405030304 63
    0x74140764401480041c240c0c0042c1c111050701518102c42c02401c80340c050707034070350f45110343c030560160013040314000e40600094014081107031000600151507004000c070b1070309400b41c80141c0f000303103030364018000ba04040e10349912250041400d0600315944116140c101c9400d00002c01c50818000010300c0700490901500005800640040c1400808840020a034407114139141b9601030711411a00c0709a5144070340640600320301c03c0c8994582d940c0386483c09815429211100c0e41d1040180500d540406038820440d01780071201c0a549045115001c0000800900160b4201e000d1469002440380782d0080748e030072034054141c0000646000c40c20000e0035020041f814015565030101d50f00f00007a8a04500310260b01e1030b81001c07446c417946170301001402d40120041c101080c8022500d00d1440e00c0c030b0040798280e1045600c81c0e859460701c030140c00c94040d80900c15100402d40e18407809005500c283d0003180d100066203060189140c464400d1544200300b80e4041da41031f030022040c402441281c100e51011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615224163 1250 615222913 615222919
    0xc11030307050c030403240e212101120302010b0607080a08060a1d0702071406090d020a03080a051314091324050a1416080405031201090e0c03010e0c06031f1211 71
    0x948640711403883c180c031440501c1000c0c481c1c0c01148422b02e2030001c411050801d800601c0c0030086603110614001d60b070360307212816801036003001086003043c2054811240d649170025070307462810070361034016106898041c05140d009101c0f501300044100c00502c8039049600c0d42131400384c0301c5c140000000c0c9032030300581014400c146000c580d8000f50f92880d08641074914155a00e40228600f070000504900031548007800d001e0000540c513804503480381c001c1c40454200d1207941d40d140d40740e00003a11003480c1e0790021a000007210300403443c860b84882e004081c0e580708030b01c08500c42e401c40c0382c0d024244548000c0751a80640710700c203015045500e030140444180c881d12480440c1c0c54980c43e6241811308041000040c410307014085024013009104540150310328151240c6296500c0000c00300400800c802950705004082c8880658078042c011940304070040303002070141c042d030703042040210392002e41498411088503811541c4821580b008100900252050307006504035801d203018045500c85400b48 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615225413 1250 615224163 615224173
    0x25051b030c0d020409080405041401090513030c030e150d0608060112050a12020c0d030e24030a2301030302010c1d1f1b12030c11030307050c030403240e 67
    0x103042e2910400034a0a43c0c0488011854103d02e0421419500c103c0e00f000e90011b080c0303052000c0c1d44800d40316641c100c0e490313000e0130081903642c0e8511074a5840d421000a00042d0f99100c0354020074410a128000031b8002021125403800c4030405d0312082d8400d004483c05161126000c001754541030103614010200c0d10042180c0b10b40603074803581c8074203a0034030051420320ac550302c0a241a00c00c10811854010141049003001c01904000d4100740541c1c4943d4454000500c8101e1802d420407504652030507208180342c21a1201d0401c01e002e1b010640a460101c058504480450010401824000d5020341c0000500702d07112072000348082c4411450090031a00315000010b141c451250900c3c000240d128a40142a2150740458000b1003508880035604001101c3c02c2c02c3c4a420090103070360800a4a081011040c1c0f1b440c1130700d01e0710715900200c0c11500203000099129001d0001482c14440c07010a03a4542a1a599401c1000d5410904140a00382c0d050400301401958802d000a01d161000146 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615226663 1250 615225413 615225433
    0x1911040c2d02070803030c070b09160b1213020d02010e030a0203030d060905090a080301030209151818070f030b06010507050714040c0518042007111f050403060225051b03 75
    0x3003014811100d008000184910019081d9001441008bc0d09001c1c080b11030310641c0e403081d16641ca500003c180c200d6203000c0354080307501861802005403e00b54050103a2445c006a03400640c0e949608403152501760041d0415400140d400340004c1c00d0701c0c483d04400040a0b414072080008079000102005050f9119800c0080401c2118003070702e04480d03040f1200241a6203c2c68124069080350750b50607009a060a2014100071082240034030440003503643c2c0303580142d04009190303614061310a50f025a910303614240082490301d4101076200c1010b04040e4035202a80c1d50781890b1402c19440f440d014181c0310030051292400d40109072100fa000d182180c1840e0900c1e011155010110019620079aa101844800360310000c410740c481a402c52025510fa113024140481641b40d910025485403030704045004500b1a4596617006407501c030380d1445d003414155680c0308003e611500111948803a51200300710044000110191483d2103103003e8603034802c14440300181c1ca01c07440b404030310a42043d4496 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615227913 1250 615226663 615226681
    0x140d09060503040b13020a03080715020f04060e03151314150a0e1011041703040b0306091305060709030212120d021b03030114031911040c2d0207080303 67
    0x501d41207504074130510712585420a11903104400c014009400100710200002408205009008058003441c04225801440001c010491052005c16104a0010b00041c08002e209a6580d12031100c007400701d0b0903101901c44403201c40354048408000740c0c40c54142074410000320140c08144449900020034060b0140c1400e414103c10040800440540d5178420f403d1519003008101d2162054141c1000b0100708058003c4040d4414010001d030044211800a01090000111012106001c42070750840d1281d034100032180c40c018140000101c03d20303030f140011400c00d2100c5401802589c0701c0380d55803460342c4140540307035602c0349140499410020050740c29608140458070414900c030401603039400000c00d16400c1c3d00340341c6101040e9100200c00411f41e511070801c80000110f08030112600e502800820b42035030840450000c100c0150048050180d00300798104400d200502d0030a00050074049205804403165034070403442d0204960000f960864041c01280c002c0c160b280c019500e0340c0341607401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615229163 1250 615227913 615227917
    0x20102190f02100f0e0c03070513022101090506130b090c090a090501080706110d0203040506090406030204090b06100f02030729010b090109050d11040f18140d090605 73
    0xd510309015000040304403440c800d20031400d02d861002800c206002c0308042c0400203118061840c0c0e02d0703101e00b000da0203151034000740709411284000d085118211840b05210060340001d5034150064250400b22280440c045900c140a00403071500041d8034a4480d040040c003900c1d4100000301d940c641200e1900c1602c58061203540800d0020505036101d0144001c6440580701c3e0340704101c02c03458400041483c16020600c0c90482d00d00746d80e1140305154490740e46480d400614210701c0540e108200130440f9040c04400741c94004d034020000280203a0f25000b06083d60809102201c8000c10782042110300e10b44440034030031081207450102c1d803ca443c0f00c0040d55034400c3c03500c041c1c45611030009009400703280658001c1d10044042e4a40d8440d650340d001c000440d008408118041003100b0170214140c14480004001c05401201e0090020040000c0c0002032512038a841e00303032511208541c0300c00407000c1e1100f103441c0c81107032002251420a001c041c10491441007400412215a908022450780101 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615230413 1250 615229163 615229207
    0x15090203030a11100c080f070503010f1202010212120a05090f070611160305101a060412020a092301170307081b0616020d0e03100e0111040803030610020102 69
    0x80c445070040a20962030326044d0202d03803680c1d00e81c0c03c0600e0000d840d544248114003a801c51340c03070254036031174030041910b40340000d000d94540080e410400b00003048591800031510350040c0151905194540d02c2c000135075024007540300c0c01141080500070300f5101482810340c00b80882d0042c080b03542d82940c1554841030ad82c49010100001c48802c4851540c0c140112040b8100c2e580e08034401c5580c3e450302d5070712807a008401842c0c16251081c00b110521003000786010006000303080a28050900d40c0c00e404484511109981091110300c0101d0401c442d481640c14000c100c00c0c65800d0714050329541140140140c000100b03170340400c080d02e80c07074000000554200940c40403800c0d03214402c04400c0c4c1203d558007404450765100d0001805041c04035001460b0190b080742e401d40701054503054050380d000c015106442d405034005507641a88000e107074002d494100d40700c0000704040e80c4800140705560400d4010801681000080c40311a01e40b01101d5149000309000035420721811503800c00e0792541e1a6 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615231663 1250 615230413 615230417
    0x90311011202090a1403150403020606150c150604061a0d090828030c0809070e0702011e0219170c090103020906070c09060f1a0c030415030915090203030a 68
    0x10140c0c481541d0075805940030b05101610506600d6901c505524807120035016560007800380551507051906000301c418862501900244600e856000034011403d802d0403042a0005040c0902a01000e050045020078500303540b044081d0705081042000301c5805501400f0610a16000600b8a6581c10705a40c509011183d0001e401c10450400b0b1116100d000c542d8480103484040c80c41d14031506c240c003901c982c101070b13400f005041e030320358010307a100c403415900c042d06540180c00c20003410346040040e662155061002003405000820700040002401c481d00300807540125002a100e810f00903079000d9020b0607e0314801c50049079074240c9018501070000040300784001030b41d10240e4040c0d01118840c50018107007598a03030380c0b41000d40e0b014a4600698072000e05041d40010109600c090410a458001c9146004003285500400c044c0d449030010940c1070105000018001c285904000c440301e107151170100f649900c0e80381c0843c903a800322010402440c40d01621201580f800420340381141024 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615232913 1250 615231663 615231677
    0x415030302390604180c03050114060d11161112010b09070e0d20100504080d08040203070b07210309120f021f0c0207081209100509030604120f09031101 67
    0x2600032076550b2013590002e50303030f0602000d21908094140c0e0700860038110203541c00c108690300c071038001c5507102070880c615502410230700500040c19a142c2c08007211040741c0900711700c0c1540130500748100d009400000d481000c00301820403c5410088040c611608112000700710645004000a06400c2c01800072810025001c87c00300d13a68030390794050381c103054102020504c40301c641c50900c02c0890011446a000d60402d4400130142c0d4003400c1982c05039403412000d8a44241003080484503150028030507071707242c0320761040000d01500d450014480f65008a0000406064501d9890780da01508070706481050b20303040c1d102d4081102c0034450101c50803149080c0750840210041240740c20103070000c2010907280207200100d0300405500038003401a081d020b4a4003503580301c044640307a1244888803c40e40404108608a61901d10820960040d090074640d09240001020901c0d10038200c07401c68030b41c4540b5042030840c0da0403c5945c08103003402d280c101c0a00d42155036041c80380381510143d03810301500f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615234163 1250 615232913 615233023
    0x10e15040b070201090b1305010c0e090c0903010605041b020d140702010503190507031532010c0501020c071a0313140703060f02090f0603011d13020415030302 70
    0x405e4115401140d002002d4482500704050340b618003144000c800c584070f62030031003e1110039009181c0444509401442800c2d00d5070f030000c00c05001d80c030200026905541e00c0502113001c0c0c0e50361141e11203800c441c80130810740070070008000c0c4c82c3c07040e23104010b4280f00c3c480038000040c4255000b11014a542860a00d8030303615113101c5042a074030981400c1107600d042ca810800301a6145c0d2080050745140d00c16103040903581c08004461083c02c2d03680400074100d8034908500302d007250200b06a8003c041c5090b15030390181d5200d490172a004601065107941091400304031600f503106041c2c54554001c00c18625501740050381928024030740e03800038070f464407060310010f4010003448440000e42c2c01501c1070000d80c0d01c4e501404002e6000ca50614440c00500c2c1c3e12000a06049081d681038402c0320740320291669070940c2400703010f00c009200703e0002520340100c4006803128006c01030350981620234040002c1c01d62a0103400e2072000c86410700013039100703500302881c0c0c01d01c99054240b0f42c554001420703030b42c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615235413 1250 615234163 615234167
    0x30d090807120f0f030b130e0705150415030e0307030f0e030f070e010e0610110102130e07080726060d1202060a050601030207020a140d0b070201060503010e15040b07 73
    0x4651016004100918140a5258101080030859200d6540c0c02d030411113405820341c11618684001c070340010308200c1600403040b0650200c0b9005100d00106e5420560703c900082c280f185c032400d16441e01401007000c00100300c3d441140d852107102800d090211798078003944160b4900407906c0240420031758400000c00c00340100345d8800f16501c081e0035210340c2036101101a9444a2900c40c0c0d5542c0400074000041c4485003a8041d0f0003003100a00c0d00040220300c00007120f07103004240131041e1956081240704944400174056200404040d0511012440c00f4034020704440c4000b0180014407907640d42110001c111000d140020a040030710840040e240c00c40415200010264000d107c0800000403207172250300000c00500c5003841d020244150340d5980f0045050303000e01c4000075048030364250180103400c3c50350303100b18400b03d029000a003070071041d41701d50155100a0702c3c000e0250359203500c1400b203070400703019460100c6402c50003005a0408030a0000290000a001504040e451404074400c03038 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615236663 1250 615235413 615235417
    0x30f020a050a2709020c06090c060a12061e09150e1f0b070506220804090e010b03100203190207021011030d02042c0f19110408012c030d0908 62
    0x100454028030429104e0303009800075804206501304503c0f0300360002c3c140e00310024540401000c050710b4030b8140406a0800e0314036107000c1c01d0b01980c240c0c581c0c001017901e114034402000840e01c00038110f0b60840c60320100b4000c84500c0e43c80e2a4401000705801c1c4005000c100f801500140c5d5500c6110441081c1c403441d40030720041e81c000f0b80c1c841a0015111051200015103580a44a520903004801c0080e40b0801c1125240b0a8000c060031001d100410102c0042d601c00c80e0f800704010000b16080506100080c1028081100c1c010125400300501403044040404607803800c80f103050031450403259400040080c00350114190412805201c1011508010f0099079810100341100b0754841d41c84014074500000c80605607010705003d070000c0d41c03408507103000ba2400b0f0300c555404407406459001d030010980c10b950705103001d02911051014810000c07a00140020101c0d0f0000240300c445d14890700210080c0c8114403214210a41131012140002208980f90716114150000f82c000c4280f410051354 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615237913 1250 615236663 615236717
    0x4030e0f13020414010203190f0306030b040501140a0209060d052e081002032202010509030a030e0a080309100302030402180c0c0f0105011520010e0d030f020a050a 72
    0x85401c8020a501480860300038206030b50050140003d01d80040004a83d28010440e51000e0101c03180c3c0f881d0301503030258a814030b0200c02840c020954a85903198100c40b540c096038115107680d03440040c044510401880e0580115660005518010b081000a1502e005020005641030703034940c040740c904000300226800c100b0b04060b129815400b510609810b48140e0b224030074260041e4403021403062801d1007160300c60821920401198001aa002c1c2040040e0b128201d040c09802c000c290550b540800000c3d41c524030aa445010700120882484200390031548428601c0d802403001c6c80b40c0741d90780c80d40181c0d80800f82c0350041e1130760358a000058241d0400f5140703007042c030382d41001d000a100d1410300170880800e4600888a14801240c0f01500305d60091085031541ca04243c030244100380b041e40001c40b0302c104100b0b04202103400c500b0180c2142d103081c031780107110f074011007400070216014080c0705d4042011410840c01c1a1041c100070300944516052003040200288040c1c101d61303101801010700f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615239163 1250 615237913 615237919
    0x40e0a0e06090d081b030406092f030f070e280903050406030b011119140609011b0908031c024807140622030605010b1204030e0f 57
    0x41401d05201450300c40020521141c0084c11480c009000d070018048001104110080300c14515078564403540001c04103454200d403401060128070255a419401c000c1501013407400c4003c07284202d100b050320309480313044503403c280c2040508000401ca011b0846621100000906038000c2c640641580f00b031099012002c9494602031100c0f00707041d4014094000d490b06038a080060030f45240040d42d4613000d13601c000e401988030201c200c501d0411a101c980c0d2141c0708400038006020251400d0303090070400ca40c1044aa1b5441042a03190f040c201c001108003011401d084901a05107082ca64583c410000800c0c1c8400f5070089041c0043d00d90740c12505080f40c0202821008500316440c0a502a41895072040980c8803d10386408141e5030b42004a6001c913240050440a2922000f06000c410b156100b903440002400700c83d04408010005922166041002068480c2549052012a04c040e000340c46004802c0c810301070902130803455140c115415060070b406c2d0390a50000561103950034000150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615240413 1250 615239163 615239173
    0x1030207140307062007050d0327051018050601053d09050f090a05070306030b0108010606080f15090414010204060309060605010c20030a080a050909011a040e0a0e 72
    0x100b4414182c2c4000c0e14590f41c5000e22035a0101c1c178a0004d114050900c000e0702a0304140d88403000c684c003d620000d109811480f19142074009a0b5a02c0301100e0ac0300c07000c0da21a0090360100400f515075115880304000b096828002e483d01070344440c0d544200500450b8050b0400c904100c203806e09021280c1e24240c60001c1e622518581c1104142c6a021800140b402189080070089890300d407500c1d40f03c1d034549014000d40c4040d640c2e8082a07000d410050b19081c2496580d29010011540049005020b484540e0001c42c0c140d1400e1801810b0700070040951942606060510a0095110340c1701403009908544003d243c0e21942070900075520802d40728404c80d8400a00007556540507000b151800c0d02940c000c0101d1a502d500543d41a0f04003c00100850111040f00260300c0e01c050420214200c0582160b0410b211507070381659692110742d0880200d880400d14400c0c52805400c01809090011708240318940116080c0e20700d4040c90160800202115000410860180e4401a03001c07140c601160 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615241663 1250 615240413 615240427
    0x21905030702090c090d11060d020f07031413030f03031d2416120915050a0f0b03210c061003031d0f010309020102010209030d26060d02010302071403 66
    0x56500d6001a508900074040100010120040c00c03090b41e04905d0042c1c0b52080e10815940c540b20030400e02d0102d184c0c4001c2c18821070303458410b2840505091661aa0903031f41e11400d0b420091300f6421120404420302ca0100301d15004000001030300d50880343c0c060000380d202111450241c0207030559469100c141a080038081c00d411f100000c0b150000f01305001c0029a00d080c0303007201350a000c0122204403100c00308025404901e8410700903008440035480c40003c010941d5603038408a0805400c803885030700d8484c01840312880307170f41c80340503404a4820b27070400041400d1004070303072101007186440b00365001c00c0c1a80e1406220803400c440409000000b9a405484d125a0301081192036020a03400151b02e070018000722101c1c401c040001600c0100703c608601310031001100681003000c001c0341195024012400765840400c42014902100d8442c0b081483c2d1802e414051003501c1d203405180e0321044400d01ca665110340190542041d02841d0250395044182450540d240706444464403600c0005200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615242913 1250 615241663 615241673
    0x60c0c1b0a1809143009010c031b03020309040b012d030b030105010e0a1404260f0307020a05010e0705130509010603050708060403081305060a0c09090f020711030d09150219 76
    0x82003504102d8140800c4841e03170440945c0c51a01540c2c0c0d54a40803c04100c8070582c1c0d03000c2d00c1e140c6100c61007417600090303210702c01c858101303082d0322308108a015a201090041c8245028002d40307500d5007080c41d040f8104001b81c401701c43c0014007165041001d054280303205411030f1085d0494112070502900a0006596410000c00d2180c8200c500080903850151031446000d042c00c1414080c5800045d512522068a002d0b0030341c6044a0584010010082100c081031408100c00746201344000d401070001d001050810030f0a560454214005d15045190140555a10703000c0c0020005440300c3c001501d41d07603d034401c80c0189181e0301302900b01d102d1850001030490000034010320442c441e980d1000c4d2a2109040c0d00301c2035240b018000c3c13a98221310001407881045a00a281c400010b14110030103503525150142243c0d41107448090641d00020503030213002561059003400b00f001e9005040c00018002c2c020800c1c0d40f04c0c01101a0100d003c10020102d500c20880e0b124052050000d18030b09104520780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615244163 1250 615242913 615242923
    0x6070f02241b0910080903091003090c1a180a030501060308040614160602031f080708070f050102031b0f060109051801111c0e060c0c1b0a180914 64
    0x6008052032400030788684004a001d41c0e03c1040050101148088140d10540e00d070710b802000540144800d00400b04150b8480da08646012004d442c00606900c4900b0007000390041c50304541e000c07641c0d01c0c1c030f0f00c3d5585c5402c40c203c80c2249001c42481e000c1c451180c0000e040454150300282076903080c18800300500a85100410860303e4030b0b1901440d001d40001c110284d40900018200c032214610a41c40c0840d2058004640c0041099591080400d000316101076552464105640300c2d4400241031001020400c0300700080e0164402e10406645030100003940d034171400c1e0b110b401c2d1919100c0d901d1000c4008010441c41041b00c5003c0c2d515541e180d12280c0d005080403200081c404030a0700520100036018840c0d050071019161b41141b400340203510390301e080811091400c0e0b05c01d6440a001600c01401e0020b135014200702001d450b520f942e10f820007454409004030102d810200080060a642e03500c9001e0001c5a1384040660725681080180c50300500d9142405807405200d07903004120102c003c61 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615245413 1250 615244163 615244171
    0x5120708010806090a03090e073c0c020a171c210209150c071d0402040e0d0903020d03030b030307060c27030209060a15111207030206070f0224 63
    0x304843d8542da80742400c075580c80c48820003030003040303007107500b80003810000c0c0003550710061038100500c20800c0600040941204440624600184100000031901c01030983c85000d1046103002e242e00d003416000a20002200c4c420a4420b251012030380f0003000c0180300c11844c0001d1802d55201c0307645405009060403003107503102e0f5075810f0b4203e0760400b00d044c10310070344401000c0505002014140601c03120300a03404500801c8261003001d100248104000692a08501d44008040f00701c0c01e0501c10700c4140c881e80c540607a4142c024a5000000e554002940700480e40c0441c0c00d031400c0d0059050550092180046c242d03014040000c0040600544d9001072111b440260352b03910810f04880000040d2015600c0b00710840b41030054104094034152640c641c1182c801024040180e948070351220101542050000100303505c6090f20310140d0042c4005241c01d80d446d100d0514125a40c0d500039107501340102018144040b803004468183e02c04c2103d030380002546044110034034000701c907111144d40101c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615246663 1250 615245413 615245429
    0x2031f08160504020a08060f01030b03030f1b1c120b120d020d0e060403060b12250b040303050d0c09031202030c1209010c0f060b0405040804050f0915100512070801 72
    0x20400666401c0c213100b15610b0030303115a5070f080c954445038100580c110084c01d4141c10907899440c807818541d0280002c011500134509850b40d20751b0200c000110343c01091500094903000008800c1080d2941c1c85080540389080c9000840b0440d4a01200002c0051203d056041149172000080d011800a1014065000d5030200d400404c4100c2e0215618644901c6407500078106020400008030300d50481c62000c0da009184081d0030201d004014134003622500001611503078400e4800c651225520044040d22035105c07040c0c5442e0642d00c2c007400781d22545400c001401c0e035a20a51420600c201e10311005158010074030351039900801002981ca800552040809000c0e00764020308403100302040310180b00068503250701c40c4c981901d42c1c1c80d04244140054400d140c64a03507030b5509644911503240300d2441400d40e25104c0f410b200a000425109203200b40c000c00132581800180306901d4000c0c146100d049071800d880c02e110390021681400303001c0c2d01d903541d01c2c3c084062042c80c1d07400411590595400f5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615247913 1250 615246663 615246703
    0x4060b091f2601051303141204030806120106090b030d0816110f0708010204150c03090b1e0c0d0305060d1203150b0a09030203100902031002031f08 65
    0x1070440c0141c0c008925880c1c54241110103800c100309403210045090310603440050b15045141418001d00759201180c1d5032000110400d8a001059005403155804001103008181002c1a02407000d44009014202a003030004120014100ea6a000824003160425000a101c916600d82800000c2c001d4100010700c680240e046900710a4896929540b0503c100403690720758402d1680140e491401904040303a407401414130b0343c9014001081080c000301140c030001aa03452801d402060fa81c00d03503138441010019078982c0c04000c00c4c2c1c003540705010741e61a01c90041c0d4070010000e1400c80c41102100c1e920740c0349008124810a108089107802c040c89040e00e00b03200030303500c19040001c402909540240401c02d03a907180c4e02002d110b0ba00180c0c40d640014070461400c0d8503803c2e038000c982c0101c401a070020f1101c80041c01141828400c2c00d40a01d0103071011f00a100e2039600194441c09082e0740101242d0b40400001c00c03107010b0300c0c01c003282301c2da0b2442d42114082c2c40304c03009d03a190890764500c0e45507074181c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615249163 1250 615247913 615247921
    0x203030d052202010804061a0a06110706030204122d03030501030c080105010803030c07053d020f0f1e12090708030a0804020d11090c0a022109010f1704060b09 70
    0x20a10b80c0390102d80d4140d451240b541e031542d546000820480640b140380c9201c042c01c416450726003425030005030a0a49425031424220310f141c0307107000e40e10307000302b000c1500600081262182c0c440340720718581d600000c504011000540e100b1306c5424090a402d10104149282205150305a445181664016807854501e00e864082060030383da02807003244100d900400024201c2d2031040701420010b84980d050394109c520070f01984d0840703c10131012801030b0304010384a98403182040390240011103c0d500c20b40c18114078480e00410f0380a489403403502d250001440b440c841802c061190803800351034040c50380b034000c20584a6903142e0200e480009621614001040c0720303400000ba034100501c1581d90410075680d65090103007810244008982c03107494801d00380320945d1002c0a25200364554182e40ea00e0b10744515000b0310313101c1065507035001148bc00c14480d9145081c7c40845104038000e003401c41051340c4e01c0300308803005521915111040182902440200091a0005031050904a60354107480d11 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615250413 1250 615249163 615249211
    0x503130501330311150c0114090c0904020a0611030903060a020a08010605090603010b091804080307090512060412232a0601091808040f0611060103030e0613030203030d05 75
    0x20366400013800c0c9005003865914940380c10b03a418a900d00c84e0f0b514a604000c050000c0c2030a4426006c041c4010705959000c018400b54100512689010708881c800054100342c0c0200e00341e0003203130007068108403440d4401002e08604000302c51200d00084c04a4500c5d1514a840e034000f9003020400c0340015079080c00005605100b8019203000c000010001442c6910380441440264890054a84c0010016085043e0301c031400a00d01d110314046e0000542d00d283c41320008141180c550011481032152500710302281500181d019401139120484001410150b401501c107103042580c5010162003010010407041c00c1c480181540780003070f03103503268224450600314642c2440c4c50300c0064940d121400401000c06160000c4c84060508500451168081e0f2291501c55100350003c600c008850003080001960203c0c0194640c030045018022a5040d50f4004180c102c070260041d20640700813030b080401072022010301e0015540101100d030380700d00040444000d09002c864541940c0741d41d8418101d000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615251663 1250 615250413 615250511
    0xa080301082a0d020a0803180a06090e19140a02070c0902030103030e0d060209180103021302120a050c091017070201060b0f0310050a03050a060b0a0609060503130501 73
    0x405140701c2070310340014000b03100d400710824030107a07849a00c1000c001000c07442070005142450354080c0342e0030007900f000c0610a0000c0d5071707400842080720303502f000c000c0c074601c4d003500c140c10040741151485282c0303d00a007130010b0240600d41115440141050005600c016401894010300c00d415042c90300e035445100c01d049000910000c2c010072000d803d9032509180034550703908090302c61640103040510440c0400e2610000704180005107200000500075860141401e04c0303002020203080d0720741004091905000140500314815203500d0340042144d41082009480941c1c2c805003040200d1240144000d0a044540090a101000142c042810280306001d0340065070f104e4034401d0703d8200281c400e08526800141403512040d03102c1400714883e40c5100703075840254000e10040074451040c0c00c2202c00c880040030318501c2502d8500c0c040206c16040030800d011284c890030810348035a5015035604220254503001010f03075180000d80c0d01d503030364180c0c809004014000760080d685a03105100c20114 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615252913 1250 615251663 615251713
    0x5040902060d05041511070209010e04110d03120f091a0708071202090d03081909020906040b040b0d1b0b0c060f0601020a15090b0c0a0806040b01050405030a08030108 73
    0x700081101d030300010351a40095401511480c846090b0302428600c85007100c55446d901c405103100001c204056140c001c004501502681d00396802506096640841e500c8a00d20742e40e00850611025005050040003a01d200c58485001440f200c40a042e01d04000e0001b0a02240c000749504031094541540c810401d1107001d01362074441d4945c07030f18001a02c1c0b40d0004d03200040d01a800700165569502d4820366070b45d04902c07035102d0000d5410a0035000f40602c613203026069205241008110140c3d8403101030641041042e100090030b40e03541d10200d40584450600d550b00b00321982145410440c0e000d240441c0002e00a0341080119100c212499903803156000490180c1d11a40c01700c0d0005d4201c58603181c10200c140100c0705c880c480d80c1d0300d1410760001c401000c0d5005075140790790000d00c50030800704e503800650900340c0d40c0b40400544005e0800c2102030007450140e5035030702c0c002c002a400f03030303046802910f0005e0460b01c00501500d011416030707000b4028540d00e800b0704040039000c0c1000b03905004003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615254163 1250 615252913 615252919
    0x1615110a080a02031f1205060f040c030803060a0b0714010b010f020c1912050d0305150d030f090906030f05010e01061a030705070c1e0e1005060318011b0905040902 72
    0x1181e02c600c80c409010b504058512000c28410620310f807403004128075501d0040040941c03c5e030b80e48000c0c0c1066400c00500410700b02400041e5410480014122141c040075260b01c001034a88a880e03280101e0803600507900145d041c0400019841c0900407204484014510520024401071016000440d0f406120064400c05a40070300c903808500c2c40c0203038080e030808810020307050040e40ea40b0084aa1040c200106944c20313001a444400c41581c94002e199100034041c1140f6a06001040442c0201c44c0400c40a0104450842d8046104d44100310100c010044507409004403902d904042132940400c5c0806c40e00c961820b5204042200d06010f03203c22034416407864040d80410611454580d440140120108101044a400080c91491600014003100341c500a59030303014102082c110141c40d00b08080164021080080e00c000c0e030040d5406480c404e80d4141d45984401118035645009059148034550a20038100303042c0b907000c007840c0300342d100964a03035042580c1c1d941400b044803510b80c0d020390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615255413 1250 615254163 615254177
    0x50c060a110106051e09060402071b1703090a0e07020705030d02010b0a05190506071a011d10030809010513091113240e0d02101e03021804111615110a 66
    0x21850081031b543e50002d00a4005482d0880c26684e034286481c2e0143c1580d40700884000034070545001c107030300c1c0c0040003a64000b14070b003081c50b000096404e0001d208407110306041500003050b95200f48016001414054101c903841c0310b1841e00a80038181409500307025480c2c1103000242441c000401c1a0168100788406a81c036091100f40a001d50081c0300554502c41000900600100c680b0601c80c001c1903950a0f408186204a4122020b628041c04140b2804100c2405002042602040711500b910900704a5500c080d0f044840c0c06000081e4000341a01340380c0f0080e550f4099031100200113280c6c04908501e41c0c65129070b10756210940c5468030005a428000340c0203041400345900400b084c10041c240b032582d0800b0b90015041e011081149130016840b0403008107403407810030250700c4030407060030f0030b60808140c0400d00c0200000074000310b02c920746501c201c800c1002840100d4403004250f111401d41040107080c510b489400558a040b0910b02c1d001d13505200c508200e064070410051691205 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615256663 1250 615255413 615255469
    0xa0618052d06060a0b0705031201080303010f0e042f0405090c15070f02040209010302070615030506070504081c0c150c2d0818010c030e070e01150c050c060a11010605 73
    0x6600e030300221b0045441d40710401c9400340446004180798000c000c0e91004554a40c1003040404403010b06074440500441c144041c0400503410145680d85e000c044811050000303120f002038800301003418040c94201d842c010078003031107640105200d20f105909403014030300509d0341c0200c4101ca200c0c810025128030305400010006262035001060755200c145005402c02d681034a4600c221071448a094000100d80e030401c104005003807040c2580b0142d1030500a040a15100307815480c0c03000d0418400c52000c94216110a0f81c0c082c2030106a01238005440d01c01c03150580f5240001800132001c803001041c03000304043c5000440240001c4003521a5400502c400102d54040e01c5501c005040804443c0f81400c04030041340003403042d04a440525940401c03250712900a1604003038141e0007641c0c1c8050010f0050281442c00c08101391950450700e4204019a1282000d80c18600d000705c0c41e80e440000018950045944144c1c0c64074903054410003002103aa0300c604028a16888001c500b4525604000034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615257913 1250 615256663 615256679
    0x1202030c0405151309061d0618040b10090c1704020d06022d04030201080105090903042301080f09070b0a11070b03270a0618052d06060a 60
    0x5180c21520218603903080c1521040040c03503407805850007442e055404940d0460b414224100c2c240104440c020030001a41003e00040412008200c04404d1007819000728604e03440e5004e240501c0c030420300b0040000e041600c1c0c92a9403081c1a982206102c2c085100412621314601c030389503140350640c4030310200950a0008030107a00300248281c0c0c0c4812200b4500c0e0105506000074100a02d41203006c48081c0031246c01000070303140b131110b1482b21000c01c0c0400c0c00141d030012100c43c19240101d604200e1503490480c15840c611881d00700074019100000c150044002402140d071407201c090300c4820481d51654078062240030101c8a803907141d800400100f00c00684c00008140c203002c1d40c9810518540c03038070f608a2401007294482d00e285131001003004600000103003000320740d400e44003688011050040000f030752002090f6001d00440c0d500e8003000c0c1d0500c813658081d060558000142c4122125040e800010800030341000d10203091b405481e8803c40c4004035030b051165200402c1060614140070030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615259163 1250 615257913 615257917
    0xf0e07051e0910080901111c110f040b09040e2d030d1803030e060405062706090c09010f050a0317090307240302040e15130903020715020601061202 65
    0x5056001d007810442c6a1070b5440740584880c00e1507640e11240c41a00304000200c0c21140420907540b034058007401076000c03620b188201540c0f0190080701c081550385103800c4083d1a0311071803034190b8404074009000960740d0000c80143c0000d078000c1303404103c00c9070700508050f280e10500b402680c000300c81e1920048414084000086005410400c4a052900312221003048441081400003c01d12041d40c41081540c94000c003019103049801a01c0c00c0d08003551504e696020190200c4140520034070100848443c0d121381c00246400c20007150b0403406c004401c00e40310903810340c00d9400380641c0000490031007003071030950b41201c001802c038000d03180c65515030f00c24404159000c03108100080002461703d6508020000140c1040720610f80805c502e8810000c29003040524507040c940184020450240c1d1114020340c0560140d0302c004103400501e000680b2860180c0f420000b4034a0b108032002810341c001011000da4052110501c0c1010010300301341da9400003442400001207001c0601d40e940109500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615260413 1250 615259163 615259207
    0xf120403050f0d0501210b22020402160303050105100e0f0d06061511120702040209010207030b0a361b0806160810030507090b010507020901030503040f0e0705 70
    0x2070001d042049161515010b40e0003150125001ca0b01c0300c005003c640d11a40351100264200420b1141c04a126a170f1440c000034010404801041c0604800c1150000c2e01e400c0c5000d690b0082003150707075400a82c40e5002c81d606140040d00007074075140010405041601c00c3c0703121030040d52180049800300b42e0410010030a804000c5800100342214440000c080d401204050705440004041202c2105001071003a030201c5401d0803240e02c5880c00d6036a15140303008a0341c080e9019100960750707a0742000141e00e00ba0260740001d10b42c0e84007200b00042051994041c00da24090f075600580489665018514100044003100b920340c1054080200066003a19691004201c048110341d0616aa646038504107402151001d00952000c60414047c035404011154404034890324041c00d9821a100c1540c0e43d503aa01496080030b0741d682d004401c1e680104181d50103154028010b102941c0c4902e82a41c4a0300301c1d108420317400011100c003003140c00500310424450300e20b5666050600320748050413001142400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615261663 1250 615260413 615260417
    0x60e12100b0a05130209090c192625020307050309190f0806060f01020a05060415020409020d0e01060b070f1b08030a17090a03091e0b1803060703020f120403 69
    0x1001959485011034600c0384044c60600603115030780754050000a00d4014080880702c3e60411180c51860b00082c58009081924030780407000d0726440c41c403207060011541408060590707030000c0204c105c0c0c0c41d2042c4841c3c401d40c1008010405662032041c2e98030701a01d6402880c641041c404c1040604201e80c000310b12424035a184040540e54040580e161005a04a4425900700608000190038150201203082d0820300c01000040d120340c40381520b4440244c0010300c0c40c0b041002002004405806403409442001000c542e6803860809078001018541c480449075400c0090004040b941041907a03070560f0040718034092640c25070385169000c100e450906000303130b04007000814a43c3c000c00c05041c800d0071135240c81c4286000d0489640321104000c105641c2075101089070030001e40d0100007201120f0501002801409201d40c000240307074000e4000001c010740100e80c9000b106942c2d446020500c0d0190241c50407511800011002d1380f02e515811500071400b00151644402d1841a46900034028 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615262913 1250 615261663 615261679
    0x11e03050c0616140d0305100b1830011d0d050a0c0b18280b0603191515150503060117011e08030a1e12020703030501060e12100b 57
    0xba0f44e140ca11300000002007446a00c00d00209442941603c166900110361020b0f035200b10349448015590b601c940b1520505545c038804502110361908441290130100b42c0003405000214001074203c0a00c0440000104d982031201c01c0c100c110690a200f0480c185403400b070708107038403030820a80e11076002990400c2081072a000b0341c004610354160007805070010800b1035180b00300c1003450700d20301070340c004009000040032807841c42d03404140015055030325842903000c00e291796000d0010381044807003004442c41d452000c114808108141c04040100d006200c0c0170002100f00e11008039044403075001d802c003a800b01400c04164180510061580144149849030040785e84408060081000307900000100c502c2c004416803960807000614042c2c4240c000450626801c11002008044402c00b010342c4418500200e6200910403602112034000c000380c1559075603880c1c680280201804d21130000000c030084405895403400b14040780c901c4003d1001004040b0715001910f00410314020003d60080300 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615264163 1250 615262913 615262957
    0x8040b0702150a0c0e010306051c0f06050a0c0f0c03121109030a031d0321030405030f0c0a0c060203030405100b19090204260a0f140a0506011e03050c06 67
    0x40c0c50b404901caa0030703001010942030141c1a0103818000c00d6006203040c1410400180b105487d0080290440f00314544201404100d5040c285403000c03400801410140c1454100404400a500f00300c2e0907060302d0b91151035030030000c0390440c0d070680800d60090001c0d240c46045481070301d49800030380d0f060004c803080c42d10702414a030002e8500824410b003180407410340d01ca02d400600310314080e0071510380242c010782240702300c01480080380c0300c0840d09850310a0020021030700f0f00004000f60368840c0c14a4a040795901d12488501e0350351280b00c0b004681402011b003010070a144040140d90086900c0300c0106200219078040f000601200021990072000540034141e0341e040c041c0d10400204000680181e40300c0c00d140c10700b580303001c404c5d00a035503e500034030f1400200c100000307800d0b0495030003c2402d0704019144c81c0240e600e24111104d040c4500c20782d0207903002e001e00850340074101e0702945850441088107444410590006100160080d080507107152490b06151004041d01c06002c010a50100302c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615265413 1250 615264163 615264193
    0x308010e1b0f21040303110a0903061d0d080109052413240e01061112090a090f0b09090c0d02120c09010e01090b010c02100f03090501111c020a08040b0702 68
    0x182029203040c03d15000401e00003496014421407410040d10740b01d1034940f18950a01400e852224480101901d6488032042002c21038003180d2a0700340c103000c050f940301807102e403402411054203002d01d00c1c0a626003000b00304d00750a104818200850503a54840f1040c03502d41c1003202c00c040903a840a5820303207031482c024084494480000501746c1116035000a107040540d41c0410690580101d024040c000a17071000c107902c0000c0b03c5070324000e00070030310b5581c410740030106501c0111a40040c100b00d0400304420340d20107840d040807468440590340500c990303844440059a03540000c1f1000c2d00944401080009402d100080300d1803524588129000725100b9404195040320036482410b060491900510602d9030341e0150290302c060034a000903084036a9000901800801a4a682071140714018506d01c0d9020360400001d480d005002001201078480441c0c1941d4480300080090701240d00c20f080c110f814a10950300550b0709a40e40c500c0b40e540303555a54103020006000c02c030135071007010b8409010794 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615266663 1250 615265413 615265447
    0x80c01020a080108150c0a0215180c042f040b120612061b091f110111040b04120302030f042606090c041e050907030308010e1b0f 57
    0x40140001a56191440c0e0300404a14041e0130000050304000c004540703150740721450756007004108290703940c0da0300012005c2e031800780c1d49a403404416942c00e0070071030710f04c419030549500225918103903045109074030100402c8894240341014210094a41d14103540c81d00d0000140e580d0513440124685900c68a0611480d0880b544203030240014600300416414405800d0072501280f000400450a002e544070040c2450b1400841c0d04100109000c1401e41c7c5200e80c44a1000307a0818800d10799031007480040070480f0f1944c0c22002d035820070b40b1074060b140d1440304407001c4810a15400e4202400c0054100d81400c010a007901144000c1c40103c000d0841600100000d080341546000c82c0c20b0048821000c000400801c0b20040e084001082103000021807420480300080380e0005090916401d0b2003806004050100c2120b4a0801081281900016010103890280d1102800c2d0f070383c0c801106020100495135020a15410b0200904500407640508082241304850a0901040c1183e00d81c900c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615267913 1250 615266663 615266677
    0xb0a060509040b041109150703051204060615020d02060610090315140a0c0f0e03030901030e0f0703150b030120030c0702121b0619050d0e0303190e0601140f030a08 72
    0x85c0c8000150b008807450042c845022104601c2e06150030402a910050414011680456035802201c0c00040402a059110002601e0f410070060008000d54600035525601c5041420140c850000807c6180c50410485c0c450b0021039940c00400314115070350350a501c509602c03031844040e155004030042000c5419a80d10511603000000380c0c0714070001e4000c1c0500c80c5101d8002c1400b003c044519060b07140402200e01018080c2400b00b12148880085c51818010560308002c2d40520800401041913040020800c60201c403403d000d0b400c0c94074101400c80e0b000f0980110222146800c0d20207031506000516880109010110304160341a001300b46401c60b0107030b98032059040303088a01c0d601c5901d422500e5140c002525554184841d61440014030800d007a09a401d00c075011900c0c0c1984820382e00303c26420429103094944908080e0300c10503554001502e0400204c3c249000c0026140d40010034904a5014905051100d05410203005c1614a54a081501805030150103008103003400d009081e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615269163 1250 615267913 615267941
    0x308270a1a0c03220e22110303130924031202030702030d09090f1b0c0512040906080d02030a02151806090d090905010b030408091801030b04150b0a060509040b04 71
    0x20344041d018041311500c2d40d0b042460248005028040048003440b414446609080321070120840c2c2410b01c22081e516081c8615814400061106116944000c8003030490304010018080c1900c2c07044600d8600c10319410400c8643c0d110301040011454034150740c1408541ca005507403504c0300c29000b00f4180302000c0500c0000c04c2d1115000c112148247c890440b00c0d0102c99400c000007001e6000084010401280d61401c100704410800c09005060003000140842c5200320f5a03a1990f446c80500508150305c00d062050040a48450056002004480f284200740e0301030044600e5050055054040c05404004141c40003100740c141d4060410442e4040e014039001000c1401c0d80c650010000b80090708805006401c0600402401040303000307070ba4001c0d50140030182c88410340400309034078160324121900d01031040030002050101d2a503a01e40a503001c0d42c0015030500c414105c6000b80d0b04c072a807400d41c00800428041000b14032410190019074401403001c911541c0700400502920101401480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615270413 1250 615269163 615269197
    0x12130b040b030f071806140909100509132d050a210536030a03080405150708060f041e0b100305040302030d020702190308270a1a0c03 59
    0x440c000f0382c0266500070400d00c0c2100c0300300341e50410307030110400c03604c00c510030300648038191040503100b8020b03540d05034409004030405240000324030144101d94458280920091701c046039642403075a201e20a86501b2880074040e8403ca1034140c1c04040718181410001245441c1c0321000400c03d00680a07500c0c014000080d2011039030b40000070030b80b141c0a0742418040d08011107a4080481d01c407040201e2070101d03000448480c03070003182c0c00ca4605405171540c580524007041e408c060300512145d000ba070042c002c8a8420403800c2d01032091ba407040d11100041001000001ca0f24078002c41120b54441d4050301c00b00300c014604905406404295400254054503000840014107040d610108040810f15084c4003505054401035100d210b482c10f04201940c00049000654542444240281120823090a9820f60b00e0030140126000540c2c002d4440318060080b135102e00d400740c48599030110007060b00011034500300c040c0900ca41080c401410420b418001c0307407428101031016285014405481d00303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615271663 1250 615270413 615270421
    0x120602070b06010f020d1b0f030f081311090a1508010b1302040b0405240a0f0e03010b06041e0f080303010e0f190221010315060b03010812130b040b03 66
    0x51607280100340e5410825500201c00c2c401c2e0f400501b55455a16609100c802d034010010310302846142180d010304491050030a54007016070001a01070300709000d503122401c0381c8943c078180105108045024140c6250031031450f10038684140505d4200e881c548001811803520220540c000140f6841541103075076030140d044a1307003004601044070a6440c501146850f00b01240e0b400b040c025405034601451803e41d8103d9421204150031840ccc41c603144101d51580e503961001001c01c1e26030000180011512040081c0b5814140a401440302008007854240303400c06c0101c107504078041000c802a1101e281d4001450580d45c0c4840d80944040b1000d99600d604104681e0103880024281d0040300400b1000c2120007119910000700c1506603a40140c1e0702c01c075514203007030030405038031446560980c50000001005500078a0115071560b40c90144001d950310141002540400d200705142a088004200b042c02004001072003e0045207160400454490440c4e0b441c13500079801490161800000380 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615272913 1250 615271663 615271673
    0xf0307050a022815030b0306040b0708191406270103061505040204080a0501050705070b01120c180b1c020d020f18090604020102010b040b060a1206120809100c020607080306010912060207 82
    0x841d501b40d4168000c00c1035051940e540003110400800090401402c800450007d648a5030114203043c0c402800340004c54102040801801090f030717176280720b0304144159840d01010501d0741011a450444400101d80c6561a204003400c1c0b03104260f08100038515000c0794958951010340042e00070fa0008010303801c01843c00300e003100c81c003070180c0f402c1c040c0601038040080d102044040c10340328074140d84001c000036850501e0305c01c4829005407040340902101c443e8507000710340c85404122070440d0300c81d55031321154481c080514403024004e908030790100441d4025050814180548081c0a409000c1c3d90b00c10203440710400c102619040240c0d0402e40500c0117641c0c0c240a03510022108480400840c03c0310000510103214512941d001d02c0317011450054001c8041e4400e400401421022102c070001c07a10f00340380103510940c4050b03c94440742c074000c001d07140b041c10002c0d00603a0240c0362030303e48881d589454400d504024076290412410390300214581260407ca903400b039105040243c2c0b030314000e25007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615274163 1250 615272913 615272921
    0x50601210b0f04110406030f0f02030f040b16050a030509030c120301090e01021201180905010e0a0201120c0207030f1e150b04050f0c090301090f12020f0307050a02281503 75
    0x5403142e4102030310300e8521303c0c40c0030448084400c24140060ba041c42402c010000d855104203a90303101e071021040280034074214920610491103503002c1c07490340e59000d200c580b01816501200000035000e00003010401c0c083e510154021f90810110303414161495952440c0a210300758100310361801000400c00d10000e4003807a500102200000e41c201151f80808036a82c241c1446031000210086c4801d41e040d0250707500120259801400074400018001d43c0b08e42d40c4c202140c0128005440c00300741e80443da0301c0703200c7c00c03110007106d038041c0070480e14544540d844e2440b0008241e44c404c1d0281003440e030224001c1c008d9090f1602c0f420101251900a152031002c8070300001d4013900890400f0204030f00b128441c0b01250b8048065081b00341c0b0394401e41d020900408400000500c4140d0b20803420302401101010140b11403000d0b800c64183c01d143e00f119944a00803d20000c180d07038407400007500180f4000200d400000300e402d503100640e05c4401a00303014050340c1e9020112100f0141140102c1e1580350103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615275413 1250 615274163 615274189
    0x8030c0f0c06030a18050a111008060a03022e020115060c050c01080a0e060a1b0f300c030c0e040c0e090c0f0f0408070f030312050601210b 61
    0x58010601c1400c00700e002c0b4032008180d9011941c0e20801e0160009540c20564000b541041c00c0f03e82c007044030700d040c1160449802c1203034030079240e88038482c1456104407195031003000040c1c200c00b0388501c3c40d400c0c00390088120003141c10703c4900b00026000e020340f840b0ba50a03090a00c2c0e001082c10344401d031071240304180c80e0300003100b04403441d00c046c408103000140ea40402082860300700410b0b40d494580a0040203c001c04031405d010344410300101c0c0c01c1c590040408165000c01240c181d044142c001c1d224010b49500c411702081000344171050004005900c0052244001180e01030079542d41d84003001c8070640c0540741e010907500d0f0382040d1815400981c0000c0000c007503800b08200203544902911290451103c0c40c498031509001801004401c0180c5030b04c6130380e8140b801e4030b850790760302c030740c00c41d034105014200e80d61003a40400100307565500d04050480750144c40d000d485840c2607103404064070004014a0601101a0b504030941c0c6108840d8008441080400140b101402c020405040001c503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615276663 1250 615275413 615275443
    0x26161214030103111002160b030114090906010308031e01030b0a141b07020402040f0e040b09030a0f18030c080a1502040b1c06030c0e2208030106140f030108030c 71
    0x84010300c0011600359811310141c10032a041480c1c4000654102d25125a03080345284007051204000f40715034010b40954180d40301c0590340b2414508440500c441c8480842d00c081c5558810001000410094402143c019551001003903a0401111180c01d400b94280c0c02111030155100c20080030507660b20461070031150f5024a1686420581c41c4c80b000c100c412800f0b0010342c540040e18004642d5254101c400410844112044269030b4440c04906803400702e8043c2d45041000c0300044424070080221802030700390303898001c0c51800e546401c440700141611100e40c00c5140141c080003080003c208400101401002820400e031a458120160f24511a000e0210b07801404180f040010741c4054480c640440100c00521020100000c005003c00341c1c4060017100c200f68012070b41503d0440c4052088054000d05600d074681c180003451013000c0d8080240c00340f40140018015507120702505140861190403681c14940b4094401c8015442079120001603403000030034144018052142e0041d8110381 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615277913 1250 615276663 615276667
    0x1060f0903030e062d0a0f1806030207110909060a0f09020a1a1b030d0b0303270103020c1606020c180a1d1e0705040926161214 56
    0x1594064040e05280e003030740e48100000f00341050104480c0e05c0c4410aa000070407062940541121039031030a42c450348000b0001000d100d254040580240040b00d01601c80d1808500e465141c254210000d4209001c100d8000100e0380c00484c007a561044407500901e242070240c01503062040400f4100d034107410a25449500b08041c3c000035030b40b8450319504856807155400707080c00d40c1901c025003a22400b101c980c0038001e80040840d5105000015184250315154108021120320081540d80d016042c0e0000c0c02c9d085001407040a019180c51941024606060150528059225150804403022480d103001101a001044070942c108050b0fa8444026203641c10100c090948244d03080c7e00040c003000d10562682a5510252428017140c0c1048400ea0709a400e885110608541c00821a80440703480744a01b000c0420140703032612480380c0d09948521041f40380f40c48440d51940c010680b00f1407500440084c0550741c40c017a042c400b07000601d0f1061a403070700c0c03003a603400c0040c0c02e00100081d02c10b610401 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615279163 1250 615277913 615277919
    0x30806210619061a040609170604060b04020d1107120c120e0321120117031b070902040e0a061505040e1008010e010605041b080f04110306010e01060f09 67
    0x4240260042240c01d00c0e411000d82c2d0b01c40ca01e01814499001c61000f0140c401350030349940c9210081c0c0103903480360ba0b400f0b9a4554a40001415079843c000005e001c0c1c0044011a00040e0240e0203030407480d50181000d030a146000003050101d510240c580d0084590000740c10040162105210740c5c40030039820221414081078940c1240406001e0080d020b1201c00345c2d02000e203544c204101c01800e44003034221380001818500812190700301c038141180c0340c0340d00400800d0b40c00d03000c038a40340c500001d20005c49c00d16200c6400004580200003440c0000c3c09800b40101e51b43c00d4500080c0083d18000354804e4003800e00c106008200c483c3c80c0c0c809501144003c0e010121300760b00c0300032501124030340450380341c40e501c03a01030700380000d50540d0245a5961030401202983d083c1034205a0440310308840400401d42c0035403100e801001144091300004108800007541440d048181941280c02140d5140b2015800d001203458040d0030f8003c003550121440040003443da004001d4a40200c06140c0010b100745 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615280413 1250 615279163 615279229
    0x717030703080408120103060b010210050702030901030f0e01021602150403031b0524070e060708030a05071e021605240313020307030f050607020604031b15020304030806 75
    0x30103400808015203040070030180581c4406a6690324090020810b15503542c0c500350b0010890b40d6841030140c0030742c0720045103030221403107460310581c0c20390007451424021800440007480c00140650815554100408450f4000d01c0a00134480030601202101c56940c010045030b40441a0200300d003110070442400041c0d402290101e55485516100020309034a00e4154288115250941c03c040c4003001240e107201240d01d0818007440d119104c6140e50a100c0d0b00380120bc3c03041410207814072908001081d140c546541c0441c0e1300c034085140124600104243c0800038108070001c003c01139110304070f4242c020703100c2030210000b071030110307102c0320108d01851403070802158040d803c00080c400400090140c115071202c6001c50703507000382a07a0000e500d0345040407461008580a0b41e0754421003000031942400050754600031905600c810302908400c07400851130000003002110381090094900c00c110420b40091401180309440303522991500100b44080001008250f1440c0010090200d6100b5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 615281663 1250 615280413 615280417
    0x106020d050a12050709030606060c03080f07020115030f060b0f010e04090309180e15040302061501091d150103021c2004270501060f050d0e06150102071703 69
    0x1402604203141c42c2d80642000f80c2d02c0c071480d0303e034900b88641003908009406a0103101407060341c3c4504002c200075a11240212240c05500e00003c0100b10207602194a85003041c0d90b031a0700c101a440041035244030012070b802600230540c002c9454201d03119802c0704009142c09030001000c2c041d510400c0c000880c10008104507400c040ca1805550344105401c2070500c00d20008001e0106010340c07503020840c100000b00107026803000180b00c1d0103102140340390800d40c0c4054500564042c1e0060201d82c480c800546164810b207404941071003612800000c00048011002440c43e590506020151803d030312a2018000080c0e0101e04040c07040008548000c8014807461880c284030748002280d4003c40e80d0f0b520500c2007510100c8180401041c0020064034116281054081c1c41c1aa45070f030b40ca40e102500b0036914203000703450106c0c448041c09191b40d4410300c081d00300381c20800404900c00c450413010504080c4c05035851070b040300d07550011410650b01007020500070500400f04078101d9140a50b915228 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 615282913 1250 615281663 615281683
    0x20f0c030c0d03270b09030c0a1410050715052d0c1b07030b1b030402130203060409020a06031b020f06070804170c010920010801030b0c04080105010e061206010602 72
    0x8060a81c0390704c4e0403c0480c9200228484081030700c001d41a484145001c50764010174000d42c441d104001500f103041c241080a0412141540081d0200d002020200221501a4001801003040c24001e0707a002c02d420f880000c298400e0118001004d080829004280d200c072a03e20b0100d8103005900c3d65045103540c1c4107140d0024039170940039201c951011040030307107400c5000c070302d01304d4072610802006000501c0007240c001c003d0761070408403108880d54014540e0004940107540050810380241c0701104a8009541c804002000068086401ea0005444000d40c0c2c100c100003d0351203510320352045180e400e071501100b0038002040350b01503115080b90b603400014516010441302001040811a12703241410410b0065114561a0042034285600800f00070405032601040c0d86210000e0f43e005605c40b41c064801039607031201d10303820754407030141080c0094203c00700d03144204000a4103c80a101c2d440c080e001002624086d42000e00400c81d441410180924450700008010000d9070780014003d540 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 615284163 1250 615282913 615282917
    0x7030c0c110a0b030f01082e0507051204110901060c0f1407050d03023706110d020403030e03060a0204150c06110a0c020a080609030409090f0c06020f0c030c0d03 71
    0x900702901021035141d03001903020002030303039011060003540032080c0b11141c140c401c1c00e41110303100c813402e00f035180460714400604462410001941d000000c0d09800807903000323803a410524605265881c601c0d58401741114152442c101d100c0b061180351400041e05401403582e80340c903500c034000941380c2e00f40f56800c019000f03000301081d402101c99401c00f44400001000c0c010040d802d510b0310741c14065101d0102032071804400101d002c091207050703028620314800d40c00a60103500111043e958020050480b1002251481c1043c082c01c42007108900003400070314480d036603c406248591052500c0c280e800b6100851030f6005000900110252000d100e541e82440d01e0101014011070400303e00030312076000215150880040e20754600c42d0408401d0414030301c01d0b6180e0b1145640c1e4141e050311203030195040c1a00e504100401c210401e40c58105201140c020f9200c2c515811003540c48909810882d400880560071254404406080c10f01c0040b5010005801601c075914200700052508284180020b003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 615285413 1250 615284163 615284183
    0xc15060b07050f0709151e0306020703050a020111070c0e180102130e060609030d05180d0b0f130302061501050c01020d05071106010f12050c030a110a0602010b06160f0804061707030c0c 81
    0x400c020841d1800c00065401127401c40d80c8a01038100141705503c40700d004005582492444030020b031000742141c41d0700350800d080c205610704004a05904800c06081d03030034200030311424054145000c1c401030084010142c5040805481c100040e654024002c207094840d49040c881e202c0d00b52804580c03070303104406614090740c1d1061303811201c5585241d0344040c5504075850458003c20400550070341400b40d000c00d0541f038011f03039403005043e5100c0340903c3c0040058000402040181c140030480c0385054905061a60510380c00d1000d860880c0c10858101c0420307900c503000e1001041e00b20040000226054010300390a41c1044042c10440c4e41d0341c03050030001d01402006109003d000c2c09114115400102900e42d907895604041000d260700d20074a0303100d4880080e00007489801440380c00300406021302140d080103403a00641c0c40c01c0300700761030950340b910304200c0d4900000c114a0017480503000c9502c0d0064a94052004031007081c600400e250185032805046140d2103410064400c40c5070340c40f0072000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 615286663 1250 615285413 615285449
    0x703081b03070b1603051f050915042a0f0914010c1e021e0a031202010618020309010b06042d1a09040e010b010c15060b07050f070915 59
    0x1600d984105070001e03100c00285014401113203e4040c02101c090f88035a41803140f0788603c052051100d07440200c041d240a80301408109604010011550205981000881c2c2d11207050101b02981c01005861016540d00359403190090341c600c0740001c0c0341c07400d1310788810452441d000141510700c3c00e005108080749044484021a8800d41d14002003075484068549940c0721410200d003120b80400d07003248603250350290208042010000743d030401d00e00401e8820414510b840e1401022081220f80342195212400800e1403000f036680d01104004240c00142c4da891301140c407500310b800040343c071840b940007000701300040d0003014034641345444044a04041ca078480004603c800382183e1000c1d180c1e035241100c045007a07000300080d02e980d1501381da052004240e0340c60f8103402c980400e02c00360702060410400b0300101d10741c6500b091608801c91800121030b80c0b203418804058101d84011181c039403007002180441c0c0d8092201000034401e0400501140b00140c03180084200140034100d11855444240 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 615287769 1106 615286663 615286717
    0x60609110a0302070203030c03120106350a060302100507030e040903020a0308041118041a010e0a020a05094209010305041b06050406090503070308 65
    0x528158905070281c00941107940c05907007600c011700c1f41c8844958100001d0a84540044c01ca0b07685600d4075030700910340c014084004240071382980d0704500390b201f00c2014408510025480182c3c0e903891040314801403801d84e20195210075001110792000c0c0d04180105403541c001d035030344083c5064500510041e181c10320f10080069009001e08408070f0f10848140e60002c1c46008042c00c80c40000d13000504051500790203030842c0528500f4001000300e03da20814007141204403025203903240c001d00e0880700a0007041030111030340029500c1002842642290030b40d14008003000d02000c4141d00e071030a407080406107130020424422a54447d12011903e110324002c60b201d42d00e1501001000440c007802e406041100e0041c0140b41481407280c0301200382016042c5903582d80d446d00e1400000810f20720050780304501a403c10780c010b0020503e03110440303144840460038424103041000d91 = true := by decide +kernel

theorem cover : BRFrame.Cov 615107913 615287769 := by
  have h0 := BRFrame.cov_init 615107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 615107913 ≤ n) (h2 : n < 615287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
