-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2459
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:46:47.232402+00:00
-- url     : https://prove2.me/submissions/42578ed4-3029-41b1-8f31-8b61bed35212

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 442086330 ≤ n < 442266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 442087580 1250 442086330 442086347
    0x10c060c0e0a05271b030907180e1b040603080f04080f1513030e03030703180b04060813030e0a0e010302130902010e010f05130b03040c17250306050408030601 70
    0x300c44902440b000310100a80031002000b40d003050304924000203020307104244000d04290342422415649244c50005591244414000c4529240c40b1a2274000030350710a2280000e040741303000081607140741280d0a00c42c00c24082c81d103d5070141d00e41e000440020701100c0030b00b036000c1e000301400c1c0e111810001082e041c030780040c03448009a84020440d1045040c1001c00f03075040000c540a003d224401410100c5040f01c104820795050b00c4002000c06c205580140c22402402c3c412000301107a541343c000e81c03074051189200e0b81000a0305c00001c01c0343e03814460341105c0c4140c03290801040108a1030045a80000264410a14204404010415810514826440c03c1100304040040401540c0040d01d07048070311803514100a902c07c17040603605c1c090011141030f400626000314500380e50b62884021a402110701311519100321200054440d080301100e485049042c01a08040c09451183c0d411245484041c0c07410072030900001011516600c1402d000b640a0a40c0329a2441d010001409103003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 442088830 1250 442087580 442087589
    0xa0605190302100e181e04050c030601080624040f0e031e0306060d0209030c0a080a151517210403061407050405012d02030c160b030114010c060c0e0a 66
    0x1316002500d03580e58820602903104450600c3d200d49404844040c085800c04c00000c003403074854180018000c0c0040c00c184111030403003c603580d90b070702d4418a0ba1180d50544080ca2001120600110a100f554000344101d400180000461a40c00c00d50700d410b83c1c0c03200e507034032005410004003425460720f4225040a4094078805d59469410000c001c900c9038807030007110312003075540031070b81e4550b682e01404601194640201614191619015110744841103a542101c002000702c1c1c240c213210313401d0b0007120001c42c0e80521a84e02180342210a1501502c0400012000c0c0038500c03d88a41b030341c3d02110b4205071074800103101d8580b811880c248084136550310300c08200200c00f0341000321265104c0704076801e640d02031030580f86e6548400e418031051340c601d000c218400103e01c03080c001d5041d40007019081151208003259076100d07003a158038440848a004840c5400400c20040c4084555050001114001823408a607c2d41860301c40300d0484014840450014409510104907172401640c01400391 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 442090080 1250 442088830 442088837
    0xa0f031b0305030d050a09020a0306051801050c090d0203070807060306170c36160e0d0b06091306020a020c0a0518180309030303040308190e03070b0a060519030210 72
    0x880c15502c84079528003a8a9421800b65151000910030600580041c0c00072035016141c0c9002e60784914000300500310448490000b90940b0700116001441402118010802c0c0311140d80341003020020702100c1c0c104030700c090760035104080c40000c1343ca1041141ca0700801090350000f0701c60f410308149070701011039080c2400f070a9000c2d00720b0646554071b80d07803c82d60650f00840702401c1310340c0010a00500c88108094140414805c0c2c041000c507000b1500c1e024026541952807018002103041013005850f11850058028804580042e416090154001d50012480740601c2c030200c40540d503400c166032120405400603080b5000064690030984441b001806d1b048407016038145120303500241d8000000c1c0551400c0c24640114502c0c4030040c000c0b0f441c0b0200141c01e03a59a49014140580b4445081c0c5040c0640c10032034008019149491042441c0b0b022504d0145d45020200d440702a1541c2000e04001c0446641d00030016090f9240565000703002d04400d001030040380b85004000304550000d0f20881030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 442091330 1250 442090080 442090133
    0x6041b020303150103060f090e060601080108060c073e04020301210c080a080307090e01050d03050a0e09090a14010c050702100c06020301090e16030210050705010b0a0f03 75
    0x200d40110540b60b018103a640c81541c070700c000c00b0040b00640705941c0031800c104200080807510880d01c0c0c111426150800084942d1038603140011034114900b441106441d4002402240740504d210001340a503034082c0c61000004501c24121040c200c5011030381d0001052120100501c070f5400c0320b0701200c0c22204841c1142507614054015103510320740040110241c0c4443c048070100410884010040e21111040719040034080c0350403d2030740e0050350304c0008a1400040003540440300b0340c00c05d040c0c1d1000b81c0240c1c220f0000d80d03000c0e2044e40201480506100701c17800c0052064680705e914a20481122000b001d10500038105080700c490540780d90340b0140d0600305101b80880c3c0043c22034900c1070707040c0c0700700807103111044080b1145564003800500c0303c1d000100000e982002c0e0b030040f280c40b004071030640304049500c0d030138840010001c0c80020b4004208844408c0c140d80920f0117089081d0041001140c0f500401000440d07c80307054008401101140c00d00340305210658089135005010142e4040d01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 442092580 1250 442091330 442091381
    0x1c0609050f0c19050d060303090e09030403050304180b030a0b1b0304050a0b0718080d091e062703060906061703030a15050d050d02240103060905030403080c060604 72
    0x318072030f1034007410b40d083d803100c180c022551080e01141d900a04d1000b0800120343c5078900100380803650b1150340c0c000c400b04404281d2a031004011101169800402145403500e42034452420b040300e01c00b01048995220304954050718140100540307107100d103500584034500810002030481c2020600a901c0701c050041200040c1c001503010105a003055003e06140d4030010300325248200c410261510b4640a40c0000300e15400082840410561f61039001180d5141c0440e500e000c0e1000f84406800180f2040410a180c050b0140e0004542c68040c030240dc040f0120078500801460b50084074225075840011060094a00c25000907240b00960420b400c14444d2895649020240c2100c44413a900c1540b20117100c00205208010080035200c50506425410503549506100c1c3c94200580210280b04102c5c0c20f0b0105c0c0c0c0120703070300b030f4201c16a4280d00719100d4500410074050219550f00c0200000b00104040002074502c1d00c083d1300091180b131034280244030903150981910201032203018100038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 442093830 1250 442092580 442092601
    0x10080619032d050706080f0105150d0f0e0a0503071104060f091a04111306080106050d09050102070203061009140c0906181002010e01060806010501051207051c0609050f 74
    0x44200c0a00300740700d2082c0c00780c0d0078144070340142148000c0440c4945a0001000e9411034403e510490484200d0030840c0e907924203010000065442d4030003804801c000e00040010035500c400904006402c0020f440360106c3c0380d142c50013000703c8059640e9480802c0b40810003c130740159810b00001038a0520043d131130300040e124041040e0181d2081107858940a1000c0c0e80101085070340403800502c03e00510720030704200b1001d6445441030f1050500c00d61800f04d00745018415140c101c0d900740d500e403850686040451401007000c140304640381d540030007510000d03940412140d805041504880011189000385000441d6405804110842c60000c00c01904100240980b240d200c2d0a5890356500d1902a5503480c1c4104440d4445a2000408041c10001641580124174203200c8200811855840380500d990300e0b50244503040c0010010001d00c44103841c10f60700c094100d11241001420500302c46000c40c16803ca0389602c84e155951000104031001a038003501d07070040442c0789080c0c7c5504202d0080b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 442095080 1250 442093830 442093853
    0x20f010e03040f06050d180c031b361103061c0b1801020903100510050411040501180b0705151e0103140c0409050d0206180312070302091008061903 65
    0x704c203119020460001d003100e1078021540101e03480b00704200e82c1c10f0514260580e401d0b03600064602800000d00100b61104115498054650310b12480c00f1006d40034144110902c01401040040c4514840026800c0c0b023078002c9030300070840324078141c1e16840c05400307104040300d00c140074408c001007001030352011410100400703030800c000620701155040c032006071364013902c03c0c044a2500340c800d404152125002941c48140210303084c1c1003403200340f90b0310402c2000f915405200301800b080200310401c8650f0060b510000b64a0040400d480401d0f0303940700000c0c240d00310303600c01d541c1500075500741c8510b2501012966406284a24206e404e0122000c002c0301c114414007004021648010011003a580c0070088c4050b04c04e00140103011071255850301c651201c01d8000c039500584566030101381c0d103c0c00702c00f0000081400701c008500b030003802d44505280c400c02424100034107030300b041214025220b070903c81105d00c2aa4480c4c1c2c0140c1403160920400ca40ca541149142d00340146041c400101508101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 442096330 1250 442095080 442095089
    0x7060f0305060f0d030815030a03140c070518070f0f050901110115090207020a0b0c0d0e04090210031401151d0a1d0709051917070503010606020f010e03040f 69
    0x1400c2d40e1404085011040c036070034502e5000462038034038410554403820140c40b400c0c0c00c01e608041c045a02d014160b5850b6180ea0003008904841d04400784840d00a0240146880d1841210405656480486c1645038005c0038000051038810421007129088802505a107642d8640700070b0740a0066001400ca00a0281c1541080315464601031402000d4110ba0341233540d254420210513965a07248000794490070b002c07809101710100014804034043c06581900d04a03801030321510310340342ca00300c50500911066076030181e5188101000740e00c581242e41a4950a51400113014480501040e42d0510507803181844811500041c6d068980c001e000c0461500640c03008440b0204210006102800e82e420260715074a03040c2c0c007003580500c403d40950203011541c48000703200c0d0722030052290700e4201184441d04000620341c00c0100032800700810032915840c0c801d4440050301e0b400040d0179594a98400c2005a20403042c901c20524207115841001950800451a0600d40501c106212045109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 442097580 1250 442096330 442096337
    0xf07270f0501060c0b0f0103030e061c180c09060803032707060804020918032703060a02040f0803070b1305010f0f051609182a0306031502270301110301090603050f07060f 75
    0x40c041c003081400c400301410cd2642d80710500410041a40102041ca0000c0043c0c980349805403000803980002d1081c0c4041d036400780d01035481c0d95246100011001c2c14503a40c150ba481403403040c10606032082c06040d010380041d607240300c210708160040020a18016151810110740555035040d6002e00200321148000505402c030780d003982c80146032814580a05800e5094047caa00300200c0c54680d40c000c000f942c0e1242c1c080c28025803a21f8025580703006452001700202c203404085103510700f040d1405100304c1d1040001140314442800e00b41c055848120035807801e00d13254400d2095204210640c111203440f14507058180a1070017070801c044040980c202c80040f59614514000c507000d6411180024200f4018105a00301c074243c000c0c0103002500c000e550381050050500f0709500c11f0700071a5040800c00034201011044a2980c40700d03c00c400303580303540c159a030300c40c0c4c13003074119a8001450007803000c940000b44a5256003803450800c14070008680003600005400e001194002403032012a030728515 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 442098830 1250 442097580 442097587
    0x11101140a150503150105030f06090a030509130207150605100804060f1d030403050d0813020906041d070905060103020a0f0e01230307020f07270f0501060c0b0f0103030e06 76
    0x484a0030310a0310340049401d0701551174845942a02c42c1e036911304036076060341118105911910344586611090340c480d9820340000b6400d9001c03c0c4600058003913a24010201c00c5414510f45800f0101c0c0e010f006c046445114202d4200d20b05001445800000c02c0f003511118511180f42c5d03001000c0c10700082008140b10703a950400300e10301c41e4681c4140001100500c010b403107505a4038109603290000e10044805100750305a0a021714422108580142d5140c012480841c130b4907403c0000c090001008140c02c00d82c3c8e2980001c160241c06030780480309110f00302604005082400d04001d036030004020074149801002004020b550016611220524a00e081d14018100000480720241004403c4140241c82548801d452003034800039030150125408030340700303002c00300d80b0151510b00707511070b804418480d106442c0b00008001090f4030000c03403400000845280e156844000c455081e0808000128045280c004000040781c4554004918a503007038010341c503507a0004c00358030840ca003882c010040071 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 442100080 1250 442098830 442098851
    0x90d08070204180506420907030e0106050f0a03080304110d0b0f06011809020901180602031e12180c12011509050f070c080408070306050105011101140a 67
    0x5940031240d00420510076408502840c002452486200b0340701401418041042c1802c00f80c401c400c075800c5c550031400d001004844030002c2401081c0103a401c10032903850400980d403074090701403040f01c0d0394400051990340f5544607801c4a01580265005906251103000181e40e4142e6420071a9030014105d56a55500e10b0164940303100c0006140d00000303400542400c0004104006100c1c400407105490740750b5500c0e004546020084071401c00c0c0c2406400c084c044050790750000d000040043c10400c1e034a0f01d006035581c0c2e0844465000c4801a000801e0f154165280d01c1c41c00305c0c0405444c8095070130111079100314280f061000d40b8039001007003142c0810802400c00c0c041c001880e5002020200f101800c403040703901904070301c0c4202c0341c0754600032404910000301388605401482170152080301d55075800825100a48400026a01c42c14140400964801d0070030040000d10f214900111303845d40341c0700c0054400c2c039201c080c0a207070341d040141801760046600d102950100d581030303022814900707c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 442101330 1250 442100080 442100093
    0x11401140409020d0b0d112812050c2e0c23010509010908090d11060d1506031107030e060c101e0902010903030e220504020411040506090d 61
    0x11080c4000c140e0041000141c61041d60301800740b0b1451188140450510001000428603c040005010b503002c0a041c80550800100c04200792100007640640000c00c69960300c0c4182d0558004520254095080d204100702448014242e050941d0000c0c540018011144402c0c00050000c4001c03030802c8622460103480384100803807040c0c110741ca403100307441804d030b680b1501c680b07105a902c100d60806020960b1a50144580110307141c20000503401e140107d002c00428503a003031025940000780d64240107050360703240c0043c0b444440101300007404021003041811100101d601c500289460900c02845082e010001c6825840d41842c017461550400300000e03000d4000c07000304104900c00d000211280c0c1800c1da00c4161440780601e01e010391000c410740c0c0c01c01500d190304002400555a61000c000007405201042c440f06401072600e00c01903a031a020954403c0c0703988800d04115103402c1031000390b08052040c0840b41d603544c0d407241d2926040802003600b900c45c2e0440c0c0c90240000d0084d02c2d00b407090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 442102580 1250 442101330 442101347
    0x30a0e0d0c1b0b0a120615050d180212031e03010b03360109150e030a050a03020d050f16080421030603050a0302071d0108100902030c0301110c070b0c06011401 70
    0x600f10f01ca2901e03101076010080c0a00790744058079144900e012004540d4041e0039031a85100304255903581c0c90580300e0481c60028051442d85180b42024803000c42005075035880300c40d014001d041d40215158058408600320340080c441d05418038a4040005106610091080f43c2e0311040c2105100f800000d00d10601d603608200703102c4d02c02041c2d984042e074441407106400c129076003400743c0d045040c0309001d182d0070011a016018034410350b6000f00070456146015001400860040781401410650010002001d4401c02c90744041d2104002c402c01c44c1141d038444080340c0360100761409078003500e0710b0f03583c002c981d1680b080c450706400d400c480c2d000d050034401e400610146a110041e1030300e074225841c0281d60b54105015001294508003401c04020846003000c80c1200d001d07100924a03170f03001ca03410000400c4000342c16a00350084034030043c0c803500d09000710000c40100500050b59100215540c0c0d05010054006001c006000c010b407024682d030014507141550000523014a14201503c0113850119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 442103830 1250 442102580 442102589
    0x10b041d13020d06020d0e0304230d300302090307302d0506040f0c081c02010b03191203020c07060804020102010c0e13050912040b030a0e0d0c1b 64
    0x6507000f007401001669000b51101008030030302804001034101c5c049440340510f000741039103081449003254008040311400c0041801c05041003441401c40c2c3c9541c42d420004170b52007000444804080c0842a1014035040c400f00340701e2034110b0400c50180002074480105120303c0d4221110120004d50004084552452141a101a500014820b840c3c450100b01c81038620800359011808100c000d0030300e50310084080d0394004003800b01591560394070244034404400c2075030340941019010411190420040410151a00b003074042801e524500038250b40f6548012400ba41109080208076a81148402003490388440020b080000b4890202c000b4029250148085e1091650000304c1907081440380b40514000c0c0d000340300c80405000195816280b03180a00c0d040a41d0fa001d0049489a542c412030700301e1510800e4407040305101e0040d84841e08a5003200d00c900000105021850300c503485201425199103001e0289648400d8001d00746144940f40a000c60035440e401a1802d100c8045140150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 442105080 1250 442103830 442103839
    0x3150b0d120207120b0a0c08060907050d060315090b060f130209180f150315010e040302010b03060c09040635010603020a18050a051b1309050703050f010b041d1302 72
    0x4440d0f07083c0784000c1501a5051850300e0703c0c2c80000c7c0e00d0b5911030035296103d100c01402e4180c680d1a00c420031200c03503011802800000d0b42c1d030700c0d0200000c1c08005900d480002a24400b041c074020a081640c0c00901c060a000c1c481c06c3c0f8044c95022544600304412111104110016101c95103038020030004401901c0c0c025102d20202d007003040184034154000e0259501081343c011045083c4185030343d07001a03420080c1d01012200041080e04a800c6606030b00a1291001181002007131020910f0920103548540c0c00e82d0001c10842d201c1d041070700c954402041d05401204e00b912591521001d01c1c0d650040e41c0348010409500714281000c2500460000c55018244441e4640d40303118044402010815451b4002d080c4804a10348013601d004007806614420708030f0940d450350b00760070b0a0681c861a40070340080b1364404000b60881c4503101d1984901516180441d0620740200906e0182505030400cae00350302c42c24082400700321400341c0c81d410110000781c01c1c1e9089480e040ca85006010490400030b510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 442106330 1250 442105080 442105109
    0xc0a15031112071407030c02120f010911120102190f0c30050702090114130f1d15060f0402040312020c010806030c0105070f06020903030d0603150b0d120207 69
    0x114441c1201c0c0c0e901c200074560b0740320310310b2544c0342112941e40700e000809400544412514000341c80c20035a01004016205e0440341d0581780386641d81d09441325440c1c1510b40d09200c501e81a02810080020f07407040000310005c41c03520800c0c8561142c030240288410040141840091907541e00031a000c82c3c9541d00900390701e442240802a40d9500c2030711080a0150300b01e40301032103545c0c0e0300940984140d184c1c02804000203078213040321802c42954120361140c0c8a409520713a041103071003510513a00d18401c11440400d203000080b0700302c1000c48010f541008145d1221002050316500d401d4040e0300514200e581030b540041c540c000070701a0103250409400c450460310640c481f03540005021160480a803600c0c19296070f030504058540c0c4824510038041042088490001007100ba160f1300d0321441004014104a4000d0100e4031b580c100d00170a200c0c3d01d540b0b810a10500460854100c1010500d08041c0050708001b0041a0950344004000b000a03030528040243c0d40d0003441007a000c3d0500c604403455 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 442107580 1250 442106330 442106347
    0x30a050f070311060c15220b04110105040308030a0b04020f0a021b030303190e0312130302010e0c0607120c060213030209090606010c0305072612090c0a150311 70
    0x11180402d100440700040810160449818681e00361800041200b0180041e00e038982d030038070940e94000300642007403071108028490142d51041c0d0f070100e4038003400d543e4080d440c6c03034034000348500a80c405103410311000340300820004000e5004c40382e01403242d06003c01c0c20032402005c41c01a00805000403031030740011480d0050246c1c00103280c070205455030b540b031002040c04010300d1348a200035921105000c8280030585040080364104050341d0114508403440d00418600ca140b0031442aa980007151600d039024100740f540c240180c000400c0460003502c40515401d0001c2c0c1c0034441d00300001e1051403450f210100143c02404852145600504150754a0340b03c1040d4000116880c04201d1084c034414000c960001e0001038a40d10407841030b100e264542c000d03600c0503140368110200c102c4070050f40911303001168910503000c0c07800d030802c0d00d03a450300e514640c0d24103520a00300030141080c5a101c03150030055070f512500c0b40c0e01102d400f420720304500c602060084018240403042100c0001c000a003018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 442108830 1250 442107580 442107583
    0x5030606030a032102031905060109050f100c0609050303070809010525020114150a0f05030c09061507061a010c11040f0b060304050f011808090f060c2505010207060914030a050f 78
    0x903202c500d4880800180d42c6d09c2006617403000e018003444d508a101ca11307089400d81171100007524801c000f820542c503000d080da80c0d42000c1d07d0242e03800b02c0d0b164001201344988160070011617908840c1c840c00900861828950103c5800220002005c00c9040b00c0f0400440c0c0e03000b1360194558204901c45181e01d0326001170400d6081d1070b40f440700b60081501d030b400019046081c1210300c0a8410041c041d00c180c200f000c0412010001c050016903104280b041100c2c02038040e94014606588548008241101c082c0068240408a42e40719410302001826650000d252b4408014141038221000180c1142000c03020004024481c83d854100d08000248000c0c400300041050400c010500240b0846020301a40e040c240c0380080000c150a6050000c41d140389800300c010030b102c2c0c8001c0d00441c14039400500280c40c001203904801a0700b103801002d6542e00852031090409801c00b80000e144003440d003131000308010388510820100003803030101c0b0015075800f071050120040d001800c80d02c0b28800d0360715a5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 442110080 1250 442108830 442108861
    0x90f010509060303070b010521070602010f0609050105010516080c01110c062a0c1f02070605070f200a020a06080703050610050f0c011401080109050705030606030a03210203 76
    0x8900c40c4240301c00003402442c00000702d920b500d52000b0788042c60703480d020501c0300d001020b0a030583c03114410030300102ea00400704000c0c401041c1c13542c000f01d40402402030820444450b900001e080b182007400511140e40c1180480e1a000008944204602c03c681040071190017201400c1159500304a201005144050082e2403080c044205440080e02c03011028803071b035640d8205201c001c000c004481d0288809070005026500d0040054918880c1041006000c03621840000c6480541c0803401d0000d11a8600c04c6940c0324a00307041484003481c82d00b0000d00601d156042498404080d000391a4096005003c14041d950b8042e014400d103541740c40340640074100c100c4465000916090000d100c41ca020354074812902c0e03494890038900940c8a616585903801075662042d250340724644441201034480b1054000d0000900001d403008107454241d04000310350f408140319600c6103052100c260342c0440e1280c0321340e0781401c0070492030407810b1301001d42c1c040880480f58143e00c04410800500c4220706c01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 442111330 1250 442110080 442110089
    0x108030702130b010c120908070f06030b1801140a12061d0712030c030509090a060512060f0a020c120a090609060206090d031a0a1205011d031602010509090f01 70
    0x2a1402480740b440c0c640101c8404180d5540011030903a20000412081e100c0350f2000483c51801d038048039100c0c1c481307d2174611240d11101603120359075410011a0b034144221181d20508480240380d1569100c0203080c40f48060040700100b04a02070340b443c0517619040810003c10741c001ca4041c0c04005810400000c0842c01d08188504104c0d031405e2152000c00f044a00c00c0e2607840c41000780b0784402e0703201101c0da40f1940c1000c40030300500700807140203540c80780b040c03500ca0100f900c8003080d118140408e01194a4110150f54003036071192081c800314815280c5d5003031b4070114810f401a1203c0c01001e8582c03402c00e4460304140c100e180055100041640480301c8415100c0365200c02103484d5560b24100e90711300302114400d0140c0c003c0d4000c000d54500c03a4100105c00074103600344041c0d6607510030000d110300c00944c4c8002d48002c50a0050301c2040428001c50400d012101a00340810218100e4540c07240b02d0141301441c0400e091003100c04580c051001d0318540382d4042c1020410340341800c801c00641001707005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 442112580 1250 442111330 442111339
    0x1a090a1502131203021b06160b090d0306050112020a030209180a0c0f0e0d021f0206090106060c210306030c090207051c020c040e0c060a02032205060316030905060108030702 76
    0x31448002c4107260010140d0304d54010f0024088035582c007554507020a0b1000d601050400084a000781e1900388811001d001d042140050300380140440e240c01c804200d08801e160a00c03008100356078000b40742c100720202e40f41000d81c2d50540100124000d200d4041015402032440b031400b080c500b44045920b08c220540300c002c108118880c442501d001495030342510004900d41c6001119062040320184410b20241890b90a00c2c80250580c03090b2040203803207801a400321040100303d90090080c0c030001c100605108100481d9038607540c17060b80c000c0ea04401c021903000e80400c00284603a01090040d81c003e004050f0003501c2f40d2100029503c00e2005072428800c0c003218100300711016404010b001202e400800c1058000c205100c0504000c4030014000e01a44d01d1402a03526440f0090044503040d901841d41d071115004900c1440b400710900003040b07105200c05112070b0b1502422642c210071400b4100301c4001c0b0b4040224013811b00340300700070800e00035a800060340c60fa001004c0d03c00a07100b00d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 442113830 1250 442112580 442112617
    0x316150e0303030610030b04060e010b07021c02010c020904140a0804090b03062412010e06040b070801082814060a0c1403010905042f0906030a1a090a1502 68
    0x4242e60b901003580c1150384490030100c0c000344036009502071a0f40340405030000c10126540d003074501202c0c009038000800b919001401c0003c6142c520a84051075400a00429445101d500001c10070980c122009016030b181e8000729060025950201d10840c000c80c0813541e0b030044d03e240840391504640f0540064608046500c0d50b14640810106d200d500d2403545441541d1140840781001d2440c002c8007a044032181c08101040c500171b01811031690303240d07001403005080500d40000500c100404020800c0701e40300042c442120007140e103107038090000720f120008090b80708900007801c0290348001d207040c15440ca4101080c4011603407601c00d05005404015070b001d40d05040e240c000a0358403000314031800708018003250845910441c0c119020b11f00c40f040c0c0307940c001c080b01c0340344080c08203c81c00300e01ea440c8072001c1c62605543d0b4562001003a40a00101d25603a0b8410080d2500c90f050390509040410000c0d5030a901007004820f920b40080507005207d9541074a28029804900c2c03c0140810701d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 442115080 1250 442113830 442113857
    0x1512010c18230409080c0a08120f131101091e050907080112060914030a020d1209020102030702040c200a020f060f07021e0d150e070e07121d01290f0609031615 70
    0x441cac05511400089500009001d01565200e41c0180d0307a1032000d0504c0040c0001050000e429a80c410440451044541b9594103007410050f00300d60042c44502000100c00044c05001c1d40c511400900943c040310109400d071147c54190110041cdc01d00e05a01c6101c08a0140103ca900255540c0300c0c541d2030b162817205001480d070348026203c07404d03001b0380076074410001080141020ba21500e500c0c005840c000300641ca41c100304841c2059415624280d41d480100310000f58031f00031a41e05010101100c1861030410f805019250314054002c0191040103550000d02841d2160f0400e461000001001442e00d9401e519081c1d00c0c8803407a082c0c40a1491400c17402d8420210001501d000f42c480032203611480e941e4200c0e00700c0765201600102e84160381c8446941188210801000341d414690b01c4c00440c841102c408043d05031034441c072083e01c202c4c0f138500c9081481c1c0c407a01212103000d03506890303440d43d90815202203440d011002561088a0380c1c101000103404803d40c1c10010504180d951307521204e03045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 442116330 1250 442115080 442115101
    0x30a090c06140f0f0d150602060a05010302090f0405010b0301050c070b010b070201230c0102041502010f0b060306010e18040609020117010e1512010c18230409080c0a0812 75
    0x1c26940c006845410880e1030815005140542000908013801c0c85c034142d280c120620664050280c0b0031303104d80000409000c1c0c586c062040300e6005044002c1001150700d1343d00010b90780b81e006440c1840300c0368801c010509102080d040891041000b900900440c01c2c501203286040c1e00115050b182124007900128500e2180340131a41e04503016514a18112a0000d2000b22030142d92510811140100441c1c14242021f0001d0001001c0d5501440b80f400084003010303080d92884030181e0000c0d480c011076016150f544d4019250410020304e00f03101480f2007000446d04140604035401e219040e07000c104070800c40c032034005409041c800e0380c40c0d40c2c40114854003808208030a000d0600119140b80000700c02080250f000100402c0040610b0808441c0c201c100d03003140c0c20300b240301c400103959010445100343e000711032200a100c0340c610b8285403035000b046001840c4110440c1445130b500c0e40c0900302405580d20550b10011032900c1907600300b40341c519182c001c2c0e80c406010117242503007050008012900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 442117580 1250 442116330 442116347
    0x12315060313020105280c0b060111100f140a0603021002060702150c09060307090f1d0a0b01050403021f0201050f0f1302130e0105011d0126030708030a090c06 70
    0x444126901a4031083c1d0041d101500b0041c001001c218140500d0780700d059040f0300f07491038006207458030510040c09050400c10030400500c05410700041d080c42d0060b0702c000280348150442900350001c1c02c1e01034207050f00081c142e0008080702c0003812a05110307540ac82607100ca81100d01c2168019080001008140d860760412a401740240e0031800c0c0151514283c0700340107900071000307203240f80f80c20361000000c1c1302a0002d60b034010002c1d4403204140201048450040051b01141d03e0088110440184026840d00d001302458103039a1150382034001039001c3e8050310095940140134080c0e000c5540d800b200f601045840040040d0308100104480c10051032a160041000098110075070b541c400c12101155400b07074003260030902d80e100001006429204034218001d1400c00407078154036010880d035620101b500e803240c074a10290010480982540a001c441002c0702c020401040b1901111508500402c9405004080300208000e0312070000c1d40900d207803510132100c811142e502e41c2001c844012 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 442118830 1250 442117580 442117591
    0xf2b05010605030c0304031202120403081b0711030304170d0e090606030103060209120d0f1101020c031603032012090f060601031d1b10051204030f020123150603 71
    0x11010004180144c0e0140c0c01154424041d040c02941003044e0451502240c1c0981802c60036105400180420181d1203031419410422041c1d180040044225800c0b84600c20000c0040003403003800040c080c1c41e1001c0c0107580040c005500b015003040081c0345200c3d103882c58806040300140b88814407004524040307a5240c011003001d81600e042d40c2c2550b44450081d80a081ca00d81d02503140400003040000030000d0802c000d4583d03641c0c18040c04000000382404150108c031000d2079005001c0e00201c2c0200205446660028080840c60f550860800b64010318009020282244280100000340503824000f03004a4020204c80450b50350386095094a94a0000604003241c100c2c5012620a601c02d070841106059120000c4510b000c80305e0f0039034640380c2d8030320711a050b2644c0208002014640f090305e102c00700d01780303082413840c01882401c140c20008005000405018840c030711003050714400d40c0042c4d24166452580888186200c2003105800c80454241e410700c82240c1c100ea0583c14401c060701d0041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 442120080 1250 442118830 442118837
    0x9090311010e03300a020c0d021b01080c040e04030206010f06030c0206010302060a0306092f04030b011e030b0f010f12030c0206031f03030810090b1807050f2b050106 73
    0x1c294104c00b00d018400044c1c0d4003c0c0c4504406800c40952011a110b0060752007000059440601c58074180c24501049280020341d0070032002400c00c82c8141012904590702440d20000d650b5682035610502d0260703030004030010507400104010560005082070584409001c184c82080d9284822000d6a103c4a41c85006030840c2c0010030060a080e40031348503044031814081400350f11007030035004070780f803d1242d800c4054202c2025601e01c141130308d99400c0410201100b0f442c007411a1545005020180300f000c60b041a00c0c0140c1d841c0c00ca03100350b0b61008d19403003601440141010200c582005c802030040040c82c020484000458000000c480424141d15031290342d0101c00769020403825410007448a84000d21041c06010702102c138041c882d028520a03140c02e48030f8100698880184115500091001c510380404c2c44429130300c490144d0000c106072070001c581c640e0341e0380085070580100300f400b11598134041000b80c00041c1c5901d001013004ca41001400300c0201c80300c074580990b8800e00c01c11022 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 442121330 1250 442120080 442120087
    0x31506010c060b0103110a020601030b181e0307020904211e080c090301020a0909050610120b0429271902070807080405130603151508060109090311010e03 68
    0xb4016040480060030504001500e8803820b170f041039960380103000b40c000680007040140100318011060719008030764900120701140f000441c1650311101403405d00101034100300154041482041203039103966014000d140d40381400c0c078003052024480b0070091666249240c480e60040d03c2000314041041d1610491603401c0d40a2a080da000840030b41466101801003001e0240742d1024001003030b16030502da58260856140c4844041280c5001d040c1622034003221600301c81055205201c0c40956940810000343d030090400081e00800d03000c5c4255141d408403480e016801d1181802c2d2618004091300d078210f1007132040c030302c40405400707420780204101c54210201d401c840a502c0c0c8050040c1507040c00610301485030710740c0c402035081500c04580c1d01e10001020300c40c0341002040c408480e00145000e08c6042e045030355158464916264810000e681c84011800343c076464031a00000300030360810349000b5610f800c43d202c054600c40205901041001488a60440051044444030802c3c0c0c80910304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 442122580 1250 442121330 442121333
    0x8153c090109090c08010e0c270105060f070209040b0703151508090a0501020f031005031f0b03070e09010203090f0706080112151d06060f092a0a050405031506010c 72
    0xf00000182030f9004034001c500880c1c0508244504600303144010001e21048030314000300007114070109244000a0100c1001c0ca0380400d05818513410748070704842c16511055028054511030095400295100e40780d002032005000100c04000d0043c1b4513942c09210b1000900d07560703802501144580e01060310171682e030000492041c489103401c07403155000d032070120302c55450751070070380e088000703007001700c41c1c002051104201d51800400c0007000c00b940682520490041c0e5803d03001000e00e6801d10081d00c0d11011505070350144205405418401c492003e5800c06400d0345000750400c80c2c09111600c2034105100c1c091600140500480c1d50f0341ea20008642e0070400305045402141e5011211000a1580060610490701580d070111666104805600c03c104540d075140078405801036000301d40e20b204020444c0c580080181e444a0103004954104000f000d07a00c00e0001c458100f48001800400d49183e41c44e40003000b0000c54004908039482d125031060703104ea50b0501502c0f5640405d14404c3c4120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 442123830 1250 442122580 442122599
    0x30503040308071109100602150702030a0c15020c032a030414040906050103121709030708071b0611010b0906090406050a0608120d0e0105011508153c0901 68
    0x5074a100305031840620341042e01003080114151080d00d46c4030070200301805080e80c10041d45401040d07400c10b00b8001d040c101d034042e4072803003080c5882d410410000e030114103001c0c0c203d028000d4142e188108541e0344124280240d142e400c014440c040541c80d500c1e01480024006080c451080c4800b80070391b1a051414818030300c80442c0d03203006904651100c00e00340c00318140c2c1c45101d00950141800102408842d04002c104a0400702e60b00107221111080c041c0c85040001587d00081c1d00441d9540d0702d0299003000c05a111075002d0924555003400e60124030311b44d01140695210030762070004d1280d50307180b004100c00c61000700c40f456004001c0302c000402007101500b00c2034120010170310002e112074407550401d040c903e42c400c0009810600084150f603c043d80d100d940c00385000540200b009504094002c0e080e904c1c44a02c15040040f6603022071b0851100700b8010307003013010007485c9010814800300d0000c8808130101d00c01621140000d140e2001c2c24415582403459100142403003441d81c241800f14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 442125080 1250 442123830 442123837
    0x60503070e06193b010f18020c100902010f020f0d03051e161205100e0403050c03041e140f040e010b030a050604020f030d090603020a0c0204090303090c05010504030503040308 77
    0x7021400b5440340002000d03004041000080c003c1034451814507600c620800c4035242021302225003a4004ca8010400b801103420410305a0f00c200b8060103d040c3d4045403a0046e00440c10680101e002d442c2022140300950782c00710b0025031003030f2a4041101c1c1c401c001661200035050100c00756030440d840403100c0c40e1281e805603078491010703550062035100b40022040c0d6034a04494154030784002525241005d5001078031044070710a401001d000610b05807440d1139100440b0311400c03082000104c0440c003054003400c203075024044007034100d07919940d8440c90030780500d050549036520090000c2002c1400c3c815020340c1e142d401000761048405039004070911004207600032071214503550340c1c160400140d0341404106200340c06100100803604050040203424822107001900c01d91083c80d210100300d4005280c00c084590a050058903401602026160b15108000081d441843c4c4441c02c0100b680590104001c08c0c052241241002c4d2a0401910244118007000d0400d92050000308000f60b0441c006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 442126330 1250 442125080 442125109
    0x70605070308011e08030d0b120a050307290405103c060f030f02030d0507030f0c0501090206030a0518030a0e122b031107020117090c031b0103060503070e06 69
    0x155038103950328901c41d800d503040030403681d01e026140d030300900c002d127005240b044010310140050b02c0c41b942240d4442c0e40e00d100340c5c0c000520254081c6403072021440c1400c851041d40045203810040e910b41890010380303071640c03114811201490401003582c0c1c2601c50304070440c08c4c43c2c2c208800d00748105402c1d503803100324036041e003070744032140c0b19080030581070500b07100c000082d0b214903500240d25405104143c00d201c680c280c200204841403200c040070a500c103040720407194031030500481d44240c0b801c20601600e10100080e420200c000240700d40c0f6040b40e03001c1c6120747e0b8840c131000c5181d0300d0b01d2099a103a220b5526030400042407500c2e20421850300c201e007810009070748003c94040200710840780440ba100c00d10314954103542501d41038041509409002d0183c40985040c0d40380029a038000380c41c8001e010b041080c03c0d0108400a901140c04000404a4000060490f04400804036407003c81e01025061f003070002c1d00300319001400e4107000070443c0c16140900308050180d55207000303000c05100342586 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 442127580 1250 442126330 442126379
    0xd14060f01051b011b171003081b0d0806030f0706201006090209010f0302040614031e0411010e0910060e010507080d0207020405010b19050c0c0301020c01060807060507030801 77
    0x44002e0030f1034007486040f1050002000c6141100701611000c0d111070300003482c076140e9011120400c080440881da160040c0c1c2c0d4401000c503181c00880e009030308500002030060b005441124140104141c2195505210b54005c9045903603030700c681d40700343d9100e84283c40350038085600c5000b092200740714104e00d048064068003c072045021000794a005480d180c1e40401d40c215400207580240356440410304188050b68202545020700d0300100408900ca1032101703265801011010545c1031811410030034642d200c1d9907094542c3d041c603042c070490084c1280b60040c04149501c540c040c2e0b50828030071540c8107040d40c02c0a01003680c07614500759080341d0440c00850400c8810003c110000e405c1c82d000c1c290410080303000684841c0c0c2031041c4821200b06801041007100148142001c0182c0503c031680131035042c1c41c002d5150307403184900303916080030280026459400440d21500600c0150301610460720180222455141e031050162524401c1001c0540068202c40061140800d40c0f2010711190707040c3c41c0c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 442128830 1250 442127580 442127617
    0x180c05120a02091302040c0206150105070305040b0a1107061112070309030b0a05161b032304320d06150b030406051807050f040f090606030302030d14060f0105 70
    0x1d002407a450f508507a030030140b201d01440482913003058442e415840c9640d00007407429040c00c0c1282a100f0300190951810842c0c00a841c00806114a0555004103083e0714060f0b01c841c000d0b4800b40100c0758100b0410b1007441544400a01540305450b034840310044440030f083e036a208681800559444244141d0500c0184c1d00c001000503002c0043c0e6204103600c1000207428240310455422846c44281d04200b0007000007011540e9218203c40d0049140c0e1500305245600a4003c1000030300103011403140d03c00c1400f01300058450b209110500c2c40343c0e00805a08240d4404507000d0008414118045403c0210703903a00c42c000480e25441a5162500d1221291050f541c0c0c0c031847d00d00354030849084070145d85843c14440c001041071b0000205002410140a8050500d4040340b445c070b041554107446951101d80107196810307164030021045030054028840e0503100d0401075a658009108100c0351464001c04140d90b403030824609005500083c80000091411001141c5030b401002c008107841c82d028 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 442130080 1250 442128830 442128833
    0x15041401050c030f041701150b0909070e0306011401080f0c071e021504060f0207030201120f020d06031113180201030f0b0a091d010207050d05070f080d0609180c05120a 74
    0x880544028407032491b014000484000c1d041e0709540d41e10000c2011206a000c051000304008000d1f24050003003911a000d01da034418208079100c41311204800e8040c0201d000201300c091610340400d42888003070321840000d4071104900401c200302150380d228080c3c414050307040010079107200300008c0480141408810201500050a803049004440c807007035400040401c602c9030003046002c100c80340740c00507102071442e613000038100d04804102d83d181941e80d4103003800c0d001020350541da06140451030420030319440749042e034070003500017144e2407083c20317403140b00d0003851428040c040ca9021000589a00382400d54010340c00b402c45d1070240c9100c251640c016602645425045400038403001030003045070b00e1002c0b040d18110440d060040303401c0c1d004004800c0481c100007100c0c00f040f00385161641c0c3d0342d9501e0801d200e80a158001c01032036203200040240141003a500f1040944040c15801c211282d10110311041c64019500d00034220050f00000300202e10305480c00c0100c850600c000e949525416 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 442131330 1250 442130080 442130107
    0x111030a0518040c080609180a0507170304060c0602070c0e040b0103170a171b0409020406030f0b01080402190b0409090519021c03090914040215041401050c03 70
    0x1024840000410101e0b44911890049419030714441007558104a9104055802000460020319450042c00c110300030490000403100801c04640e10041034070740410007864699292503903403107000c0c03140d10f00c0400e96440c1103010080310126007494603090035206180d501c400203074109007010307240074a070300000082c45000f40d0f084510640c8a5070607a89990305524000ca058440344400c40d41043e418003840f001e0b00e411501440c40c003c0c102d503900304035030f0750034007a00703410103c43d070300100804408a800210703c440c42e006002900d1050700e090003210b007107001c5c00b012202075400c011300081302c80d008640542045103044441d0705c42845208507441d200c110a4101c1d91061b4094040a5641c2c2c0c241c900780701046c4014210041d18101d075030701d0725600d0b03000188500c0040c198250751100c5944200101330003111043d00a01004500b4410201d1500c00c0c6c80500c441145c0c00c2e40a442c0b41c01219002c100d0a4048400345c801c80000545c006040c0c000440307070341d009403001d40c800307201c10000030511852 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 442132580 1250 442131330 442131337
    0x10e13061112011e15051606060503010905072d09020d0b03010204060c11040513140109050d0804050d080702060a02090301060801020316090e06030a080a12090b010614120601030b011103 82
    0x1a0a6843d413408000301e003140a9081c8103911400c03281c41d50000300304807203a00004903044401c480380a10150f84040c144200245500d5020a034158039241c1038004109010035068201e07606843d1440510041d174000d00d030420107403040c03080303201e41402c01800003182e560302800c0c400c4109000091140500030209007242d105030402e0002c105030203107000801060b40c58880c40014152001e200c0d60402003c40c0003d02c00422000b44010000c800d0000c0100d4250701600031641c100d0215000b440f03149001411090060300c0c140c0382405004800c1e0451070251a01030302600060b4020251a6220b0710640d00070f4104e0340e04954103549503680041e00312024005503000300c01a00c0400a00c903500e040c00b404010180c1d004412054500003003100540d0041460002640c11048055407000700c003008a4540980407c00c0d0001d80c035160320001841541103145040e5a019103c0701c07694400a503000c1414010a0460b040c000c09840005070b140d4840d800c14105650107041008103060310145413401c43c1c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 442133830 1250 442132580 442132589
    0x3050a1b1211070c050103020702060f03010308091003020a0c0b1b07050c030d0906020303220501020c101107170d06150e180402030d0305101814010e1306111201 71
    0x110300560306003403105076209a9800d45840c2e02d042d440e240c034603602e19030303c5500e9100b820306141e40030a084041d501e6400880d0b00840820740025641d40e1685055011038110300e801c14024410b55600e403082c00d00a05c221030540e1925202d00300503201641d11069000001001a040c11122103860340386113440c0000752005c5031251000d0181901c006050610748031485024404000c1421401c0000ca42c02104a90b04070240c1104c9106200b10100c4072608074003a074074000c1031903100007803200144001040c0c0001503640c0640500c8510301504100300b644c010004003a040008120940b081075294000a224089440d4000f1030095928028110540d603040981c202041406e03188821902d007402203a00703031201c0c02c56840d0440c1016008240e5844028410b4010b042c0c1da5004544075000d40d00244008016088010304c9003413810403c0c40142058074031603207030807041d40004104040c0c0552010b2140e1380000c00400368031034035210900940407940c40307001c02201c10062200c035842da40c10301a0181 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 442135080 1250 442133830 442133837
    0x801021206040b010509101b1a0603070e160806030c0402040e1e1017100e010c080609090312130605070e031c02100f0608032109010c0e0103050a1b 65
    0x40c0780c40401e0206a420700c0c411030f41000b5080102c0d030020b0342d43c4014050350360b42c0c0385401042c09402d0301c064180d52080c0000581042d0780e480280088a821440302845400240c050300c00050342c65101025410065a940041c1404491150341c074078420110181c2c040f0005048900b80079040c4003160880c0e00035000038202d205040d0400070132400900240c01c400d021144004003503e4100b0403a004106203014000004151081780290090704010310050019104410001d0748501401c50703008040b24030240000c01c0100740000d0a904e00205d01c28461030400e4040c502d408040b03501041040c8009064412035920841036a0210350248140782c418600ca03240c07a400c100541040502d081215000106070140c0c0308201141d0710fa010848000301420024041480d1040c040311402602461700221070380d1001190300d650b14082d400d0742c0803001c15400c019407200d807505105242a030b0f1001c00c82d140403d640e01c00c424519403099011591082076110000340548100b038080461043d20030b0201c000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 442136330 1250 442135080 442135117
    0xb0102122502042a0206090a02010e01020c13050114030307050601060e060705060f0a0b1e091905131b1d1003150e010501090c08040f03110703081c06030201120e07080102 75
    0xd46510040c100120306417800108850b00d0448104d6035030307480c0520000e04201003085c40402e9070f402001032049070080207100300a0060035202c40c0008040c00d02c43c010039407a2282510b003050034080116180c494010024080760b07801c000d030640340319034100821500030100b00480800f1030003c0c0030403801900243c03090030366030070011068029550400c050b0380c0300301a44c2c40c1c000c0504281c03044000d904103065641960681e035661381900d114600c0c000d1020369034201000c0050720b1440fa00c81e1090640b0440040e080d05008041150b069241ea01504ac44110040b11400708411908102c903841018022100100c94a0384d64510f00d90030000c403c09040c6884042008200100b0700615002d8041e10008010070039540d5001090200043d00107404a03070f21141c082e09241c0b144c13080311002c0c42e8540c2282d404e10340e41c0c90408000d9000e01c800340c00030380501e03030100c6d5541c055008620440b501652070045d078010090840c001048007540c2241c251282507000a106c0c45c3c03c0c005000560810001c0300407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 442137580 1250 442136330 442136381
    0xa020d020d030605031f0b030313080d09031a1308070b060a0b03061809193806060d0e1f0e01060803121b1308010b010212250204 57
    0x1d41141c012000041c981000c20601c6580ca00196041038550714043c401c81c000039260b6428020311032070000343d030540400540b4a685111600010007203071024401c03100c168450540440e8089900d000007440360440401c1e507004001c01c410743d00d4024203101d261a0119000b90f817506400d5000038811100d400390f500800c0762a00c0c00301100c01c020100e050500e881e42c64902c000601200740d4a2500310000040720110b0442c5104200014020b1003842c502d4070820031a0800c450003070814515070902c0c0380d444d10a480c0c41180c4481c20b00e0035520300c540d00500340d20350071304200705a0082060a100703183c0d151040b00780c0040c00c01102c020011031a4010350b65030b40c410645400d41c0d204a010b0308160303042c03240402c84124000201e039402c40381a196043d41d5200d829004451040d088194904008042402c004c20180c8800810440e1211802044410080341c0103903218000f440c00c803216000240620208000449005075900d010400641400384182c3d0001e01152480030ba1010001d40480c80d040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 442138830 1250 442137580 442137583
    0x2090c090607061a040c020304060309110301020c01050108061302030c060901030f0501060e120303060603060402070f0807150612030c0308070207080115050123090d023606010c0c0e0c0c030a020d02 87
    0x4c0f0744042c02d40302401044401c0d40042e59a20540c442e80c400c243c0e403841003505000c440b140007549018020025035903909504c04440c0604800c0c0902c540038081d070b070301040d51400000a8180817944c0a0701524401307000d1820084160400d64000b818184c9234403c0d590740003081d1140314041c240c5900c0390b1039800c1503002401500390402010361403d034020070605c82c040e070b5410280e9510400c00c8070b000d0b9603000e4030300d0549041100c000000703021070400300e49a02003003202007030002040c440440c10846c0d82e03621942080c503c008558068040f844109100b400f080c4949191640281d280c0100c0b15900c1c1d540c04868210b0301890158083c0d940096800d0150b5030b4800c0f403000c1801202809003c08030030000d50300703074244103040d4014800e80d10300e03925030210745901d1030350b5814007108944001c00e1006040195003c14814101500d01d40d00c1e1400119150300034038805440030b0b005621081c40714180150b80310b0b10080038103030124990091211983d0302d4000c00042010030010390150403680590701004c2d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 442140080 1250 442138830 442138871
    0xd080408014514281a0402010203040812030f060901030206030604151a071a091905010603080f030613051e040c0e2a0412080a0e120706021b01080402090c09060706 72
    0x341e58100801e11100041000041c1c9044c03140e03000c017624030803900d451005074603610950b8004810350064900c8881603d42a1018610400030500e50210986e00c1400308400e14109000081d0702c54020310211701c442c01c107944404420450030400c0388500346c0315004c008c807080220000310102000050f01070700f00f06000c803030300c250010201440c0e4404c1c03c004442c1904c0340721141010f0f04500300b090000303007880003d42040d0000d5401400d856990f07401d00d0011040d030303841100c105000d403822242d5140429036070f00c58507106401c82c07000e41d05014020650030200310406801030750701103855040854440e4840d10024058403041b0103542461300c1c0040702ca00c0c0301084407181e502019007840204221036404211200c51640525900e035074104480003960500c4500529680161401c0410545032800065400a4600036000c0b95042681070419143d0308c0c2d051007195000408a0b0701050050401c1064140c00295a10000d810b190049010500682000d2003d5501c1910748400002420070320419 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 442141330 1250 442140080 442140133
    0xd0f0513031e0801030b070c0b150f0906010f03020f04150c0203070f08030f07060e06090c01090e010b190207030f0b1501020f1c0e0d080408014514 65
    0x4000751014282c8000d40301810511002e04401252000680c0e490303c28030068021a80c06001e0019034103158583c000c0c030102061086000300720b09400403070189007003181603114020581d10140c1d6403070701c84022000f035040100c001c3c0300464140b10218000315802081e02d4141314640e10b10a1040380b500405140c0742035680b003031110240c12182481300c1d900110480310311013101ca070517036618421841c00c04010000b296000407940608070501001170408102110890003d07602d0b0603545803644448036485c3c60030300c1903140b40102003281070300c01000740203d41c107000224010740b0145036480d01d40502d0151180f004840020f98002008580c080940b0444420202880141410780785800500d5880c4151410000440c940645200381070384115a210000b110103010820600602c2c90203a61540207801600c429500780350f1074102c16425800c10000603c03038107200300381c5840206482050110040034402c00310101c20100b0000c9480c09003020100d8807000014114010844011144007810044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 442142580 1250 442141330 442141367
    0x712060b1503130201121d0714010c0f06020c0601090b030d09080d030f0e30090a1202131107050c100e040b060d060314120a0c080d0f051303 62
    0x4003214407a1420003920b034444090080d54107100f1090005031004603451001204440c10300080c001900c0c0c039801041e200e003900070110f50340b00e51034088000420310315650060021343c5500901000c299020f18000d00c00d0b02403080107140c6040c041040342480c000760440c0c2411030326480308000504003044001000b901624208020509102d5482d4540c804194510101615190094071200710b51f80001c80c004000c8013140e2300e49000308040701e024120610f62031468040c0140021899042904540300030000500e5250384074104465a80440b082c5d641c10b9810540080f01d40c0b514940d24858012001801e0702d00540307131303600c0b842c0143c03903d04060840d6000b0349004c480c3c2442c4d2a007090500d0710b425001c84012450b01884070100723045024031a400d10340301d41041c40000c1806213184684140901c2e0b00191600190105103e1b04180300c5c0c0300c7d201001419001d0b171000864269406010719100c0300202050001d4051051810754074240c0f020124940030300444810107804c00c0114007900080003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 442143830 1250 442142580 442142599
    0x212070f080c1605030610090e070b030108160f05090c0d0f0207060f0b0415090c1403070c03020f030a05030f090a060e06160c120807120203070c0308010501020327010905030712060b 80
    0x6480f00305481542c808c0450040e10390b01c825403000c00a200603030140c281810b07960748944e5940b0302550b0340c0c00e0b00c4000d00402c4d80d0801c0b010900c0480724000c0740590b10050400c44640e112a69610126400040f40682e195503c00f00004039443c0c500040c10000c0c01650040344103d091003604080350f41314031b005413150381342c142862621000300c1d0b03120003140c3c0008000603902110766004e5904507003010803008071660010820604e90307082549218603500175421507901c070f50908003242d46c80c80f84d801c1c082e0100b003090000402c508400040c542e44004001e0545040c10500ea035040250380c2c142c40d045426402c214204030b00c443c0c0c03011030501441218079280d01c0600040e10b41c840386055520f10b180400254070300203540d036030281b103104409040c04a0215078078a072443c0e00500d031501c0021308800164a040c00022103610020030380e0210f0b030307440d05015490700100541d001005540300040d41488210000024542c1d011320041c4002d150b210780340c035070754445460840d0442d074902c0c40441c030550152 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 442145080 1250 442143830 442143841
    0x10c02031218070513020f040b221406280804110d02011d010903020a08010905010b0414070e0109080a06021e040609061805041a01020606010905010212070f080c16050306 75
    0x2d14200704e0301c054402410040f40c289415000c2d10a4501c49000786000090004046d40c040700149800c018541c620009854a80c1c0440380100d104d10800d4200c0c91107801314480380c5410070082c04961607011801e44102d003882390602c0346079007020602d00800c0c80d0600304030a20990401701a43c602045503c4410220540d0001c0c1c000c080300300042c1900c001804401c8000d0340610010000b864004048e04403095560308207074007030504141e003103400d135007403801e9010a418140500c40e1042224046200166103220040b100822031320001030401c1817003800000ca11009010315103485000d00005a0340e04500a6190101110358001701c400c1c2c10104401c000c4c031a404003491003a201d00780b4001501c0003007400d810111042e150051035119280c1405c050429142442c07108d50342100780c081da10540d54280c019030703281016118403400f50300030818413460040b11400914140c2c0c45202350300c40c3d00aa54507002000d801c011400c50303140d4480f41c0402e19500c0150440c80007000e04070020007291604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 442146330 1250 442145080 442145083
    0xf0601050301150909170c100f14010302061602090c09010806030703021809100c0809061317090d08220b043210091802160f030c05010c02031218 64
    0x1521441c4c0503296191512401c21140c1040310310981c000003c00e588441001e010340341c5035075444800b81581480e0800090036aa150300840109031001e541c0303600030343e00e16002e010442e0f0010300245d800c2e0038004101300060b510180700d81d0041101901440d100d070b01a4001424517000a80928400c2d80200404c00040c1c0e00c81d50304500650b00c00314644d12035201c2802151400d2a000c0721220700398188041014881c0c3d0220308e1603c110790080c126022511100026200341ca248440a00400741140c0203009040c508001001144005440c0444c2c41d4440e480d9a0465009051490000805141209002104a0030681c007030050005100d25180c0341480e80e616401303d04005800c1c41d01180c2c020319950650125010621401600b02400c9000b4080024044070503400b415000c58182000e40003801c03400d100b6100114900b01c1200700c400d178a500c2c0d01d0b80300d405500d022810025069120700015a00b8055a115a00e05400031500c03440d0305802c3d081240c03001400d50004030f014580780381130103a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 442147580 1250 442146330 442146371
    0x161a1806060306041101090e07210506031e070e16030c0206070c0f020a03021e0a060e0a1e18050f070507050a030c151409071d0420040e0f0601050301 66
    0x1400138845c000740b0501c0740141c44500720340c1c3c01138400c2d802c55000c0018894021912510750360503249000484564540e400d07040303c6007601c00c0c42d010746c003050100c01481c480401f503e03d0308040204550000355544115030000384100d404071590140d00c0ea945103900d426010791401040f05001405151400510060410f600c4810203806646107103101010b545132042100081d50b0050240c502d6001d0000890702441e4101d0840d03805014900800121144190380c1d03000c429000900c5440e016152003c0074080e12400401c1600000c40070200041d00103c441208500840d4054003141c10300d040c19510303c00b000e0080548061107400c108100c00503501040c010611641414103103802c01e40da05004518200950484080a26150100c0781c0c4002940301144100d00034800c039002d95440c0d498044e40300307165191480540000c0c00100c2c00140e5140998950f880d03c0e80d1071003000e0300281c000501034554a51000707140d41c001c1220b002c0c41d60000c1c010745014003c190b000380300454083e80f0010074481d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 442148830 1250 442147580 442147583
    0x2150c070f06291002030a05220e01030303151203081803130311030703032102090306070e040f050402060f0c010906060303050a170615161a180606030604 68
    0x2100160302410016441600a400c0da0800d604101c0c040345481484039400007841e1a040e0051400000800f0786020100807074440500e50242d42002c484500c1039805810000903480d248002c100346040300ca10103610000100960100ba80d125455404c021301228110040c442c003407140600103009030756060100c02c03050340c0e051031702200c1c0799a001024101f624641c2850f4560b4040080c41d4046480040b0034081564001c8480e510741d40d0402c1d04040d568070082c4401808241440d01d1141c2513205801141c000b0f10500c107003d841d0900c0013000a0a0030812036110011450520701c40380070b030410340305147c160324402d0300410542c01c254000441d903008000140890413400038880d0321000e400c1d00900600c2c2ea104600380701c0304c6d444c1c0c503016203a0381021808000140040c0341c103284030049952441c0c0030380c07400b601c2d03000620340400d0441c40f103521044614400c1c04032245590300003002d1054a181e000345442500d5103500700031a00f4998a4680c2a5010440d13001d10180700d8165004200c040d01319 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 442150080 1250 442148830 442148851
    0x14031b0307020c04060305030c0c0102030c15070c0c0815011202011e09080613030f0504031e14061609120b01090b0409020306040b061c0f0201081b16060b010215 71
    0x703580d1500120b10781090710301c0ea01d030000d0900700c00008000002002d802d00c00e88803802e5801842c01c2d2001241d0343c1c010007082403030030b6008004081a1000302d0b18040e410402ca0f162507200c812468441076000d64217544041381c0e59000c03461418801d522065018007401c1c64681d10000181c0580008100484c01c0d080100c034960780314940400c8500580d000001021700c04259065032400110f08180000c0c541c4c01600401c160080f00d0a62a03c100d0032030b8281c030f51003810070380030070100001c0c000c8880e080e40080300c403014414502a40e5200401a15114039031071038050b804520307a100010545011a4807000c40c41c021003100d04001010b4103083c43c192140c000b000910200710b140000c014207010107029406000d0b10044c0800c0c03041e1010202d02c1384d041540c0800c04000f1110700d400034080d00d024050000d61091141d203005610805c9060780000761850303260b94400c11044048aa40d000c2c00c040c0e84400c0c0000c103042d003082518091341e5406982400504100740c0c11000b8140d00940040900214 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 442151330 1250 442150080 442150087
    0x31005100e090f04231c0e1c0203030409050a02160501050717070e0402031f151d010519020703020306090d120209010906140c100203090f0a2001030b090c030714031b 73
    0x9004214051002006c2d02504407854404c01020344010882c1c00c6040c0120080040b251107184421003000c03035103502900843c40c0a20303102080703000740405001440001d800b004000c411125101400a50034021400007601342010000902882c0303000000e48507444442040000303158000030201c021260079200542d0700c0c0e0703840c60300016030215610000350840102c1c0300031600894002003038000c00d0040e1540070040c4103030104061450080c254282c0054403c104180101c10103070711741d420303880701d03030045900c05074407980044d0900d03c0403100590640c3c0845244200c09900116800315001a108214904041000002d26681c2e543c000c860900261801c400001132011044600e403041c9101960200340c3d020341418044c0d802034a840c0c0c628414042c0c0071a51f8072000c24855070440d800a4911825040010303006d14050080c4102411701d5076400a10341e00391608102c15201d038078900d43c1c2d203540b444e1001000e44460b0184210140d400f00510802c82d48100803107452503000d0000d00a540c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 442152580 1250 442151330 442151393
    0x906041412011a1513030b01170f1216051b030111040f050f0d060c0806040f2313050a0b07020706090b07060f2711010302180402031005100e090f04 65
    0x149104151851000710005017000040c8000100e20364140d03403038000040d4100034000e40d0284c2d00e803c82d141c0000a90003d004260700868004014a9510070706e480900f4000f00300e48413039003060f07506d070109001c00380b04000e848001d00d400c2c4204409100c4400c0c0380ca041c5401c2c80150050752826000e040d0044100c40c3d500c1c009595810000b036041540b081040c8181200e504005100e100300b5603c060103036041243d48904100c4500920402410b489400f60154510f02c0d03429111040180620341c40c01e441c40c4c1c003c00400c0c0c003400903495a0340a1404d17015a0304103440c2c024608800e42d4030030f80c100884400d00740b051010180441781c02c10f822107408505a108408454010170102070040510203100071035194486502d500030b0640350055480d68480b4000e03c0065069110b92203002459103a0120518801d241c50b6028641081c40c841c541542152180c003c900395000e160915400300754080c049584910b80031502c50b902150b8007061030036908241e80c4503061520100703454040350180d07007109076 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 442153830 1250 442152580 442152619
    0x1d0c09010e0402130317120612151e0a11091915030b18060a030f1a01080c030f0d02030904110c03030f100b04210302011b0906030b030c0a0b030c0906041412011a 71
    0x8410ad2036021b43c0ca44c1ca4188841d031144039a000c003c12000018040e0000341c4203007000d20403601d115041c074549a10303210007201080448024000e115024060224011031041a0320300341801070174890b01d0015040000104200c00c980b0644031894001000b00104805610340d12540c03400c03a640a0f050700d040780e885241c0700c070003500a1381c280360420b120078000007400c1d0000180103d000d003041e0305076640c0e10a200105a00c0301c980c0090f000140e4030030402e030009428241c0c4912921103001011a040c98007004441d801c580c42600e400b1000180c220610480c42500f408d828000e0612196140c50680b0701000000241444e8244100303240203115120180740c007c2d0003c0a041c5041c800c0c0854013080c2180207400109540200e0001a140c49401c40341414001103c4490750b000810070541c140c640500001d40394030040040010305428010070015442d034401800140c024640c02d00c0008100c5010700c801c03500b4a1000b802c41e6810406030242c58141100d00c943c100c0070a54103442417220007203501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 442155080 1250 442153830 442153843
    0x207150e04020706020a030e1b31090312090c0b07020d050a060e0106080c060d1e060b0d11030f0610031d060a05011d0c09010e0402130317120612 64
    0x207030081c1c0001500b4042041030703070082c52a00030a4604001009202a810b40e943d19101c0d058160b041d08076038141c40c1442c00303402000c1e55000c40300390100c080c0030040c07205044003032004810444c5901c440000041507080b11460a254810841c10880e84400752030f903009000f40740c890b22801500020300501551194084a1a03aa82180407501c4c0380007280b81c01da004040f0100c3d42c0c0495407a00d000401d04001c0883c0d04866604010302280c1420301c5001800c0082c0720491700856192200c12401070184031f28003c80c2c0c001c001290560b074a84204181890a94142c8410307402075500c1002002203c40d14a00c0071504030748107840d41c031041ca031401002d030001c140c000d00c2c1d41101c2d0720030001c101d403922001951030b00c2090004001d12007641e075524800803040450710200c11455400d00007620506040b4042d010034201403505020010049001c00d0899002e16000d1403070462101051060000602c61702d0014009501680e01d04008030320501c2260201508591007a28659500c8810304010010f1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 442156330 1250 442155080 442155107
    0x30c020405090622020109170a0f03020708010c05030c0a0f0522090e1203040602030621031b0705060d150b0c030304030e01030912030903022d01180201020715 70
    0x401180c103020b0080741c3d90b9041190f460603002c03030004c11020a000304218060803d40d0603100c005945080410030349040b82c4005851600c2d200d4031034500c01250280d025030780190300a4000d461090b0801d00c00900359583ca280f00401e1080410a120049044404a581d400003d281c0000b403104420401c40740e9204100d0b4090300300c1419400320983d039451002c01400c540c2102401c10060044a00c542d880c1c0301101d1808960744820b00001c0e0105445400469104000510340060303109480c040d0300034847c005440c03501aa03c0412060361118284100c0411041840014980e0618240000341c80c0c0c801d802603030601c0c1d6100d04441b405401d6440810020b0021a43c0d071135103803543c4103075240d500e410460b01500051003690900c020355001e40705941c4441d4202c1000c0700131074802c8a007a0040c008000d022800c521420082041010105c1c8030701154603140e0070119681035820f8031103401d442802c041c640104030035034521401031380c0010301c81c0111001825411a0001110810f640d81000c00c0e21 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 442157580 1250 442156330 442156339
    0x30306030b01060f0e0d0305040e0a0b041a01080906042301020f18090106050f120c09030f0607090b0309030a110a050d03090204050a09020d030e060f0409050405060606070309060507030c02 83
    0xf00750280c000d500042581030039911480000d0559080200c8603030030b00c40180205100300400d0003c09a000d5400341c5c041d03c030075008110030041e000400d0031a00c4c01c0e00c0f008103840c5045140181913030b01500080d00311010100411507410261540c00160704410b840f103880010340c0c09040000a004e4066400003103e0920007070316001d490884000314500070f075804c0d02c218422000400d4003806841911a503038550303004281002e1300b19070300c04004a4080c01c00d4480d01014841040a50383c01c225042c480c50002d00940f04505080034050540328260b000080011010310070041100000015036405005514107001c511500605803030500040b5a0702816502030410300e5041c043d0150424046984242d4080141e5a40c1103106000c4400358400294070542181d000c0b404244a12020b0803c0000100360a140000c161818420341c0d00c00e61018034401d80351820401800400c1c841e09030311003c04e0f543c0e50710b0165541d5000340850114041e80c0144400491701d0814035100319210320100350302072b2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 442158830 1250 442157580 442157603
    0x90c09012c0301050106090803072004050403090e01080c03030924030103030f08062b110604080c0406060309080a110c1809060115020c09040614041a09061003030c03030603 76
    0x44100c014501c020140602940c2408000128a44036603280c404490810010714201899980d841140281c4001d603c2e850725000e034009429540e41e0300c41c16000b030340b191700d81d0040207161500503610000d05900140e0340b50000d203541030580e100031080b150f20788801c944850701d11481070005e41e0107407250110015482400700c00032003015044203003160300c0942034603102e406503105000c002c1260b040c501060030501032440401110806210301d201c0139846441c0e103000b64103549000c29441e8115902c07005c1e00d82d003d20060101c606191013404007809451606000d062002d8403544c020b44602650b24007040351111f0743d4048402c09011041000200912510001103540030340c81d81c80006850802043c050f6400006204014840440d4501c0a80d00a400201c0d444402c00c0340d1900014410b841203034075502c0340900151182291807041d840360782c5500c1745040d20403007a4520040182150ba01c3d40c055400d00112800d10300d24881129418681149400c810b4a8114080d000d00e92004113040d06c40c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 442160080 1250 442158830 442158887
    0x81501030b041b020a031107030c06080403020c041524090e1b0d09020f09240a120c061701030503041a120709060f03090b0f06030307080a1d0f090c0901 67
    0x1103100c8040c50300030303500c1040014410708008c0e00c40e60b0a210050030013402000070001300d40101a540d50003806170054410100b86032011038180c94030b80034403542007000003231f09000d24200f011888460300c01084025006070b180030406012070030140552040702c2180400500785188102c40b4824520780382c0c1145071105005943c0d28050280d2207012403240c003841580f80100d04000d10300d103110320b420b00b4251480c1841091048400480741041c01e0300584604030210360351010388031280c0390030700c10744403031400c03524080c0014020084055100c0c00d001c2c02c40d0040003c220000261001e442256007000c500740e030603208411051064004082428a1342d00c100311050f81c02641401c2150070689509006800d40c580840407545d201400400e0b0010b0396000c980700303961400500b503108502170101ca01c1c01d9983d448002e507982000c030000000545481c580b41c10b0b420b507404021803150080d90100c0307103107401100091542c1801400440d0100010942c46c1181c3e1240d265031903040307000140400c03c82c982 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 442161330 1250 442160080 442160083
    0xd02061e040e0108060702100b01170f0103030e01090305030702040c090315050106030506030325050f120408070510050304060b010302090a061106130b0c030417030106050c0d081501030b041b02 85
    0x28450042c244002100001303038180d021921038803407483da9020380480c0b08091424802042c00d031501d181000381c1c06040d294441c1c1c030081890301400000e40026003640c914a401082042080c00d400c0c108a42c0e0b10041000400020665804950446001c184000710180071a00820310b0340c030242450040d80b0741100480030592100c0d060711255034061202c2d9880200741342e903a01ca1030440c40c445020001842180340025a85042d800e4400c5003030791a21241409814070744040e40b2022071007040001000c000c0211308000100040105440018031207414032000703061400014000707442c041d110441e10107168803031b50448040a400a0040c080c0d640ca031000189120a0313074240e5840c0384034010100300c0303030b030070000020b0401e0780c0c400056007281d99000d01003021743e080540106c51540c00d180c030003616440e004024602030519030795000c2d01d6140941d03411b8035041c20b200403401840003200a000040e05a07513a0242c41200c207003404180b010560003c20002c020a00e4661070001d010703a08010a52790 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 442162580 1250 442161330 442161337
    0x40b0d0537121205010f0b07050c031f0501060f05070b15030d02070e0f01030804060f0c0204020706090b0a06061d06040e070503071701061707021e061008010501140d02061e 76
    0x10159140407000c00011000f400b2a8000e00488150890b84c007000c0004080500003840407a1080013901c2c65601e199008c41d14140e150400036100300300c008880401008184200381c010410344c540f1031505a03035603002520310b208500d4042c003550361400006842100b0b2618200d5402c00140442d110398240c02402920380c11180610b0400c0c035403100c04907410184c14111f850681c1d81042c0038518003403408030190346984601c0001014000301010440c09603480340f01811901c1c1c020080854a4105881e0040d000c0c00020b14004406141c2901441903e90100c08103c80821403000c42c1c18094441000451074050b981c0240b03000c08084080003001940280918082d038030a48032618548881503c00c038001c3c109020364000608481041109412412043c80d00715905006a03031400000c94160208081c1503180343c00c581d070144003402812841403107418028030b070000081105504092903c0b1f07410100d0201e03244103810000034a0295500c400440b4501640007110400008281461169640 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 442163830 1250 442162580 442162613
    0x50709050123030c010f02100203011410020d09030605091e030c01150b1909030f050703030f030e0601050d02190603060501030f0b100804050102090618040b0d0537 72
    0x90300602e000004542c1444451503000b405000780240c514011a443e8140311420340461080f92207214481055200540c0604460b400e03900840680405001c4885c0c0d414842ca4115400042828000b540c0300702c0c0a400d499100e8004692620744800075460241d100280d014001c10901820030400400030040031a02610002401601421f080ba81c0320710f11544242c49000800b002404035820000404c0c440041d07003420010300454590f00c500b0403440c1343d1501114544d002080510500d030300f000d5826150300f12880d061010380c01c0c001e0070a8583c24107119035405a0f140510300001c5650315101d000f040c02c07401003026001c1d035035000c00402500f001c0c8a0b840c04a440c048818040e03010a02840c3c009400207860781560100c0900d045846140c01001514695400d1104018940d24030004221801e50922224070303e4401030200b00842c0c00816800c1d00c143d2118581d0800602c000c9010f45200d8840ca15101000d80c00b020000304c1c0b00c0b8103c1c4400c0da40390b117516418041040e42d100410412 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 442165080 1250 442163830 442163849
    0x3050d0c09030c0806070c14030708041203080c0c0a031428170f190b10020102120907120f06021204150e0105071e020304080a0b090615010503060603090a0507090501 73
    0x44d514aa40c5807524010703201000015502250140800c03502c030f14245070414450100ca1070400c294035020340340c3c0c00c46c0d0480184540101490b20a0503400040260000b40d6241e206107043d01c280c41c46a512000300c5801005d0104a025200d01ca0f2640c0e810360710007035140c0301401044841d0708280c08030061054000404034400305007916900d11400f12607842100903403050380c02616014001044a0160f000882d445900d400a000e2661103062943c40144020340000d03032030360798070034200c3c001030001000900c240c2d20081003000416001e510b0100c2503038100e4500304004103282401c030060300c901c1da4000000003c100a020401030101c40304d142c4a01e000e601049602c410f01840d6082e5102030b2541e41c002100d0401c5050f080c03000064451200c001401181e142c0b41d5a145d089090a100c610140d1b03542c82c1c0c1c2401c10080305420700c0000c0e0301c031124109000c0c4007152034001070914000030300b58900420740840000d61001c41000b008031030b2a0440115030019a94685000c042c110900651000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 442166330 1250 442165080 442165103
    0x9010608030a030e100f0c09060f0c0605280615030908090105030709170604060c18050f06070507090b0103110307051c06090504050105090c01020c060708071e0807050715120903050d0c0903 83
    0x130340b2404040c1404ad01541c0d0740c080d01c2c03a5988503031014000c040c100c0c464017210303041d192055020703040400240078070344100403407090702d8628842500e0300c000051100345418030030700e000000d203400112803400c032007424030395103c0e15168011181901c1582001e8010740c51220320448001000909520030b920501c010700c41c1e4004c1d00c4007140c007508407086822904103103520900c568505641e0150305460302808240c10003e5541300c19250400382d6201241140d5540c4000c0e000d96454015449003900d071480061950400b084d00900501c10510122440000440c00c051085d026410560007441440c00030720442c00c0904166009002c2030b50031400d1403182502c0c8041550010442040c0702c00014071190130003000b5210309126500856045072458005000310600c11103003013a410a090080007010b0700c903403152074451316001c00390300005183d0310203803800c89440e5403291400d510341125090100b1628860b1806880c3e070b0042072043c1d104113040041c1148810b9203d0001d40403a401002030201c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 442167580 1250 442166330 442166339
    0x31306090f14090601030f0b030102220f0b0a0e061201181a150c011d0d11010203281e230103230703050a14010509010608030a030e100f0c09 62
    0xd82e4070100c08290b8101040000040c0958001d5100c80a41c40e07800e6004030352030315014000303403c990008c2610035126001c0c0b42800d0b41100c624400c2c030081d0402c0c0e404804114205100c903103040c020140d81c8001c200048200c25a0354890340141c40003010039411458241d6121000c0c1014005581c1e070351841545004491b0038404404181ca040014016200b02c04014040210200c164040407880314959203509030070815401074010f502400010b14042d104240600000a209294244064001c0c0c0e00500500031a9081e4054400e034030120440300100700c6842d05030724006804e0407080c08403c000400010244107001e9000184007100703420003174008041c908034561000b4400c0c000038154910400040c0c0c01300c40110703001c04030741045d18110345206617240d030740510b4044a001c04131003c1001c0080c1541c00e0b0001d0061303039000b5212800034040d5901340f00c903c5a49008100031281095140da0030522059070a10000b98801001407044c010340043e2a0744001a1042004d00350000c0e010400014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 442168830 1250 442167580 442167599
    0x303040e090d0e0f0d061b0809060a0e150402040f05011e090203010b0301051908070603150501020c49030e03070b0d0b0111030a0f02160e0109050702031306090f 71
    0x9078940401400c91001c0342c0c4c3e60707041c40703250742a030841191402c1da10f03481c0d0000320140c10352905480505640380451880c040340581c0c1072071000351041c1d00c0035041400790f5003007103404900509080c84440528501e503035075000003000b50540420580441d4600300010680741c0f0301500004800400303007a000307074003035a174110901244000d2040d031101075428030040c03002d40341c80005654182446d190803012141c03a19900e500b000c4882d40280007196513000c100c0354556200c5282c000400090003d0310410300010082011300d03d003504001014404181c1d803800a241aa040107408203004d11a0082c003010b841d1400340d80c0d01c45100c10b80104512040c4560303580b400151440541e1a0600b8903420080038942d488041c01301d80c00360743c0c14803590222084000360b080015181084243d9110011030b4400c2c0006030030241160869a00d00100c90414001520741c40d00050450343d012600140c26a91018200d0543c015a42c24420300b20b00064002541544400300741c2c15680725140c1039031840c0e6900e02c0e58 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 442170080 1250 442168830 442168847
    0x91208070504080601051306030b1005040501050402040e0f06031608030705250314150a0218040b10110f030304081e030403090509090c090c0703080609040503190c020303040e090d 79
    0x443c140e030721000062205003400c0f001d8005101c4805030215103d44c40b999031101d4004106c40007052178202e17030002c200b140783c9070161030b006190680d0110302e06401c00c2d00b243c2e4800c070011320008008084001045003520308000c0d10060034804510400d425403101c0c84192030703500103103060781c0500c105551501e0501e502a98903070075040302c00c0c20182080c51991081d1342d44c18200c00820503401000d488500c051b01ca02d040d41c2c03180d51164001a9140c0c00f070f80320300c803150000d9242c107405203182141000e425221003910002540b11801d207500c0c9008403414042c60220401130003100c80c0408003d001c100403c0001400e0f89000035142080305c001400c64120b00c03030001325400ba00180005c3c0013000581072071207403190003c0701b00382a40c1603000f960006c03038440001911034411000c4002070300130905a04c070200c503400c52821204610281400e0b00c1c1d242d90f0317000742d0307801d42c2082e000545c90344511800b50640103101a800382c1a6515a666151700308114541201c10403020701440c640407a407907100d010407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 442171330 1250 442170080 442170089
    0x3081305013903170106120e01090b06060c191a09060415230c090a060c170a11010f05060f0d2102031605010603050d050304050318060d091208070504 66
    0x80c191000c80c05000b1000124241d08241c082c03094075601d040c1c0340503007042c0083c0a441c1a480e03a050135806103050504551044c040300c07507946d240041010001d5000341d11150042022522142c85220542c01c203401e0408201c20300c4e45000394048024100316240c4c0381814004030a031005200d0b60340705540d050700e540c01100c0003000641120000301520035117600c00b1829000c8031a0718405440940c504a820501c241c511004810f004640d41c1094540103000c98080c080c0c0d403400190f41d4529039104002c09138141901610600081992800d040c0b10b0028650104071000080c400c0e0400003d03500d00420080ea0010302035500d40001d49100d003000c0350140c9409901199150301c140a440241d03000c041208003240460208100510400c0e104000717125205000c1c1000150003855450401e1810b07404010007014001c051041001081022059416889c20b400c44c211110301805c000903110311807a00b10b030060928000140e028032041424211601d035041d110000540c071012400d0f1b03041e0003035105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 442172580 1250 442171330 442171397
    0x91302040e0f06091b0a050403140f070603110301170312010303120b0904050a020f01020f07031a090106051c0206040905090a0506010e090d0e1201140a061d010e0601090308130501 79
    0xc0d05c00c540d88003e000704241d040c5403a0a504141d2241d403880f01c184140111801640d011503201400740304280800d20040001c2d00b4100f1540440087c560450301052280d4480509034090340e111103501401100c00307084404441d00c80b00c1d0386a250103400c0c5a020300944106a00e801c034480c02c035052203825103000c0c83e04500107080c500b0090742081003802c1400090741c114003650840240300d40c0c00f00b14000c040c45c446c1c80310304c0f0020b0948500031078130580101800c409a04000c0100882e499a28088504507458040e05030f6040d03050000c100c452040e507028092103807030301d0204500b004000c60110b400f180b28505035030150741d80c0c1d284518006400e1310031761600e800c80c805580030706005400001008030041c040c00f059030300c0d145215007116020385407032101104c4802001002c1800788101ea010f071140f400d1801c40325401c5c1600711030524050061951583e9001e003c0303103c9038054152030006540c804415a075a0005240203281100903100d41804108100b4140303001c040300c072583c04d405444400d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 442173830 1250 442172580 442172611
    0x110a050301140310050703020901020609120307051806071a0a0c0504270509010b03241602031902010615030905030702091e070f32091302040e0f0609 66
    0x820b03104040c44100250f161113032801210300b1007824000c607032240481e5100180c440c04500006030820600804298890300402000c1c52405900d0f03055a07000306803031414580741c45055040d0040380004d11520b0b83e015001040c82c00c20000c0805582001c240300c904800c00540f1443ca000040c1c40d00e0b0300920300899824072050107842c0f0780d840054000f80351b10b14032215914146000500700c400071f451940069442d9125000c25050422403098050000941c0f00381c41860a4041c0448000c00b801c880d0b0b50610003021201074510800a561900080c03c030108400413003e20f003c3d0081c442e40c860b8100c03805044141c0c0003c180a84200400950058081c600d00449542000304529000740032407540701c0e904001c12022160509440d01c81c041070b449650740141e00c900c0252200d4041c50226007142d01e04e040b01d40c8100643c3c440501c803401c84080664880c403000300010000b40c218004040342600c042000076100d032008100f00d00860742c80140741000c0e1915814000c00d940115001c41030140081c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 442175080 1250 442173830 442173839
    0xf06160314010b0c1207080c0c060a0f030b01090b03100f05040207020d060b0a120c03020a050f06090409050f0f01051819080f0702090702030a02011505100809160806040501110a050301 81
    0x104028102202c4c080140d070403075180340c609045d07175402044013516080310109804040120420000102c80000c4890318104455207000404810080c100c0303104068507001c1860241c0d000307a9101c0040c00517080850745034503005001c0b2043c14040d100d2103e04042200303001401c0d00f424422541225000707003e160071142340341c40d400060442d441c0f26030b1304003070407040011700b10109a41900c6514418280071050502e5401003166a650a80005126209451480b401599a5411036280d0942601d001c200d00c0804c3c28910b040c1015124030040c10f001e9111724070704220042d030180d84a41a0f004520381060002740310719640f000340c00c107444000c4405452000c0440c0c4000081e2a1284104581d140f4052065020880922098480324090380c070100e640050f035502030292503c0011000242008145080b0002d860040740d4903a8509010a0802140350f8031014402c00c0000ca0785a0303039121019654111045e80d840040b1804d681c035503e00207685440140720011542862a25038443e810759082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 442176330 1250 442175080 442175099
    0x1006030527070b0f0c060705040621110309010605011e0f120b0a1706060f03102004080a03260c0d0905061f050d020618060403050f0616031401 63
    0x15541c0c046640b18266000903410000e80041600f9242c0d6041c241c0c48880b4080b4841ca0000b01800903400d1080c00e000600800e0303480012402c1c51203124007081d014100c840d907074000138401c1e82201c450400c400020001600e105400035412224282d8605d0b036201a0482288c0b8a0019034a201e00007031101d00440803117a101d01d01c401c3c0c0c5001c28507000640c1070f4002d00003842d940a9a0b00c03000904c1100300034400142e906103c2c0742d03803211042e15400e01040c442c0c40069151070002301c0ca038800036500c443d240d0603845030440e0881c41c1ca500700c1d0582d41d01d9495a0a8542d03c4004d95001c400280c90f521008020f59117000701040700c0b4401d4400302c40c0765151200c20040541041060805035a603444025002c82c804028850194598520080f07480d080c10705040c5113a40181c12190140d07006203150700041c5c403a84125074070200c40140c00c1b210074413141c000980c5482141e1000d4402d01c0703021600d0f0100d60010610302d008803a001250f4100280003402034081d00c070324000009401149000400c4807135403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 442177580 1250 442176330 442176391
    0x916140909070b07032001091104021809091c021203010e1b2b0905030409021308030a0302180a03050c0d230c0406050d02060a110c040504060510060305 67
    0x110003902d000503100c0260300d41c140c00c001016030016800801c24200201d070003e81c0d0245014640003404150b40c0c41c0c0354001491010401c05025590010324440040d00104c48100410340c002c18211440c10a2140190f482030f03108082c2c1e119049560102c0764803070000859900809400d000070b03003540e10b056001d41c0205001000481000d24001114065406003002000d84c1585240303440b44074040c4178100400000341492a1000c989440091004641c00209450464003809400f41e520f404001c10303d8203554075580403454a20000c80c5840d0b484e500754016241c0f000e030030700c0b6000c4265a141c0c01c12a0301d148a00c80901541c00ca804403085a0a140d900c88113614003d6920241c52208802609503022010300700d0300041e0882070189407607190070700841c0000d00007142e00c0702c408121500040d0031440748141c40303070078000101908251004148044d4280c0d206c001d204202600c0c0605110303028150460310712498202d0381e0000b1135158040c0c45028041c240c419a58100d68000c158800c1d600380d0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 442178830 1250 442177580 442177591
    0xb04060b03070902070303020d0501050111070b0309030f130602120f03010b09150406020c0a081209010804060905011506180303020304140a05090114030f0c10140705060f09161409 79
    0xc1e1070300109003e00c0324002072141d00e01c2a0b40050340c8503200340340042112010381009041040503040d441d54444c0000384c100c265029113010729640d8a9013210310340386220368688200721170310124603d5007001210f4a0700049560540030f407190b009448403001d5080c4030340d060340641208140010300c411881e0307401405404901800c02c03c20b805078401e80300c0e0702d46c001d42c1c01400140c2c04200811800d0070031111690081c1010401824200e8131910b6204083c020444118100820400080c4c1404000d030400c10b2000d070401d00070010030300050040103c410042c01104081b58601e040e0071010b1004d481c03054100d030782550285080034280303c0c54008400c5c941c8003060380000c03c2c10b4003040954450100500030074100030b10201941301101030500344880409a811103402203c0c000003940c50b50404199074410900e003100c820101c52119101c18000c904000d8900d10841c401c200e52222209102401000944102d070002c0410304901c4610400c14013034508604100c185041c098207149103180e4000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 442180080 1250 442178830 442178833
    0x5030f090105071a01051309020306071b06020309010c080601020a03141317061602060106144005220f061d22020d02130e01060f0f06020a0b04060b03 66
    0x2485a1941840d0100002c100f02e1442410001002103150441d0a40d10080116405000e03c02340c81d000252101d0b0010300180034031100548000c044079540700980e455031380c020340440d03c1b401c101c4009802417a034000715401040c00c94000c107050b5800058610051641540c92050f1007900803001031460b003120aa100040009900c00b0407000310054a41d81a4068400103001a24040c201c10484402911001080d5000000180301e019840b0f00c000c44c0c4011282ca006503105408002c404020751560f24004002810604116003039064040c0380300200c8052000c5503800303848000b0040d0264038004200340c0380c6400302405181c2da04940088148400301c00000980f02e558400341d07010440807081241c011049001082888400003100707036030100165020205003031581d808591410200c9002a01c500c199551144d00c00c1da00703410021b6081e41000c02401320315aa001c1c0c50341000c1450003009010100708001140541c070000ba80851035401c8096001952201d07140c0c0c500503d0a8100306405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 442181330 1250 442180080 442180087
    0x10e061c0b031c020307050105060406030804060c02030313061e0503101e0e010305031b1b120a1202070906090e0c011202040b070b090609070b0f0a0c050d02060f1305030f090105 78
    0x340b036142481e14000d00b83c0c0740c0140d96100554600903007124001014503114900e404400d20200e41c50000350b030180c858604040c00141001d00000385580145104120840a14400400c50903803103030341014480501c0015406503503403080305403007a0004403411a81c2c0700e14400f0400914100c8034214400d08c0041c0c0d800030f026500d42c50310f5000803009820585a603800062901c184001601c0000d084581d01005810283c0d085000e900d21030181204062107031240201014036400f05104190106600000c3c03010709101d0908040e40391a000c2c0304103440d0a1420b00d0006000c03595000c2c407822415444c2c0a459002c072075200541c0c3d0402020041c0c80b03550740c2440049071280419009080b802c1c044e07845ca00c503030f01c0c0110b0014901100100691000d800c0001c08001d4032004900f901c40d61a115100c564542c100714804480f42d20300900c1c0a00540320380a20240e1240c0c010400c0780c090060741d10a21141d555101d031007420b009012000a040b80d00401c0724000d10258480a00201a41490204d01c0d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 442182580 1250 442181330 442181353
    0x4090b15010c0b092506120902010516030f020c040506092806060c14010216060506030c0603040b0405011d0d03020a0e130b030f01090309030f05070b0309010902010e061c0b03 77
    0x71080c000f2125008207601c6000900740f4411030581c000c3c00010351710071000c034031030501038000d1400c581c0015174070352103482d8001035003168003440545080e851520b9124030031a02c1820b0007014005940380010140c024059903506908150003024401c11011704648825241d03000e500200e0169417900241c42608a907402c5030003415409800014506035884c070b110444603042400751407000c0811000c9903071041002c0010010001080c01c189504860005090b6a03614042428120b0f191501d960007000002000308215510310001d000b68051802004040c03454084001c446c001012081c00036030080700200c030300a200750000c01e00d80d0340500c0c2608401c00240003061001114032139420010707031540a04031540c1000c0100d03812a000010007440000341645026060140900000d01000c0c006090702041c000b003000382308024140d071100280e0740c1c03511749501130090882c00812800100841c1c112042d030b141450070740b02060900804411340181d0b90394208020140900d040c0e40501035080641c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 442183830 1250 442182580 442182593
    0x101d04080f040f1a070b0f040c09090309180209031203040f212304140411030408180105040302061204030309080415080105040203160513050a2304090b15010c 70
    0x81490340f4040c1122818142250410003401c480d10750b86003014429600890080003080d1380140c0101511200c2d611282091a40c40c641c903007040300c840e410310f0303084000c1681c4030307011100701d441c9403185884010740a2441e0059100e50001c865043e44104111212100031100458100f0700c83c9803164076503401503880119090b0f0a00940c1d2603402140c0d41504242d8005a903a4104801a0345074900307000c80c444028050b00035801503541c0700b02c8040e003c1c1c0c141c0d251980512031200c1c0e00802507850340781a141038100d9078014001d031440108042407103d09540140d090300c00f526801000c1c1428084410b240c0211504000c106a04258070f42c052007000c0745a84000380050014422452104281040060b0041006a01040c0034901c10800c2142c1d580713114002c2c0b200240300d40b41079983c0d10040688003041c0c01290f08a10b078028441540040c506408008203501c80c0c100348540b1a07400b841c4000c100031580000300140003000e026000500040340200c011540390f41c1410b060001c41c5c031030349820 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 442185080 1250 442183830 442183837
    0x60f030e0105040807031106090607110109080c01050103020a120b040305030a0f0e1b0102120a14121501030509010c0e06031314070503060c07050a0320010e06010e101d04080f 77
    0x244c0d02c05400080c40301c00d01d0750003a1005c0002c4410320040296092180d0b8042e51343c1c400500310000c006544d0900c0702c007805c00b90411040ca6070030a808584030300480368050f00911003803008a104010380c91001619580390031a031000182c0040080c4801e540d261000e0302e02d6403004203103101d00703035a881c10045d00c0d200f94132540550000301c4004040ea00110150318017805040c26229040d94060b581111141d81510100d4854010078034000381c5480c0b080c6110601c90084c1d00e600d001002e2100300300b00d4146160020310400842c01d0782d081c026506e510300c180307080b90801c22400d000039250003503900320b509100f00110307000450414185a51403072a2580c00344031800c0300c010080d82e0802e01c8108542e01e000c01003c0e405c0100c0c10f000c180780c041503650741a95180c070440020b090100c1c1914801c1928038540c10204040c10500003402400d00500382940c548900340542c607030118041010070744120300e001078001602c4080883c401203224144200b622100020300460f40754204125910a01c13480d58050b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 442186330 1250 442185080 442185083
    0xb03010e060106110309090a0929040b070f0c12021207140d05191107170109061109010504060c021c050708070b0310050103051f1503050a090c060f030e010504 70
    0xd0700055040101c01481309404299040342075000303200199290382c6408803290019081c1c680007400c2402c62500301c8600e0002c0c220106480f08011001c0d040c9250311103454410381c4035a4108840341d0342d8072000e03074007900e04149006c0040c6003016401c1c002813141c10040d20561482c0100c1c1c00d2540d00c40040d9510340d1108800304c403a544040e1400c204244200191040c0c0c4654ac24914184640c010420380c11154401849080207050045080d0101e01800104064078402c040d400414401c0b505050103083c1182084812615116001d40c4140c807038001c2e10b0440b04140c0d1014600b030b03d07004086800707014503074060340d1008900328000c0112605034000c04081e4400d80207402203601d030101543c100043c41c0d000c8440c210081007000f1802541301141030507074400b4200003403191680c89400e100f03c0058000380c802148020000f1400b940907041030726100000e50703024031156941d0030005041d00c404800052000d1008071042c40540d018000078078201800345000950f82950700c14041c2074410a450 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 442187580 1250 442186330 442186333
    0x80c0c0f030f0a12050c03040b101d040b060a0605040605250c050a060203070201080402060a030b0411190e3001020a0e010905040219030c0521150306010810020d0b03010e 75
    0x3c10301c2010f90000398180c1d145140311410015490700c5807104070140310003040141041c0d403120006100e0040c4d90780d0b030009003042d450314056403444070401c800d01c0d80050314142d0320044100002012841c000b44070ba8192162a511ba50a042c40c011042d1030980144040c0b200320b8800d81030001c0c0041c1d004514040941c05424501e40c46840c140c203003c544142c6400040864004001c442c0160760004205500a9410354425540d00b00c0303910110005e01064004660190902903100e400c0c55a410251184950742043d0302d8400102d00d0058030500203010341c880d00040ca000d2110f1042070361a000c0b150114003108a044410501a1640d0882e80140c07041400710302c585002107020350b44408141c003c2c21081d2011440d2103e028100000c8089040c100810540c5030242c02a00a00c0382d010b5030000c4002c03403502c00b00072403040008a42000102c07007171007403103c50040711042072400181c0e060481d40742c030b0090200601143c060501070b501c80320ae1b143c02d40b0784507060150301d51802d1180a030220f00c48070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 442188830 1250 442187580 442187587
    0x20304120b071425020f0405070801030c050109030b131b0b0403030e0d08090d2a03060522030305130b16080604060602150604090c061716080c0c0f030f 67
    0x480140c0a1903e512045103030b080c0c184501c1002c168204540c144840070182c09102d414081e2000403c10344551764140d401505005c240501b013900b00380c4407816281300c1c10032001303002c0c0c84400440b0041203d20010f00003521030703004182030700040c100c1001814003480d0071441d008405140d00c500c100043d4030543c005c42e0001410003d140d481828045a01030855881320440802d4540c172100e401105002403081c040320039584100320070b20510340310342c00d032181010707402c050f140002417209031062205031021400c244c00696085040004610401240044241e141706a41c90440040c00d006060807500900001c808020800ca003088910600b0444440320b417110706180000c3c000c02c1e02034001401103042020a000d215004103103a200418050310502c3d55599850004024100010000d48003040c40e147c0400c607294450312540000c03442c5d481c4008161a4980b000c90514000f41c181070000700720300c4c0030503810020b400042000704115400c840c090070740364500c1402c591101441e9041d060000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 442190080 1250 442188830 442188841
    0xd090507030f291612060b12090111030c0f1e0a030c08190f06050d0b1e0f040201050f090a060207080c09190903050c0d020d08090a0213020307020304120b 68
    0x400507402202d10140c04186400b0f4199044200d11201805604e840e200c00c00c101060360340b20f425a007445840180c4140403c581d258114803c0764007021483c01d0014205001555501c2d050091800350801c540300c1d649107648006a0200f00d030420811400f4908041210031140c5554500c80c84240c00d00020180c4d9805010001070100c41c400b04011090240309020040380841040918040c00740c1202d0100301c018060005c00000e0103e600030710751180c0340c40070751814400c8402229110b58001c03c035044507034901c08080e004101080f41e40720310701c40e41100001c005510580150001110a8641c0d90500c00b04c2c1000806003c1c47c1d030000001039001500c2000100000c2103204070800c1c0c1511040d44900b0480e00702131100f4085d03503403800165150351500003054410b404131074200702c45001b52a400d00001000039194182c41030700900140b801b030042049400082160b081896004003207000458004464030003035003000300b0500641c081840005070f03503040e132060172450314801d00302c2d1800e40c60007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 442191330 1250 442190080 442190093
    0x9090506040b030604020907110a0b04050f0a0503160c091a030124050d03050f032e120b070e060408010e0f030c1209060d0f02090a06020c150d090507030f 68
    0x5010600c103a09040b14a0520b803001324801da0071540640f680000c0c3d960f0418207440c051030b0221303e42d546204200028003480003414815002d10311440981e00d94042400741c85a07030702c007000300c050b169400400c02c48103000c0d90190042e502610403114682c00ea683e4003410700444108440c6c03003801d00701d418071454280ca0300303120f4403a010400c55200b0710000c2940c002c403035203440307940241c600442c14a00c80d030081c14001d40940340e00f02050344270244e80e03240c0607180e5411201e56a041d4100a0450151510164001c00c80001500c8a4401003510200c00d61100481d10902400300e1042c88440d1542404548a1500510142070f041001050000c1c003046074914000f03003a40c01c140345410500c90448110008200f01c815807054100941e1074010060000341c00c0d114081101d1116882d1201640c5035510341d801900e0300c49070403540805015547e05081c3e807203010404400394000c01004080800302c0400010340700c0240d81e18800074820380786035165403421010ba0826078a88a10b09211405c0085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 442192580 1250 442191330 442191341
    0x170a020f010606020d0c060509070504020a0518010203030c1c0608031605190c0303210507030e0c100509040c020f010603260c030d0903020309030a230c10030b0a03120909 75
    0x41ca07100900e80c20000b0a4020030290310354400508480d108e8000c6400c11340b0811071580a404014011550f4001c1a100900554080c654500040c8031b00410310b01c4540c004000c2e20322031414039140510b4040c20203d0040d644c84034011400b030307050b9101c0000c40c82c0c0e042000a8044403000720501c111200d55400c0036450003035042000a0340f0b4080c00c18210006074107030403480840368103080c084a0001d01804066007000070700481d0b0700030340c5084c1c01c0002070b035410317000306428060190950700300402d0740e4140080c80014040c40c03030220303201f00110f84e1a0700b0b281e40010030040440c4142c901c0b00358503160b02425034055078804c1d0b46030046a0040c030050500803889034001c0381480545071034134444140c02c0707840e4010075100c1c40e40640d46400501c2070600034001c031203600030b0080030381d284490507140100131080c110032044001030080c0a2a904554005505543c0d2003000302000e0310780710b00000440203090100c00c0650400108040080003801102407486004040c1d201e150059040c0401e1004490 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 442193830 1250 442192580 442192589
    0x10b030106033605190b041101030c270e09010c0e010203040e070302090409080c0d030e030a0c1403071203061503060302100305150a2c0c030c07170a020f0106 70
    0x101440e4060f024054083c010303040b04008031a2261000164105903003014001c16003e00c90b04d44c02c000c140100120400700d94840c80c071552207407000381404401101112007174034464000c928aa60801c11072000c0a60200e20030044401d06ea0070240c8a8009084002c0c3c20b590402d00c1ea0344800d500b88825802802192085200b88011400c1c503280800049c032403d4041d0200003419070000341d9402c10745541e00300107035440c0c0114900c2c1c1c0c1e4142c0303080340550784c0c1000c1e0f2901e00040e2030320000c842ca02340003200701c940e080c6240d0740d0b0b0200800141c80f03460039501c181214515900c801c0103e0000039000e070700a101c1252994400240300344c50a00c90041d08202049900105031511000b400165a2084482818841c1c3c0c9000901556403104404086043c004820740c4825910800031348500460040908226098820074011210090060851000341c401c1d032060744042c00000c175840360690141c034502c0c1c0100312001c9003400c150b8841c11030360b01c0b1039075917001600402d245020700750090180710b0042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 442195080 1250 442193830 442193861
    0x506060108091209030c0a140f120a0201051c0501170715050a0516020603240d050606060705100533010504061808010c2007050f04051e010b03010603 66
    0x3440d006400070b440f08082030102400e01d00104007449a81c42c01c0214581105e806071800c403810703450b01096100390342c0841889101d0b4100c1c85510040b8106200450b1100b501c680040004402690040d98290070049d5220507803540000032026800380f50003094000c011890841065100240800d810401030741c000f500441c442014600380c0a078890b040701c0d0240c10701d180880e25090201e44c5103d03d80e03e4058041e42c880d40110070f0101c003850004c12049d800100e0390f004c0300d03480c2c8a00c0901c05072030101c0c00080d0803034202d84005012070030700c0401040004c0c8501c1c203072500c607034204005104454041d034802404442d010304080c3c80b40038020f10401070b40c610349000c468140401c0300080861183d805400104161120b141011091003141c0002501c40b800003031100d0820a800100024004d4441940442c0c140c0003c4079104d40200d44a0156038001e000840d06072007410510024003405004041022500712100d0000948510650b01902400180942c1e95241c600004c060310350b001d0014642 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 442196330 1250 442195080 442195097
    0x306083c191406330d0b07080109060909080f0a091d010509060906030a12030608030f0a0f090f03080723010905011b05030412140c0f10021812190c0305060601 70
    0x4e8010b104d1209440c0440b026265907685100c0110b218556000d900401060100003801181034200c40e01505840e0701d80b104109255448511005450803600050721000c0100821010710701c040005090515060a005488660ba490540b4084c01c002c100080c46050b513000610007450014021178024000b00d07403440103030130441300194a9040d80744c8024050380760101a141d4803806030b08120020140c0700181c903201c1c81d0856040b92164440d1490f000040d03481e4090b4900b01c0c0c02070b11240c040c0d030034005480030f0300d50440c1d070341d08081d61001c0b90a54000b510a03010350079055282c5105d2810300c100000119850070186440c5094a11790329924607108070a03510541069400b10a072503000740c10184502100e10110001e82d0302e40054002010075100010720704050001c0010040303030040b100c10440d1032840612003007034101d0194100d0006a0004070344a1030f0580f626110200c1c03041e640c02d007500d140781030200c807035913490f135101104840896007001c042091000c24001c540d401403081c20903d01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 442197580 1250 442196330 442196371
    0x30e0f10110403080306040b0f040218030f0f0304060813020a0b070b1605070b19060305070e0106030507122a03091a0408070209090a02100306083c191406 68
    0x2d136000080416000300d56400316207289a407003001001300301002601c02c40d61400c07000740752007528000c0f02100380223105506500c0300450780092141c1c2d600300600302442c20303d0305040d002c0703078030305006003140c1e00850030400a40096600d9100d804010049649039903603030f03640c0f031408215003c801890b01b001c06881303542c2945520b400508407040d0540c0610000344980e80d590300ca000d002030f00006000c4480c138148008c01004400180a002e0f50040c0183d588140c5c1d80d4001102510b40441d039810000340d52044009c80c020258004001400c5810013013840700344000d90764201c0e242801c8a10000989510002c014001c5420400307902c4070b4100440d03c040d1a00e921041c0c0c05118a00009016030034050009031030100900031401c085600800050041c1e10080d4010050310b01405407611601440000170f248865225018420b040000e041e5a100d280910b0002c1501d002c091f21203005019814440d20144158144090418414291944a0410700031180c1c60154020071076805500c0c002c500a4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 442198830 1250 442197580 442197593
    0x30a050a090b01090b0d061103040b0c092412100614040803030402060c030415050901090501030e060604110405030304030503132c04060609020304060f150308040b0901030e0f10110403 81
    0x3d065602080e070104512044d080491501d296118028056500d007102407205120070030002c40c01280034081103142c58030780c4a069200c030f200c0d0410b51075001001c41a100c0102c0b8198204110529400405c142440c08040e081c1a0040c0220348181841940c102d0a02c40c003074000301540c1e2840a030303105041c00c29060008055030f030f202c045c1c40030b031042102081391401180200103c4000d020310301d1190802256031800a000c3c3d4200c0020b4a022a800c00000b0503103512030310880200d03003020340047c89940c43d160240402000c001d04017050703000c4100404038441e00d003080108001d6208a00451780d5200740038200403081480e421204c40401682e06000d80b41080c001d4950b002c905c08409061580c40340e1a081008000c00c1c0e020581c03050000c01040284402c03030b40100070ba1100440b0a120f403841080c1c44924550060200611394007050000f40701c0072b1502000340c062181d06040001d0aa207400d8161403520304460920a044d5000320610400c2e16441d0164008401e0024802c0f402c3c1410350307441d907 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 442200080 1250 442198830 442198853
    0x12010207150b030a020607050a0b0f0c1207090f030302060109050f06030d03020d0618020c0f06010521150906160503060a0314210a1d0a050904080c070b030a050a09 72
    0x403900d03141d142d0220b0780c1c0c2c2c0030300100e00c1c0550300500d203655403015031401c1134803206025022b0742c50030038940003c2c002009418155205068148086203800b61404484625820103444034080007601c0e20007255554017551482d0146029400604c034a61425481c0c82c180d4500800c0000d40c03030403400034030917103440c0001d8000040990342005030f210281c0f81501c2c0010b20b0780c3e9020100110000080e011480042e5008107480340b00241a40d240817010b1504694440c0300384191604441640400400c00118004610080c55010251351404070840c105d1520b44906503030500c0a40c10040601140c500d84c2629070b13a000c2801d0074003c0c110f103030280000f902018907110142492004010304020240240440000001080e1300074426103044511000942c100b03071510307004a044002110340301e01d003540341d60225200080c150152203080906022a4290181007100d00396418031500500080511408000d0f124a82d01142c4034607007003103101c0c19600003911a21001707140051000104910101c40c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 442201330 1250 442200080 442200113
    0x6030605090c130b0c011b031b0e03190602090a03032001110d0e030c1606090e1306020903030408010f150e04210216080708010b0915090a0902060c0a0212010207 71
    0x5145c80b40002c50b11207014044100b540c1070840c4008130000c81c010380580c00498101700005280c070802c0c11100c0e0985443c803203041d0360744c0c0c07603407060a00c0c0c5007101004010448842c400c1c800542003003100780c04292501002c1e0001c0b80492207601035421781d110030350030990262020a000b40700c12143e4000c50300451181480c096480764446c4941c0360000800c1003101c102c12501c100321130f01c82c44e04a0040c50180040d0080300000ba00c01140080c2103015a5412801041e1240301e4085c0380100c3c5d680c40009520880340c07943c05000c1404001030224082c420301c00001c038501c0380820740d1100300c8a900f5034607200390084101041204140400701700704421a807500030312025980c000c2d1140f0f24050745480d040fa064526240c214000200314440042118411074246500910890308242c042102c610000c803415041c201c1a41d054108901c4c04052868100c4491a00055030300b180b5004611241c2c05071681c0e5055034801c00301003045050010101080e179010000031424050103640750340044000141 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 442202580 1250 442201330 442201349
    0x3070e0115050918010911181e0901030303020405090a1b0e1c21030204060c0809040204030b15010e1005090904082a070902070f02091302060406030605090c13 70
    0xd11500c40c0680100d982c0f111008100132242c3c0d0500c89068030301d03c401d00400d1111801e1120101504205100b6144003462000320290705034540400d02039032070782ca02030f200d51000d250b0381d88941035129071140e18083c500a940c0540d0784c41c14201403001c50f08016200350035032481e008a041c2680303a0b80c0e84162040c06289000241c0e00c032104002842d00d0511000460340181c1c00f91410204007040c4090f00c0c0301c0c1d4920404201e16000c04209604a004900c910404690006c07956000500b419004115000c00240300600b400c0c0c40351580d00c102c00781120503003c4802d40c200c217914a0f60b040720501c01d0440301160f1040d0340c8200540018210b0040e4030b4114000c170368120208040280c1d8009803160360141850410320561640c4800c0e208000038400da20b41402805404a1081c801e4000c40b15113980141e01481180302941c280b10800d07400a18814116482c01c40840051351028014401444a980c0c0420268280010000c00340e41c090b140381800d600c00c020344107001c2c41d9907512500703da038683c9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 442203830 1250 442202580 442202609
    0xd032403020f130507021608070b0403080f0d0207080c010e0607121d030a090515070203030703110109060914070b0412080901110f0601060e0d0b060f01030b090406020a0e03070e01 79
    0x40440c079210307090a00e5a080509000402c1a403586c002440c401c0180f144048003e8140d86480c140c0d1900c03002d0044034080b84007004144042100783c0c000b00a201c641d41c81a40c074090114011b00d040340c1058200715110400000c0f00c01411030240a0503012584400140003182812503002d0440d02e443c41484046a8543c8901d026070388035000c40083d61440d40d03081da81d94071020320000b07183c94a00d0181f94407405841d216001ea01c0d03004810f40300303202d40c0903006500c0c11803191410359924400031030001e00c1c0e640b101c41890000e051400760301a440e02ca0303902c24603800b00c41052103040c0100d540103011400320600080140c204000701d8003404541100641d5a40c400d8240125449404140080514400c0f03040c01c042602000401e1380c1203a07069607030311004402180411944c1d0350030010103032031900f902c0701103091407402002d10301c0480814100000c02e000c0c49000300b262840704641c191409507005c40d01a98054000c6901e0386800c10440107090b00c0da0610600183d10304060049010666041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 442205080 1250 442203830 442203859
    0x2010f02010e0106031a0112030509010c1103030a11062823010e060109090b030d082203090f05010201020f030411040f05042004051311040207140d03240302 69
    0xe500c041c402c01c0c502c4000f448001e890b0700304801e900701c21034050f59244245000004a060401d1040c501695040c2d5031540b500d0040c0c801100e4440c2502016250341004c03110140300c41d6001c0000b40884080350311740d958000b4603401d40781d040c540020b04111a601c40c8284011051041091991150701c44078000643e04d1300c2c015110340310010511140701544407034800810300c145410415807254000f6650101041d8544411006660b070340e21200350075601200865540b58094081c8130b601101742d10303800740c501d4808641e007010302401c2841900480d501c40d0301400f0000007140d103c006004c00380000e526151000b030381c0000300d1100a001400413582ca4906d034032180e82d56003180d01c004140c07500034006428281044549005144808100c07a92070f140000c0d83d50926000c1d842c0318900016280c1c00c03100690301c0b60056414060109684951308119910010f0755608982a0403c00c0b200100446d017490700c0040c0c203ca00550180c2054003410281c202e00b6403014507650240c0e0740c142d03000c00c0e4644d1074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 442206330 1250 442205080 442205083
    0x1080f072001020c0106030c0e242e0c020918071502190606060e040e100f090204090f1205041a0d1e151205030d15120804090501170a02010f02 63
    0x140304034008070307500b0303c0000003d1250422400c020381d80d00c1e00f800c010f20346480d00d84025003265001402041031030b01b03903103000c985001d2190b080c07960b40b400c4076510200e40e20240e02d442c02f05c818440310003003072441450b8404e41c2004403005074003e01d4004525400c480c11540f050792a4402d02c99804003001000864242c1c520030711503185240c1c061318a02c03940269519241e0702601007070003014000b40c40c4240c0981c3c6031410303008003414080404041c0c0590b52960448502920548004d440515203942c1e0000c0140c460713110328204203010307604801c207001e010300d012001408070807180810040b00344810302140d482c4020911003122402d00e52943c60010070007003000340000000e6000c25103070200c1680e00c1240c1d590480151020340c16100038140740c45d1206c0d010f0401000b10050269481405104000b0680f940703d6585141d40c1100104825070310440b03000c0c099402502180c8411020404000d105414001c00b0301408011146440d98981464a582d4a60030f40d000641007105050801c50120300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 442207580 1250 442206330 442206337
    0xe03250e01061d0418060c0c0206030903030f0c03220f080a21021204060203070e0a0f09050f04110904020a090f0213050f011403041b080c01080f07200102 68
    0x1039461a2181581d441c0307005000c001294003201058118280e910481e46414444d03d48580c0e80d4140c40741722107007180c072803e0003001040c01c11818041c20b40000c0d07001d40d5580000d54400d19a600003035680b4603002403000d00b0007001406d8290100b0040c414020409814841c01501d0001400b08607920302c602d0030300c24081d00b010b61001d000c0c00c0c1c00180600e10181c0c0020041c1c200c03100c07111034451400c15071b6029812845102c11415200701d0950100d000140c480e001143c00c0f048030320744100b100e060140060201702c10b0307074003402a1102c15002040204603901415902c000400207080507803402d5211080708180c0179038a80e01c50300410001804548e00c001d040c8001c0c2101081c200716078050504400025071001420070301e07070881c015001a032480c009005d038216010603507840d05500210910303c40c032b0381c00103003048902242c551181500000c0e60751040c2e0003004010b00400544841d04000340044401418a401d03c02d14401000702240e004041203800700d022501c00d0700c0391640c01407018020700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 442208830 1250 442207580 442207589
    0x70f24050d05040f0f03030b1021020906040f0f0e1e131b091d0307210c0b040303050a0e070f06050a030207021009080d050412140f070e01150e0325 65
    0x1c40c0e8034401700034590b141c0d10042c440380342525501c10130318034603400385d800044002406105826001071481c0f40706e944d8000e424654800782a007070409071286402007a00b21581c00009031101300d0340c02041012582e010b43c0d6000003170462100b4003d42c46000c1c6000c138a1009040c0c0d0215201c480d0a5410400d210b0f032040d0002451802d013210480d200d580f000b0151201c6840450015182c00840307840c103602100301c0340416803005900c819101140403440058120820103418404105a841d0210301502c280510440c440e41c0c000800d440c00e600b0602c01c8491a0081d42c0c16940010000e0200c01101408803059544a0402030b46400300040100c003e071003440320007504040040c0d112001140c01c00c1004054500c51403e80c0ca2003020502e0482d1711307029500ca1014080c0304c8a07603000119400c5160b140c200f000d59419907603403001002c456480c243c026880050110801030040003d0400c0b1542605a40320074a881200c1c603c80c00002a9503800d03090300ba00300f0a40141b901c01408111050000007807 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 442210080 1250 442208830 442208843
    0x5160503072120030f010e0612010e062d072106030f030f0503040c060e0a09180201140405030601050f0301060f091b0f1718070f24050d05040f 63
    0x6103015086000b8148104a404400d020400783e4000846800182d0b44504440c00a58034035031720307005c3c0c0c00380550f101030f200507000040b4210b20f0381507800c280030b500896034000c80146400e00f008030044070380384400180007100314280c4201d052200000450f5640104951502501941180207100030340c0303800c9d040030360480e403401d40000f0404c00c00c0e009071030409020351500a203400048a00340c407644800c4500610b400e615000600000340545102c07220803030054696142103031903c0d410303002c985110600c6100c11010042c220115031f4000400c0303089403500c2d901542854a4900031958860b41801000d04c107031000c4250540e645c5095200d00d00410f01c440501f40b61030358800c0c0341802000c3d0f400705000b00030003c03480b150030603004222054140d03074195070300003a084000c610108000e0018010f0040001883e500025220040000c400644140b0700d40e440c040e4036050501708100c042124803c50032041030020400f150b0450144d600050440501196540d00e41c64403a00c00e00281c1002030a2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 442211330 1250 442210080 442210127
    0x130b1201021602040c080f07050a0c1a090606041a090a09121d03150103060b042d0e0706020a030c08040f14030613202205040507090516050307 63
    0x902e0480b00d810340d000d0003500c041000c0c20244c9400c84400c001119202c10981d2201c002c1803086110307000510f20941c1c0ca10700210503248583d0b030000c5120741e910781c0a80c401d4031001840072400c0c2c140465030f00000221010080d48a000c4a5143c0c04140665118441c40101000824401a507001201e0031395200c0700184c0030f117854500c050404031403520002505090b1816800c40c40c10009405084101156003155540c1e1859550724003030180e0402a9030401e84500e500a50407003220f54400c2c030032121360000c501c81c5411502200461344540495501513000750010001940c010441040c015003521b08244030b0400381c2480c02940c411580304200030b00280d07000003441e944800e4007084d541000c405461042c0c451080c64120f04c500030350044c041080000d42d050710f100101001c4400460043c00110318020b000e00303e01004104082c0d400440c54a40f4100300811106216040180c51030705400c1010b400c0c907068841e103060001003407805114000001c280014043c0a80403010b40004152000c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 442212580 1250 442211330 442211347
    0x10c170a080106020d050909070c0b0c1c02070f120908030a050301170a020102150a06050307030501140915040204050c12070906030b060a050f031b131d06130b120102 73
    0x101a031021044400256810001081261001c2404002c00c40a541c03040e04250035101003015508000d071581c000d102c00800c8590009165280852150200e0b0101c0381d10303480ca851002c02905000c0140c0305a2030310401140340003a10501561405030b03004101d41088840c0e00310f007039904040f00d40100c92144008180d03c20100c1d80580214140e801043e04d00d40e99a8903007003017540d03400a6030300081c00740c0c01c1940c8907402440202403995006107940004a0500c0d9683c1c0401c1c100b01c03080d042560b0594441003030004500722a240e40760888240c10040001c0d207076881d40c401c00b154010304000e105a86401c0415030300d001c0402a540210501110b921090030801000307402002c5d14071401011a04042c00d4075858501001915100c0301580c46403460002c0d001c26882d6581d00003000d0f07040380084081d60002c1c00752990003410541280500c842c031014240750f019a110802051412401078800341048401d840d0341280e0002028aa180441d079a501da900080c00341303650124100182d1700c0803d440f003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 442213830 1250 442212580 442212623
    0x30702060d051006030c050a0c05010f06060c1a13030309050a0b010e04020a0e13080c030c070b13120f02040504030c0203120a180b04170a0f0f020306150f0f010c 71
    0x90260f001400c60016203640c4040030b6041d5408100d640f00881e405000d00070700c0354040c3c400002040e100c2c100009024405104080455075250001000100e907001c400042100401e041094079403002c126480d107243c402007180e0030010700b400041c20951500e03010003c002e8100010702c040e0340d1010404c6915030319041c43c0003e41c441102e050b8880e40f6003590000b84100c0d801e12990046d20b140c00529810a02c503190414150f002c01001c400300d2008100e00c0c1011901400800090030000300b04642c0e50501c0c80f040144441140c1082e0f00c1e0089a902070400640c3d11426003c031258141c0b00400c42d03540d10300301980c08408486010b074140c00b6211804000504010040841078016191900040c0d022500d0441d0102240111040c10070104818018416000342c01c2c00d1141402c012282d681846a541d00d0890002200440d0340640701e13a2080114035003886160340c401218109000f10354041000105944043c1035410301030190758071120341c1c81e4494070441e10010f40003616428441131480c02c45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 442215080 1250 442213830 442213841
    0x7031715010e040e0c0f0d1b1a12130f02100503070f09030c0e0c04091802090c03042102030c1209040b0303030f0f06040603051005060a090b13050702030702060d 71
    0x80c00907419000300302e414030309032183c03c0712142440014402c2c4100f500074010754080d02c0164940c040907102d1440300080000c900c010a4100e4a2445400c9614105007040482032404042d401d414040c4650141c070303404c04803003d6002074407110f030081440d03003402c180d507002c0c5404102a40140450b44000c0010307030032900a500808041e990f048621001d0102181d0310707019404014200242d01c01c040000c140401c51103600407414600c3c00d4981a901d001490480b07410868075090804d8020300201980781042100d0340c070401c4802d02910b145001c0d0b80b10402410322401c0150000c035010391010289100b0004d0b65945404003085500505001141e8081c541085003494480ea00b4000b40c0203080c00c0110503203014500003451540c46807035107503102000302c41c001c2c025500302c0c0d51600000041141017010612150000c00f0006d00e506046050180001243c3c111090090600000d0b1810703031a2540200310f10310031480009156100d80c00102c2c214429070002035880768002c0384c40d400340100740e88107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 442216330 1250 442215080 442215121
    0x90a0b18010e060402041202060306010302310e01050f10020c0307030c090f020a05160f0f03050a0305100602072102040203090607030b10050301093b011d12070317 72
    0xb41e541d00d6108100a80c4600d002c0c195910710342c50501c00050030320f00051504004141009402c0c500e0a01d02d405045044401314441a4501d24240c0c0200d00380341002c6025201c00711840d101e03581008041074094450100d1280108001100303890420700c02d02011800102c0102905c503507a80c2c900700381c81b2003496800341e20501450300100c0c5030800c50510896100c0a02070f01c0c0c640c1002c0d00e152102c140030104040551f503041c01c584c240400a42040f660882241c400e443d070383e4550b51500b1004044800040c0300c072004d80901d600500420f03400007110740844814a5071030a0003c10a00600c940001469009400030700100a1103540900450310b6485020266810006d014240040100000e0f260b0a018045070080005120619041e041206807100e08204501144500c0400c0090a4800c00440c40c20301141492614402c4003800b130001e0319000001c60541c000c80c51078007182c9400c1b0344200350400e0100050300c03008160059480400d0001200142c5040d854039844984501451406 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 442217580 1250 442216330 442216349
    0x314100b0609010806060705030409020703080412080402010905040f020909100617040b010512030c0a0b070318022b050307030c0c09021c05150306011508090703030e090a0b1801 78
    0x900300e00c40d0900600382e55510205030340708840b5407580d00c240512584034076003e40d006e00082001092940e441c3c0010720300c44d40b0a0741c90300c079245080c0c2807400141c40718010310002c0000c0d074806d000c0940e034000341303070801e40da421940082d1309a07029900c1c0c0001c0c865222510741000da49001c01c94034083c038140c2c8038111034103511201888c41e2000b401880b06101280c00405003010f030030040c441c9007440c80101000d0320421049a2900c00d402c030101d85043c000040072510341411004018406074540074003030050340038202001944e0f00d240e00181400c50072944400007164070441a42c800b484040110001a800c841034954030019414014195480d2940c1620108410075000030504514800c880100c41282c000c8070000c0c000a1740400a03050103000b00040b40201c21040600d650148500c0740240060071548a007c1800032001d4118200144007400700e400400d801c101094000030f0020107104200e4030040035581741c03544040103000640b85103030050140c145400c070309405400a00d050752110076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 442218830 1250 442217580 442217591
    0x4150b0f1e18010e0109020a030623040c0320030619090903081605090f03030d021201080c0111150402150d0507081503030414060702061306030507020313061206031410 74
    0x2c8600096100a1140360103109100d801042801d4281d07010340203124042c6800720703507aa80e644404600b500b8800e041d600c84850700401d0040c43c500351140d5030001109007020300c892443d00b44060540e00c400c0c007034009440000400207042e981c3d04c022680c401d14035148074001c0ca90301c51007140c00414054904802092007000400ca01c0c0e0ba0611102c0c8848101c0da0713510b8a8030a6140600080302e600010b81901880305020300840091f0758006042480c8120441109035894000d0441c54080741c0000503051103400d1905018079140401d414070748181500d94200f56844030310203d280c1003488442042034134004120b074510764201d0f4100d2401002d01f580c6450540d1501c11449071104080e0b954184d040e481040b04110307a107a4510400d84186000381654102840c640100e0100d6100c0a810420b00c0e0601205004480e098800e03550401812b10045080c1510200880800b80642c003070701042c01410f041d42c041c401d029410010107194041d5800c565542141401c40d41c41b40d802c89506a62400c06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 442220080 1250 442218830 442218859
    0x1d0616050f0d0309351605010f0b01090b0f0715020324060316030e0d090f0b090604090b0d021810090212010b090d0b010b12010503010504150b0f1e 65
    0x1d00a40b04001d80000b1712100a44540c0a251426440d01e040c5494204010b0841115110280d000d80001c00c4402594660f2030024601582164400754141c088189450191425644d02203400c1d01039070007003054956031304c14a40b40c034021400784403001008164100c23410b1131200b80640107580505401030f250240020411240705d550920842c549800c88401d00001b94074896141d50b101c40d1035054200002c403491868000c0307041c4021480c030b81000c1013200d0700401c0140b511002000c0103100076201c0c4c900300006540001c0d036500c00e40c81003080268035100750305299a98117401d081c607564010909140d202c404c08040442443c211641d06060504442c00914010540221202203400d126000b41e9607080010414058010403030f13098000c80184036500c0052015503105020309030700064140c0340d00791f000c102242080c052704000d0290741481d05000c00620392030030003032181d2070514012a140704039070086001003109110031580103244002003104807110001441c034111040c0c0d0f052400d034403031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 442221330 1250 442220080 442220087
    0xc02090c0a02060c090409080309070f060c1a07050d020d0f05010b0903100e030c0a03050d150302030a060c0e06040e04150501030f08070203120a0f02070f061d0616050f0d 75
    0x70010071001580140f00041c0c11160a10020302c6108401040050f41c00e00c1900c40700010342080310802c46031350000c00c040c81108040030400c0010421403400382001c0b00da039903c00c892241040e110801c641440740100c6c010354000d906803510508000c1e811500c4480c00c801e0400540342100c111012140f8100010030105450022280c1508002e0000c180f0350303070294078003402882680c203d5081c50100348441c40d6203280500003d9840c1e030013a80c805407110340104510080300c0c1c1e55481036405410b0410200010b8401103440b40324035810820008101079112800c0e15102e9a00e0790140d8031070030000b000700349524000d00d01d03402a8091207010b441d01810404280c102d13442800068403c20300f6080c00d034001200c4100800c0e0b858800b034240c940d1900d000105009a0b04100c1650010800c01c0c0000c0002a60401041d0014805c5450944040d4a092006032082c090910103000012411700c4030401c64a1703002c112000c3c0500c2084c2080810f0f142e082c125103401840b90000443e000c2ca98265104510 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 442222580 1250 442221330 442221337
    0x501171e040f262d07050325020a06030218030102130f090b030a23010609051602011e090c030c150908070e0601030e0a0b041209061d0103020703110106060c02090c 72
    0x303c6803d01480c05030324490001c00d03241c6900074848082181c4612030540c9041c00041d0000612400086481d41129003918445d00001081c4080211118001c071313016907075814014003214414100140d48414550b03c00c01200040306203190150b00004418440c204409108004c5030520460b090007203454200080955401054039541640400d41c0000420301c07541c81400110304008145a51004524105096a40300c0c3c2c052104260f0710030070040c0c1c2c0c0107211100702080d00c0c14402004000c0342c07180080c4c00d40c1c52018520003181d5440909104021a801885000e540c00850954041d43c0d5401b8881c00d480c000c900c80c00c0001c880c28000074040320f000483c039080d1b0301500e840c00401c3c5e9a000044000341840c075035070f4016105a10045007ca00303019521340c012809195001c0080b10000b401a02ca1040c0b50b010108214a0380440c1c5050110464000301c602000d10700942d0325225030038100e0301408000400b01a41d4078000c0700150f0030341c05c84108002030b8825a4910b0659954482c514120b01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 442223830 1250 442222580 442222643
    0x1e0307110622030c06030b01050702130e0309040504080c010608160b091302030405070303020c0a030f0237031a090307020f1c06020d060801060501171e040f 69
    0x104a890802145400c00151080b1181e151242060300e400d408104605641da07071080c0c80d42c907080e20302400480c0c0d2500500b10900c5081c04d10364546641c80e4040746c0c80c00982000080902d586000510000701c0500885a02d100004c0082c805401c06081844480c1d0004500d1000c640c6062800035500d0404a00804542141c0c0d00c0d000e01945452941a8998085007489502110300e018a46900c0c5140c4003860150340900010004103003503240107854000d0b54204070b407191444100070000600801c0000d29640e9058845110b50180080074100c0220709607140c1d42100030701301d0843d007c1201442c450085a01540d40c07144595103c001809000c3c60581d290f98603900100a06030150901d00c190750b44452015064000d6103c410915200c401da070724004440701500000c012600c2c046a01032980030340480d000800c4010b00d0a80003030855a034000d41c070003d0b03060600c002051080b01d480251000b040070340c58186146850302d070115440d005c0480031105580c4003140f001e1050f1036166102100d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 442225080 1250 442223830 442223843
    0xb0102070e0a0e1c050915130b0c0307050703030c0308010911040e070212030705040e06040c230d110703030e0609072105070306050103020a0905160e1c051e0307 71
    0x240c45040041c805003c02c3c0d080515948180c0c41103603034100d2032080c43c4000c40400d0340c8091b01d07002c10b8820000484c4145c101c0103010082031114400001d00461840110b810700d130700e802d5940442d8030815045000e13050003c0c0841c01aa07000000b07143e0460f030074000b0305100780d85404180c6e1300c038441c0300100d450114a48a41d14014801880041c807040c0e0201e42101e81401182c0c0c10700c94020140c0a80d030300840355100012400325003080b41c000844005a0000c104407010300c4a015500380c01010210086c10046c03111040c0c800c52448200004119020b0003c010750600c9000785200c3c0d260060740c0322490440009160000b0f080c0011008a007080c00341989001402900789000750301500441c0690f034034540f0803c2550301e040040c0d01008900e00a5105d1400820250301d14010071480e01c90706c0c0e110844017405c0a0400402951200000d2548207450030101c2280845c0404074541c65140c07808d600c40e0a1320554190301f0300100003031190075511201564050300175038022842d2680107820004045 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 442226330 1250 442225080 442225109
    0x90c03100509060103141c0e01110a0506150105040906030501290901063b010e06120f04080403201c0803011211131401060504051c02040b03100608010b010207 70
    0x603c030901c014a80116a0100ca041d81e00c0071216040c44410440410701240c23101800e0070325075811001c1c101c03010f1403402c0941070348201501e4041e242c001c001c00400481812880225490303010303a081e54090142d80000308081512803402500804480c901422020b0b056500000480c50307490380203101c001c01400f01c0c46180d1a003001590302ca5000d02041080d07500c030160b01044051400b200a03803189880848440c5c034401c02e4009000500f161111a014070403c0040416114202c01010340190407400810400c1d41c039402c0c035681902494000a04c0e1202e180e10b1aa01d521007000980b42010044030301100300c040c03100384181d4145e20010018117040b000d100410488000b100310054480c015280c00c0007144140c00018000003641980d8264140c1c3e0355a59403082c2c090b0311801c3d014008606001e40b61a00384800540074100103100144403040c944e0b1040115221500300b1221880003904440d1121807800a1b000600341c3d50160408941c03a0500e00b480039840052010200c80ca4170403050300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 442227580 1250 442226330 442226333
    0x71208070605192405100503070f0e0907031a0a050d0602030a090b180706020106050f10091a0c162706080d030504150c0504120203070905090c03100509060103 70
    0x25100c0208010b4007401e424081040112031801341d00f6850244074519003010101c5403560500d5540c58100381d0040070340ba01c0c421b10307442c1c0203c2240e41000c2c0e2800c100c0140c2c0c9100d4400c44145840081ea148c0160b600018002c00c070341c15401600c1c2080b60001c548010501d4081400036203005c0d48619030344a503c441e480000700d02641d0003190440e640c003c0104c0e1528003505c88411708030781618022170006100c085060a41c1c018080300d0060900d07840240040c3c0d2a10b07000070901342c0e584081320310031098001c1e0746003818007030114100101110b424941108101c20305d0180c1c2900000c0b0301c6211400b0b031a0350340c0110030019074180165001c420b0226081c0540e01c0442136444031101d40000c40340d60701e0f90702203094442045402912001c5542c041008e103041e140102548600888201040c1e00b49894400b00540000958042d42c0c100c0010f002406110700000e03180c10410707807044402d9032412040c00001080822020800d0805600b2a803914459061000c100c030f00407500180d80e40c02500c0140b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 442228830 1250 442227580 442227593
    0xf0e0906130608060f061305090d140d1d0c0103050f1812160614091e0c130213080304181d1006030302061f0902090409080c03030907120807 62
    0x4004000c086400500e803620f5040d031919000e070070703100e41c807228400f03004000386407821010140c4800000102880315040c0403c14507030f104a40c0d0590300c02e10160b00c40707134911a0350303950949001201e40c400c2480180403503500c1d403541d04c90504031881240110722540003154003d0003001c0c01523101500850311980c03003c00c117203804110110718610034001c955883c00540b4114002d0160201402d50404061800d03281c040300302c0b1440f01e08840c1c085000002c00c070001c00d000c1f640c00c09007105c810729104941d40c00322074070703081240003102a0ba101c40f20085221841d40b542d07024008103590400c02116050b19054403a9503070144d4411128403201e000c1c030b04104103131141c100c7d1489110800f0551104500c2c0041d040c1801c0d41c0390a5101d900e662050100b0905604002e015004529000080c044c1d05904e2280d02030f22580340118a00039030000340d2090a500c2e00e501000115800629040c0c40b00140903090f41c880e4401c1e02d40703540c284149000881e4540c42c4e030591004040d40010b0b403070f02e48240d565450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 442230080 1250 442228830 442228849
    0x3050301090506060c0f0102030a060e06010f0e0111010e03030901050702010b0901150507021e0a091e1a0a080a1a01121b0f090f0612030e150d110a0f0e0906 69
    0x41d50001002d21011010340c170100b1020003040c01890015031285003190422080354031a80c409130f05217000d04c1c14802c80e030341c0140d42d4510074038a52510078550340007940140e54004201380343c14490362814a007041540c4021001d0b5015680c0e0708024800740d15000b004a00f40c2e020b155103036500c0404240100200c9d4020104052020501c0c03d155007050541e40008a0150f40080700300c1411904103800f03141d074a0105150b2001e0942807404001140310b950600e09001103c0740d05040d019942e02d1410142c4004080c40f4403041c500800880d1059101c1e1a01511070a4407a4100e8601340c40b070f0590184c42e1810004a03050b40c4030401c1c0c503020034901e42c54030302c14021301c42c620400d044080b03200030580324240c074120030241250480104071300b400352000c94221803443d44100c0401c4001802a0002903014000140c1041c04480554422a000c580420707207101d00400c40174101d2038260659800400c3c400900b044462030348903660150300e4684169405c102a40d1038a03400f41000002a40518050415 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 442231330 1250 442230080 442230091
    0x12c01051b01020d050105011e0906050c070320190602030f0703110f01020a110c0901050f150703030f0b030a020307060f0513120507330e180f0601030207030503010905 74
    0x30288140000d4403500d089901002d501803025451780018000c0356002120010750303803082c00409400c03d00d0000010103008050040c5410800c000440e45034600d0108981305c00b954201040400310140809440c40041e5081e1069002e030165140c08074040c142d1924030300488606401031880c00c620181410250380c0414021018080a5503034807c3c000303020480c0c100d8080c496400141d0301c01c031607200070306515000b081c0c503401c0e54081d415201070f0343ca401c0c0c0c3c2181180c2042da1402100d40641303002602a0003241468880b002d000320300c0c4814558590000c1200c00d45a0030104050082c2005040e2100d0710040041d4242d80032075010000385104103c080e11000003483c003d810141c21080c00880c0346419401444509102180001800001e005581c01045042303042070311071450b8100215050450a090400402c5120b203100c80d1900034000c196510340000c18142000d9280d41034890090001d4403540c0441c003c41d000200b0710f5000f0710841d4281609a10b03441e0541e8a00b07a00c2d40080c00c3c00508 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 442232580 1250 442231330 442231357
    0x703060b0c031c0f140a060f08100c0c08070c0f05040212040f02041104091505010513031509021809010c050309190c080a0b0106140403080901030209010e0907020a02012c0105 77
    0x2000c000400c20303200d90315402400170a0a180c504269054805845050b0414001d05021000400010380d002942d00444a2084001b0030500840d11040d60000394110001d00b080500051080410003e03034100c0c0151042480340d059080c1c0c1b51420f020072801000e04110281d8030344008a8041342c420040c0c0000c6a2004101240c184100c800e0120306e0342166000040842e00d42c9070305c0b02006503515a0201500c000c2c6421400e04216500205009005210103050500349508941100e01c150f08030001043e0043d00d00300e244500c0c034a41b615501310840314031900e035282c003a041c2c0000c0d11903011603000742e04d09001002c0c65004165603081d110003c0e602165002d4240c100002c0b880800e0000228980c0152410030f0a9031528401030302c55040402c450100b10402c00044c40041c0e440300c10784212202c00e2800584814140005a91610207541441d500c444044100900c81c0c0d4001a0300026520030f0f600d900c3e480c50402d0780c007a42c0800c400f501c40e41102c1da82c03444100d1544a0b0340a801140c15058 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 442233830 1250 442232580 442232591
    0x1030305121005030106080c040b0f0619120911040c18140a08060c0909010617040b27010e10050408091002150103230f060609150909060703060b0c031c 67
    0x40005d00f183d100e0390040c0d4803900028803061241c6400d218040c164001924100360104000d070000300f00340325858801d000c2d03070b40e030034003066006100380280c0040d41848031301003002140b14101903124800c0744030f280d440741e820240c040c040e05100d004040b0702d0070009201a8829800d0802085040700c2d14020950402c0104500103405e0004000030750203182215030541d5200b050300d050100d8188160070080030300030582d808010260303003000401d43c0181c01c8068500b05031100148040e00d003010707004030910f018003506501100441035000d100d690002d0001c68060380410007003501929011240900b24020520030141682011200e00c012501c141c416a101d402d003020a011905000780c1003603d0303d500100b00c5007289003002c88e409074101e00d42402800c69182e00b01c1c10300d6448100030151405100f0500120320b00c0700b20712901205000c00105041003d00c0c14100749541c3c0c02e41104c249000a04189000500c020000102e42d4072003a41c00c0550701d003607407105c103440c03841c2c00c5001034454403640c03603 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 442235080 1250 442233830 442233839
    0xf050c031b060906040b04080d1d070e0901150504050705090a0902070309053f010603080309062503022b0e0607030b0a06080a020c0d0503100e010303051210 69
    0x144000c1c0500084014144007040a0400c8145400001041c2c1c18003a80180184000b0807114200e07280d115030702c115081c0d41c88035030982c004090324090321070082003000d0000140c801e01022400005032140030960304069918071900b2400d032001422010140c046905080c081030034160006d5030301a42e9400c1c00da00d0119258089505004c5650002c0480d640c04a240c0040590041c5020300501c0c04580104e401d108048e00140045804c00200b010a040b41850000c10b40d0402c900103960008a002007050320398a04040307003543c2c0100e411811900814001403404589540d10680c10214800c181d0f40100d50094154001d43c0001c64200d000c0103401100c0a188400380b03004242d17040310600102e907c810320900a45003030320103042e160070300d0b0410340407229603101e01202d0000c41c1e01500d81415181c9410045200038840c3e0b07051900c075070103400950008241c0000c000c5025460907414848403d46ea01182082000c0070301005000420400c40840c2400440da502600310201152544116548 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 442236330 1250 442235080 442235083
    0xd091109160e010206070e0f03010b04050907030606080f031b07031b150e0907051b0d020f12030108071802160506011406030903040306021b0a0c0e0a0b0a060f050c 72
    0xc60303808040100390a40c040c1c0c1d00d540000002002142800207005070305200b0000741010480780c0106005584050100c4803556094104440e40040500308218501340200a1034503038a00740406c1d15460b00b4003000041c10f5030001151000300c10740c000654200520b1184102051585260030401d034468901c003c0046a5000e42e040c1d1340028201c01c00104030b00d00194419480d512045c403200b4007009001000711a1109000b141d80000e103450020303070f620040f2402c80000003035001800701c40d00c13402400380001900018803c0c3d40715500302c04c803901c0d01031402d5002c200e440309010b03551150300406000c0008038142909034031180400309000d030820314a928640c40000e000300d0192800d5110000400c0781640110754080401015a207481c614604181803542d01c0c8a80d1100400090f80000c03000c24885148403920108082c150964100c11414101003040e8840f41c012491001100c2c004030308a81164454511005000fa0510160603d01581903e40208440703107441809810484040401d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 442237580 1250 442236330 442236349
    0x90d140102030708071806030507050432092a0c06070f09090603080711040e0a06050415060e04170415050301080c060309030423040204260c01050d0911 67
    0x61100016164076042030000e1070480040c0c0720106002081011800e010301e80320301d810988000d41070214040c0c0340c082080300c10307118903030003019603260302c5d00d0004c2480f642450108044140d030b600c10300c06803805400c2000d0141c060340c074491b42540d9041640c2004001c4214075003d441850001820046040308a5007403140444201000504095003980c032250000c40d01d0307010304104001004464110340e240c500340d1046074800b8107128441140c0384034541d81c0350018161120141c06580e035503031032440c01e43d000e01003e8904540581341c04d100b1070800e9050744030302c1d003c407020003601c40c07510303212900c8019400c2c1d5480603480d5092010000850311410140380c0321074981c4641d60b61590780d0700d864001420503030130384113042c400c0c00204140800d8001c0002603e0030b50380781c1840c031603c40c00320a81e40d88104400d980104d400c41d00102d000101c412201800d5014407069030b1b1407110001c0310742d60141d216000c034106540460014440c803040304409900645d001c511540190010500030400501d2402 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 442238830 1250 442237580 442237613
    0x914060d0f1d03041a0d021908010e060d020907030209150a0905120307081902070929030d020318011211070515090606040207080919090b0a050f06090d 67
    0x1500c900d1442502c900d4900c120b032003951141c0146042c00d0510b980244684c81c044021100e80c0c01c0403507940b0000d140b03030381107400d00c0b003a00c1342c030786ca03104804603024105180034460358140b1540c102c0080e085007400b0b0b12480d5800d90080640c1c80d15550038000307400030741141c9421030300000098120201c0318031807801410741c8107581c1c4540020078641010400e8140d1481703d4007096030024085007002440000c161a0124036801c11415031a0005004a1800c9036a5015410321810110707100c3c1c07000341c0d40f42c07003061030203040e8604a000043c4409142e030f11001070f800b00700140d01c10805240000d11781440000c000b04149454030180e1041e010001c15102403141200d1895000030b03103807080040c1000781000c448800e030403134105440d200e40300c180c5864000f80f0407402a500010180304001c0040c04464603802d00030000c003041807010b1800c6000c40e07040e000750150b01d131604080401b10b00c1d05103070040c02c5a80040c1203c0400004100348881a044050100c0c0c1019012202d00c000491540c804000c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 442240080 1250 442238830 442238861
    0xf0e030315030109020d0308093a0c050a060c090810060e092406120d0801030309090605030c060702030f03030406090201021e030a1107121a010602030a0914060d 71
    0x70309019450020303258000965501c030341c0c580b00f082030041e00c030707010f800c00d501d505820011210741d516403000d0304082204034100c0001d140040e400310344905510100500d04105414402411007800c81960749813030325400038096500010ba40000a102d5411003004007180d40742040307030250f842c0d880f28a03051000361441c0b60306d5120f61050004000700510b1aa00c0a0b0020051104101d90f060300940703410720000c4800d030054180c000507629140c8244c5084c21940b0b090490311040c0701008010501d00f002e000481c002004480300190080c0f01d80214025a00010040c200040508040040300d90040c1d204903090702542d01d8641506d6824005944614080c40f4003060004d190b100080c14070505200007a12001c1e90182d514440400000752840540075080c40b08421800c800e80501d007040d40e82c0482c0781105000c4a040401030080c000b0440964048024400f0340d80302d010513a140d001304560f80e4001a6860301c10003000080700900b200850000c1c1c8540c1ca07000a42e81d4100c2518803881a0b074090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 442241330 1250 442240080 442240087
    0x503150402190305090c0609090429040f03200d0c050c04060b030103060b0901140d030201090209070207080f01060e0601180306020f190207140f0a210302120414060c010f0e03 77
    0x2490144050304880f0707002c4a00c01c0c6044170000003c3d0300008050009002042f440c4401c070010211100c00000403000a25014000d10b01407030b1054040c1b641c268110001480c05403e401d40103d41598404031600e4800982452040a80116054040484142c3d40c3d40300303154141c07180703444a10400b00030781403081d41c0a0b62581942803080175141c0041200d030203141c0b008010046042050030008002c0d10490712060701c00703101e040c102d02512240c1000b0798440084018420075540001e0810b0071241d100050f0f80034001c0e0641030b00e0885c0c0d228404d402940d0003140006107990311580481d90202480b000410200352203841c0d1504036004811042c094410000e54080c10615050601586075120f100822800d0b00703000002c0003801e80da0f2103950003050540482c14450f664051400d0140111076020035680240310a00c0e841800b2002003600540920200352809881010481d41552051140e01c502c0e40a00c0707003400050b07440b0002101035551389402e400c4140a0318012105034504040040d40c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 442242580 1250 442241330 442241341
    0x5091c1b1b060e01080a0504020d0b010e190b030c2806030506040e1c031107170702121504020d0804051905100302071e0f02120a05010b090105010503150402190305 72
    0x14900102d0304a8002c0c00320300549100540e80c4405016407240301c01d003002c5010b448070700c0407031031400a00074014501d2881000200b00030701c1420a0500c1504604601d41070050300450200441d040c03080d07a81c1c2c054010300720301081c90500a185150003490705429440c0641e44841c02c1344580415004240065200d1060081c50f180a001d21040c0700145000341802c402a541c642d075221020320b0b168000c0c5511802c80c001211200c1c000d850b04650801905c42c80d84201c16a108480c1d84104c104a1160249000e40002d00e000041d0940d951078164040b00c5041d00e458080100c840c503800d80840d81c3ca0410400030410b41c581900f4240d641c0052940405c0441c02e040400048090f602c8030b88082500c140301070300c00302d5078008080e11030905094516001c940c95041c410350407040c40c000690020411181d810590f640003a00819142c00f444c001c210210841c4208549a0000e00c00d86002460600101d1016840b4081041185e400140010b01d840030803064007140250314010540481c0d558001c102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 442243830 1250 442242580 442242623
    0x14040506180306090c213004080a140d050307030504050a0c030809040c030b01120911060f030f0109020a0518030f0609070905090304120b1b130501030c020105091c1b 73
    0x40c40c114402c040850815840d00841d9614005414088a03072940d00400c1508503c1120b050482400915031040d695910740b8107032038ad1460610012116002c002400540f0f50300302160a8803031180c41d544a62850721565401c03006801c020340207480a0048031175100011789a409040002c41c803460000d500d44200300100000c6039500c080f503400307150500d000c2e2062a07070700c0070300074084e01c03802140080c5654071810940c2c8241018060140c015a00184040ca60002000698480c6242e0105941181e89a071210b40507405a0030842010030b50502c0f04e1010254101d05600c0402000703400c441d0100b20710345940f0315001e03050b00d628400b9084808240084612805002e5200300e04100442c80c3c2883c3c41c507144000901c0c020301600145407a0041200c0312540441000b98004030b0220700d0b02ca035003651000c1c03100811886031a010074a80300c07a0015060042c00b0b49031240600c240075040c8c00c0b908056101d0001c8412051000700304100030845281c011006551601d41e01592140728441840410750303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 442245080 1250 442243830 442243849
    0xf021002010c081317030708220b04030318050d030c0f0c050c09090f03030702160608040f080f07060212010905010e0108071e03060212040209060114040506180306090c 74
    0x4045905140c44998999080540540c0101149100c440b5600130780c180142074120030500080300324000818001c3e010303403166003c0d000741621464075180100c1c0da0440d403507100710114001c1c50600340d0400039021074040d52014030380c14503500e455082040c480e59624105980000414042640e9031120302626078410380d0382d102d00109003401e002500b07950311019522580801002c2c49000360343c0005040f02020301c103030010440100126512800c081c4800303912603900300c2c1809404045c1107030009050384501c40ea28000d68120001071052078090f1109174465210040c03407181038508100740000106e0b184010b1102c001440c0e180415541050105019210103034000c40b560880307040180002800440c0c14004c4804146900c1e001e4000c8507000c03501c583c125400030300700c0741c80442d04e500840d08100201d44164400c960f03840c5141e07034000054403a01c00318081241d04050601c814015030410900616600c030a9000709500d03110341c400005e1a001c002c4600034850340100103001c0b0f2a081c00c0707020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 442246330 1250 442245080 442245109
    0x120709030b060a060c0f020102070f031a07050a0f030b01091805010807062d02011503050a050d110c01050306030109140f0106140603041e0210030204080601051203030408030415090f02 81
    0x3e1030442841d14a0003424a0702d404d0001d425040c1c009500021a80204001001040003820b0304030070130b6803410181c0401300d40005100804043c1d60015082a1143d01210302442e0140c5172070722603103000341c422001001020030700c038140702e001c40011400030907103074a441e51203142d00d10202c2c8560600c10764905011040e4011818004603101c40c078113158940c04841d040e4a2049540a000080c1402c00c902402030b000c1c110a5a0140070408824000c0121314081902d000b10100e803e0300b00d90035801c07501c80d640740011000c250001c042c0002250320943c001c68102070024004a200c40f2903440e02180d0a64000a000540c0d11038000031407019820b025a40c01400340303401a01e80350b10803030041482840014002020070100c1c02d9022520f5059141074100c5039005048401c403609401e402400070b6215000d038640501c030312000001c0324902910504400301c2030501450840e00c65907600030150f000907004035002c68030714044c0d0071100c0003403151341c0244e401130820240300340040c010302c10004842c052 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 442247580 1250 442246330 442246339
    0x2130216030212130e15040c11011b0f1d030303070f140301050f0607030c2a0b0c1b130c030212130b04030f0203071e03020717070911120709030b06 65
    0x10a14035210b44e030b1550300031103907550000b00c5145e48442d01c64140d2400170414603446417400000b801455441180d820424129030700170005803031203039519a00200300300c0703d460015041082824004e4400c0c81c14106c01c8a001841c21850300e10000080c0c1150821680c14000490242a0118060340310000c100550000d6211500d50b504240121360070f52001c10101c0e01070000050001c0c1018803482103a850f0070340040d42d0f080514210340208a5a111003030354a40030132590440410041600d000300c0d46001003a800a05640307028503800c2c5080147c85a80030f03801030391015100400411800340c0e0008804581e0016510501d4005a2188040c080e080d204201042000300000560049040d03070055098146568052081c0c20200d1a5101c0e24a00804510007080c904000385801080030b40383c14440c5d026520150388501c10f000d00b0751602e8a00042c150305c280c0040000350255846030b1215280382034118540000c01c0c0d00342e001030505451010010f58810010030911109009194000c2001c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 442248830 1250 442247580 442247587
    0x30c030712020405071107050103091406041a100503030d0b032104030b130302150c0d06030606050310050408042c0906060301200405060d1503030f030e160308030402130216030212 79
    0x48201f65105500e0003500d0606640d480a2010300074621080c0008601d41d80448540c3c3c0340524004091151081c803080d0801d03400c00c040350303126004480e031000b038400140c000e504150340c40c0c10f1007000d84020fa402d10342500918142e20f85540c042d107045010100a06841030707485280d40f90101c1265001405086101151842080041d40c003003501180580c9600000e001074449014403a8184164109083c0746442c0907400000c004554110104442c070441c11348001c002421b00a9003a541c00316070040c50000104401e01c40075604090b1881a102d0441442000d001c00c810404200301c000e41e820710040e80040d0400615113402d01440c0e50386030504605002d04030b440140c1c030242c4e02036030107120b10450b00801c4041e0b0b00d0400d0360000d004c21120041d40300501e903807410040c010503d01004a0006410709a07144141100040e42500b004419002800b50600c0c61f00c9100d565040980304983c02441d80e02c45001c0101c60340090039581e0354069140f8039410051401038545406280100da6071141030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 442250080 1250 442248830 442248857
    0x7020c0901090c1101050901060305160b04210812090f0a020916050702040f020703080f10050402090105090405070f0215091509030f040603090303050f0f060f030c03071202040507 79
    0x100d845904403a00e001d80868010600902a0740c2480c14500ca8100e56181404000244605400200480740110705540c7d00382c1c45400100c80c103218038000c0c043e03080d101b00403c0101d03500306800d030700e01044240d03003107001503549984940c49580315285080507003081000744070900c83c0521403007403030000307810081011254680c085040580018010078403044200c602c100300e14022021030340c074660b00800030000031000c240f29a009400240064000481c0000005e50141640710001d006074016000040890318000401020754400348020341004401d005040464540e0b000c0e50b401101283c0b0f17040705004801000074540030710031000c030b1521a06001448a0307083d0201e403505030700f125201300c03484c15a43c4d00c01c010300d1340c42401c000900352400085e000071125410780c8074144d514840d0f0360a001030303182c40350824803442040c0c5008011250040100e501840d00d0043e0414400c00541aa080380b1000790000381084640d6006002c40c81640d8066000c61601e0b110320780d0b1000040c1010302030315102c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 442251330 1250 442250080 442250089
    0x23060f04030f0c050604150605010c080702100525020f03030f03010e0c04080a08040504050a1b120e160315020a0206180307060e101a010e0d1104020a0f020607020c 72
    0x1810141c140101c07095072103901481041c40e010389507000700444205003414075040310390007400110480440d280c8900418191300c110151558903401a81c440d080160503001c0017040c400c004110010700a04000d905020b0356030f040003240c40043c0340d10102031400135005100587c00c0d0804150301ca90070810400d0b9501100740240c034155004480840600d40d82c01c0500c0c201442141c2094001d03100d41d01100080011a00042c801c5e0b80064038148060b403940503064003980c56480c104c202401b48049803581143c401c1200500d00d14283d200130800f00701c400551030402882d002820046d5045100500500a14000800c2c9100c51038200b1032a0206a12000b0345424024001250780540c0c201004c20403082007054908080c0c000720104400302200b0030300b030b9547c000d1030701d000c1d2241d0034001c2d43c51030ba0703022111800c114041030b120340000c0e08280c420000c1c0000100411101c2401360364000844e03403914801707401c4801e00da8990b0604200c80ca80c0c060f141c1100280040110740c04070451005540381c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 442252580 1250 442251330 442251361
    0x10b031306050405030912030a0e01021207120903060f0207030e06120402120a0605070801030b070f0504050f0d0606030303061d0106050403080c03070b2a0f04060f020f0304032306 79
    0x2005240040c2c65100d524005056210f60440c403580440700c4008560014404001001c6941154480e96103100c0141c0041e038452080301c04001c440d05c0140b20440108040c400480c040245a00d0305803551a01c070760b5010100e41c1100101e90680e5404681c8900700743c0c002001e004421811900c036400c000506000b1400c0d80d500500080c00707061801d003000c0d04d4080801c142002694820f0040c001c0d850301100c000c0c6180824881610890001c50104511a020780a0560103040c0ca42e038040c680703428801401808090240e1054000c1110a8442c0100b0600d21425015620995001c40c6151905450204900c134041490411b80780701da004009485d0003008031000c495010300034030b40301c0444041d0702c1d06500a449002c0c2c07084400f00704003c109481a01c0c840003400e0380d01a003460009000040a186010301240c42c0301d01352003000306000040c0030707245400c1c1403480c2e03104945801040c0c244060954010303900403a024040f810605034126002c030b0f60080d4101080000301780c24034010107809409074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 442253830 1250 442252580 442252583
    0x302131403070e1e07030e0c04051504050a0f0b1c0308060a080d111b0f060d09200a15050d11130806040b160903030f180b07030305010b0313 62
    0x4920845a106440c1484407074001d2003000c015603280d1130000812070035041c0300c800f410741518040b00001d503904d000c0c0c800c0902c0892504010412119800103120003040058084001c175031420860b8200d44c0d8031406214072401c8045004181c00c000c04881c0000d507074810400324402c11459050700007501140c0400a0b030f0581500d01081c107500d80030040740c00d010080d00f0254440c0200c2403840c05d5160004441843c4000360300464030440710120001c484078600f030000a80c000c001c03010359401c5240510140c08642551074000a40510359900e100b0302040c0c82204152100c030340044402e2901c1c20320769042c003c0403000104544541602c030f00070b2031031140c40c0e401d14009a4030001165603210840c00e94840d0406a1007520300f942e110f17207080d9907a4500300c45c112200060b1000044d2402a00a0810511112910fa400c40b09040d5503007520031021f6980030004100e02c40714500c142455840160008103441a401070303840702c480c00c00905992050b007004001660400600c252600030920032000103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 442255080 1250 442253830 442253849
    0xf020a080307180b0a0f0503010b04030f02040b0a030b1008010c080a050a060b0d0f110f0324090f0403201903110303010308090901080d02060a0c0e03060703050106020d030213 77
    0xb55500701003a034501d5480203140105207003410002c40c0042c40200203214101050300c445e04410a81281114180710901900c101c0c1c10050000700002040f012150074503610040000c1200055400400c40b244900d80c02642d01c4450071040c000c0360725980d818a805480300000030b1280c1411a14060a10700c8050300c1290034944d0b50300003614019903a4400380261100f0f8a403039694000f09503250000c0c180d911384044c5403034503152494130b5604481045404c21840901002d0451342c1c0c12180c4080c1a4050f044030004000000480500c0e5442e0000700b1b01c01c03440c1d1640c85013070b801c041c00c0c0280034a01c41a10f00002035611041c3c15421a80094074403001c1d40b548040c070407881010324040343d0310403003075804200300c0c40088004000c0000c641c0161603610001da0b420202d680e40d8400081d614000d801076034000da0005004541065029000b00d141422a03003480030540311507101082c80d021f8221261800281c1d180b0050040e25414841809034030800d00d0154101868070000c0d0341500d04520424804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 442256330 1250 442255080 442255087
    0xc010510150c1e0b0108030c0c0a032112060605071101030509070506091206090a050d05040b040501080606040e09010e010c0c02090609090f0703030309111e12011d010b100f020a08 79
    0x20024401000d01201e138031140c3c810003569200034542e40c81e04140c14480150040e001001124107000d12010201c4c0c3e04070103214951f800d600416445040d111441d0010030454083c210019003e0780110001002c456a906555000609008041c2d0340e40000e401d04050416003070040406002070343c03405441c007c0350056540c0b0001c50000d221098640c03103407211401944100071211001050744403840b4007030019100d03100f90405007151a07104600078003c2c1d181d010301007404654420b086603079001d0030180c401494940c403030340c80e07101c805e00440305d68910741c3d100da9403400344001c02c0c0203515484646007884030641d5540da00160100500a2281e40500140c01c000f81c0e106000f0400501c1115440040d68101912414001c01605406d2010740341200340c5c00c518056410207043e078100e4110141041c90300fa940e00750801c002060404209c2c0c0f419900e500b02c00140c1c44a0440d4042003200d58800016100c0310002406108540e07100c032003040c804020b94074050b50750003040c0342d02e81a030b200c148550b4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 442257580 1250 442256330 442256363
    0x120e1c1707211e170901020a051804060504090b3301140403060516031a0a03031b021003140f04030c02010f1403040c14040b060a0f090b0c010510150c 66
    0x1032201c0101a03c4141450546011925070742102d1240386070005180400d40c5943c3c0e50a0040c01d038403a0200410018104004c4444442c86c512001c0c03c10200c020701c046101590b5200040503a04604800c0d10744205d80300a10268804141030419005c001d01d098014040081d040f0182da040309404040c188a4030710024003080d41c0d0602114007a40c1d101900704002d013001c0100400810070b4041b461b020a20b840440c1026103412508880c40a000511925400b030541d40c040b40d02d10403800c00c010003104900c1d14034006a6030842284150702d200e43d030018058600b450078045800001e80301e00700b1049400244000300c1c1e40110440780160b028200b06280158040d4101d51900d041c03207074515081c00120078070003002001c140c11030880e20f100c110700c4040314003602040300321206080301c0b82d03004408104002c2d0450080242021010050034604465551813022030442d51101c680c14055941d00c0081188540340000103801900c40b640c120100c080450b4030180c540c540c030700009880c16400f004d80c2d01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 442258830 1250 442257580 442257587
    0x3090e072c06210912072102031c02090102010c050310030b091e0d09090e0604060c09050406080307050d0503040b060402132310020a0f120e1c170721 66
    0x80340c000d202403107000c0340d07143c0082c414006102600d4140d0b1900410008108035117088040d10a0719070051114107440f01c000c89440c10802c0118041d6096000921800100d00204598901145081900585d8480c1c624000a00f16001d40d5940e80030311109206210360130240c4240141500d0b8030500001450b00d800034114900402c03072242206151450715007140000022032848155185605d0712020503848614020a8a81e09032205c4015444080040c020070f529800c601c052404a040c0008100d40300c60201303050381c0858000c0e4080e07a10008448080140801c40940b15411a1901c542941020340d109003000701d014045a00c16600801d00202a030b000290308001405524800344201a0020000d125000a90f103414402c413403200e50901064004244402c501e60701c5440e802c103141c000c2c0d48560003030f80804d0043c002c10410f848098040e0300e807601000404201540041040d02071840d003910701c0c81504842c00d0318420f0a221003400a4084540c141c1c110060005000001c0348421044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 442260080 1250 442258830 442258837
    0x80f0a020f16051903200f0a060207050310140106230a08040b0f150405090a170417010b0105070b040f0618030207050f010c140307050a03090e072c06 66
    0x545490140310721051842070050070b81d004a81c0c098075014801000001c041900c46003034400036060019100c0c080c40401040101072400400051040881440b40000f20704800c03002e4000001503480120b00707102c07514042055070203c0780c0c0484e081c4070100540c14180d070700100601c0f4480912014904078911004039894004bc0c0000c6d54507040c2d00e408840d40300400460303003038a080c0d90006584010401c11011002c4441c4550440d8041c001205001c5003031000a01004192585034028020001d0004da075003195050041d40241c411a15141803801845c031005128825400c1685040362170301080e40c1100607268400d40180034401c0329a0340741003c0500803122140180324901c3c240701060380c50105101400c03900d011341d00702c40c80c1e142c9410500074040c0708203e20b40d0104035002d01d2000010764100201164055034002e03a03040044956a41c1d141c40c2c00302c002100031070102d0340140b0192104030300c178a40c005901e241c40355038000504c411300035094543c0b001d01044803008204d00010f48907032044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 442261330 1250 442260080 442260103
    0x206060f150d060b13050f030f070b160215122d0403110609030a1d09040605180d03060317130603050a091a01030506010e0f0a020904091527080f0a02 66
    0x1030741da80c0c503510500c07176401c5540d5000c5d0600c01d050154a008507800d001404a20080c0d05500500541d828a201310100746c100800340c1c045d0404002c4c8820068540c018150909110045901e45825202c03c5101d03038008001e00344609404220742c00340454452250440c03500300014080301064850b4181140c59800440044060b841850300780303c60308100000806403013409545a1030b01030b40713204c000c0803c1003403507450a51180c80701010501140195014940183d100030b01c4011054049218506004030421100e000c240e59980802c24849050302d203400070f90344508440e140c038a0314a130b0304400580f0381c05550201a40c850004160761001c1d0310040c041604800e45170848688841c15080c903907000d000c11107041c0615030000480c0c4c00c0580405000d00241207400c40c8075658601100000c0d00104440b6900648464503000404e00d195001c0e07101405811001c9202c00c200b034050300403041c050440c5001c041d41e401032000828502c601360f4640404804a50303035541004c0d40100e1401513050078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 442262580 1250 442261330 442261349
    0x30b0a120b0115020d051b0a020d030c05060a1b120b030a05010501080d0804021c0606050411030601110c030a060b180123040207030f050703121109010206060f150d06 73
    0x10304400d024140c248141200c0c031441c400baa06400d00d4101326120300001844d50040b44090140c1d1110340c500c00c41400502c4061022214400340c1d503000100030b07011541c4103801144041c410700c81405018841a680550241024851218180d01d40c141d801841001d200402c07040d0b14085250711815000700ca80707903000904860125955081c014002d120030705c60803815200b00c0b51a084003d0064600d2880b0325002041d44030000d0403000c280d0a140c000d804215a40342d910030000c80d0aa80d640b1415024803001d101458032032800500141501e906c80388d030f19045903c0b214504c4034076170f00001c00e040d031564484000301d070a0320b02c000030460507400c084000b0b088048207000400d90001c141c1d072540c4c0342c505040340007200080d0007040c0307c00c038810a000600003071424655a00414000d90003800514800c1c07401d1144071501c0030000c400c40b1502e42281214840c0050307507030440d41c0d04022103070b002102214400740d003401400004103a60310360b4840c8502c11074081507640d441d010961005006088031705 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 442263830 1250 442262580 442262609
    0x515010e1807030c020105180309060304030e0a060c0b06090105090a0216150207170a0c03200a2004110406030b180f2710050c0f0c070603062103030b0a 67
    0x46014000c4d11a0b219403a00643c41c00000a024010020080042d4030180c40a10714107440b00e420710032258001001541407081c0250001480d0301c035004a8001040c80381c2d0360034003120191820b40c0301308070003405d06d6204c0e1042d030380140100e54a0718201500040000b1005a60780c4442009443c0c1811a000240c0a03480302408001c0d01c400c150010403100c2d100e28603995503442546200c10070390050b68060400615074010396800603004120000c281820324809500020000300524a0454124011280340c1480300c820520864024000e00c4096400c84d0b052000000544040225010780c1c80b9a808250320703540b8058480c0c680f40c8415203510b41280c40005030749010840700003000c00666020152660400820000d101c0fc09005040d544d081d84c0909a0304403004110000b9140c054154091448108141a001c1106c1d4004010301d50308003024103407140c9008030240484070300743e0018280d2210100003c007403003401c0d10956003095044c100051003106180c0880d5103402507420403130700e002d0980c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 442265080 1250 442263830 442263841
    0xf030a17090c130f0510050f03070605090904021804060603060612170d0209090a1401061d01030b01020f161401030902030604030f140307030f050601180b03060316060804060b01030515010e18 84
    0x91070a0041e40d0060700c0c0d2100000c2423805042c1c3d9203405203d0480068401e020031089468094843c0383c102d130004190180705441036251284d542803c3c1e0303007150540d036204000c00410801d40038940040c01d0f11400c2811401c0b9a40780d0700c005103440103203883e4050000401d02441001581600c11242010300034003501e281a201c00d000070400b0341d003d008440700c210300000308944074204001c60101c00714001c01240c880c000055010345144d4810b1410f5001d5a0310300000708608001c9001103000000c14070411034544004000d030852605070780b60425050007401000f5807400500c3c190003c0e403500e031240d0024030343c0030304076405000c00300e0f10800b000c03001003070018455054101c0026090140420052790b1500c60054a140141016a070010b00048508009070003900c0040c681c08000601524000e8612000b42940107030070340c20007008141e05034284401d0040b2440b44100b520401c5c01c3c100080d01f07000c520061780159110a180c10080320004184003a20745480d200111382007040542d5840c100f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 442266187 1107 442265080 442265101
    0x40c0914040e010509010209120a21050c07060e090f190f140f0f010909080f090f030a11180c070809120f030a17090c130f05 55
    0x7030399040c5041c2c204280640c0f40300d462030000042e40c49041740c0420880a200340410b065503880182c1c0c2c50b000603c0b0280350360392035550910149400c82c1410b011100e42c864403484403000e000d03006000030300303e030041c00d000c45200f8100d880070010303030b144008030500b040e04460400c014490100700c0713080803003103600c428840450000003040c0303071200000c2040d401000381c810708150324a03102006000000b01c03076461f000d00203c5c6400c1c0300c000c00365101c4860703034042d11804104409001072058070f0f690300c0d10340d117801001c8040e094034001a010f09100c0a4031641d0300d0b402c0e015100f4092500003800711061050b00c00c00140003080d0405000341c03520b20598101e501e029810840b101802c1d0207024042004103440c05129004503a1050030000041413601a010307054003038101182403000b04880402c00c07204c801000d0b02d5480c0c08002d400f410b5000b84c42d0010659200501d04414041100714 = true := by decide +kernel

theorem cover : BRFrame.Cov 442086330 442266187 := by
  have h0 := BRFrame.cov_init 442086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 442086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 442086330 ≤ n) (h2 : n < 442266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
