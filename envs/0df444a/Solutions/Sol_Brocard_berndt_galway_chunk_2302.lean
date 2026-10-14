-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:17:48.353577+00:00
-- url     : https://prove2.me/submissions/7eab7881-507c-4d47-8588-c9c0d3fc4a58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 413848920 ≤ n < 414028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 413850170 1250 413848920 413848943
    0x5060c0a0b07090609300c152a050a080d0209041118150f0310090f0608070506040b2218090510290f0402070f0224030708060307030f 59
    0x7541d005031343c08004100080e1040b408840009000303002c40e54945000204e83c280031101b40034000c00441020262444414103583c0d142c1458001e82030070900444a0030b842c4240e1380300a001c503804080101c1d03868000025003c810807545e903148441e840000c81a1700075074203103e80405500c41d88110442c41c1c0d4007504075030341c618400d5001460b05001138125445004d801c0340d054052003080055800500101002c03985030344403030801010b000c409030000d81701039140c9407030008030036125007006003162040800e85004035102c2d424005075100c3c502800020701c1301040303a440c908040c103442c0209100810480514140c03211010140140c0c0303c48003640c05525046110113204003071204000c198260740c2d040000c1c0550700c00d120900c0078115901820b4407003982c0250466122181682a5424024400c40d07940185241403540c034005400242d01415170580700c52805a4403084c05400007086030352450460b41c420400303c80002004001d26098080c0c8000000003c400c00c40c42c030300c02403148028401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 413851420 1250 413850170 413850179
    0x120c120905030d060f2601020913140702010204080a0206130b032707030f02040c090e0a021e090a0e09030f0d020c1605100c0204060e070801051c0b0105060c0a0b0709 73
    0x103662568214200588940ca01000561b8555000c100ca49007802c00e20038030716030130402d070500a01992070400e0b00113402080d8100725440580c001c462100491001da1100c3e115108124201d000742e0103500c0d016445806240058a4000d001d488542440c6c4c084035640ca46617502404075030803d1303c42116152307051110316400802e40f50003000400c006401000602c0c5143c4800c986240003c0000c4d016070750300d03c101a4014410307600705000d046945030082860410303d0b000c40096000a8030b10816240c00c90104002145800032900002802001e11b144141842c0c210303903109501a0a1440c03d2008011a88100e003242d800340400c02c207074440040e103811b030003e60781d41000da0300440599a46100c41050009540e00701c520034081d485481e003901455020303c04038001b04529007004000580032410042c900f0350121000f03060300c405449079203a040c11032810032b00300e200380140100844a00c40040c0040e00b402070140101c2d00d503190840301d0443c20b0b41c54175124028159120400030782d06000501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 413852670 1250 413851420 413851447
    0x102090d030e120a02010c080d1b0e0a0603051504051e07050904050f060108071b080715060b040b030f040f080706091205070c090c0e0306011e090c120c12090503 71
    0x181d41c04031407004c4c0854003041c0e80000c0c81d44ca6505d2000340074400214101c80680c4441d404101001e10752168841000d10f07005018164080a4254611079901d1041c04180d203486401543e020b00a030100041a0a1a8004000c05403000031b08601c2114070440c14811000c01000c2c0701d41c0103044607116543d48000c1070080c88140e45d03005140720345001815040c820580d910003040b0345d0103480c07450402e621261101f10080307041d0305c8000141c80f41d40040b449505005003000444503150010714104001c03503445013005450b009511a54510070000d00c0000e01c0c940302d1401c2140d02c1440b4805020340c1600e40d07078071f03090544c00c003000a440c15035440b10031004001800d4840742820001342009400c0100540e42c030414500c05008a0082c5030b01c5001070040a03001e0a640c69244400809456503036845004400c0340d0944e41c41025403580c101200014001c0b04e521901c0745010031661010051094518110064000c000b80c0004029003880400002c103650303c140691584500d0103503580d140b0310813664 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 413853920 1250 413852670 413852689
    0x90e060a09050606130e03070309090501120201020a030f0203161a01080303060a0303030b120703051506041103010b0315060a21060e06010c080d14010501030e010b01050d0e0102090d030e 82
    0x202015207400d15907000b240d400103400360b1040c02182c800b54448122008040030306000d014100151101141342000c05404c200c4900030342d8550340c010031150f030742c0700305001d22403104210290140e008411004086031080000c2840310f03544d03004603494500020000c0c0c0b80c4e0011a181503541c5000140c5030719032030200c06411801048040001d42c1142407283c000794000e903181c80000c0602d681d6512150b01ca46a0079100030312441c000090303030405540ca0802907201c50882440d8a00d5080345800601c06190910400c140c0e056035828440c1181e081071004960350780090505400d20710750070488d9440750390302d0700244213441496462805048151003403403031840c0380030a1850300c40d091200911030b1603031890300b844d8005000d113400b06211840b42880025485a5450a0b01850600c06c41c0303441c44403541c2140d07040317030b6085c1c0c0d081128200c503014285c03c0782d42000c400c5000440c100807161072041550041140c107510f000005191070544000160014210030045010a000902e1800c5030300d04002a07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 413855170 1250 413853920 413853931
    0x90c16060218090106050427051312020304060f0f20100b012109032d0e03060f07030c020f0f250803162d26030c070303020f04090e06 59
    0x75955a5040c045c000d4101d000301c5c0641c554200c0e1500300c9442590119040e440c001d02100b00800c154100301074103416079000c168060300c1c602150054001594800411901203d4443c0d41e115810700b0052170454001d81d011244000300992280f601070020310090015660310180c3e401880d105405848280c00c0d240e260010f90306004a200c0078101100982d1400c2c1420003080c1d4000410b4500b0b072a050324459031480c0700301d8680c901c5040c1380c8612521001d0302d0030386071059201e00d540c00c1350980405944e0201203c0179030b0388564800c082140c00d40a900283c0134401c403401902d5800b800d18040c14603010801051105541c01284d1081140c00c50042c103114100591002450031400e04006d00d503a032040032103c5144480340d503401028029400031444000c420440c24400c0601c40c500d0019080066507003c0c2c50311700c2c06840301020b84208801495010412440003821651001d418400c00e400c144c805805154080001440c150764640003040a0300200c1d6000038030280c0c44154514043c030042c103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 413856420 1250 413855170 413855179
    0x101706042303160204060b040909030e0d120305060310090302060610090605220f180c030e0c0f0406080d050a020706030b012001060b0301170105060901060c02090c16060218 76
    0x1c0000140200c00c64075036401d0a4a29074450210f440450300401142d48944035039107020602082001c0141c201c076541900030f60b11500c82081c1c1600300700240a1545000b40390030031110f00300c1c13845030284c0c100580c80540142501d8012107844002800d0b9501944200c0042e000501000198230702840e403910403611502d004800d25040c4000a041e51041d88401c2c0e0512115813909000303003d1404811000c2c14071313100e20b01c4e402c0341d83e80440380007101c070501c13069405e5081070211640b45110b88515164010b00750010b0031403650b85824042004020100190400e88803440410714450400c0844180b0100d0b503950f66603002c1415009081500079004502054140442c00383d56a074804901c1c141c040004010320000310703003001c0e042e00400f502d500030038000c2c002000025030710b40400412a40003c0301d100920003692801e04100c4098402d00481e40407802e4211243c0246c1400c0e0306560b4030a5211082d00c1c07030324402d8600209460310000080380c4480c1c000500030300c07007110013082c4e03441e880007500c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 413857670 1250 413856420 413856473
    0x5090c04081506210a0c0f03150e0705100e030105100503120708121e0103080a090f080622170306040615090603020c0a0f0f0b010e010303050f0310170604 68
    0x104110844413030800c0442c40401c48080c103143c18031040700210391040031892120755a5400380740e04080d610013074603907090140c400c0050314454084c5000c0344c490071014101090400d010403150000c101c4413181080081a16070031151070900c50329000f440c80606000c1028500780c10186003805d0608035101000041c405180007410300e4040e00c0c0f280d650034501c0801c80e518800040741c66503141c1400210600c024000000740400d000050900c0e801590300c2da81d105840e030b0060a20040c0790300c01c01915a01150000300c061901c0000c44d1071070f04041408011014164907011491048000c0e01007040c0000130601c40070340341c02e21512000b004178526018081e9000c0c400035200849070301c2010b05054000645d480c85c200b082c0710003403402d030703202c2c8601c2481c4449050601d26800c2c000e0040b9110031194002042c235529951966048a17230564a0a1401d00c0d008002c0e030141c2c00113882200380c514104400702c1c00140694000b501584000c00420f55032a01c0d040c450040d41d40910420799845101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 413858920 1250 413857670 413857681
    0x9010513024c051c090206190f090501090501050f0a090e040308070e011d13110d2004050303030109020913380a0e1005041d0c0108060a0909020a05090c040815 70
    0x4a02c0b8110b2a41d522000142c5c02c5860012812910a032225800e004606100c000034035030b085034041540c845503540d0519810386450043d2445105070040d1804100e09203c00b00402440100800c00e000320b84c6040700c0e103035950300c500382840d2900392012008105500108121140c1c4220404a17000c0c092a048150b400104034442000171a150480e02410103039103a05009209600005241c05942c50440d40d06c0d01d24030100d2009201040c0b0907005401e403240d62520305202c4009940c15160010091451640b0704200440258450204640c000140c0385188500c41a44c3c49001c06002458444501d4007a00a81079000d01442d8070b40c5007070284185001108688a00700b001054602010b180710303440c0c580b80c0d11446803d8455001940c800d091078864100b41905851461802411000b1074092144444c0152034254040759017a0304034640c1042000685180d804c203039041c0f4000780440c88a56182d9001c26080e1108441806640000003010000c1303000801c14507035180c003503620741c50030390522 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 413860170 1250 413858920 413858947
    0x19080c030601030e1c02011a030703110603131704031103010603150b01050c07080a021219020d061b081b0c030708071b0e01090509010513024c05 64
    0xd410707141010f40d100d0041d219108104840c0b545089002d40044440a071150028041c20510710505034020036888100003605001840001344c990020200c000340c4412814843da03a0030080c4010740d095044c001642c08114120004c84034501d45402440c0d0f11415414600310071100c6244650190785007950800c089103500d281102030140c18440404e4003802c0382d00480780d5000d0b004c1c4840090051035000603e480c030000d6410941482600c0c0500c8003001c82038099204c1c02c2c0e1114901c01050b80b90481801454004030156295214100001d400c00c5500c40040c400300c83d1f10f51840128031181e0600c640065051440c144101d0104c4480d403034160036811060301c81c01112030042800d01c000c03030840c0411410104c4100040001481030801c160341e40070740d03d401403080c80f4010a00e440c20380440e003004810b000d41e40c890b001924960240e8909030342800341300e00044140e40c01c1e81c03d064080620f645c035280c40d0101c155000161401d0761403d802010f41030b00119581e070b1414007004120840301581c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 413861420 1250 413860170 413860177
    0x3090d02041a03012334051b16080a02030a0b3408010f03031b0c080a0609020f060304020a030b0402010215071701140604030809040608070b19080c 65
    0x14141da01007508000804070102c010080c0c9250b503890b5081142160b0b01e841c0c01110320284440000030b005103602d81503105180014070070b800000800a00d01121000d0300c07001c0305e280e0321b07800500d4060b1501c6800200101030881c0555035503455007285102c01d0580c4944103404000e00441805042c3d10086030703001943d03415641400078a500050030005010701f0440d020030461682c0c5041c400010b00e580c900b5044501c80440081001c200004000306507400c0c480c1201042c0c03581a2145610000048a03010082d10b84a004603841c039041800814011030500c90920f540f4071070340e00420500028810004203644489521303000d840c082c01000096500c0da500d8004894115080c40d8441d281c600040741404010000544030321050814407055940c000300041607004c102103020100d0b42c88498259039881d55141a030f6100001784020300100340c03018010002c4407001440010321175500e25503141042001e45c401ea222080108103640009041604243d43c99014070300307603c580c40d052407946680d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 413862670 1250 413861420 413861423
    0xb030c130c0f081e10090606050304170307141303120531050d1703180c0406030203060c0903010b0a0f150905010c080a260709050405040803150109030b07020c01080903090d 76
    0x7101004100c0103170300000700070041c014600d420311000340c4400307001d802a03200340d40c1152500f03000d0112141c52a0743c8820b5901400c40c44d65482d1484460b01b03001c0003240c0203080b07100ea01100403840080014212004c94007070390f1490300c0b2aa210b4010000049074011440c01e01340f00d2600c900e0017100c003100001c40c2c0205030b42d0101c0306880001e0290400d00800603440c580080c81c40000802c0c0b00a018084a402c211440318070101c5850207074100c1840241c0c0d425100080d0158003e40200700701d4bc0c00440500750b540806000000e64101076000218480a594041810002451030502400031180101d1160350990f041024100749400300081c060400c110001d0a80d9401058030310b20b56100c1c1e450111480520659100c43c5450801c240c0042d041c03d0304d0340400b240c913034040082c050a05000d0f00344980c0d005031941d410350755680700c030142e0f03441210f40080c10071104030404400200c0803c0309030700642180d401004008a034200150581c0409000320800354018003010701d0303d80c0d86c5142d004455 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 413863920 1250 413862670 413862721
    0x51e010303020d11150408130b040f0314010e0705042f0a031d06040602370305090a110f0a030506180c010e0607170c0d080a0c0302030405100b030c130c0f08 69
    0x30740c40c04103608d503000341c580c0021031a00400640065000b2000c0f030b04000b9240103a9014131481c2c0d0f0100a02d0803034800c1001206550098141000945000d500503000001100011503c1c24641100303406560600030300441e141c0c00101c1ca03050400c0c0c1c1841a100703d11610920491a0003d80803050355544000f4001802d4a800046000000d5405019014481a04581e5240c1d1121408964807a000004840c10000b840c240008a03030f8200001d15102850b08007440d0076850038510140420281d140d4181608080c0c450320000c0010f50401c9014402d01640032041e0003401c80c060403070b040c80d092010b860b042008110f020140c690700c6800310b8041c0303a4030100d82181c110810300c001069005500c00c1c005140101001c817454144c0004490340b0480c080366080000d8992642c09030200c0c0030640b406899680416641e0042030030f549d00c80600194014119a15444600c0c0020a00e45584c900c0c606082d4581c2502071126030040440c26240c0d1860403d51141e140240d848409808a000707039401c1d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 413865170 1250 413863920 413863927
    0x90a0b01030204090c0c02030d0e0d02061806071a070327060b131d0111041206060b070f02010f0206390c0312150f04051e010303020d11150408 63
    0x80c0c0c02a4126401807a05001c24020901d00003000f81480c1040f040a901034010a02c0d401d50080c0f0444a0102002d802450f020340400580c0078000c842d0000d07070680e260340116000e008280d41da9840641506442034400380c02c41c4100040e80a5800390150040c0e06150802801040b142e005542d10300c43c0310b21a00318208080c80500308100503000c80300b840d40e00701c640c2e44800d220914044c1c1001d880080329100b265035003059282000e00300d414002403440b41d60011b000901040d00c0d10180140d01034007030700c000b0900070f880f61400b90300ca03403240c0b1040340d0015581140c402156000303d0f08a03c000440e001070041c41c5005000c040a100c41c0001c035101d03100703103525641c01716480924202c0640740900d00e00e40e241c141c201032107aa658840200c10a01034041070018039141e411400419882c0b20152980741c40000030404d00014000c040c02c42d4000f104416a44540203d851242c140218040e50041c0f03418800e02c0c2d409440c19407100081c040c00d40180c00c40b1201050b0704415590002d901040c910354 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 413866420 1250 413865170 413865191
    0x1504060e0f0d0b090f160e0c0304140d020c18130b06041806020a0e03030307021c030b03010c0c111203030408030c0f042d030b0a0b0f0a0906090e0309090a 68
    0x1c464220348001040300b1143c4041c0303c001070f00000c180303d05841007000c84001c481031740124408000944201000451040c0000d00303c0e442d03400145070014420102d000003080140d640b181014030140c400c00041c1d0154071560030760307d8000c1072541c805032041c00261160500300d290183d5100c0009000d4240c1c1e42040100c0c0319030700c8650001c009005103d40034154901c0381d18280340650300c41514040050300000d140103052401004890003462150001c2c94116103003046582c0300130305403101d0070506650b10800800d54030207010f60300c4c0c0c60505940d1684c4070100d51401c10b8140c01c08101190069200701400041213800000300c80d0845e0b0007200054807507a50030b0091016105804d0300e1412214042400507444406c8500140417041280320005030201c40501904070000c07900c0041e040e1840a130104446900681c403014595030041c0201c09440305c20300c0071402d002a90b44c04108650754a51042042e00264494030361007034001c4018502e020300001c002150200023414001311565182c07084034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 413867670 1250 413866420 413866429
    0xd030f02100c0503011d010501050319150e0414030a200c12060103060f0c0903140709050118050903090612070c05070b0c1e1c02071703091504060e0f 66
    0x8003810201d041c1441030009203000202a60001c1c828100003080781c0b02884000e00041e25082d050b0350060b5941811603596180b00c0700c030345c2c0090395003400785566041c130202040c51030348080020380f0029040b0603090a00e03241044c400d060b86c00c035502254000b448507503103065000a00c03582090342c070340042d51f25032010b8840780d050000700840d069001c0056642c00044000110303109049900a000421003000100041740a07500003048034800100c0190082c000140780c03904004211820404851085803102c03a460107d0f0400c1e04010030b10040e4540c2104406210b0003001c0d8800e020b4000f550508080710080f4100d03001d0712521001c0001030400090115105002d07034140c058001085a032056034031140a1150383c020000e034409809014030300c0300301d050001c44845852a10310000c06078030300030340001da407403501210580c0210b004a1500140c80e8600448134182c1c1c1c1c9071600a156102c2000d802c125010039800e0f0200d0407918140003c115a9411034100c0d044440150343c2160758840300ca0000f03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 413868920 1250 413867670 413867683
    0x1409060f0723161202150609090114040503031803280c0503040b1c180602030a09020a0f0f1208030f0703020706090b01031b050f1318030203070c0b090d030f02 70
    0x102070401c002c11214020003d0b1456110840d000c4c03a080e41c1c0310702880343d0490319005090000b00b1004e15040104a40d8104892400da0081c081000020340c11010011030340d11314800e5805a82035400030040c0407d40426042d650301e01001301c00107514001030000558001c041011886265450b2441e215003504c0c014801d1112003039011065030381c0d507034607000d030044130f500303e50fa0301a0752942040d4080c040ca111031003060036180b40ca00c141450b00090380d59a070080c0d4001008492056254040d00b0700507110342c406403004e08038013070450340590300f84040000c5085d002d0303101040f81c9143e02416004550034000722504a60b00e0340390601740d580d940718182e01900c60000000c10303141c40c0000d00e030207000102c1c4840f41070340c0c420086900c034510080c82c150071000b40d5000c2c1683c49108403404c1c020a01d40b00c5402030140c4400da9011811889000200c66111101001a00546c000151074003c210a005581003c2d0080b41000c03070030002040081201030a40c0c1c0b0b0010141706090070302d22402c0b170081164 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 413870170 1250 413868920 413868977
    0x40b1003320304080715030b030c040e03040b0d021b1603141c050a0f0201020a1403040c080d02030307031503120c0606090204060f02010b030123040c0305101409060f07 74
    0x8803643c80307a8464199035200010f10860103040c0b5202e4120380e001d4480d001d103c0c00c5201c01170051582200c51001c000041407c0c41852400c1e01c0100400165518440058590590a4600181c0340d0074607200f80c000710382d2010031410054014400501c14407020810714070907250410408440000426202c620b4a000c1d0b14184042001d1001c0f00d4855a0b4018001c18035440e05680c0d4154100352102c003a0b003070f4001c2c1c80e280c801040003040810044000e110281d40d000e4042d13102d005d240da94032002c00303003081840c21080c1c0058100000300074420ba0036008540308591500001861039140d0b844030301d074082050300c07108100b040c102c4404041c000c0c1c64000c000079115512085507100e60310100600f080c048004584059400c010095986203018843c000000b00c40106e90b00000f6548420500a0440200220341c0d0000303070715012011580402c10007000d01213241000403811544080b50f120204010001902c66208004000200243c0c0e00b90541180c0c0c1b500702080501c000c0b41070203201e00c890488 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 413871420 1250 413870170 413870173
    0x30302090d0605070e180106050f090402072901030c03030f020a230d030908090f06040e040c030614151905090903090103110a0503071b0b0708040b100332 68
    0x8028041c0036003580003601400442c0c0b40c0e41100794000040c0440419000703951b00c1d45e0414900104015809800140019080c0d100241d00d08406100010100e80260b041a1500110380d801340403050000f9082e40740541300024191a40d40c519610b01d0105003803408010104095180c114404500821940c605540d00c041c2d64106c1504152640f075030005c51b50649603071880fa01d031500315854003920803224113540040a0758a4a078040080c080030303020b400d6000d80c0140c810000002c100b102c000c0c5aa01403849400021a040c0c650b0900c40181c80f070007044400c8038004101031041c801c501483c81f460301c076004d6403101c8030b051003051100e0a4a4055114a4106140800300b00201d440400201040c0380f090700d0400c48400071111105803405640c203c07401050042000c03a90031401030000555030b5812034081d02c1c0810b10b954032815002010746048000c00c8e9040c0611081001e0721041650201c0e01e00450b000291a6454074801e17108099242e004500c1c41007501205648400c00a0705006a003d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 413872670 1250 413871420 413871439
    0x110402181f08010b07022b0b070314070f02030a0e150d0902100809060711010f0f020910030b0d0b04050f07120c054c030f0501050420030403030209 65
    0x8500c0e65000c07210148600041c6020002048902e00501514034058003d001c1282c02d0103603410051040411545200c2d9921840d0f01c40703000075141d0507813103200b80e070141d90120b041074a1b081d01c400d50b0040a070a8606101c0e08030401d0008950020555680000c140b612204000ca01000724034880200710220000c0741c000a00500b01e40a02d40048411901c01e40f2108a0604280320840700c1d500306869050043d040000031440725031042e404042c03946500400002d40d03005400448045444141c00d54800c0c1d500030820407001c5c0b0b0440c01503408400741d4181805007a6078000060400903441d0001043c0f901d03400c02003403d00c502040f403119060b14a40c00c8441c201d46500341c0552180c0a20303001c4130360700b40c2c4160204a506160714041c00300d800020010b0700d280655546040c0700c2c41c1c00b8842404140c111442d841209001c04440300d1a1170507500c000070395201c00c1690400384c80d4143c01c5a4000ca0030640c541d00621003001103800425848540c003a126101e529044001e8031178031080300d0f4811b54a1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 413873920 1250 413872670 413872699
    0xa17072304050315040f0807060e01020a0305061311031609080f0c0a150806010c030e0a0b0a20030d1d0a0305130e0601020c09180a0c0306061211040218 67
    0x190000c2042d50700c1201103400403000300003d10881081101d0040c40c3c2da60403001680041e000c90080e0042074401d1801260410009140b2422600000b014000007501c1c0c20038489503081403401c400007a015103c041c4400c010028041000e44406070034018007140c5115080920f51140c1c00d0071020305102c00c1500c0540901d400c107580c0c1d038200d11003034621400e420500003d880ca5140c620744810080b0f03440b42202c82e07a4860041d80c4014002d0400c0d0240050710501c03c116a54000c030741d001030b0001e0a940380d250407800000400e90301b001e08821880c544001d20840e00c030f00000007030300c0105103210300204290000982c120305241001c6568111440703182d200c4002c068200b000380410f88010b030f50640e0300907135038207450412610035107425015802682000610782444a00030b07a01008600c01d50f11340340c0c40c807051240f61110380d07201910758404201d003e1081018038010840100031280e1660a01c9807642c5034421804900d000440c400e9500103034400648550107a09468014001c01016800e02036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 413875170 1250 413873920 413873987
    0xe01140409050105040e0a030e01140409050403030504050f07051e27040303110f09040b0609060c011d010608190c091107030e1e2209050d02060108030a1707 69
    0x3805410320175418140414081000041d1440302c107505903860413804c0c90654015200d64855101d8201d40e00010030022980780040d0040a01580c8241e500081a1509003000d42c200031004564810641041808105c282d40d04281125010406d907a50100010b005001810b00c0151860500302004042203041034a0070b8035212912440c001e403010320500180c00550f41c0b0611640c10a44d200d903606010071041d5040c0740d40520b041904c0034080340d16100515001449a8105031010100da80d1501d141d150b900b14240c41244038440400024000703581002486512035000300048a19040d0780c00103407040c44041041f590003800c2c402410403414001400c44861680204806e4000c034880450013807160602d802c0016240c450400030340c1320030710b14104100d10400380c1d015910411100078298030112415100b140442ca2040c1c0060045d031852080280c14040b05900c00003c44d00700340b044c03142094115104291988444090081e5503403015019a4010005034858118000072010102103051 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 413876420 1250 413875170 413875181
    0x1b0509100b2206080f2a130905010801020a1202070b0103121e1e1812030201110d0510090b03030d05060d21030f0501150e2d121504030e01140409 64
    0x408800030255a500c0c00c0c818640c4006d00701240c3c4a4030f0112864a6101100c80502280785148010403034040d90380c8400c04c1940c00a070007004860b54002901c0f410190041400c41d201e01c00c0142c10341c24001a80c6031001c040905200241c0349a07410010031132043d100d02a15016650042880c140b01c141c250001851000b158140c0c052035840303102c0300c800840c002c490300000320070b40007206c0c1001400e02c0500d406002000004905542d200d40c5c200d030307143d511000501905001d031003001401c0c0c40c01080d0f8600724281ca03407203a020103103824207407040c0303072000b004035442c41d18002d030040b03919241c0750007040054000802c00b5040c1410210300040d803100084120000e6049550305200030078254800d801155000e1181c1c4004141030220030103900d0040c640c0340c49045006105c80c1003180c1d0144c4d002d004c1000c4480500b192401942004080e1415500807080c208000009000007440740c610300e10041005030025060051950130b0b5000303a81304061040d0700014110310992034030b41c0c608100d07000d4035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 413877670 1250 413876420 413876431
    0x308100b0301060531150203040902030f07020c0d030203160809060d0911040b01080406090809060d0c080a02040302010e0906040b1e030f0c060409050c070f1b0509100b220608 77
    0x2542c460800d190706100d203a0504490201030340500300320301d00706c0402d101803040b01017282580014400018103814520140d0b1003070b690910708007610320302100b00a0800b002d282007a4890404007000c003020a600009565991141141c0390a0003081424403071030034040c40001030751104e00050910000c25290b04035080c128860904400e245040704c0420040c0c9001081e418000b82d4180b000070040b40b010780240d82e0307440c020302e0018605064038011800c5640500000c0c005551a007121b13186503980300d00f085500001100e411070806055900084c01c596441c00414400c4202e1700200b03805d5076460388880115100100355640300c2d01d035004001c00850a0740880c6229004c1d0050340c82680300c0c0810350030400480140524901030070058007500070700c03000d441041e0030201407040b0f01c00500103119a8801500036124521400140c01c00603d009007242c005034080c54500062200030011130b12500152000c0d09450b40d129120000050070390380001e100400e51200114000860700d801c900000d0003203 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 413878920 1250 413877670 413877697
    0xf0412030e061602040b0409022e021b10030f15050a15141602060d050a0515060d0c050706240e04030801030209041104060609050f0a030c030308100b03010605 70
    0xd03480d08002c80381c01005030300000c1c039048a524800610342903010240005000f040010403181d40d80210782020512024002d50040300440c41400d030011880c002c003248128402000000f004903110003019807030a054a0244c2c190300c40c641e101034061b4100001d4400050010400c5202c201c140038000304240c41080d00030301c8140f001003124180d9041501a482d0140c545403110005c1800441840e800007481e051070030440d00e01c3c400160380f502c0050800d0451103a0208642c28480203840071a60f0203000d00c0d5038010b034040c1c0d02a07680c0b0303600c00307070b030300d000c0060000041c8000c070100141d40c01c1c454080001c16a51810300c030301c039400000403010b0301081c448000c03a40e0382946030042268014416203014000c6110800100010315000141d5a40a440b941c620340030b4100000204058400ca0b411070404141c0c1ea040074009410a401588070300481168100415444c5468042c00d0030840c0c04080c0400041000040300910341c01e2001e4020704204003090b58030342c1d407510f0080054200344440f00c0794 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 413880170 1250 413878920 413878937
    0xf1202070f050a0e0105091308040b0a0f03090201080c0c031e0d05010b03040b01140a0506030f0103030807020d23070f0507050301470604060e09060105031018020f041203 75
    0xb90a05043c014151802844c4400305a401d0400f00458440018008905001c10849202c005504040540003c2542e0860683c4503900600c01401010507407103000101890600c007400541c0c4c2c0910803e4200d500409525919032608800b141907114100711a1801e5811000c4003144008200c010a11b02d6004102002203076200c403582c0e171581c44280c5020b400002c4c0000107110729a2142c20800740c00000030301c0d800c01c055680d00807c40940044900d8207034112810010814550020b06255114100d480a0160a55039030000b81481001c2da20650100e0321120441c083c1d131541030b0486880d039420100328040c030741c0d00b840e10580c1c80388540140c0303000e5420034044940c2c0101e03c20450b80d015003585c038103200c07050a240c42c4a00b90b2a28010645256849007030351985920b030003000784054142c0c2d9803040036010300b040074000c15040c09810320303040100030030410402803103004c2000b054409a2411400010820550b40043e018030103500b04070402c0043c0008009455848448680b403007070702c45005 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 413881420 1250 413880170 413880179
    0xb06161119180525030b041401090504060b0616060f200307020f0703080904090c05041805070506090a12050f010515010201150509010b0a0306120b09060c03040309030803040f1202070f 81
    0x51303104010360f01010880c4201d070000d002e020380c100c0c4d942d0f8040540000742010500c80588000e107420307071010ba0810355420621003440b5843c0241620511f05072020751078001c2450000b840d110300007401070b010540d04d2000c1d201e014072640010118002d102c0020032410701d008001c500350350060341d10f80c000d40305202802101e1403010450ba01200d411000b42400d2500c07000500c00901b00b00b08040310f68602d0305c4404903032651113216401e030142e02c40c0d2201c80c03041c0461030f002c6e1501550b80c00040c82000701740105295940c3e0065010150307400050440300f003821500d002454a80c140c807242c1c0280d420f217410085040c00c00103405d001d01009a0090288809086581e0784400107401120340103207200c001400750600b04002010308040070314000420b80c0d99003a01d5801540d442108440e424240400d00c00e4041c0200403160b0401e5544074400e20350f09080ea000b402a0000c1e01c0010b10a02d070110028043c050000400044d064001d4640301d214101c00c5402074645055004162002068010209 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 413882670 1250 413881420 413881441
    0x207060206040f080903060114030f030f0316120f0902090606030403120507022103040203010506012c012618010c081308160c090b061611191805 64
    0x104460098001e07055030b840740c2c0c0780c440c9118510001030b1407021040060b890a034400704600c6000705131180c1d600070000058000c141c00c00440c00d802c0030079a4018480114000c42502c22640c004d80344c560340c90b000402c0310382c065580d030800709000445103151070382d910b04034040c0350071114005108442d050f40d11380d00c05c1c003004114081610007600058034841c03071000740c45040d406150030014038011644034900c0c0308680c41120b6441052021100004001c0c002103007002d008840d000b6109080c41c001d003560302e8880381c00e05130380301102003c100a80017840c000d9900828401942c1180480007001d80c01c02d41c040810810743c1919207080f807400e000138030000c43c1018401c00380008000c1e910326a468659034850b84915070a650241c5607008104010b0101040c418000a1264030880b0030b107080c10303d828100381c22941350300311403402084204a0f1a00150495034000106944000178204600d40707840819200804036150020140d03880601060309450781c5400b2a1031801508140150342d00d518682 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 413883920 1250 413882670 413882683
    0x91c02360702032703030412170c0d03020706060504061d060f0d03080c04170d09080d080c1803010f1e0204030c0612020f12090c0a03050c0402130f2402 67
    0x4070300503002440b90044030845010a04074800031440000712981c2c0c0e03c80081d0031980709501c2804400390b5111500304104c0e00c52117000400d040c0c11202c0e820b202c80184500e450780c46800c003c4042690014540c4c0401010398008400f17014054030402c013140c2c40b01840c01408001000381e80c52404034500042c001e00d440c2c2802400f405000d00740129080035650f05641200f805000003c0040c0140000f040041c000408091074003e02c0000b09241807602c4d1b005004071040360030401090300185001921a5001441325401c05c61100c195560b8498102c1c1e0f00c2249080361201d603a040d400d00ca191580030405802880c000c1100c0d2030300d40d04040c45000400228071840c40000c1c407040445404006081c01503664881c07a200341d500c0540f078044000000007003607100814046aa12541d0240280c0107010042c00841000c00c1d5050a44941540c40c0c6540d1882d007649003900c00c036000501e000c03620500041610041001c200082c41d0b09407900070340070340c0842244c0f62410100703240000da580b031407000509 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 413885170 1250 413883920 413883931
    0x230901022104152102041e050a0b0904090c030602032202130b18040f1a100510030b1201050103020f0d0b040611091e040501080304060203091c0236 65
    0x7800c1c03074549403e02c140b1200400750890014081ca5010342807881c1401541401d02c8500080016501c509003c055080c0d031070700e8100140a1140c122044c032842e11441450001e0b10381c414001c41d02d441103440050003402c44402c008010012655000040002c1500554012452080c0b41382c400ca0b200c191a1040b10403806020351b201c551240610283d200c954840089004040d040c004114540352514000d100d054500301c0f40e801400510323038184040c10002442d035070b80f0030078540c0e694140704482c40c01403411801100e00c2484c142e035110307000307500070361004450641c040c142000d5050f01d9000340c2e000706024030003030703015213401425103a40749001030b21458010b03030142520102c1c1d00c46490f400c00400000c40034074080b1b1070401401c200e41d501c180f0809a64045580d01415441e81c00f0140000c0d04c50607032040c1001d910600092064a80201c1541c030001e1003600c02c0155800c2c4030106a070402038900e4041c0d0005880070003a802c501544e100481c1d4007104031700c80c02c100d0024550078807005200702c90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 413886420 1250 413885170 413885233
    0x103020f070803090a0803090318010806061905270301050105030a0203190f080f03060f120703110414070519020a0b0a090f060501080a05070e0601091523090102 71
    0x32410002c0c00030800746401250003800c60b0b01d80a0b00e41c1e0b94010756441034481501030f5001107068100500300d2400210205020300e0a0001c60074800046030081c0180300c48110924154103402c0c100030f220b0700503500184503190004540f806402460800103101c07950300e90083d401c005c00801c2c582000100340c4682035014006050085200c101036200b6800c880d012581d20196564403004189502e000e0300320300701324808076580ea0602104001c4060150352200e80038007011040c1000c01c1c03e0100d5805c0071250000a1340f001e03058210700080080c500040d0440502074801c0500c0038150380000a044e008038040c2e82d65088020001080c0d9842c2c100c4c0070300610080714000000c1a111943c0c2190b503049108142410801b00c15903038100c1610f50036000a55254800422801800710410402c03008000d0001c1207007090501d000024002c0c00325018a06568440c89800351025216030720315038440000b60b42e036008041c0d00c40101c1903540c1c82070200e40c1c010b100c1c0f40413007840004001c450a011484000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 413887670 1250 413886420 413886427
    0x81603050a03050d062c06010c0203030f0706110307020105010312140906070614070203130f1a0a09080105010e06011713060b04060e101a030f04230a0308090c0103020f 74
    0x503030031543c0d039104090390640ea58680500095100440a905d9820580348004442400c9481090121100010202810084400040b02c0903803004812100b01f50210040c0c0b6039a80c25a003002c0001c3d025801e2a50581c50f000410800201c3d419405103042e41c1c46850303100c00480e0f41a0301200e40180040c0701c25012181000041c0d010326082000f451003034492040400c606c045100003c0c5014030480301c01000da000090408040d80100c10450080c2540040e1003030fa1a04180c50780d03210165100344c80600c0c000004850003154003c1c103039580140154002400b0a40e1129012009064252032490115003c1c0d00140c0d039460b219141d541c410140300d00c00e0482900c0d15141d02001d000141582e0b030300715030358140c042911190022450321035450110034010329482c00031540030800300ba10024809020500178892242c84044d00e158100e43c22019890514025070400c40000c1807500740d41c011845140080d9081541005403244038144ac041a50810741070030f001907069108082c0400300300c69007003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 413888920 1250 413887670 413887673
    0x61005010305181f0513050303010b030711060117190209060906060f0409020c0d0e09280501031b05010906020309121e03040f141804031e09081603050a 67
    0x241c0c0302980c0800343d040c0100015039241a864141881c1d0610405544040c00402075840c5080c0140d80e0000c43c00c0e03030190070071907441c0c41c1c042d1240810300815681007800004280e10078480c4c821200810000c005440e0a961368100c208040c50800a210000e809288103c80003c542c02c000031021503000b80c000d9505685540070481240001010164011414000907155070850340180001e08902c64005a0700c880d03003400c0d5031810a2000c104410014102c820344c50f95107072100c0460700303c04252481c414511200488182818400c1d01e0101c0282c9001e0000060240d50084002c01d01030304200b040c2407a454100442c0c00304c00a019480150303100300961451410009040e02140e0150130036901600c111a9000703407401605003259509a0020600b030200c0c07522120090010070000002c103072205000d00100e211004080d0126400e5003182c40024240b500501d00031000c181c1415280342000d407810806000c110040c06505603501c0f5460418031124034007141e004c249d1760080300a02401026 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 413890170 1250 413888920 413888927
    0x70618050409140d0c03081b040b1c020f0406080906011a0a0908070312022b0e0d020310050a200708130e01080106060e0108071d1c050c0306010806100501 68
    0x40008842551040c0c2805803d600309000740740c0d448030769035500c15017001181401006084e000d00b0070814100c036099200b001201e00002c80d01190309112001d9116900a40b4698514140350b06440015000107150240902d40d10b00400a4840d00c3d103800c0e005403a8074910640e103100034001e486069400f45a104420f200e408013400b03d0092900d01005180d4031891102e04200c0725600480e4101000d88890040b030380c042c0305501440c1c8159a984020020400c2c20000c002401c54282040c00b03504002101c0780e444031868070b0f10907500601161088021600d219004041c02c449441038280707001c01e50b00b030042c80020b410340d04014180060381009480c1e20b8030107080d84908034010422044101c0083c05d0700200840380e00078903602c0e00004902d0318240c0d02511a01c03070032005c85d0420492104008005801c690380520400c005201e140b24030900d20045035680121160f8441401c6a03580440304003d0005407a8182ca4825410380d15240d0361200c045a44030826205910700c80c658540c1488035520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 413891420 1250 413890170 413890181
    0x1021209040609020f0409140907060e0a1508043813021002100c08070807030903020f1e0c0d17030403031e0f0605063c0f0703020706180504 62
    0x40007000001c20030f079601c907014101d80c00f90b603d51895403404078080244061504c01d0942000c00c0c089865101e00c1c00406c5d09448c0e05543c001c2da014001c521401a1050f100c568151f409442001502c03803c00401c410040c01550003103508980c0c046150011100f03507200903c410304001c069420391504840580c4200720a40340052618558070561103128001d6510380c1242c1c00c1003a410b8024241c1000d079074043c00300b41e54100308114240300c181400d2011560740a001a0ba11130003030b01d000209604189002c9043c4031a80d80610000d2040c04100f14042c00d2388051042804084000c0315042d40300c803c1404088a01098040d1442c07030341c483e940f0b183da0042c1e001550301c10322924000440300c031001d21000f003501c41c1c03c40560060b0740c0d0340f1805000d40b03054803881000d000200d030300b14104031180c044a0b000c0001003441140003051b0122017054140b1419014074049814000107484001d00030390200190001002a40148100b43e400900d16000d201280100e42e404240700040d5810001070001400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 413892670 1250 413891420 413891437
    0x130501140702040603030c110607030906030c0917071d2a070c03030e031b0907110c101e1d100513030c18140a0c110303150901090b010212 61
    0x1035003040090010380d00c0e0310401002d58481d49801080203400e040440f03082c8882c0c070155000b00b06c10003001c40421b41040b0000100c03105860046400f00b1108021681c000302640a80e002c0405e40c08818048400410424295010f10300d16903040940118050700d004415182031f40f591240070082c00280505241c0082d10042c4e2002e842c0c5084070980e40e000c0d00c238449a2058000609081880010340380078042400c20750071403265905840344d04000201982400750040742440700008200c40300080911200300d00c1000240b13030741c500c0003c0790806040f00700c016500d40f00000180305602c40180c080c2c0b10320440b01c409819980310b640060000e005500c201c00d11f00700e042c084c01b8400b01c805249004004400385200341910f6511900e0008102a0000200c0c20a040e00e07080028442c2c6c0e40840800459000b8644000070850002100042d15403140e900c60072440d50000104002c408c00052058003102201510701c6009a82c0ea801060211540a60140d0058008426503401111120049c1420a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 413893920 1250 413892670 413892707
    0xc03012c01030f170c011b020307020a05041509020d0905010e0f0a0f2103060608063705060307030501030c0b030705030f0703060b0714010f0509030d020a1b05010917130501 76
    0x12541303540344140f03682000c0b283c0038042c0e44030079103400c48500b802c2d44803032400d003240011401c06010368000b860030402400351602031a0394404400341c14110080e0540281203100f000c55580c2035078000d200c09826a980701f604c240d800c11200250304013000070300c0010303100c0800c050490010341e65140c00c50f07a241000d003075500041c8402000c0400000300e075030f060440d1040d140019042d18144000d040c180c00149403511a00e0f001520202498103400c07014106a04031440000c580c14102340011550810340003150000b50100401c4091901540030a05a81c020800c0e5102c80356100c0502d1481d04c0225620400580244040f8011100c18148560051402d08001c603090780c440101c00300542000c02c1c2a1142001d01039800740c00c82c0203225151041550000521440c07811204445d901d01c20325031907020455000805204c1140f00360540740d21040070102c046040446424114080c0101c1203066a9a940000750b5002c581002d800300d4050a114a6280c503105250400546850310400c4408900 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 413895170 1250 413893920 413893943
    0x901090605070806042a140c010507080f0f1303050903070e130309050d0314030403030b0603010b0307030b010f020607180b12100b070201020309060703030f050c03012c01030f 77
    0x5240e8000c0703034440c1090390f403007480500c1c0140c100000e8540a5201c4466115013000d2080543c0180060500c5465035041c00c1c80203c2000c490360000d4482d200140c900d6500e01418400641ea2002195002d00c554040c002c3c00360f242c24078050b852707030002c1d50790350b47c482ca0b10900100064061000f0700707030501d030050071754009561b00c503c201002941100c0d041c0b103e8142d5a0700c501015040051007020740390564a080c607001a80c3e03005031103c1d000b44010b061108012001908152207500710401107003024000c01d40b0307946e4408454529420507079810002c6030500d400c410441d44104032007000801c9980c0108030a0310b0b00038003038414954410b901d0000324a03800380843c0030003051000b0500b0000d244a02d07102403400083d610f1803059140c03c2101c086404018070000741c0e9001096415100c0101c941c0c0d0355a00741c516042d0002c0219190013801d15080004002801e401c10000e14101e4180305112608000300d0410350103141c1a6660b084001c001030001400030030440c03800020040e214a003030841 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 413896420 1250 413895170 413895173
    0x2070201230426100e1902090105010c14010f060e061c020f01030f02120711030a050a050a051b06010503240c0c0a02130b010e040c02150903041805150901030308010e090109 76
    0x801341c1c0440b20605164a6864540f4807100400c02c2d844403505141e556468403d640d8000b8100e0841807003007a04012051315650b0602c003034030382060701050031403001304040341c038140041c400360029118400c0307001401000a402c034101000c5e030041e6007807180b16038692500281e081104224104554904240e90358400d10001020b500c0100710b10810006200030a20303082070300900da22101c01080107190414401364510580007000e850444109041880d100c605603003048405001d00b010703080c1c0d00003008481c031544c08004108903058500a0742a248034a1004114144248a00d0354180000e1110000544041040e90280000e6404502aa0000d51090f000602a4100708041202142d07481541085646c1c01038001644403009407014444000d8480b0060b40301e82c00c420850f20407001060001e01401410f10803500580300c80841d20104031040e00c0c4010080a080710943d052031a4404140c01340d190240d0f0315030489902d0741e10710010380e08110810100b0316019085010941d00d43d0640030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 413897670 1250 413896420 413896423
    0x12030e0114040605220303021806040e040b15010c020d0606171006060c0c0e18100f2f070f0c090902090703090c050d020a030605070302070201230426 66
    0x100c6924003070540066420a810210200c9902500301030980340580109500c1c04e41e038a100071210354145c180141c542203024020740550030b000c098250b02110010700403030035201ea42506401a0f000e04480500342c2c6e07841d40b01800924001c0b05107400f00d1203040e1204010300e04445128800c910880c40428600c3ea41c04040e02240d5580c0c5400d141031300300c101e03202c194440601c10031005200f40d1901c1e00b4800c04c1381d102d5420140407400303038010070f070044e50001d807840402c0e514413101c221384041224000800c2c903038800000c0501545020001342400040011041c05c040103805000080c45d6504c807540d4440d400c0c003021340c03114a04480f504007008040c00130a80d4184c504000b04035141d00415291a18410401c5545004020005052804501d0782c0880c1c09034495a0a960f000e80300031642c03070182c1c000a0000c80281d800200441e08040400c01105d6154000d0000c440c0700382c0780e514100202d4600182d440070325645176600030400384000c010b4080d014400d00502c24545000c911040001d0750302030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 413898920 1250 413897670 413897681
    0x210d0f020301090e0f010506010801030206090117040825150b01020f0a0c181b1b0203030705010b010e0603010303080a0b0d050a0507030311070f092c07150f0c12030e01 74
    0x4900881e61882c1c1c113081d0040c02d10038506006805d00080045203446000a0b10104060001900808011030b82c1d04040c2d0040300846010603040004611600c0c00c3e1a00d00385591140d00306101007688407604802e03d404003d60111004e9101e6880c9400c4000301d6001001003225217241c50451007141072880c2c100c401030219040c164080d81210220504190107030b19880700b00c2c0840012185401c4550340980c0c1103160f040f8041500b0b19090240b50f00015090401f50410340c5d020358140000142c4004004056000c3c098100c400c0c1c0700c070210104041c040240901003403101401180c0711000082d00a000c641c0701700038126004084480000682d01d80354940700b64a20102e5460b4031811045c001e26806c000c0d00541444070034001c0448a051192203555140503102d294203182e1a001ca2003000701d40024105901103a032a107110404010f07032129550f40f070552081c100d03010320101009802a1064020110541060729200040710b12962900106d030701201c1080101079584181a49103082800707103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 413900170 1250 413898920 413898929
    0x60d090f030306140a06020c12010f060b0306180712051b070308070306052b0602071205070614270709060f05011710170307060606030e0c0102210d0f020301 69
    0x388075080c407240116039800c684d0307580d11506a40344208182030340007606400c428801e50315a24142c0c40c4060050150042000f00039005041104c080f9501e210007020751f00c1a0b0b000c80e91a080000300f41e005030181c03142525254006400e00000c03100400080d000607401c0300c400c044c2c41c01c00c0d40400b1410034198204000c00c80008500c01c0a000441e98503010344009400119050703030428801d42e138204409418025000142400c0d0804042032001643c140da400e950000c504c020440740007c40203060340e20a11080f55141d2506001c00400c0b0714a021440c8152445206c018000c4511308000c0807081083c0d170180f169124420002c2040031040c0039136001000318030215554242046d0000d8102403290050070400035039503040003102034100d032070001100d04001d03000518840d0020201e0a52160b9a0040c1105080c09400a64690b0540c07112054149a609903030144001c0001261903e8101c03569000407140c104c0d00c08260541100107000448010000003003500780380854005070b070002d80c130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 413901420 1250 413900170 413900177
    0xc0f070503030f150f21160b0301050a0905091908091020030c0705010e01090e0f0a050c07050c04111308030a020601080d050f1303150911120309060d090f03 69
    0x21312030304100c00610304255803c2101e0040d8140003110100360058000c071034516400000009201c0401c00510085142c4020000745188013611820070601a0303100f0b02c103650240c03448040c005408a81440741d1409501400003400031105c0b4a8a2071100c82c00344e10069031200810040ea080550316104103554080b00303038450b50040c2a804842c40440c1d0002c00052485400c05c01409401000100d8003900359070003400d203444031013100300c0121850a500c0d003000c19205520001c0c0700190301517401c640c2c403582c0b00e08000e001c25521041904818059107500030724950100001c01001e18098101a49030506080c03034500b0003081c0c4402030000307011944101d00603000015141202d59040c01a9030250402c1c10081946140c9008014480d22171950b440e42d03000b10220300e240d545004241c1010085030000281d402d41d608490310080107201100b030894040300c0c03500c08101d140c140481c2a01a002201000e035082c800f1480c02d10015510441c180d070070703031640c0c2c1c41e401000644102e420031003a070103582c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 413902670 1250 413901420 413901451
    0x504020d1a01140d050c12100510111f0e0d090302090703060303081504020f0408032106030a110d02061c06090510030f240905010f050403080c0f07050303 68
    0xa82208441c0d10303a101d00c504104801d08007400300d11082003110f510700910f610004460f541d90402c02903a0041c9a5000324000d6004207000b40c03440000e501d8401c1e1101203441c6c800200d10360001381c81504406c8210f614a0b0020700f0300c40384009511078070082c0c42c09a014013040280d50715034000d080403910b000e0b580104000035028029070804084541d0703c44a01d0404000140c250b44026021200050034502e20400314031b605601500d86d034040d10007040e9042c40d02074545486903145074aa0300000c91116622140a40c0705050b680b00481890080304044c0c0030f44150306a0751103a8500c20087c95810703400511017401f14005855507001011441d480c02010240300e40051155020783c1c3e0198030240c081800e2030240702844d03c4071080b078012a680001d040c00e00d00300524003d403002c40400c040c44580c03454010800000b4900d40c000e01e00d4148200001c0214402540d0040b00b01c480c1554041c0c000340c140d10005031046030700030090030007851030341c0710a040a0b6541d540900d194402c48030f42e2079010110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 413903920 1250 413902670 413902691
    0x609011e021f09150b06091002030705070f1712040603020a02010e0303010e0717010e130204090f030e12070e040f021c0f11010516060b0d02031516020318190504020d 73
    0x1038040c2041300c40001400e000380c082c0100090a613000b5034003039911542184000e140e42d11b0007003048407115640702007548c0c007041d81ca0914644200c2584203c41340320641c0349999400c00340103d01c4940c10790118500d86d06160814001310020b401400012040d0740da41c00300320b02d2075042040514020000c608207081e00d460005c0c801408400b8201c2448009040e03000103005041642c4842540440b0501d1034034840703e440c5c0002009004041c2c8081c0403c1c49030324fc0d98052580c84034050b0743c0c8010650310075200000c00d108044d981d07074061007070981e012000c5002c10300083c81030f041c094043d40002c0c004130106440c4008043c940c1200c2d40201ca07855001c0c0200307000c100e400c8241e00703078014090924500b810010700803c85444860341c00240369981d540720704110380d40c80d6805698810740181c00c4906111980494240302081550791224208020420060b550302c008100c1d84e400070314150a40d0245d00e680c043c405820340109206490903414000410103172200e10203842d50741007061012540c911103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 413905170 1250 413903920 413903933
    0xb130b0604080618010e0f0d0f0e06030702070806130f08070201050c07081b010f05030613020417060a060807030201050712050912010902010908060c091504050301050718050609011e021f09 83
    0x10804104801d400941d01582c0c0c0d60b0b0081001c3c14118401e091270303400c1210b02c0104407801c02d0150301b50780c1c1c03002c2e01205201c0303043d40c0010070304203070384041007101c0c01034840002c60b882c00b04184400500e038200d6000301500085d0903102500049206052460510007014041418103c00780c101e166190b100803002600029000e03400d1010038000c1c00d00141030003804000405034400105201e01800f58041610201c42c1d03140e048400070b2007040821039114040303600541d01d454090b5a0418030508100004c01c0725003001c00c6160480382e05845035464046c503566000441c0001c02031090901005200c2110161a000100c2004103002000010141020b100140003001c1c1600a12019440b140c01c01c07030b2103d80101180c0d24500300312040004bd80f0f201310803d80c103200b281c01942c0c2550a01050008464028141b008070341084848403c0b0a6203401c14080a401054041400030381980301025080d0100b20b861540c00000d403040e84c0c010303160282e05541c0e107540441318918080c0d40c0e28006051151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 413906420 1250 413905170 413905181
    0x9060d09030c17040b030a05091e0c1e0d0210050408060112050d0e300d030213090e191a0708100f05030703030503091905150a0b130b060408061801 65
    0x201d04501c3c90400f400c2c4000c464640c0002012042c050341c1c0e40020400a000800c6020f910f00da00c41213040d03619001809864503529501c0c200340c0540944590b4016aa84032090341c0120b00d40500007001004540c2c00b00190182c1a4001c881031000c00c100100d0028814031005019040a0b41c00c046c03020003520f4280e1a14205400c1d8004101d41c00762000090740d1214a00e1000c600250141e040d0101c0c038220360203040380018002c4006200340040d000349a40c26402070715055404100440040d96110045415580700805da0502500081e0344910840341540c5055411405200980d8603001298201c800506040c2d07008400b1500b01020000426017825507a4043c091084130100b0951034400482d54070449400001c0a000000c00062031543d000c100a208183c03003960340104022150070706a0b12104105c00d07035014056039030001032440800d4025000c10800250590390001615244130b0020b01e0308502e1580d10170010000010b001c0c0e4100000c9020300f4108245031040422011417a007100c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 413907670 1250 413906420 413906453
    0x503071202010b030d080c13080604032c0105210708060a290a02250305060132030c040e0c09100302060301150c060c0513050916030209060d09030c 65
    0x82c1040f0104055842c041004860424a4101500300e521903003030155142c001c0e41d011918a285810300000c00d04c500140c5140200d0107070b101d52605029405c07100254080e240e40c03103014690741c11035940855108200a00c00c2110502a0340c41c828a045074880c211130003a58100c000444400500180c0d28040c0806401000c4030805040221203002503810100e0803c0303d02e040c807000c08a290400c407402485043d0355002034174880d080d2a4114140200e4415072400151001d2050000215410503030b000600a81110200c0140e14407850300b02000300f25519410050305800b40513034060302c5880301d002c1c40c462007400d140501341074201501070007030202c0c00400c40b81625100010410250b1140380481e8159030604270f4032503c0c000c0a040c29100815031040c0104014030304150a05126480405000010000794070306480070f55580030030046040c01d840608800000c441d4000156000354010080c0110180c0701c02d04010465402c2c20480e400c1d290164045994030213940108042107441c8480076 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 413908920 1250 413907670 413907673
    0x405040813080706020c221506020f1204150e0406061d060708070210230703110703082205040609020403030207120803070c050a12021b040e0c0402160f0503071202 72
    0xa02d000c80081d69103141c1b161302800341c8610801c0d0300f040c00419007a401385038aa14018015000d241c0589411a05203104550041c0240703000d03146c54044c049040412805171803061400c02e401d0600109280c0940d940400910201e0101080c0f0340e03d450142100400541d1920180c4c1928444151035040074604418414081040100001481c1c10705454100d5016600159100c040d8242554151080202154881000000e4a61108034200200603c511035518040c48001210007a81d5890701808004c2110400303000c2074800f00500030100031141d54400540310f01960310008501180c200707801c05008590001014410715404010030402003018442280a441e102e40706c0308040c1c040680710b803040001140f0780c10f05100d004c101619100d60040b441072404248080c01030754440800c80aa0020303004000c000707909140074440d40c500021040d019000c03c030704140c1000001e610540c4880408000e00c0707d517001060301500701800140c0701d5001583c2d100138505284410702010058407086 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 413910170 1250 413908920 413908933
    0x1501150c121412091b04050417030c16061409070609090b0a08010203160f0c0f08130b07080405040501090515100e180f01060c051515040504081308 65
    0x281280c0d660301e9024414500194010030880110000f88208208084940c4a003404e00c6003180001ca0f03045490350400502e660034542c0f4005020664608075405007548480080801c941000a00119402024444101e182c51001c40d00790f8908209143c003500c64a40d10500d01000d0301400300116000410380d001000c8182c036007080100304003414021801848d40700c82d586d034601d444d044200409810004001c0d522454945041c80e1040d03881400c1358001352950644042c541d0040c100c0104907900141d00203071900c1c3c00d8582d00041c0d40000c262001c8d200d900180040c00748040000f40c562107104091450b66145000e0030041510010303044581c10702d00d01004c1c80314200d94244c80301c24010302a20b4500c0241c00400043d04c1d8504001030181d045a0902ca07040260035104280f0b500c5141401c507100001e0362500303406c0343c2c0c18496400040c0070b607010a08412400d0119410320740c0c80000074860b2031800c01e41c140820151482900c04550352900480c192000340402e01c100c40141c0f20031802400c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 413911420 1250 413910170 413910173
    0x8040506181b0102100906020d050c0c030f090307050604180501231c020a0f0614090a03020d0809040603060f1d060a0f0b0301020c0618060708271501150c 68
    0xb00d506503450311920b058014046200c1c1c6074003d000704035100115a40400c5185d2450074028042c0d030010103010207040c40c140c000707000351140005584805410100850070708204200400440d82700040b9990301d4072a0070340c000340554600c1d0060001d403560303214501080d0707180b011510036188103800c003400000e00715510245e0703d09c011480a18005007103900c1156007a021f005210002024840650071000206000c5002402c10030342c04205c4081e903685000c580070404441081c0d000d0341c10402c3e4072a9000c08100003525040d00d8244025001d4030500346011031840014040304c1d510751007100c03080c4d195048980300005a02c00c0c0010603040343d9403641188d840c0020305484000003400009010fa803894440b841a250f50700c484680207024000315594130303001d0b0142d03503200c0d01100d070794220301e065403c203c1c2d60b40000f01d1000d019480300e440300310282d00d900f960320071201403000010200c0500545105041c003030401001d10141030109186000e07504203a040c0c038650485104550900c0380a081400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 413912670 1250 413911420 413911423
    0x9030706110c01050328020a17010e010b0f0c010e0d09050f0a0603110f13030506070c050c040b06072f01020d080a091703010b040603140402030a0f06020903010c0804050618 76
    0x14000c80302440c004c0d9881d40c94400282962003001102c61602c24403909410041078103034010030780c000d0b003034641c24080000c1d0004090b000d10b00340640144581c01800401a4006048c00382c1498011041c0c400c1c03c240b280e108842c2103403c01d61480d82180c4c01803041c41003813500040380a029100941d210000c086211b40403481c848103a1182004150b078881d8041c8c0c0641550007500c10300c409001d0303280d9403008201c1a00c0c007002594081076455000352404a022180a002c61505e0140e01c0005080aa0032000400000300740181025400100820420380021360b94414100d82c203518111032051600c0c610303084281e110078a054241590306c5505940c11090300302d80c01c3c0b07074032001102c008103500105241182e80004221000c3d404000040000324030034a0050140080c1c4849a03010402141018000282584140d402941641061010b1004513018459031280d0500500d000b61812200d40f01003400c407403451110b07100060503036003840100701c41401810b070011420300a90b0300e1180040c4032036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 413913920 1250 413912670 413912683
    0x705090d061b080a0b03061006080402010c211103090109121721100509160908061513090507061206210204200f0702040b1201020903070611 62
    0x8500c954500c54018042002980000701a5094100700411054205901030141030342034525140d0301d401c200380100c213820000348040c8a811034260300d03880c291400509036401600504140c0c104000c0313a9000c3d000c2591a842040b464610321400145031898000041040182401c1120742c0c1d0410040e03000282e034030980403000d0700c0752111501d0281c0c60034642500304800400360301402c1007000c6440108404054800c010912a08030054016940d1500203080b0260b640541540030101a000c55840c1342906d4030010150300c2d41c1041002c80c0c0d00d07810350910b085011200c8090f074016012215031107041520b10341c0052107a4100c00d1264181e507a480980b16801070080c54104198619100209001c0303402020050074a159014082c6182c1c0310150041e0744000801c0e0301690900d0104505c0715030780000414418480c04902e8140506549210b400d42d0007140107a03482501e540c0b100c6041d64519036090307000304800d000142c0d00d003051000e0506001d5076500000901c404000b40304064080070490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 413915170 1250 413913920 413913937
    0x60f0f090e06250201090609050303090706020307050319030e161a03010e070807021204090c0f080f0609060d020a0b0a0e12030a0c1e0302101a010c060216080f130506030705 76
    0x504032100c000f24101d004203000c0760060b24260030445200b0a003d40480294000d241c0b800070350340035030b48072081a6030385d104107900284103900030031504900103111032900c00300100c0707440c011804d100b01c20980c80c0741816000003c8601d803455a410801000011041c02d0b0544480d651142550324112501059940050903082030044070000240c0c0c080c42441203040c42c0c1c2150082d161915100c0d91403070001c054110104001c908019484200719000740c03001445403070a1007100d038140e0784260501a5000340540303030a410803828840c000050392080700c450040e01c42d5940240c0c03101d1100d03400130b022201c01507013140a1000c112a5440500000c0b003124400351b61414150010151443e248040102a24050b41c1203c880c03051801016030100e91410326a0394002e007442450403040ca02c0500041d554800e9000c0340303c0c0409000050403e802a242d218a40c020210410805841c2c0c1501c0d5800640040000000054074403185d1255018040c0a000151003a80c110f240802001c0d045119000c003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 413916420 1250 413915170 413915221
    0xa030215030403090b040305010203070f110d21062702070b01030b0408090a0306021c270c0b121602010614011b020a1805091b010c030201060f0f090e06 67
    0x41c10f0500070581c1500500214030540e13941da687e405e200d8000d40041c1d87c01d1000404e41d00a11500611030440e40d91406040405450507100c030140c00c0d600a0f40c0c0d09040300380e1801031403088032803d041c1d00c80e1000618210398600111813100724003410366440940c0c3c01c000c41c1d00c1800440007140401c10000d0540b64000d0780c280b5035850300c0c103103214107010b0240b07410340c480080b060100811505402a0a00e8407810744d11000c0102148094001d0b10411080d08982e11008a09030395803208100c5000308440c0102c2c1a8200c240e00c8200320500c56001c0c01c1c800b940d04e9503030800d01c508402c0d9200070000d2000144001c000c414100304032082c0b181c170005075190400c40c001180529803c40d510070440c0042e8003c19401009580e400003124800002c40c0c1411458034080024481c5540418001e07500040c41d01e031803201000103070065407071000045041d4110b640e038000200340e4038003021401c0060003104040380700f558034081000050b9658441450440d81081c03050110400040c0c0107107041203042507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 413917670 1250 413916420 413916427
    0x80a0b07080a0209031e0105130803150609030109051f0203040507050609060d05010e070e060c0a0219030c0303020705040507030b0d060b031006090213060f12150e0a0e07050a030215 80
    0x299200113405a9125940c0c14000c030300c2c0130190f105031148401034600c0210024003a9503259410f601580490740340c00792401d08200001062064010b145803004000107021609003030b0b00c64040b82c21a0000d04044406170b02c4040d05251112103e05800d20005466005501d945850f03034519456440d28810301d40502400705040038035a07a82e0f4152440382e51241c4d010001d42d0b85d01c8010401c4041d00791050310200308400319900e2282884002c071070840d1b01c104c005244c0100507070b00f80711441042206540c40c0d100229400310008082000c8100214080d9000f054813a041104000c1103850242120b000c0c10303d408007100b9951900312404c0034080d004000060045c8076040402d0504641c078005004491138402c0c003041040c400e07070190001c101056502d1340308c1d0b40c8510095075902d4130b4240c1100400c00d509880d09402070b190300041300e40340c4490400c81c107081ea181c2c40d40305100f03c141d404507115a160b42da043c1020f141005103c00038001219011209445d58011465527004003000144c24800007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 413918920 1250 413917670 413917681
    0xc0a0207051e030f07140d02061602150d05070201110412020904170a020307110a060206040b1e090a050c040c050a0309080f0301030f050106090522140f0c0901080a0b0708 75
    0x7240c00802c0010003a040c0d8038400c0d08083d1403502c5801c0da008446880d0320b001894030325410008050403280358040d044a2401003040300f80452504034107012a440383e10451021540d0240c0005000700558601c008502da04001d00042d0a403000809080000740d0140001c210419000b018000366903011748641c901e64845080002c0c003080318509000c40311500007881414103074008001c09031140690080808140c400e0200701d8a00d005202c1c040c010b81c48680441d000c038a10074111034101030351120654151500182c0c40c0c1070f41004590300800754101241050a12105000039200b004084804102542e8074900c007409600a070485501003503914030003101004296070846030507841040042c0e4407503a5030b1400c0240140010000c40d135035428075800080c0b04c2c0f9580103c6000d0046071980c544c203041c1c048481103449009850036107900c2d101e55004200c1d148140030301d821401041c800703080400c00e84002c1c4032042d0701c1039004070301c030fa4404107040340490208042c0940115141c901442a902c3d01c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 413920170 1250 413918920 413918959
    0xa0503150a06110c0411091e04050a0222050a0b130503060423031303080d020915090a050d120810030c060504140603091b06210a050c0a020705 63
    0x8182046030071910700d840210320b041d042038810320340f400810100d601c900c040400344004c1e42d48031080ca40510905000b29441850a0014038250600d524542004a00b0b0700001400361034007920240c40701c80d0b000503803000c3c00030101000000343c0c001081401c1400d10f000c010640c03c07010313071103082ca8500b000300b40e40b031811400065801c000c08005084030381d14145414100006410031081c04030002034140c2100703c3c1c90002c000d0f07400c01031900c28012005461621503800541c003800141c1e0a1039800c001c0c1000640d036240304d03807150746a000c0103903444074909014011180d00030707042039105901500c0110006010740e610f140100b0320a15040f480d03511015045002100d040c2c000610036078066602203107071b43d44003014008840c0001003182000d6614001e000c4035101c250f80780d510035008082d40b146c008944003240c00c01303908060561407600c0f5952000d014144110a81200c0d0300c0e070840144412030205008903900092b8542ea0176103440151800655500124071030b5500500c610440111080007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 413921420 1250 413920170 413920201
    0x120f09090501090b12070807031115120108280f020607080427060305032a07081c020c01081801060e04061416051213050a05150a0506060a0503 63
    0x940080c1032245584403120000500703106225580140c0600e9460003070424002010402c0710382d00341c090000142182c482501e00c019108605070401c00d400b5814210002050040450040404200c0b5480d4100043c09041030785014941459501741f85400400da0342c6032100c06121903100440c254245091300c081000c40c05501c001401a0b400860700040c503680c052034847c038101c0111507055820000a04100c111245408050195030050001046440500d41c0d4500b0400440c030351401800441c66800e0303d40b10f6141c108100c0f6800a0406e0300102c3c070f100d410400d41c03a41d01e001403c100c04d5480300003003030090010800844c00c80c52002440d6181429448840500107803001c0d0b4000b440c01d810400082c0c404802d20ba070b1503600110006502802070500d445014603035555040c90300400000b80c1000c13500103080401d401d140140e40ca400660200404511584150b000e8402401d03100041e03004100024650720101d810b0604006031541d601044500c15045400c0c1710752607403504e2403220304842 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 413922670 1250 413921420 413921429
    0x1020f100203090a0501090b07030612080304060b010903060c2c280302030307080c0c0405040b0601050a09080616020d090b12040615180b060c07060e010c0f2d120f09 73
    0x1440c0c40c1d45041030200206423903105141a443c00d01609541e00c0f6440305982c0b147c103003d804001c0a0001c01d00180550300028440d100502d003907440c02da12a00e907481125814149078002c9038802d0400414040320110b641c071607440c0c140d80c06c842c80400c100460316001016420207600750523540550100b0645540a07009103801608aa40b900d91500d810880b51f0b11040c240283d503c181c249900441c82c003400b0386440355038006000c159076200d5400644154100100420a0202c800c0001c035070914104a110300c5a41800001d045042d08407202034104001d140891080015003882881000340c0c02e02140c04111200c510518560b172b49051800040c030b0180468040c0e46050100043c0000300300c5070009540c00740a9082011160050400100f84200c0e2000342d02504400c408101150180724200c0d00700300103040040742100f850340c0d0b00c0040da9420f50104c40c44442212500c2d0039400b03c85102c2c40b100c5001c440b030000c0410644411a42170b08181c5010100070185225159403407003142c00300000c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 413923920 1250 413922670 413922673
    0x13090c1215030b1f060306030212010e0d1202090310090204140c03010e0c190905030d030b0d080a140a080f010605040e1f0909051c0503011805090a020d030c050c01020f100203090a05 80
    0x5d4803050f0082c05444170b80b10a901c510344090080031101410b01c2452401c4d4403a03c02010f801c0e004c90000d84c4c0b0500401000c1c0c0b442d036800e100c0c1e40346035101070010400320030204a0018001840784100800c84482c61804c6003400400000c1202070049002145d0540340c501e230030080c80e50707903010300f1590900c20301d2512407440000350100a000781c3c0281e160b5085d200b04405450a46001d008110308464a0311890b52b441070100c201c05000c40ca0b0003004007240502da01e08043d60200444105616034000c0c2040c0c00000d2130201004100038a00710000e026260b0751505900c3c15180440b007400325003000d401c07442c2e00100c00d140c24008155103800c01c0000e10304d100d814000c1c078049003001910f4005164800120401c80fa8105d20300903c00d104903030581d11076003840034403621011b450b200108070061042245118010249026948621500c9040c501c40d649000b0440300ea460b0031800c0107100e040c0f49046d503000045050101d003010801c0d05001c0508400140c0f255104206c8501c3d003d104c040180c4107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 413925170 1250 413923920 413923981
    0x1090e07150c03080106020c0a0504151a0316050301060c081821070f06090e22111008070e010309030e0d030f081506040603020f13090c1215030b 64
    0x1294000350000c041500a1312101140e0f0380e604d00507611100403004d00e5034001002c050070301103440c007513108103002c0d8044940320b455540c88800c178540c0050325414103601c0715404030411010880b80e141d906d02d8400c462814500395450003d0103840c0b80c01d2b40307000414044012502041e40ba8a101741e0342424003004113440c00c030b412107447e1044060f900f050b811260b170050803030128003154403100702c4c030444016035602544680341007000b13401c00300e0103001014404403042c2041030303002c0b2006031120018000d40c521410003022500700940511400900c800380040c1504004106420000ea05290309080c00d0100d50580d440c54110303200d600c40003041e42d010600a070180c051550110740403a400c441c41c1c07100e10341030f15818502c1d041d0324040245107901550420040c17084d148280c000c1c002c846402c040c20750500040c40d92290000c0d2060b0085581e1954500c084010300b540840030240302054030000f004400401c000c2040c400031a400090100341d810004102c2c04007110501c3d403110010034030308450 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 413926420 1250 413925170 413925209
    0x8041b0303111005160f09080615040f1e0b0402040e0f04140f062a07030f02061e04020d020f060d09020109051215070905100e0405150901090e07 64
    0xb011031080c071041070034425090059050700e0306108850040000ca01c4501c00c4481200c003c0328000e2040c0317032190802c1012100010314020030400c541c042c7c0381d0b441c03403c0d0b040040b0300240400c03111210026a5014205411002c0784821003100d4000f155940b0400315000d08288003003400380c421641b000801010803002c0012003100c2003103450003240b0032000c20703600f0901d92214070b680f40c581507030043c60760300074002090301c0d1011210250804c00209402003d442209260900581c00c541000d5010406c29000c1c0885290f051082c507600c00c8125050baa0310040d0b2034080803402e130000b070000b0f02400303016503440259660f12200d00101c52004120990f90720114903054041c00d0140400c0740403800903034000c0703007902c1c1c03019110020820140041c4006000b28a0b190600800500240b06021002e030f40880d880c0c0f15034a4816640601d0303121091440d08a0050204440009000401800c08065441d1030703a40c91010031030449200107800b040c180c001d0042c076070a0094540c030640000c00001440380c1c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 413927670 1250 413926420 413926427
    0x40b0a09080105060d080a03050912030718080609030a140d022b021908040c080102040815090d020d2a03030c0813020109120602190503040c080a0203060708041b0303 73
    0x8180c42140700240929142d200900ca1481000c207401084544180302480e8402c0c07003603001c070360721075075400c02c6410740b9050040c03450080e07200399005000075031900d0756a00e20152908a0703800505510000b407030b46d490408021a00c0e4025079903550108242c08409001d0054080309861129452003002c41d030b20000e07445c078043c5451044c90390703940d41c4003100e102c40c542c06194800d50b4806010482c0071144e40d030741404200c4104000500894000708041c2000c504d0203002d10150002c1c094040c01080d03403105844e031001c103580c4020100901544042e40c5104c01d190302003000a00517106080600c0382c1001c00d41c15912a003241c1d140101d0010b014a415002d1682c10340046070030388a1920b0b211015105c90810a00a102c3c80c80301a021030351550381000b0300c02c141c213004000d17140901001410010480410700200005940d040c001945c04030901003448080d110810081039004e0040c100d47d812a400b2a440d1600140901c2c1400300c283c0c001828020504d1500b140002c41c0c4a000355403a0301c030318002c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 413928920 1250 413927670 413927687
    0x30f02120711070b0a05030a020307050c12180a030510021c0c0c20210a05060901050402030705090403090e0c04030f05160807030c03020405040201020312010605040914010e070309050102040b0a 85
    0x1aa0360b481900310000d070a6207440221180b01c816580d640c1d180d640e232198040040c0d030000d805081080400c0002c401d01c4501809114a1940340310020303656402c140740d101d41c811848420070b500c1112407050810000c1d20002e10380c2090b00007044056111000a60325842d56440c2e400c3c201045410f103400e0303000740c580c85035002c820300b803288459201030746041d500c108002291410f4103400c100c059202c0c0f1060303003140c0395240840e002a812640d0500041c1e0ba07160810b0400d444d2018183c2d141e005100840c6401c0c403a55014010645070680039182075100103100c40003078400e0700848030b9480c2c003140d0704d00c01d8003007102d01842c0c100f0028104200303230f454000d9903489400d00b96801510364120103d6101004210403040380d4004040220071030071602000700a04010308104e05610082081c0040c460480c1140c1d4002c00081e03d0381c40d1128605040c850030340c3d1104d09181c6c9000c40c10030042c840b85d07459081141c4c001c1c02d949000910b4010310301d4202e0080c070030342d00710f844507160216501d48030b5580407806 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 413930170 1250 413928920 413928947
    0x90a0b06120a140c1c060f0305071703091e060423090604060501090b1c15030501050609071d0a0b0f070302010e030301080706050f0d020304030e011e020d030f021207 73
    0x1c02044080380d04100543c5426a0b0303142140d42c04001c000c2c1040c408410341001030080c01e00000e9415070f6020710364014203056004031a503411480040010007200301c00c004032034035100b01440c5031403034010004900c914515150002e0901410034803190fa25400155000751070b4401358031801032a098500360030020748030541d510468102c00080c2403400c2030302400b0100c59040e12410001400d007880034038580c1254900f2600c04210840e41da001c0410307030080b011814141c01c1c2185000d41141810f03402d50744020085402001000f0500c201958442040b241d81c945d1001c001e01e0007490314000410a1140b03504c2441c54280200b030240c01504c1000c000c0104903c69002001000c2c0d450340050744070b0100748034404007908410000c00225008000910a648407a04d91518040e16140460304a820990b4141d0028102d5030701d51045581200d90001400c26100c0d40002045903258020b50310100004c13844c040584444403005000900d170152010708600c041c01e0b08151800220003002101009203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 413931420 1250 413930170 413930191
    0x50705191101020a1203021c02040e040510060b2a0105010321030603050c061606050a0603060b090405120c0f0a080d06150503060f0d02060304030c12030b060702090a0b0612 76
    0x210003910341c000a88040456400040c1d4217182d003a40c44181c0003500306210044e440f0394000c955004050340c920080c07029104a400488070380c01d040c00d040c1d20302001c840c01200f11524094083c000000e1960a44844580401880c144c84200e1328581c0021070001180001c29800d000000c41001444100114084000e1001000c401c9002e0400c80585042e440b016081e070300454030784c10310741c20301c10002d0a5490080c501500c28803103035074400b005c89a00300d40000405507184c90900410205004107081c50100b00e415880904282d2241511011010318900c040480007030300c0790130f605051080808403030184d81500d11006241c1822442d550180c1d04c1380401e58544000421040081072041d8003a41c01552040c5c25035907090188241003a800d40065807104290704080c0069840c000154442c43c8641c0d911140404545804031000e00d4044141e800d141c20503101e5101502c0b50310654581d507404071810004d90b1940e9001200804000f940d1540018002504a60710300c900c8000344e008541410 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 413932670 1250 413931420 413931443
    0x140411030c10170c1201030302010b040516050d09021201090303050108060c0a02070311041415030708030306011d0f04022b051006050c1e01060f0b1e0a05070519 71
    0xe003000589520a0110004030b6800800b6015000400081e10b600580d01e40c3c0845c0b51024404001d410a1400d03881200140e441e4241e030142800c16010300d680000c280701e00640c00c103101100281a0740218180364034600d544141207010740d9201c3c882d000c1424080002084143c00394100103016217002d00410001c0e204079404541170091b00d104035081c42c940303680a41900c0d070565880380707910308580241700e52280d101d48400f0b480f400304441003070040c4d2218028000703090030390003803506003580c0f40c3c00325100750414000c100e851f03600700150030302021840c000410504081d0b0000303603070f4020b5402102d400502c08611010480340b641040d0014418000000c0a5688502075020170b80310102e607441c4c110181d54100308060390080018000c610000c10540c2c0c2d0700c5000c1350b166030380900c036803110420700d1307441d0581044482d2400004c40007610804c0c40e4203181080c01e0a5080e046031519142c12503c81d400111040740500c52419075548540c01011b4034081ca003800484004081280b00075102c00c107418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 413933920 1250 413932670 413932693
    0xb070204180b010308070615170c010809060a091401092a233f0111090105130b040b07120302030f15040902060d02040609081b040c0314041103 63
    0x1c901e103000080d0301181d1516140e0850b5106030036a0803404040b10819210120003002503051081d030009040e00b41400e04451000194841c074000d05414590f0601105006001443c440441e800b0350020142c0c0c00846d4070442d91400791800001c440070b549981d441d022a44040004481c0701d8a440555044c0111100c0402c10079902401c5172449010b41442c0000301c801540464030400441c1c1c1d00e8024014841d1075041050000708000c3c0c0e460380c2061161200010007110030310000c240203e16104000c21005016a280d8030461003090089070522030080b50400d115066076940c000500803039408030361181e0ba13481102415810000048400040280700c03503011511920036a481906108407103030564030b414490907501203a2800711504603884041940140c0c8400000700340c2c102c144003005039107074a0540c00500401c070b2500412040d800000101c03884a40056000c44903840840c1c00107034403a40b0300da0540042c40d041103403550b4909060100028030840c9103001c0c1c501d8400b5410341e589080034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 413935170 1250 413933920 413933951
    0xf12080c0c030909040c03020d0606080105150d0206030901060f060306060e120a0b0a02191106070c121805090705090a0603060f0e040501061d011a0906030117160b070204 75
    0x1041a540690381c010f00100c6081e01c3c12120740b0780c206000d007804074106501c0c0c1e0049140c1c1d5400c0c14007034414548032441005121401d200b200d92015016014a4102110030700041d000655610043d00c02d02c40800441e10801c801c0d070001b40140006184c20f80740d41d40d6000083e002c1d102c1c0340b003408007080c0495001a039904091501704408030840b0090242c5100c1560b4000c20343d0405031002c000aa801d002403003100b090302c03440800340103030340e202c1492006801121620f4020024100300810041c2e600da940002c3c0001064404038189083c96030b52030785910f003088003114003a440954030042605c00d00120a0b00203005240c0d00d002941c036100055250701059090391110b214a022909108500304600711107180710a4103c1c0c407400c000b281c11136442c112001c4082c0d00d4140c0901c68400741004101b1000407100c1d4252003030060443d14103100824000586e039000510ae1a150a448109103248219060141e21145590485200380c8030f80c403172003d046c25810603101203028900c0c100960810b9440f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 413936420 1250 413935170 413935177
    0x1615090b04031211120703060308180a050411070b09031204151406100c050a05150f1501020d0804030e1201020307020d020a020d080a02030d060806040605010e15090606070f12080c 79
    0x8002082624105d0124416501100010007031010141c1d607a401000003621400200421100b1141c240a007a0f04101040500140b070340c0b00c00d07c20752610a18481c11103140c2c2c269201b8503001a0050440e43c0c803020154291300c602b860320b10340300e1640780c02c020400ca1480300403402045c001d101000326450001e41810440801d4822580c890501c101d207001d0f4230720403200903465612900a4450b906d00b6941e80c14640182883d0340031030350791240200940343c15003070011a807004841510301c3c081550000040d4643c000f0781e402d07038100700c082c4000406050040e4400582007030040c24404122401e103207614000d4000360f407032500501401d460b420110b480040c0401540750028800501245103540340c840940c440d00d41402540820b00400030648007910039480105065005848c0d81c4c038103443c1020444d80141c0001600c6040107091180801800b145c51048580c250f8101c030140c1c45501c0018420700503014000e204c010008000010050800403070b041818881d04d03010304584600c1c190038103600 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 413937670 1250 413936420 413936441
    0x1090c030e0604140a06050a02090f0907140f12091609060501090b0a11030a090305010c030216120509190e091f0c180806150103060b1615090b040312 66
    0x90110b0b003c07501061604500c00445080b2400703c0b81c1003040f90303580070300b17a520071189007801590100304030b201c0f402c02c1060000d03000f104070340c0503056180200e80a002400d548900075852071000c0b03241383c451b02100089407400850644030004600d4110203296031307000602904101e5006a000000d5800b002d8005c5400342c0710f058550114550420505440c41d8010046807410455806c03503107015904240018030661025a803a03903541401c50410b10b0a4620203102201010701c10004032a040c4150400e9071a9242d0000e0344912010142e2000c0340c00b8010381281507030100111035080400005180007c0031501e02440a41540ea600001e40d511807200e8281e8000340c07031b82000700c03880c0d01e543c07a8410040c52147d828540c4000d208041d00701c1e82c1c0710251b0400b80722540000c0a000d18a044c0303079480e12148bd405d180611001d400d001982e445400348038200ca00f03561003503011104000c1c82489504008200e41400c2002c008241403c001c4a08141c1d01607001c40c00400115030805214095400d904 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 413938920 1250 413937670 413937673
    0x3110f1c08030a09060c08040605100b03060f0109031203060e13020114030405070b03040c06021b0f0609030a14030715092303070b0103150b1c110a12030801090c030e 73
    0x30100c0351180e03036180d030008149156503680e800a03040040c185104a5589802958800340a0325041c83c000080b034002801c511a071242e000700070003444000e001201d0b4401c405071007000e0812810401600e000780705070401828000083c003000c030101d501d90300030400c03100003030000005500e8054a15010320b01c494070290004411221066003451040700454026108a0445040d25994005007825410544003260b40850086080080c00c0d410080d000e01c0c0e51309442801018800c00e0000b0f07210896010078030b400380c0310200e6583c02664051184507900e64100002c9030303000c0342d1100925125484140c0032203c5440b1803c0c5c02001c00c00303510030950f0181d8010080c40001600201c440c505054034a4901660300c810001040000d034660b500b640214031440e001010300100c1820031040d17032488070306180034014080400242000c00fa094401d070310b410a1070a4624501200031807c0c40c0640d0300300042c41c1c03a00348415000c050b8441205c904840c0312410802880d801c1143c00c42c00e42d020709944c800c25 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 413940170 1250 413938920 413938969
    0x6050403080a03150b0d0b0f09090619020904090606030b010803030106093606032013020307030b101107050a080309010f03021b070305060f0403020712080d02030103110f 75
    0x40b501036801441c0000e0740b0f10f181c586403a40c404d02c0340b106501041c94841d445403a10040b04050503d2203c60025041c01ca6007211180781211000340c0e2108010400b102c410301e0381c418200400d440b5812140801000391041c04400554280003004d044d403480704036211038881000042811010080d030f07042e19145e50703a11403031619003402026030144500c5240140f0306500d50301900d21010b9407c0302e01041d8000004100ba52450400d030503105484c2545805400c0c05410380e108a950b80c0504244007201d8000042e200d03114800c04500034003580c030303002d0b402c0104c07a01c44402c4640c1101d0310405040d8000100d442040c0c58005014092059100b102c1c5035a20502900b90650302030b0448207220407280c940142000f0360060000980c0842581804c3c0c0354000740800c0c8103000c4140311003a481180c03213501d80e456003001d580c000e40d50301981c410300000140440c1100d04000040d411034000340134284c401e5480c0d5840f03090520b10780c024140030f54811344c00031030345500303504040100a88214440201088 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 413941420 1250 413940170 413940187
    0x1a070c030e2d1e100c1109010b0712030b010c120c0c09060303200316050316200102010c050d0b010c0c0909031b0f12020102130b130605040308 63
    0x102044241d400607071000740040e40d4009101c140758420340303100400c041590455294001c0c050400f03043c3c0c0071007805200c07414000d07119072a202454100c2c001e59151010a01086060100a03d6140c040343c035440500c0c0000068403106400c0a408103502520703910720601c0ca8032406400300c6520111440c0820380290143c40400c9031507070b16052400365401c121030091040e03580c0144040c3c00b9044800700343c0d40d400c0240f0606511180f41c594015240520786600d0402504482c0d603801040395454034a00c014100c082002014030a403440c40f01c01c1d0012000c14526450300d80390120038000004680c2950700801c5150350f20501803001a84416241c661606096001c0d04000e444081542c1e81441000044040000c00c22502c4a0041440c000d00103815a17491600801404620041000072514010607501064901d0220415160f02154090300c0002d01c4200ba03019021f402115250356030b40e46400902211000001c20491a102c001000b4031038855000b40c034680181e0201403d0200c06012428 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 413942670 1250 413941420 413941427
    0x150108330402011d04050901020c0c03030304020d02121c0906030b010f120213080a0503120c070803060d02150307091505040305030912030408070308040609170c01120b1c1a070c03 79
    0x81c0a800015140502c4d071280c004503007074542c1a28100d40c542c0d03000902d0940084c0c01e000800001704200c001c1c1d469418241c00241c0301d017514040180c0300b08100164024508810406045c100d105c01c3c07100d0b080111030035809041140e9a1040e2404a810075000300099031142641c3d42c415401902c8a2215a21100700e210080d008017400540201c40b80e240440c03201c40800c4070100046c8540025907940c03040005074411003501911713616545000b40000d40010304650240ca92110064600d44850390f801d00009150102c401c01c6510a003d0020a11007d168880300c158141c85024522402c058005030044515110340e00c006040e40c2c0040c441340d00180703066080460840d110400f1a414a03440d130b140d0304d007810090340c0100e581e844001820442c5a8004c110100101000d45910002280d010003203a00ca003946090181003000c0a9124803c0300314039801100bc4440c068480071450314844244081c2000d040000e69540b480b0300380c070003500305000710f4451180201c0d640d4030211349c1c00b50344c056 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 413943920 1250 413942670 413942687
    0x4231f05070f052d0409051602030403050d12091e0501110906121008010507170a0621020d0c090e06060603070c0206070c0b0a0801051c08040b0c15010833040201 71
    0x11904416642071070f400300c070321310300648040c0000142c001614200040c0500c5110680d44091042d908140800c1001c01c8011580071079070302d804e040031800d8018040d0f4600090103030035002040a010509100100d001c1a0203034814580300e01c00070881c800f0b00b03052003c0700d070249441d5698080010070041252840b00d800054000c141d074030100080c66100c910b201d0a54404450305400070304540c003500c041c4ca41030865607403c4604808104442801e210000c1d124540c5886456109501c145400c400c5490b88905141c919812054405040340c41e40f41c1c0301c000d0b10301e41c04c04100511801380440c05d01c0c98540100c0c0e01940850f00c400c582c0521a07800d008c80340e04070030340540d10202d80481c0010b4640c1404014110f80805c0d80d40c000c0ca82d0f05050403c0f00c00308441945480c0e086c0d1600512000400b000110303816162000011512015844005840c0c0220f5078000c103400f15420b0300010300f18100040c80290703080381c480b5800903c000d403c151084034225150b2025a6219400443c0155000d00041c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 413945170 1250 413943920 413943967
    0x6230102010b0603070507120c02102a05070f14062b022a010213091814060612030f03070810030f0c0f060302090904231f05070f05 58
    0x1040b031294840000d4082d80040304c80b90081034001408908000008203040c00c2c50380d0074185029180c015401203604000310303400850030301100a040c641c1c400120b020780702640a8481b003d2844c5440b501d030a640304c010a00c40c0c1c5428403a1000003264903410300c40502440b4401034520360030241c0803a580100c44400c0302042c034029542e49941054400f8500081c041d4040201645c455811070000c0350710201916180c841d01644140221040c406445030001f084542090740030480358100b5080031030703601940704005d02d002028540a14500000b090461199101715948005824590a0a600d030f114100300701013099020000a0580350107004859003000502c800304170311545a42e111b4404114204050720000b260100812544000540c0070002e4403036480c0c1941090145400708002c2e0700701910080c60840c80c400300c0ca0a040002403070a204007103131011070744181400046500b6205d00c80342025401400e0400181450340102c0ca090030f02c03070031036440e10300d005003d03500400d0185000c0754 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 413946420 1250 413945170 413945173
    0x509010c0609170409020301061d0d0b0603120c0f07050409081615140612030a1416061415010224190c17011203050a080c0f0406030b01080a06230102 66
    0x140400f15010800900050444070100581d00d50410002501104588109002900101c0500001900c1d8000000c04440d40444032181d2520b0f400c001908000103021603010304c2c440495a4111840c0000300e04500d140b0030f00c1a1070240340c035082030000340c9904100242002208003c103a07841507a00b8141c1042038010029042d103402502c00d504103883c0b42c018001318452402083c02898513114082040920b8414000e515040210001500392a183e5281c4c000303000000c2403034500e002c1d403908442c030b00d1540700508200941004c4072110803800c0c1928461100c018183c2d1191255000003540c40c84503a1100210090304280d4038800350170b40009000041003017031000f0011200c00310b0f010f0108480c15684075905840a0800742440001050b842030440c4550704804801180e00b1004440c01c0882c245010203c3ea42c03070000640c807520030302000c010014000140050100c0c0d141d48211080c0c4000d80c0c0c1c15142e03440d404c2d18101520500d0240c0840000c000d203003800e4410021002c095904410300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 413947670 1250 413946420 413946443
    0x10050712020f1515010305010f05010309030e10020d08070f02060f09010209040903091a130303080601020a051921021018020303030f0a200702010c060e2406010509010c0609 76
    0xe00504054581c842010311602942c02d103c13418044809109a151082c42c0801003907240038800c0c00d003c0c00360300c40c1d40e05240da00c0804000f4140300300803644601d0406000c3d0428401044c0c0003c1d5108500c1034030038001a5840003003400c0341d2180590142415643c0e0040055844104c4a10110140075029860741d650030401c41402c1d1721140180c00b89039009898801ea02480d05481c12064405d040140e811003104000040b00b440d0a056602d003529018030700101542e68400041c2d1400c1c102980c0035003d4800d007003880d818418941202584a840b4090402920040007654000c03c0503048020001d60401698506809040c1d80040d2284010308284800b02d260343d00840d080d80e1090b0f8400b01d15120050412111046502440709201d225800c10204c0d89240c038240b440d24020224001d04201c4525031350740c1401100c2e00701d5004240d4020a031040c0703100c4540c0240100c14240b405480500da041c000500c290f0141d030540703003082d0040e110000260700c940d07503c1d40242041c0c00308540344100390 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 413948920 1250 413947670 413947693
    0xf0604111c050114070906080103110a1802071b06020c15041a03061216061b020603090109030e01030e0c0904060e0109080a03150323010b1203090f1005071202 70
    0x480c41c80450782c014000058642903001400c42c0e800001400181808002e0104200182e44010400c0c1102d070412041201707000c00c2800a2038810803580525039010415041d00583c81c641d070300401005104000003081c0e07040d094810b40001216115880c007682100740030b0152828820041080302e041d04070110710300341d1200c0f51a0b030b40c041042c54620881034080b082208a0800c43e02114030320154400401074044844100ca42e20903150081b14204060880c9180c840e20384181401c0072164020412a200d28110840034004d0802d00400e40000c0c0c1a43d41405140d4001e11644041080361406804c800301590107000b4555400340040700c81941e60305948014030b000b881620107842c46404020385d0703040004802026110112003010b03403d00d0580082000550f05004100e004003004071072514406030342043e6004007603c1058640020501c0d00c201300d41e007070105c010818a05c04580c5502050066401c4c0403d07420b41c00301003000701d01d0401520307010822412090101048920450703910b11280b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 413950170 1250 413948920 413948959
    0xe0f01020315030709110f0d2a030515030c1011010603030207081b011e020109020409030e040e07030812061c08030f06060a30140412020f060411 64
    0x4640d003059800b034001207050b46103030a114000040015840c00c0c44410410207210b66584125100300507514000200301d001c4c00255000060034258881030f0801e04c40b001e1519020303692070480d80c0e070002b0785070a0000d50042562501c81050090180041070160601e00911241d4004a640c03c000d0000c1cac9034000d50200b80902500d07014501c680e0203454814a4003554510b003031280841c0c0880310b030100b41120001d0b68031103000c05911444558a8820029620059004141500d0061341150030035065400341500043d0118204406440c200300c2000c01110342e503241c0c8600c1c040200000744c00c001402e03041815403c1da5401910042c840e42c40400b2840c0c00b20001d600600040724803010101c02c200b188510381c442c1581c0510140c401910f0302402140040004554500c0303801c0c00d6550581300001444204404d090010030303075404100c04414140d007803101060850303045841e130b191050342c80c0c5443d01c0810403040c1c510310311000b051681c4855803840451042d149030350f42c21400f640040401e4911 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 413951420 1250 413950170 413950177
    0x71209060e0304150c0b1501031e0b1201090b041119081c0c120807110d09090506150313080d0c030c031a030307030e032b021b060301090e0f0102 64
    0x440e840115522031400c5901e84d10b0340f001c06003ca05000c8203840c550041070006102e9a4004c101f0541d01c00500480c0e0300503401071440501c00c0501a01101d840b00311800d40c0c1c1e001078548501205e00800da04100b1040c075080e16900c40004181c940b040012030002019400740e83e41c0844014001d0100f40103460b140400b004150303104410359889482c080714003a600f98075220416159240603c201900c80d1200c60f01107211031b2640e0708002001c000220030510400000208051410544070010400c170001000400c2c140521003d01e80f0b04400f091852500366613404100b683c02c040340f4150394a5120304204801d901c0421b540c3c0031420000009009854480d40014110344e850001c0c00e81c04118004048500b034500b030380c0208000c0c603160080342d84c0001c02d03a4200d80e41450003074401302c4400e000c00d00f00710007020104a4029008a591103154400c0040441c0c1040c0d0f80c00c690030200b0071000100341328081c002880d0450000c00c01030040004e5a00003002410b4840c088480f40780301c95400030708a91 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 413952670 1250 413951420 413951441
    0x61d06070c060e030307030504061206030b1e0f071e030f0f06180c02100213080307080a0f0311160615030b060f0d0803270304030503091002030c0607120906 69
    0x6003030324800e01c501c035081511003602c01c0f42034008500307140f496a001380c00c6110b03d0041c042484102e078000c0341c0041c5180c000d94043c1d5802901c4c1e00312800d0030203990310a441c4500c1c3c2d0380091109034000a500b428010003003032050704151b441c2048404814081c0c080c41034911400020103460700c131840c40c0504c02c0d00840c2e50680c41c00d000011007030700d80380180f1840141d4070502802c0509000b00340c1c00c166030000b2007001c01e00041c0380050350b0f241e840c1107a41068a8640c403981c030a02012403031201740400c0304050052070008e80c6440c40c0c28490385000700c045841122125520700402d0220340845103500000070721440c4104000180d05200f01e1000018001d00d0b8802c0360840205410010581451039000380300300000d59007a0108812955840c485010041c00c82810481c2c5080100b290f030001201b07481500c0281d070582c0d5a40c0d4880c2005500d81c0d00014049025840703019400207041c1c800001c0b08d48802e0301c0303000341401c0c0d11000c1003200d810324550b10494095448003650408101e0381d100f5030780c608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 413953920 1250 413952670 413952683
    0x5070f030606050103020909011701150905090706021c08070e210c010c023d03020705010b0a0e18070f0f08060a140703051e0108060603060a060609061d0607 69
    0x50300d1490a6001e844254000904050040c0034045160720340e02206e03415542042181e0300c100c012041d885004089840083d9005a041240021000e50549c8900e01400c0703e40c081d1351403140c4800050f45d0f21404041414454090700c0250ac040c0c520a048a0f030f0000010728088403401ca04070000381d845131040001e00443c02200940c0c45c1480001c01ca0f40ba000402802c0c0304000b41060340008402c14500c0103000740328408600410b05074540c03800800b0340207890718040e0440302207a11340140203422031502202c5641c038007600040b442c500403240404850303c000c00480303d680c0d82d454005104c01881c0d90081207118540c4003203254800f900d4104040d060888002c16031071300e040b1030249800006055410b03401d15100000d03c282c580340200982c000c07c5420f01007010b4803080455944c0316a102c0d40c1c1102c03808548008600d002c000718a0320f0003844210211603141d101c0307140d244c080b96030034450794001c9000000100b0101d03001d00009000d404001e01d07030200300340d07186000c201d02e9444800202c544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 413955170 1250 413953920 413953949
    0x60604150f030f060b09060708040f0303080a0e06160e0d0c08011a0409050a02010c050c04021902010b030d02061b0405130b0a0602010612031b020301090602090414091203090a0507 79
    0x15950520415106405180e800e11134a0b00d021480c03a410301c980041140035000000303102050024210480c0c00608a100c03202c1c000383c3e0f483c2001820b100042c6e82a2042070f080190492103684000789840c01042148400c03c50114140130a882d4209020b8030b40e60840e032540c060002150b044007282c80103084080000c01c2140c2101d1016400844d00030301c19200790320f8680c0403400329900141129980b035083c00c140820780b1560910038505960341c042c0e568001e0001499070700b4107071954502140008035400a20508060404260b2180505080440140e02580002c1e00c241180780450007244401403485203010b0720f41c00400d01d031442d1017140250b0142c40300d04034041d905110004000500252008021060034071212010440c05032201504111643e44041d020302d0310421004c41c002d90041c020801c807411858044080e40110107000d101c0d514140001d880c078821200c00300c2c450217402c4060002442d112081d2019608043c0196006220384040b020002e4020452040070781700508402d0301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 413956420 1250 413955170 413955197
    0x40f020909241003020118091a0f0409021e060d09050c01020c0306040f06050a0f0c17060105090303070204020c1e060919320327030703050a0b06060415 67
    0x484801860303040240b422150810452010001c2040b080e66070902c0c1c00100882c01036410b11107541d6980202510b5031038040005580f4010500f0441e0845080e5500c140c414413250420048400a5001a4201400f011761a082d0061121804448e40f0b00900070b9083c0003050b02400e04440411008454580c02500d10308210f60f0100982614035408a0007040c807031900d41d4481c030200da401c58008000603110004544803c8481d00300c1c6040050149081041550082008225030800909258030517924070105003036500c070394101c41075600060011840d1481d280d082c48003d5021031155070303d0380a4100d40b1000e00102900f0390100001100040c2150308210a4031404c03d00005020b1111080000040c00021003038401c07005540002600742d10529090384125490300307401d80b1640f4690200046294040312090000c0c00d819492040201c1810420307018159180281d00001d409980b00000310800202a521450762180020b421641080d0351400000c4207511014100000701f20301d13003584007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 413957670 1250 413956420 413956453
    0x9040c1404030606140303041505030603010603240501090c09140d0209130302010506030309010f0e030705030105180c060a020705060a030912090e0a05060901060e0a08030c010c1b05070e040f020909 87
    0xe8a085c11400380d498103240c1540d04030014610702429040c4400400041c989176001c0d4440360081d42c010b04101d2500031b00b5240c0c036a89401200f00500442d03d090000f1820301c0291080d044141c10b5500e65078141400c00b0061082c00c50003800d4168801c0100c841d06005848171030350640607010101c1e41c84900a000c0c03a020b42034401c002c1805019038400c2c407000003640e038450308281d410112810425001d040c6800400d06040143d000307160150b00303100a015495200009034025101c400013a901102c0715081004814030604400c2c03001030b800b4400510a618180c0006e0071942202e00300010b08106030740d6503000c401020310188000c90124102000000400b6000682c0100101010484c41c85c00d800040c4442d50180038100400818940004264840e46c100902400e6100102d03038882c424070a2880c068040140d500380024007002488404207681060b41d00a02e0b417107030142401d5818081900c0c074503000180155940641400c2da40d01680b5400c030880c0c001c44400c006003402e20100c400c1d18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 413958920 1250 413957670 413957699
    0x7050709020f040302040b01050d0504030e010e03030418052e06170420040e0304140a0e2203090510080f010f0e01030b0601030603050f031e09030309040c1404030606 73
    0x3018030500400040180200010032101130701e604440000d03440c80100c0c0100c41c18080d452074a00d01c01d2070803003803000b0326030007a01d04d41c4c8000e0240d94290200007400140b40e01c07070146100d0f42c500452125030360b241d1110185c004951125060703086d0480e810241c00030b80400360840c500a00108107020302440680d51011a903a90402002c902c011b0b5414541d540001c3c1d00104034014140c0010303442444030540d03894102e02820205141140d481d2600c0780c04802c140d15400111510605542000094812942c94520b11440c1c04160400040c3c1e15480c01007400c464076082201009140310000c100f43e6038082c1c0001448645a50380345031450560f144407a10a41a00704100080c0d00d80001c0113901c0301042210705603a0720550003001519031030010307170240106d500010402e00454104142d05913002019242c0b4400020041541410919a0f038500d8130501c0040c6405800400c02c0440900781034001016540051520340340980ca48002099560800d0300101c89580d01c464041040c02c82202d0003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 413960170 1250 413958920 413958929
    0xf020d230d0f0e01031a120304090e010507020d03110d02070503090f04021e3f0f0f01060503060a1802040306140108060712060f0b0a020f060108060601051305031002070507 76
    0x20031080650300340c001e4620243c520036507040540301c40d003012650016030940150b08002501d450301847d0290092030310b0b50014001d00c0107152a02030200e0402105020700c50050207030340c0140c10100f000c410110040c048614500241131810400b80c9400c81140c4010410240164007442d159028030040210742d8080b04221803280d401401003003425000c8804c22200b0036140c0c1b54103079495040e01041da07404010610400d00e41000481c60716030490b202180c0029413500002e41c40070a40e103540006003801c4090b1380100e1598500c0c40144074403030140000f15080840100010a0240d84101c0c2629803e040700344001001c1d00800e0400802006024000211540480b03814a5605040800380d40b52402000070007000042c00c0081d4414500390301c1100503100040100c0d0b0015290060052140d02c0141d00100600c51440806000030022505905882030007010b031840340c03607110044582e504044204000b8000e5030300001496901001907402c1e18103500b0015803180c245080403030804015500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 413961420 1250 413960170 413960177
    0x10020106120602032a0301060e0109120c063b041404231203060f011206060504030311060402010903020105030601020f010513050d0f020c0409030c021008060f0402070f0f020d230d 79
    0x1d17100003903514001582d041d5085803400c407a000031b00e480100c942e003210354045404138103401005014808442200000e8560646660729810010b401d410008500d44a400409512145180b2868001c2841c010344210000b08040303105600416283e4a0403030566085804c2001d0381c4e0a0400c00e0b512220040204104c80c01624100e07202c6903c00c201440b005000714865101d505a101c501e80c01400e9174400c07000c049004010041e21000d01800c00c2e4414002900030501d00118661150300000c0c00314407403079042c0d448403083d5185a005441c0c0d508007601e01815401070a0103c4409034003480340701c0c8104012186290704590604160341004c40600003034081100000c0c40042c0c05400140203941b20b0f100355000a101242820100c85140522000a6021080c00700c0100782981c0034220a026003000c603044085200c0103400c10049200320741d0014045103804c03030003401044a2084051049002401003528420540e5070841d40f20280c1100c0751550450f031070050303110103080217215041821800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 413962670 1250 413961420 413961481
    0x1b110a020603040209090f0a05030a1b03020c090406110d050105040e0f15071205090606010905010e0f06030901110705060412030902090a020703020f0717010b0307050f1002010612060203 82
    0x8000c9034403484003c1002c1d004000e9103000c260503403000c0081624422614094446410380351900a8581e402107104000182c9000260107017039202d0020024a01d0b0b140d002000c0c400091014804210000ad02c255601c41c3e80b44088119400b5400c014101d0341100f01c40081c46604003c02c03c0116800f04110481070790040c3d02c801d00c0d038580055010040a1075542401c0c0c10b60355503030112207961101c82241d01941c2003006204480400144090007250240c0b01e0298640c1c54400449034a0010b40c0030a070b21003501d82e020700035400c1001c001c0d0b8016070701000200c1d01e91008841d491b65644819003c65141d442001004207100c2a00a02804003501d454107100d02825500007a0000d20003402e490f85c8641d0000d90207042500070400300900d81400016a0091543e4501c007002d450030001c012580e550034501980310a2402080c5101a160700828036084155002c081c000e04c42d100d100b00000b559a10300300407a1885274494106040f034070400015950303250124015240103805440b000b0101d0f00741 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 413963920 1250 413962670 413962673
    0x300302040e010f120215211503060c0306010f2d110a080a2f030903010c02070e0a1125150c0c081608040e01090b09040804060503191b110a 61
    0x100c81e0998160100e070420f080e1b00c0f165440491a00c01d100188070070408100500500c8540c002003103108003103000e51a14034840e4007080c181c80354000c8441c030711003e0040000a0440d1f010b0700b030b05041484c092030103036125034644101040d001419240d0b1500c2d0f009407003074a40c280f036101c800c00181c4e0b803141c030142234160300c0d9907900c9200d802004803403414865104055200c144184180f03011a001030007000c0362012060400984070f80c001070800c2d00079401d1000405241e80001024400c40f000c485c3d08480d559103084031107004103000f07080c803001e01008100c4000e82050084041d0080a40c9a0100600074050316200b02c1c103481c0c6040c01100075040c0b4a94580c1c950b0054440190b668001c164580d0310246003d010004048040009004140114010480e802c020800a060303802070301c1c1c01c102c0a04180c3c100060301030101c1c0c0080903050b04000c14448a44a180030b19003000700c20200204405a141544c41a2020b4403880d00e605a03062802d56681c5a100d0741c0c0d1003c04164001400d500c0006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 413965170 1250 413963920 413963939
    0x181b030209100807170307030c0314030f1b070506131a070e1003050f070c080f0706140106020109050d03020a0210061e1a0f03060f030f1e19300302040e010f 69
    0x40301f0303028040c030003007484110901d4000c2104542810b2440030095580c9440380c1c00320b21400b008d035440e4945181401483e40084e01490440752000d07041002040c0c3c80c0c0e00c1607184500c0c00f200940c00c80c2c00e21184801010b00792130701e40b031440c0900b1040c0ca80300c2950100d0400c0c0000651502400307402c0504180a11005160180605030068150300d444d02d03600c01b0701d0038850701030320407280d4400e2038000000303034030b010301045a10007070384002d104003019056603070703548124203035168100d000c0c001d82c10100c1d07140c04050103940186005090740c0146c5800c1a034080c05501103881c84c0d03004400b4044a01d020460f4009880c04070340282101da00c6035a50f140c0220030041c2e1500134010301c0034580340000003090040e0ba8400c050350400000070101c0305480202d03846181c48440c80a18128500106603000c1d94401020400b19503000041070201e09421403526051100000254001100e840701e05945081c4a1f0610031447c0c030221581700941c2e203618020030030f440c1c4501613000741284003000006100b510030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 413966420 1250 413965170 413965177
    0x30c122a02030a020a0f090f0b01021e0109020d150c03152c010b0c100501030312020703030b0a0f0f06051e0c070e041b09181b0302091008071703 64
    0x42000c00c0c880e161140c0301091030aa400c2c84060341c411400c240004000c660009000140c442c1001e00b0700c24445582c141c14180c0c2e040488581c0941c20140a911051584226a00c000b06190b0000701e003810341900490210303192404242c1c0c3d04005492240905c800500076206000c8141c0760800048000e00c1e01c11080b601c40e0b0199080615402c1c1c1030600102d010b0030fa1088602d11440c3e4480c80396581d100b10783c07040e401540c0e00184ca000301c1d21b2140014803244222412250907483e010401511030207c2d01c02988991400c070300b49030341c801d07403e043c0707488440036080a40304a001008440c1e040c9100c54000d030714250700040400108001130f08179821103c01e16541007264956164441502520311420402c65410aa00c00c4100100300003c0c440d000c1c3d80c0280c4201e00f170f0f4240200b1030f10362022000759880018503041d0b141c5c05015010026600701d044103c003c5070004070500c903584a0307000803031414046d50201080b8040079000d00000748188110b90040c60443c004450b40030380d08080586900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 413967670 1250 413966420 413966477
    0xd0c020a1a0703090c18060e0f060d08041503090516030305070803090712080d2304300507060c021c05030601090f06020604030e0f1305090309030a030c12 68
    0x1201c20100e491503010380c118030140340c0d0000030300f502d0742d0f01c80800340d0036640c01d441c2000300a4148480015172900c0c9010450280070f804e10708180300d03621130f014401030440450f0b0881c2c01040c00c000004940e11b51468000c251032050364081406141410050b1070f20840da02a16402d05843c40c0410009130007d08480e0910780c4031944503107984c0c4002020b0304101d2550303c042401031100e40000204580703600201401c04040404000480221200f041d560390184070003440e60000201040100707100001581981c0c141082811500d0307081480052080982c0403060040349012a84074100881e60281400e01c02ca68401080303030f14a00198810701c862a504d404d0b040c031000202050031030b4452034800d40640b502e8502c40e1210759603018000d641e501e08032400c0e00000d448480d40c50f050714019104440d147d600402685200c0c5088600f00002e010180c40c51956200400c520781041c0c80c00d04c5220482402612500f89042240c28112a0740c41c406403500100500c80d201007450070500949400180c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 413968920 1250 413967670 413967713
    0x412081218210408010e07060f030c0e010c11061602040b1e0108072a060b03011b0e0a180b030601120b071d04150602010e120a03200309030d0c020a 65
    0x8542d64903a0701d2662066030440e0005509000c03501c015a04000f81130411200c2c03d41e140714008610a100700c04035228207440000284010b18204840e41c4038002c0c0c414102d00603006280112419000910581d0159180c5a041c003640f041c50800e520b81885281810441031311155070200c3c4103e010440b42003004034440c10b001200003c14a014451250000783c0650707403c0d003041c40c1c03404d8100a452100703045030480e4070500b00f921440c543c0c1010b00034030415000608480f8290903501106440e240c0004c0c080d150028150000062224484518114040e5558000041080b1a14281818202c0581040c4003000c1013854510008403540d03281544101280703060311f6258012010401c107413100e11413280e031103030810356407000404c03c0d007258500315117054000300000c03440c600c246070300c1c0e03c1d5544562900240078031034520614040d03040743c41000001001c8059001201d003076000300341c00c103852052942c3e101091622100e0440d2003180c0103071220340014846901c2d1540c904481404409400340f45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 413970170 1250 413968920 413968963
    0x913060e060f0906030c2e020616180e091203040c05030d020312061003090210030b040e0a02012a0c06090501030b010c23030c011a0a17210412081218 66
    0xa00f21030182011347c0c1c080d81d91606084051030080d500d200542d00b900b134040004e25409074403405080c802c00110118420300070490b1070b0a100300350540000303110310301c58040e2a00ba03d00c00310f21003008521661141101c0e8580d00c0c101000d140c54006000e1005d01554400c00840351044003204903a94490021120120b0440185201720702421041c10001d42056418a5000341550140c006030304e4604c05a90802c09c640760343c6082541c1302c00f10080030713001c900c10110030840e04c2816090076040d43d400100d400501d07003141e80d541d41c904880d644500009520f40384148665a03060082c0701480d0802d2074190b43d900c1c0282c036601d0030500d0207500f0440c40c1c068203c0a041454080c800d40d015040040001c000e010f044c40081091440001901c610a10307480d0b4000c40d004144410880c42c0440b00b90081040503c807600008402400118a010b681410320000131019070800c40c60940078031840956440740b640302400c00000d40050201c840e089044000c45104800c0010400d00038200d00444000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 413971420 1250 413970170 413970199
    0x31c020c0304050414040b0f2205011103010e0a1104060e13060f0f030510051015090e0a0609050a060605030c0d06120b250c02060913060e060f0906030c 67
    0x554816980030750340150174994a00030000c0410310b01031086015801c850450b90307403500a512419000c58009908000381d9202c2d54598682c1003205005510507800021000d5a00032903100c1a0800d0b4440d1100c0d40c00d00381003105546a6015403034400103440c119505050030b085000d04652010213000e4041c00070000c09059491451b00f00100400d10140c1d00c0701201d458824001e50741e0303c2c501040c0c503940700304040402007464611680d4800d6030066600c41410b81020351840d21855907030580020812070704000301789103109000850080d024003030001200d6162a5005003030720070060410480c945032550420846402a00300d030752120900c800b07240e66842c00c000700d1000302090381110b00b200742e180802d101005050040303140a80c401d10341d460750101e030404000c8007400c41c07500d902d40001d9400703403100300500b0541c01500151034000c10700d0700800c80000507181103810580c01000084041b0301404858104040d660081c7c82c4140c5640074145020b501199480354001800e074051030103a603610a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 413972670 1250 413971420 413971423
    0x120206070f1a1504060807180e0f15040b0108060601320d0515091302060912030304060b10020708191a100303090b09030a020d030207080a0b090d02031c020c 69
    0x20418003400402081e142070126035410000030740003925004c0c5203040000f08030709100013944401c40d1603070005043c911060702610005040d0f182d004110034456034900703e4401300280404016018030741c0b100e68031351501d402c0000300d40c88180e20200103600705030240300e800d9034404109000b130b041124004a2881510344906c404800e80c180f481d030711100c01b06115002c4c1c0030a4100d02e0050482da1583c041c00000d103810086104400e80c1e02649180c90110f08500504046028181c146801030603540513494080c6000e056600440e400c8a50316941c600741d034550f20b0300d504142c1019401c1d10041c0f201600703104131a517444192500f4454118041c0c5030007070400601000001d80b4a24035000100c06040c8484858007180c0759000842c0402d0000a000c030b01020318101f620b101c185c00800809032081c05400340064482c44010503411070251840c00302d011002040155040381c400c0c0c04000c038610384280c10505169007001c0c10001c6400c100103050451041428082e01034110850041c1c2d41e80e40050700a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 413973920 1250 413972670 413972693
    0x411041d031207201c0216030b07030207020414090d0f09060c080918010e0a02070c0e060d05030f0c0c0405010608040222061410080c040b160206040e070207120206070f 74
    0x913240c19504e08a0000c0c0c00c00304070400240040794030350f920022240400d0f600d94120050103107410320110802c0000c5803484a51a421043d03500b001850318800e03030049402e41d00425103401c070854038501844582d00040101d9022010545041c0120720040d04004080d2034143c400d080401c40721208e12230030310071114101d602000c80203010b4203070100300918011070b0b040b0074400c01003000b42c004006022040c01d40202d680c0568049107203607001d802c12003940340103c0c1c00f4041030380144a6060f11400280104000d000115001516a403140020b904840c900f510741601c0d5401241803000410001d5040302200c1d80207030341102d412505010041080c0700010781d4812100f0580d0508000054581414081c081d4245041d542103104c03510f240d9058501c1130341519003002c40b0408000400038100a107000c1c04211044103845c1c443c0b1182900011203e8205400000f6415024018441038540400883c0c00904d071400325511208c843d900081d00314010030501815810542034400d0412648003410f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 413975170 1250 413973920 413973947
    0x8061e13030e0d03050f0706200a09060503150307060503090c01210216050a030c021c0c090c050912061f030c05010f05090913060c0e15070611030411041d031207 71
    0x9141c7c489404d0700b001405010041d1800b811a00580c0078070000e004e10404407840709085465040400345008000c0310f040c1c0c8020300500c06815013520f4505555402d0100c017006013a0b81d5a02e5840341469041582404800c04d80181801681c0088071030f1b0088402074110b90385503180340180ca405003460012005c6041040041c241d004680c1405c1c1056040031800c10064001e80e02c200c8480c131038440702c1d0266040040007070206650142c0801c03c400503900405002210351414a0170510200f0104110200e82021150b030b0f50440d00c1040080a0350703170206c0c1002240150f0480c08a4a551101941070f8a28080d507810084581c0c0503502c0140244216005044050301040561a03c800c01008044080004941040c145104203031642c0c03258031003c12140008100e00304e0015444d101d59915405010203d41d40c648600400c0360003070b10600610b1085000da40c03400600c6982e1000c01c021984094202c4447c0d0700c03d1405c600ca05207001042e1a60952300b9019008140c80c0c2d000e0035900074a1031042e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 413976420 1250 413975170 413975197
    0x1804020c16030f03020705010806180702120c210a090306090f0b0109140c0301062a080310140102060103150e010b03120a0e0f0306040b1008061e13030e0d0305 70
    0x7000420401d078444003d1600d40240d0a41d801c40303413218011203001800762041940218690111500043d80001c0ca0740c000c1e109004440322030035419410f00c001e411404145445411018000700440c3d41003103855000e4019008451506c0400d1101801002890001403c019900c03600b08d0300300b186009003602d2907500100c0e107a501d90794640d1039501600c0d40340408081c401842011451400c48102500c0c10382e002602d800c20268641c00490101d06090b448035440c04401088440104041c28029801070018004004406003042c592074182c0e24140c40050465000c040100045540303e03034a29410780000c0000b14241642c0031055025250081c085507150003802050706440c26a98000c08050500703840d0100024100410000800103400e40341d0b4044d041640000c0004180060741741e440801c0154a1070030b0790711602d8052502c401100c0040040c2800b003c060752004410b001c0c507038400e00c4480300010322011568000d0120821010040c003074902c1d105a4000c150050b000d84101410020 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 413977670 1250 413976420 413976463
    0x15020f070b090c010309020a050f060d020304121106040b150d050607050301050f0d02030601030f051c02060105120115030321050c0d060e01060509210a0f06060602031804020c 77
    0x101640440800c0d685a0341603c101c0b04015030550181c016045016001481d040c1a9882c01090080500a80044a0740b20310108501d54100c01c8a1010f54001d6004440413415803c010001410220343c0054000b85a4850420400001c8040740c100d03910100d0f070f081000000f44d10002203620100c00c041c0052540c0164000c000540754002d002d1412034070112110404202003000f40440e081900700080d405420840043c0046a030b440c2400c0342c41c5102d4421180507d4001c55071a1a10f01c0004e032080040e0007410040010f031805042914030303000c2c44270080001c00241003000703801d02d05900c0000d0a0040c614880c03403001c8900c0c0c10800034050306160a0090340b030940007010542c0c3c070030a21052081c2ca0301c00c0114029107403104d8141a03d01c503031a9146040c6603101040481168030544902441c1600d0380c00c4c11080b01408103103400e91241903860640e08076172410038155031842e0441c400b154000d121a92841031070390f01e410b01c035001c00e0303e0059075540e4103400303103081200c200a00042c2c20040f0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 413978920 1250 413977670 413977673
    0xf07140d02130e1903090504020f07021003050708060103020405030d080405010f0c091d041509021f03050405010e01110706020c0715020d030501060503070c061509180302160501080415020f07 84
    0x20303005503e410001c1e038140c90141a900f40b54407620000642c0c040c00241ca1881c060207141001d900400d0040b22031041c0a040c41d0303155000480c00c2c10510f0f1031300002078031442400203140c0c000c0304040e04224242015401c01d410200425500c81da01c0f409581002039460104050000030762240300b00f40c45031442400b8014004a0240c447c15803489800d6a100d001c10346000c07017031000200c0034020b41d440000103001400501d100c00c0a0250307100e0030b0b03030f000030100403904141000c42c4000748820004c0e107000c0b4282c6401d0414031f0855006000d84036440c2d040000d002240c003003000c1180d60441e804400140ca40740c13002180381c607015042c3c0250b00c101c0107041980706403540000303603164070401e240d17410b01103a030321038000b02d03110302050f00c40c803004c605400020340c0000c4c890341003404400442c0411131315840e9211071000a4400d001c080ba46800e50044589042c50b6051000756035008840f240e000740b00e03180c400001c02a100080c00900561a102c40d03000c0c00c80f0381601115001c040c886040f94803070711103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 413980170 1250 413978920 413978959
    0x130501052404140106050d06050402031302041a030d12020705070b0301031502040609050d0f02130509010b150304020f0a082506031b0809010605041104050f01020f07140d02 76
    0xc01c10076508071241d10710a1001072510740201c40240ca21070420705116403900301c1c1600e045e00903034500d04517542c60380008549901c4500c0a14400d0803a403c1a445181c5c0324018442140c24201040d0a004a540e40c07081c2d0b5524002000c404024291620800c036014115849000f8001c91070010b1681c0140b80c0700140510101d005981a80d0040c03000042124101c50a80304034400d034404d02c004600782000030001868006c040c0402e0502924402a00c130006034000b070b82d02103e40301404c000a07035600902c040f5400c02d01c261440080b003511403680d0902c0c041e075a9803003400000d000900c15280f402515070180c40c0c1041b004001d1055200311040107041602903c41402d003100c80b03640d1121070b8400054014400c7c0030707140d280038a01d5858141e40407083d000300c840d00c4008102c016a50b480f5440000d00e03803120b11408568203681110380f074403a4109800c020180620200c0035045500800c010268071102140c00412111440c0c019000580d000005c18011302640c0d2000e944040d0040129402d00c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 413981420 1250 413980170 413980201
    0x6010e0106020f0604120507020607061803090504150b090307080a030302120615120a020f0a11100902090a020903010f050a240f0b090a0306060b0a0201060f1202040513050105 77
    0x5240e000c1d03442c0074625800f12a40d40d4801c9801501102042d490071041602402c0113010140c00030305414540510ba8407801c094510b2440032800c0211030001420070700d54420701001c040c0404032418000094142030b0030658040c0e034010080c2c9040300281c1d984840c1c0c0d042006100800c000000e940030003206050150083d003240d10780200e00741280e00012103510f0b040241c80e0601d0740c88981503060050401528042280040280d00c0d01642081800e004030051070140840c0c0d016940c0b00c40c094074504030700d03e0810003807241078132030706062611203001a52030f048000d13400362120900603101d00043d40001d014050318403050715803c0c54074003400f02d00701b221b4004008e0310500080c166030722411194003080ca10f0307141c8039032144401c01160074802456100300900000a004120140c265145e481d503601701c4040b85d000f814050720004088180640a001e810014222001407200741071518001305410b100040c030092086580300001107402c0791980340383d884950030170020402442c001d16800040c81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 413982670 1250 413981420 413981429
    0x603050a1502030c070b06010315080a06110c06060634020f01020f0c0d03031d03031b0c101112180f010b06070b041e0c060806040221130506010e01 65
    0xc0401000389810a1038000c0f240140300c3d05000c20700d070442a443e007410940000e82101d040544444000c7e44042d004103001c00900a460040e0109144a1400c00101e4204405900c1c81c044180240c0c0e0b8180008144e6a1340020155076865441c86c004410b18040c03083d000105101105a603240000043d0f140020390002e031096480c02d0b000040000103a07500c030300240c40045281d102140e1007029003000074010440c01d21a04001c1050400b100c80078510384019422000075600210420005885010190301054844003800346440c0e45010455110000c424151400c1a190081c40c0c00c058a07980403144030881030001440309040c070120f649101e983c5c3c5000e00c10380340b140450100c904c0d4418450b041c41d00e54002c24091612080b07681d50080340750000c01c142c0e00001c0703280480303540720200c4034a204541e10a1040000c010306140700075080c500040c0426004604c148210010000c84021340d1a41840f42180c514007540da07249a5454260380600060680c010303003000080b00c150406a19043c2d9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 413983920 1250 413982670 413982683
    0xb0613052a13090b0402090303030112060612151d0f070e15060304060b060708031501090f0305030a030b0316060c0506071b150212150a0f080304060e040e010603050a 73
    0x2021441d01c10728140c0101c0303122401400b074a0208000c1020300781e0100d01c8007600a0070250600e122000042d00390b400c01d9024400026000c40404c1c1000001d21a070070107081d48400411003c0e13075940310104036240f0b02e180060000d41c0d40a180108481800f45500c0000c410801c9810070120b0b5010192192018481d404199203001c01041d040c402c400c00b032484001c0c02408141c11030b522622418090848005000e401a0041011b02c0203e00004011846003544000451190188a0005043c9449540503e030b80781240034080c00001c0c0080212240b03021586008902c1002c5480040d04010003442a40481c0891100000300290481648400070f4001d0054601c0c07035503030860903120108084294104e503888451907400140700c441c01e40300b022030094001401c10202c541c410040400c25a4195040c00711a500420030303260000030a00074103002804054150b2030300f50100d81c1c900841c014a8148030a01400030b0307003611070ba404905542c2900c0d0084c040960340c2d0070a43d445400c15a010b8448 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 413985170 1250 413983920 413983981
    0x1052503180b0f090f040603030519020604020108060d02040b1c031b0507050603100e040c140415060e030a0c0308030609150a061d0307030b190501120b061305 70
    0x4003a5260005001c5841c4000320601e450f0f1105501d03811a0301c2000c5040d400740d100403422486407120b02c16003014510039182c85070380c1c50304c80b102d072402c001c2031055007400c6501c92020080182d0307001024a8024109889203034046080c0d1000402800071408803e03000b181e81480700700290310b68403046074207c2c0640c64503002d54014155044880d00c190501410640c010b40c0b04001c41e0400394002c642c080799120340c400381c10380c88040c803511524080d07800740c40300c44540c2c40a104181c880e40c0f00c003900000494040100c154044100c1d0381038205445208107101040c5600501c40d1002d02c08030442c141e0000c04001016241e181c2410f140e0400d40703025004082c4000050002c25541003410740e6020000e01103503806160800865a08880c90607a549540340c0d001910f0047e00d0810040300590311070b4a00740e645152018040204007440300515800a042a00403c992400140e0481a0f87d420141202080d991203021601503402c10000d042c0300c600c0d0070100010f03000d10305440801a4820408940c0c07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 413986420 1250 413985170 413985197
    0x4081b010b150a110601050307150207090501080a0210020303070801030b060a08031920060a020d06030f0c0510030218040203071b0c0617150904020114070308010e01080105070f030b01052503 84
    0x141c4017400d00540d50940e010780001d20580c1c06100c0090810f00c013610440d5845902c885280042e50030aa000c40b50503405141e00c9330852404426500318091544015030451070540d100900888041c400540401c1d02800450015241c0848040c0a4691602100da4034515003101103114261080350000055050b80c0c804103450f00400c80106604905c0c0c0180085d40701e0080c0303140290300000342c1c03d0100303a440c54004006003800703410040e841d0045044030401703490301c01445000000b1a40d040d04051041101d01c4250071100c0c80b031441c84c0d10556005032265943e050684955030b05128402e4403130207140c80301041001440456050301c1003681d80340310424214095040002003960180d0421150200da6003890504c4811141c1c4503005242c00305c000802e659801c200b1f603108400980000f51a00010302c12540c0c070010310340c018402d8400800851a1242c40109088076458a210070113031107141c0318000382c2c4a102a0f550520034080365401140c00c40c13180658200415004030003003400c100340c010307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 413987670 1250 413986420 413986423
    0x6030323040503030703180e01030b04033203100b0c16080105040b0718030b10050108010b040602030f0a09180506100c0528060c02011e0504081b010b150a11 69
    0x1070441e08060020341c2800038541d0181c0381007148043d4100d104d1500c440000f2044501300095008500803401c100c2e0328181030500500c1d004502c4106084050381d5a41040500b5141010003140c03440115403585035116920307413001d0700d100c1e98441c0e40c9140010401c030000000114458140400704903c2004296803100150b080c0d500c1150060032420144000a055a01075243c0d100c00301003003400030700c04030340703d43c0d444c140782c0c200ba22030300c00140252405010381c1d6041200b09000d041061201410a860900020740d603118441c4144012100031404262150140c1c5210018068141200c1030301e612059000c0000e05040b90b100344034404100724019400d005599290415801202800d0840c010380030201400004c6080181c240220b850b0903c0481c4071071249503c941007590001c41d07501c2c85196100c13060b07a01300030000848c0745410309000009070508100c0b002c5040360700751007520025400031a030041c80005401d40d04a0001040284451b01d00c00c028200f03a1142d4480700040806448847d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 413988920 1250 413987670 413987677
    0x20f090901080109170a030b030d020c0a080f1c050408010603080307030c0e030c01031e09060e0c01140913110d0b1207030b0105090402040e0d120501150c0f110406030323 75
    0x5400d030b008502a045c240c1d00e0500040100d41d4003400d0108003440c0301b8010900d0000c00c002d010006801c041c41035007c0c1c0c50143c0146004100503002004021044446151600c1500d0140740344043c048901c503010500541c241c0c0c0040c050000200086075032410320044c25402240e4140c0000d2600354803074400390040280d8004840301070014040c400c850801540103003e140031841b800441a100d10440c2c0c03070640106d552640c40340102107aa1390b18480c04502d46003a0407000f034103100040310321219140c003150039100440300841d06002064080c040b960b0083c001310b0780d1251601800902079400f402c00f600002c1c108901601c0d4199600d02d0b01d040c91b61508980c1c04000c0040d4002c0f40104280c4c581010000e030054001000040c580e064031085500d030640d00010040403980040c401c2140d040244101c42c0145042001300d0720b01011003200506121041000a0088010301c40c01420300440d04c08041030848081c00802c9490b0b101c2c00c0c01b0348090281d00005000c2140c0b50643c110240b501c500750f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 413990170 1250 413988920 413988923
    0x60a060e011d072304081209130c1419090b09060d0b060f040f15050702010c1202010e060c130801060503070e0910020415020609060402090a09030210020f090901080109 74
    0x140c80100d0400030504031100301c050f00c107a0800009614240180307208640303592070803004a20346036459141101d014102800c2c1c03441d20102180c00e001c100150380b5084c4460541401404001660403400e080644800a00304140300000001140311040140c4042c181100450385841d01140c7ca99240c9912000c0c0c414080c005405c03000030311800c0421001c2d41c0045120850080c9803134100451600000e565030055803216200c0c00300c3c82010420585c1c00e0344080540c50b528038280e8600240746c6c00103068000f16000c0280180810105405080d02c00c0d40a80c01225121069503818248891810b40b41c0e009501d4031a00402c0194001540c0348d414403c200c11903c010700a0207000340740c04480410484c0c0184006802c0c01881a41200d5091078030003003001c1c0400c50405400008038440007071401070000c0c87d403a0990f01410600015941d1086c9690b07000c0d450b10300120300700b803852070101d0600b00c40c645424107050021035090f01440c070200150110340b9090700c8840050380d131002080e01340d4083c08030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 413991420 1250 413990170 413990189
    0x80c0901050a06050c03040504020a030212072a030e10030c20060c070206120907140603041a13020d0b06121c0f110a0c090e12031302010207080f060a060e01 69
    0x104009950185015140c800c485e8000d0b00d0600d5520301c085016a404500c1d4000002d90029040c95010411441d03a600040b941c5031980e41d510b980200c1042d0103490a00c3d00d0171210811107240c0c10184181c400c2c402001c00680101008c074410301002e0054601d100003100401c000705000103d80350b134645003038400d21b0000000c100c1e0b62500c00c100c81c01680400400d982040040203840280a12008454002c4101c64004c040c62441c0132250f02401d19011002849010100140004907141c0b180800364101400368816454640f04030014403004d25460007500010301044c628203220520700e503281314810644450b209a4681c1210320b8170354041702d440d1a00d01003801d00070b06045201d00c1c2c01d400703920403504010100c05005c54005140840c076800c01c8520764010368050142401e14011030420007400002000c0360b5400840034509400010700d01e0030075a24414104082d0383c07081195030300600355842640c00d500ca00c061459110001114918900c0f810710000240c15103070300714a14101c030340c0d994 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 413992670 1250 413991420 413991439
    0xb01030e1504021c0206120106091d06210106080622030c030e0303070611180103020f04030b040c0f0b0d0b0d021f021006141305100b1e0a0504080c090105 68
    0x10300b08003078100e21a000c0e00000511020784001070703c820740282580c4450303001f0380c1d4032980b600400506d0000e103a005821054050010304003400001060503400000884006a98502c840704a8900b8565011170a40c0c541c01c0040019840308003103411802224aa1300044035610111104440840f25400080000d103902d065100401e1203400c0000c1340500040c2640d1070004103498400550f0000b0002c100c0100000500c1510f0441c070038000600a0001e00302503080c03d00305107800742e0f030740900d20000c0c01000d002d20004080000d11120b5001070500c00c19460350140e00e829420f0469085444101900341c902030b20b4002920b4401044032a40358010b2803000c503600b034035511049820716140b0b0075055101d034000e10b0100c86490b0189d1000b40c003d03d1482403c034011003081121110740c80c10007007513076031501083c0400107488803000f106440c440c1e0780e025035580c0b0001030548041c03c410095601400c000c00c004000550010042084503008030403101002d032040100a99824203200e19980210b44a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 413993920 1250 413992670 413992673
    0x11e02091908060112141e0c09091f020d11030609010807030b040807030c0507031115030c04031202030c061509010504020315011101140a051b03071d061b010b01030e1504 75
    0x2c00c2d10020f25100d800c4565084a20f036044521f0000801c0c46440755501d4070b038910194660404c19080c5010048488d0f0503182892180d09455103030810107483e00143d908403090b00d41c2d040d501155841d4041403001c121030f00c0c6814070803256030400d90700244034034401c0b400040d1341032000900d1015207401200e0b08400382c48a1782d500500f0382c41001c0450074070541c401c914010510600c004001140036030400f5161170001d0081003a80300e254000d0542c507510038028401d084000ca802c0e0ba054941c400c0030800007100c01c190076855400383c0c3d211032109214090070840c2e10000b1080031030041704292000c0013035903226400c01040e40411161070544480301c1100103190340c400c008890b01c80c0c3c50307034000150984004c3e8900c0d0720118221440500f0a4480007400300741c40d40e50400e0700e0a00d20a90fa8a411818149002000c9080c44000c031281550588484e000340d9640c03600712041000854044c9001d4140e91010034040c0c0025010140481d145c0b040103801d03850040340c102c036881c500f40010102990395 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 413995170 1250 413993920 413993939
    0xf03020a120905070510180510110f0106180507020c210102122505040b0703030617161e09090807080a050705281202011e020919080601 60
    0x26141090810440c0349500c030600e282403240d04401c2d4014000b501c607041c106400c0c001c00b200104201e604211110750f8100704d402600680d001950011240f0001e40c4040d008100d60721004207003600141c0c011103428072003041d01584003034202c03031240004c1070460401c1c0140310300300d83c802c03111400980c20624110b010341c42d01c5200d01c44503d01c1004082101c0840d03d031110b0172a0024082d90341e5014225081c02000c407603a206202c0b0405c98402d60712161102c0c1c81c0000c2803800751b4441d210440e400810401d081600030703000341c00130344a0015110701c80c9100301003043c2c0c0c0d466000380f15803e17091215030200d06510042c02541c82c00d58002e400190161401008000400007540140c50170b00c01444201e001600700d4004001d181d9040d9911900c1c2c0b07030142092410080020740d10740030541c80c41603c40007840709003c40d103c101c0c3c002c03500d408c00880c0c0520581c0035001c0307001d1884d40c07011f2201344414003800550150140e10002d40b2010b01308080c064005400c10641d000d40c0006500007401009006003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 413996420 1250 413995170 413995177
    0x903050f070c0906080c0a1509062a11011d0f010c0204020c0102070309030b0c0403201207090f11030105030c0402031012050703030e0303090d020f01023301150f0302 73
    0xc103108184600c0d0f983d240e940b040320348036001281a604108040c01c810310384145460043c001205018440318204a00a044a0141d21492041c0124640c0701d45800c07209208000e0540c0030581300415055003407620000d010304542085000c42c14003c12404506500001e14440c0040079040d034042d00e0381c4a0054480c0d500d40c400880e8055020090458507810038000340c00007610a403a4041c05501394902852000c3d4010412881c204091000f040400c42c00206035030700e030b0030141c4000c2050401c140450300f18000040b90301c8942c0b080c1c0c04000381e404115481490300d6115000e08220b0f01a01078400b00c0c61341b00078455a54190710840306004185007590082d03420290300d440040070156210216020f00360250300c19101608181d0040007810b41001504512541c203c0c06585402d03103a9000981041c1401350180c0100c40b00f001d40320080e402089075003149841e4443d8094240d078203900d05407030070540040d0580c003444142c0c0005502120b00c10100715512564454106000308400118020f40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 413997670 1250 413996420 413996423
    0x40302060622020d0b0a06050c0a20030102120411010c05071a120405010b040b090c030a11160c09110901050a1218060f05010608090c010806060706061e0503010903050f07 75
    0x14455202d10001d248610044c40382c1d0302c940901180c0b42c80e00d01c0800030340c110540d01c804140f09080191900c5180c02090940d020b40d0f010303004640100143c044c046405040410680d0517620015800700c0362030b0020401c500ca2880b070400303004107410900044404107480300c03004001d41d00084007807000314101074103130000810102c280d6041c0030005010b502c48440968094030265500d41c11410b031400c160007100c1c5900302c26501e1218501300080d08052a03c40100f01b415215941e11b00444600f03401c01c00c2700c3c050604644c0200c2d0780e00d51428403150340c1d0900c6c4a0301010318980408500d00340f480d6001c1c0c5090503016140c1d1410101007140a880a814011b0b29030421a900c55407011269441c5060010150041c80d000540341d44e25000001100c4040e00716105001c012010855811000504608529400e1801d6000368980c81c011440358015510020402401d100f008a0101650240b90090000c1e804078452542e0b0380340e042c18221100c4850280010343c04110322441a03256070b00518040d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 413998920 1250 413997670 413997709
    0x10c020d0e030307052b14070311070906060908060604060506070308040311060c1b070b16020a09060308133f05060f010503070506190f0525021002060403020606 71
    0x104e02980c600742083d081120b8418043c0f1092101050040440580c1c0b0740700c0d42d54207203881e05c8940d04410402034000c1d640014104075079100d10b03020800003400324038020b08a00206003c22038580501034600c071814010001c0510801c0000350191030325014140c1140c4000c0c0c291032030807989450490b120440100282e013486188200c808455404002c06071056421255294031611001e80500c013071100c00002c0e15107503010184c140843c2010b40d0840d0300d8007014840c0780100210510100300c8580c0380b5408861140d01d030007000000c0c000f902000380031020941801400658403001c03403000348035040100032010198517003190403560010014000b8080c0b105000d0105011654078180b602904071405083c10000d200100300078241004100041c00007181c4190500401440c0041082034200e5030204110b001100e08104a004a0450703505c0f0821a451021030302c003600241481101b5040100d01030f07101481750b110007520204800e40100c1d8141d0150415441e03100c20080c0712a01d00704100c054 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 414000170 1250 413998920 413998927
    0x160314031201060527151803071203020601050a030c05091302280503030a050708030a0207050d0905090a0204080d0309030e0315160c1205030c0706090b0a060503010c020d0e0303 78
    0x880315078054900034100d82d90b0340c659601c2000da242007000792a13034210500000c1580c114043e5512100400a81410f03141001c2e250440c4140880702040c180301c000c2e815005081000c904000401103000080c2c1c0643c084a040b43d03030ba8010b009102d2032910015111550360042806645040044e10740c018003003868101401800d500015071101503090105041b8181c0e40f414103074050704400200040070101c1c055414a002c100c4090640d1240040c014200807000002130540c030542d5044c0d600340c40c2c00c001224140c404c2103c01a1110b81c2c1400390314840c882050000f040151103000b101c06440b10a0041c201d20031030054164040c000d40c080440505c03480c440111260386081188400c995005440800942000c0c0700352480300c40000441010400c02c001000042119620000c0303000b5841d28102d80c1d0f0350340f061013200d00d80c01a07090041c055800d04a404050018940c07506009071081102004443c0e5141c007014201d403a414003800241c0c02c01d81f0210300b0f1130b00500854406480140580c0e14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 414001420 1250 414000170 414000187
    0x1c02070302040507050903060f010510030e1204030f1a01050f0f01210609050c07051507091203030c080a2703030e030c011b182d06120c0216031403 65
    0x43d11000c64103000090f10114201c1102d1508204041d0000c070b080103c00010f50422001c5000c4e61100520340083c541c50301d0f025190340d0700c10030102540320040804580c50780e4482c50012001481810241d62000e0712010703010481441d030201a040301e500400452145031028280b0040d55400000c00f4140209018880c90003840781031074120b1290088000180e05040515001c01c4841c003030180c14044100340102c0001a500083d00702c006550941c1d80c84290b0780b100d1040344c01404a170812460700d60780e102220101609900308c105038141c282c0350020582d6030130410104907800c400300e524400a0615039500741c190a003459603800c40c000d1502003421078090a0540c42c50b4014084098560341d00d25910b00d81c09101d0b00785540140040c0350103840c40224410322030407000c5038003810990091818210007000b518030030f0b01c444402c03071560030b00c085a0b9a20700076003000d0240000c0d070005410051310300007440c800300e0307911803140c0b4015601c0e00080c11925a411030b5458a251a4114882001800d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 414002670 1250 414001420 414001429
    0xc120e0c090a0f0c02010b0f040e0f0a060212060108040b070e04230604060b0408072c0a14070309051c170405060417070b040204090318030b011a03091c02070302 71
    0x788a42580b40000c107001c0910001441210040c036184011645008040c0c0c103180d45543c0d00c007403a060b04880c08140719082003c541d00b02040c40c0c11004103403040740180810004944c002d00b103641c040d2884a40300717035240380042d600264101c4006101d10100d80009070300302c3c0140c0414100003030140c00010003001c4007044070a0b042c5101c1c0940015014603041080c240f40a005601c003820b6040c103250305240c600070800740d44076041c0c0a0088022010ba00006251a0311082403800300c00441d60300e0a64241740305604020002034200340407420801c0300160515009014181016601c00010062001c40306804500d603028414108204140506511910b085421f4001d020314041d1010700314034141840c044000c200c481d02440c2064000b40401c8000c82c02400005501c00d4054070b000c6140b081624040740d15904512401800c800c100d41c0200602c440c40d80024143c80c41c141c1c403001070440c1400411601e0004a51510850b40f04d50444100785814503c0b56440d046180100e640168480e03000a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 414003920 1250 414002670 414002689
    0x908060703051819050705040e1f020f07060c030c080c040603050907152c0d020f041b020309010822030f031b1e08010308030705071103060702060f0702010c120e0c 72
    0x159040130300f84d10600c18050240446030040c5800c46040000c0f02c0c2c1c980703145d0b0320b5480800300750060150002c1c181e50044030a404469695030200a06555035a8502c0c1640003440c6941000c0000b915100b0381d0034655005020050044100340905400d00d881d150084018100061501440307001c2c0010001e010412880302090b07042003a03d880d200720031080d11840c0c01d031a0b2104100035040c84202e02c0c04280c2c50b0000c1b240500b82e0140d4170305113103c00c0b07400403801400001e40740032100f06404031007454844d804000303481064404d0743c40d0300b05922608141550902d000200e0202420800c00d014006400342e0001c103030800c01400c01258422607000600c0301051040071040104212070700c1010000a0310300304c807a0031800380c1030510240d4116107030140389000060007030090050020f4004103000715902104004000242194410f03d06881d009480c1d410550346086040014000303d0f40950060142c015440000c3d034400102c1229143d4041c05419040035420103809060042000307925101c550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 414005170 1250 414003920 414003943
    0x2060a03060623030a0c18140a05060304080a270801050412030905060105100c0203030f180d05062403011a0a1d0c07111903050d09080607030518 64
    0x1404501c2d00102601819860b18969400810355900712142594442565086a0078441c006842d07030140307034192481d0b0800941000700c40405080022011041d03000d091030300c3d40c10b50780100e10907603c030b060144501040d10001c0050300300f40007045400307201c3c1c1414030110312040d000c4003640d014500e4260391418242c0020156035142d20402c030a00c10700c6801410143c0b0300d840c00b0041c00f84176442e00f5890701c1d01805414402c8210080b4090058840c85050f034038190001c098035601c040d06031000d81c0d181d20002d010258820a6000300c044c603c1c0103034038105050303080307030140c040e40c1ea403422650054a041e030701d004240444d00740041031548091150301071600c2e240b803941c17002e012800c0070030210250a078091242407603034a58401c058402c070403400b038101d1500d084d1a0f46a582c145403043c103d4485101490700050146000c0668a4216441c802124014002e481c9005050700c01110b90125a0003001c8007584840007241906109601c8039600030255120320200b0500c4801040c00d00c1c207560513 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 414006420 1250 414005170 414005177
    0x150a0f0e070503040f020108040c051216050a0602070b030a091707051b031506060c01051f05010804030e1905150912010b0102060106050705011104061d01020604020616080702060a 79
    0x90900c4100c60403203240d41c1140301e5051880c02d620700ba0780c9009042e00ca000c0024100720b25100820100f1a04c000d183d00030748001403c0407075800c0c1524681f941c42504054208488011030350004480c18443d58038000d46030b8a50240035003a0422045000640c0044d100e41c0301c1c2c41c0d65060490210340701440c1310302306281c070800e50303991111a801d0403854948403240c0b581583c404450800d11317640c3d0005201d1401c41c0b4900d90009642d41c1c80000428a00030424a5101e40d401c6c0310810003848940f90183c03050800c0f40004440c62034480c001166007190484000740416003021002415107000308040802d040c1d4a6170003140300b41c440c40420103142c1c800700000001580440c404000346810100e5800550719500200028084040001c2d0764503010b00c070351410f0000c006240c60038440c080d040312000020400d180790b60b595071008000c1881e440482032007030002081030003105643c03011035514000c5800625140c10b15020760140780f02c1d00740c00ca0040703480d4101000520b0040c0c40744070152121000b01d45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 414007670 1250 414006420 414006449
    0x409061406090c0a2a03080702070b03100506030603010f11030105310203061305090601090606050a0f052b0e0f030f0d050703110d0606030e030705030405040203150a 73
    0x154400d80160018010520560010003008a20351000041d41d00004d090710301805407259440610360500005000b08400502c0f0300c210300300703058000041c5c5000750600d50840300403503510303404d40c61640016203c0625020f02050100a81d10b0400080c682001d0010000030b00e00c40e4030a1982c0c210b403502c044200340b61a000c4010001c0303103400d49035003000d1a90101828071f01360f081d18021540309096413010141c594003001040407a1104540400309440c09070003000641000201181d0364642403181c2103519003043d4010070203070702c92011784008142e9500c1c0c0b020703c00c0c1b070120240c650b90489200300f02d800c4244000100084c501400541f00c0702c0300000c1c001082c0c581c81e007071181040111000e0131000c2d8000c1003400c40c0e1160310030890302c9204010000081c0c80e1580c0c841240035010449642c03121240c0410002c1c0c80050720b40c0540700700c4074903450811001e030011201070780f03038003c3c0036000d010380e081030204012500b0f02e0340046174409003003a0010611100384e0300185882526400540d12240c094 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 414008920 1250 414007670 414007691
    0x3040b06090619090c0c080a0e03011109091b0d020f040f08010605130209040207060e060601030606030606090314030c1204060807080408030103060b0a030203030a021005010f031a070c02040906 85
    0x559202d40225040c0c0e100540010010035001502102c0c0c864024180d988038a000356503031050106004283e0302071111951540d03903110041080e155080090300c00d51034600c1d05080501c0140440c2c80004015000c1c0e46141e803681041a0b0301082c451384c56444441c1000204041e00040c8007c050180d100c041c0d65880d0f40c01e000d42000340580c00c0d0000c0c001685058421300040d45c0701510012000140000940e03030720b00b8500840c01901510200410150400d01e4116901401180141c80341100303a0781004407075a6208206c080d1041ca11413800400d981c41230500c08201c44039001d442c080b00000c2100e26200c62171403801c0c40c02a1080b800b403012a00401d051166075803045509401111515142d5050706098842060a10043c80010305183c0d9520500b07501e40c88165901004603001015242c0301c1d141200040c2d104d100b024200c044552804001160341188040020305403504105230f0218100d0300d580c54004850043d00e44030038044030150f1240142d65501130902658402c000226942e00407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 414010170 1250 414008920 414008929
    0x3030f031d07060210050c040e0403120f0209090604050714091f0e0907110309040c1b0606050f010c050c09060109030c1d06040e0a060c090e010801050f0f090c0f1503040b06 76
    0x31900f517415030782c00c01c024004220f280781d05550039603404014901680e03c8520701580d0558186905058450808602e0b0517401030707135409001d1012054407038500b1341e03840c00200001c49004442481c08102100c81c00c40059003114040e0001401c05002c07104401841100e69820002545c521800219008500c0c1020b042c084441034100c4081c0c02d01c0d06490040c403214a8903070083c246190301495840e40c401002a214214800742001803103c08851020542880c01c06082c9070f005150080580c44810302c80723035109440d0500295040000303454049041030401600e581c0262605040260151021010800e600002d50042c4040709402001f206100c4004202241c0242140e100317034035201c00410300000120303440c0d40e00c542c4518001740c01c40d103003241500e0f5904281c004c03001d8042d03100004116020154404d07130041a082034140344659603000488402e00080f2604420780d005048002e0306400c14440200102c24000c10464900000c01403c00c00b07900115001c1e40d80700c60001c14031249082 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 414011420 1250 414010170 414010183
    0x6050a0608030c03040501020c12281515060906140d060b28030e030306010c062d0609060302060417011409010b01030e030c1e0a1e0308100f03030f031d070602 70
    0x101030b0ac005846243c0d8186854881d084207010010844031106146516400400d254241c55801540d4403599241000480020020074003401c11b0a9920b80c1c01060240c040d41190f02102c0040d07031a4900201e503001c6007155904910014600c2e41e4440d46d001c900301107004054040d1022840206c40380584121485c444d40c109000403030706042c40c190080582001c044126a4040c0302828006418031407841c0c080000c2289030201c00360503031180701c00c810104140ba400300000c000b42c079040c0f200300d0700e81c41140200e035003510000354400410401000890b122030185003103074480500002d01d60700f040c01e14001d140012913031a2216550742c0008000356805100b4006000d400d80000d41c01c00c0c00e0681a1540d0300510003211180e900012400000402c04200c01c0d29a1707a40100031120420b04040c40f480c076072101050490110f00e007600028000501440352000b140c1d14158926011450b589007910b4040c0115030450401d85c07100b40d101d120300856028007144070118401007100c1c918115000f0308250 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 414012670 1250 414011420 414011443
    0x6090503041e0b030606070803040203071710060b1219020403050d1215060f110f070303021c020a020f0d050a02150a202e05090d0e031906050a0608030c0304050102 72
    0x10f10074420300645480e14819151032551201c0d2041e900e44660002a103840071a0f030052440036104030244002e200089120341c1080b1b0000d2041c8074650311900c0c0c85940340522640c0300301c150002c0000070816400d440c1707204000404504010714144e142e468141c100041289070300082401c4c92110924000240700d403442c0b060740e03103c10120190070810008c00710315004e0300324400c20112601840c5421010f01190310f16007484c4c0d0442c0c20587d620300e4040c1d101c1081301c00608090110340c2c220000a4008603404184a074010420012000740d481000400c0b41e210764265101e00c1910113007030043e113a0340c54280c0102c0c2000b85898030390802010040c50a10407484101c240503281e041c00b40c0d0100300081400c0c8000007603203032200215070070b0800311802e40c45451580c4814100400e000508001060f8041d43d005169280340860800d01d06065032428a203602d13140d9500803010b0140802c515600c42a00006412030108a40345e03a00300c40c41c9960044c0e031603a078580c2c000290410203503804001034140e05 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 414013920 1250 414012670 414012689
    0x230a090506070b361c0f020a02040507050c0f011b02010204060914030a0b0a020301081209090411120a060e06010509090d050a030b100804020f0618040906090503041e 73
    0x81c81d59038801c0715225014007440004215415081385484c014400d400c140340e845540202a50079102c0b40ca591a808004042c6620840031030411600d40300d000019454801e0790000d12034035003d9400d00004050003440c10f400c00c501070001c0d001480042c0300711072014403008008079030780c201a60071800040002e900300080d6881000200300c52900a25050b04803030310a807800400c5849a004241800a00c0500500b804401020080035441540c040e505840540b0112946249003003200512031023500c11480c1c2c0403a60390002000101032885c200c1c0c000e007000c3d02054848031a041d215282107032458045840540718ce04602c00d60703500300f000c4d81c014113088840c40e9841c10058410741c1c50765184810b00e0100b00c2d00280081a0070700a0b080342c10f00c0b12019040b000500001c0300000c00da1441581c04078400c200b181c980109034070300b00b0103881400111100d6640c0441c00701d41080300400c0c54420071100540c50345414008201e041c00604001e00155141c0c86d119980025101c66880007074000c0c0c44c0e40d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 414015170 1250 414013920 414013927
    0xe032b0f030b0f120c040510090e1b100314070201060306050c190f05090d1a06120715140a081f06090303050a0302130f080d080f040201050901230a090506 68
    0x40d40e102c8a070141d840034150340304c00c030011085074520700301180c0c0480a600203040000748a14920f2a001003011114041400c202940301140c0d130545480e02001c1101c0e03243d42110304030382a490075020941441382c1a04000858180c4a00d01080c031000865034000940d5641604109100e0140120707035020158001c010b1510b190440c0200070341048030148401c0000700b4116505040c0a0011610110340041c151301524045191605441038000500c0001d98028004030b02a1700b48144100011800040074009850030f00d4150008101c64500f00800c00c10801c00c005a2819075500800c1090001d0b0f41e0415249400c90801c1c101c06042d5040800703400304030500b08809540410300c0c1f82580c0d410b140c82a5101c5012000318041e001e02c4461041c443c0845500181c0807143c41e040340f048402c42d20035140314640b864030984211008480c0d640068840000140c01584914000c000a5105040100d0042011041381c034040d1984400b84544c8040050801304031500801254020142110725518 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 414016420 1250 414015170 414015191
    0x25120503030c031e04061b020109020d0b0910091b060507030c300e131a040903020316030801051c150e0f030d09021810060e032b0f03 59
    0xe40e40310081c4401481c5002002181d1104003000a06205098481680580c0d040070f0409000910710f0782414451100c1c0c04803100c42490041c010050816001401e41d100b038200c3e91264202e05000504c42c3c600e600039035201408042c820311a226510340111289120050703080113a40c000b030301503040b02c003d1182c24070030000040d6100d0030700b5103525400f05150b0565180d4405d460344085140c001c000c10b402800c00040320880d4455440c03040c858088441ca42321041714003610b01240c0b40783c0d00e611141441d120071580390f07040980002030070034442e2040700c1ca401d96412240010300c1c0c940d0002c600096400c0d0040000f80f40c034010300ca061059222002c4003090031551440c1c80d54904424480c82d4a485200b00f0034200002c0c4601030080629070700396a40c54045840890081c0342c0c03030400300c0c03080340809a0405500c62100035548542d00050300f00c0c801c2d40c00c1800c1075401100100449a0610440c0e0301c25941042c074101501079801d440740840030b00001c21001414000b20f0201c06020145407050340c19 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 414017670 1250 414016420 414016423
    0x609060b130509190902041b08101413180204021207020c010f05180f03010e070503010f02040e011a0d0f021206040b0a0510030905060f01030c080c03070303080c0c251205 75
    0xc3e0300640c44c90001240d400e03505c00b04001d002a1540d1900040e1100b60f8540340035080020644940000915605a00e845005a41050000400d1150804070f502695189040aa8040c84034120641440071b0120356940c0050f0690340403950040c12825280f082c4803020360100b15072101c48000b420000011520440010132a00031120314964841580070908010703140d01c05600f234009000350082c00001000069540c3d07500207440b07210b000350b20b0000c0d000308005481c800d582c280d461840006609074604040d20511035034182c00820207003000c1040c4d07083c1500d42d125014500c08085030240c4c40300700c0004c09201204006010b28051410705010104940d5030f00700350010340704210340000c1e20000d0482c2c00c17401003401e000e0080c024420320003841490142291201e040324031404c1c107950750a80b40e01c03015803210305407068140c00da07200403001d100190040c0207440c5d004143c180d81c01c0c140700d01405004c0c64001c1329421141a0105203880041c41011804002c0103402c1401d040c8607020900da0f01c1c1e5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 414018920 1250 414017670 414017701
    0x51215040807140105070801080f0313031209120c030b0f0f0c160501050a1d030408061603141003060f0209091303020703170d050a0515010c03030609060b130509 71
    0x18614003001410a041002c2c01d1084408419040f000700154541070901608a800a002c0c1c4056031040d9542c4a4103441c0010032546650312844012940701d16580c2d402000196428444082c8555070704041109080c401e00000080c3c00b4860340c118807440d50401c0b6020388800350412844031105400c11268a07222822103800441d070005150b95204602c80301c90f8051100312000f0529400c11041c0106c05a0b5900300e458401c1c1c0c0550b20402441c503400782d4950744c0c41140b0400400341c07c0b690000e5005501000c07040007143e2203060220300444040301e040c07203420b03048a01900e59945c2810600911900d441502c481c41840354007140740219039070000e51030540091009181c02c42d9241780300105482403003034a0080d035201c3e14000000724804020030040d005114215112480e00e00005d8820b4038a018140c014540303050841800c4540000455410507003500c00c0d003d154845100043c1004030380b007500300a011000500362642e03006003110031103040c181e01c158170079a180824440c050000c1c0c65003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 414020170 1250 414018920 414018923
    0x20609010809030d020d0209030c04020901270f15020607090506120a09060c0807180e0105061b0601080309041d070b03100f0b07030f030c140a0302040b0f0405121504 73
    0x4010740c0d039504442680386102d90341c9080400750010480348101d89454014283c481400ca003981d030300b110aa424481240a0084a680000c40c02c91201d042e00d800341010f089101010244209003c1d1502240c1075aa07845500840300d1030403003912a41e000b42e050107040d03040700c414607182900c10b1420000500138042c01c0f048945945040022880d08400ca51086403840d6219105018031040000e01900c1243c00715044808142194941d0444c100c0310001c0f40b00791041103180c0d058907428407082c00503d0b00288403400c03038600c0c083d1151802c0704040001030300030120b80c0000d540e00c5076a08184420746020842d4400b44059140280c2c200c0d100c0803c60605a60280480c00e0316540c0c0c0c0500c50184820395402107001071010b070300228010700b40d80000c1040d41c0c02921000c40900c000181241228594004900020344074014040c00030b160740b0003480014a21300e0050704068468800d020380380c0c085040051424400141000340d410a9500c1614070210174011380640c035025050036512500c020030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 414021420 1250 414020170 414020177
    0x1003020d06120b0f01061704030305130c171501030834120908030a020d03020a0507051203040201030c05120105010309020a0b1803070909050c09070c1406040c090902060901 76
    0x10303500d000340c905034844001800d4000501d90200d495080011046800b40c03000e040c00000c200000c18000d029170109081058810300f240d43c03503910781c1c404070000c20380505031845885090500d400030511000c40c40e00545401c10003081e494407211a20743c40c0c8102d0700300c00320340c604401e0010004244d510040c1d4034094142022844d560300303c00c0461014a00628203142000d1400d1000d500744001000340c1100090b030303a2154078200f911407640321380d07071300450f18240010f038004a070300030383d90b031098010f00b104c000c4030f00b81705051501a59031a0709000d00d42c00c04040a0402108000a560741401410b8022416040542ca07003102044000042041406158180360b02c44070040115110709902400520700201040e80340d110f691700b803500d1603060040c0d092091150b4400454030802030710605001e59440707402002c0d4142800207001d10060001c2501e4107001c88480c40e000402c01c1509002c80c0c400c00c80b0041d0000b4549850700c610391549a400003d142860031600740016150f0700d00702d03480e1070344c2400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 414022670 1250 414021420 414021427
    0x9090201270308070501140c070803150f18090c06030906040b07141c060807050d1410020304050d03060914010b3702060f040c030b09010207050a0c050f01020705100302 74
    0x803001c1400052503840106a0300c00014984d09011040d440041d8075007800070044000c0d1035901480c0014001c4d5000a09185030030404511400f00c03a803447c0140c0c003005800c00e8400d555450000701c03214041250310207844041800c0101084060204807444207046031102c2c00c6007011303003180781e03103010082000f026014034002240096000f00d0403104d035203981035030040d540c02c0c41c840a20307810080d1281c0244030500b807480102d80c041000c18400c0c2650006400740c1940e09141d1500f0080c0c17400c2201c10740050040300c810303290b03640c902e000071880f81703004500400b0003091b0032400900303c0700d00354042c140080c42d00c40b10707083c64402c40410904445c00c003000580c880501c5044a44100300c280c030002d181c000e10054015003152034113580000041c140d000c0e86d40d00c0ea00d60b1786c682c00180044070300408401c050001880051088078034690098080c0c40014104481699030910b0840780c2c403030503034400095603410000c52410600d003c0d540d034400c0c40641801403400d00484d0380e00b50181411418540c020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 414023920 1250 414022670 414022727
    0xf161403250506061c06050a0603050c0d15110d02040605091503010e0f2508060406090b060a050c16120b0112020102060f06011803080403050706180605030c0f0309060603010609090201 81
    0x8459171035030060000c1026040c11694403006085901c011102d900507021110411710f081c4414120054000d600103914180400180004150078901c80e045050305200751481424144058000360082d52074450ba11145401000600100d020035000015010401880301c118810941900040c50140c82c1c000d070344801c0f02443c5141509800404414294130b00761a00981c0900b50a0191000b44c408000890300c0305000025101d504446540220040000754419803081c2e0003808041003000541d004200901440e00100705a60b00021170070804112100c10b01131860039150041c41c2190742004030441c50f500107521002c00411010cd8407a04000080082e40240c00558020600300c2000ca0382503107a1a01c2c15003604140410380d580e01c2000000300f4107034010440781e0402d00350000300d81080303483e00c50100d4140d8802440380d24401401d10240000c0c11412020318003500d40c0001400440c540101890308480311580b00d115164242610140541d80044021000880240000b100c0c42d001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 414025170 1250 414023920 414023959
    0x31a1b16170a08041b030201090302060901020f1002040602070e0717041511211306050c04091a011101060f05040506180405031b0706050f16140325050606 68
    0x50310403180041d400907480d001658401c520520440c07103117070407260006021030410b002103082e0200a000c200440c03810b002510b400b8020f0421104144129515403100590840c108030680c50725954091300450140861031301401100702810104440f000c461034030070fa0007800005100321050400340d45102150034407518002c40340160b9980383c42032189840990304031540b036101403070801c042c5203840343e200c041b2106454850702130240301c101001d1504442c2c4407000104400741c8800001c031010400055800b40500500e0395100300c501952002c1079184001506800620b21001d2059140090900c0300040b5800f100094690030744000440750341c1c030340110f00507405042845809035004806c20003008800001000401e195171400f00512301c00d510060b5580d6124000c5601080003407242003680d82605029013107440342036a072030750324030141c0d11a02802402d055518610303810000c1c034040c141c800e00080341c6006884410200d00b040181c2c5070613803640d4010b0300c01da00c182070041c00c2c0c10340030341c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 414026420 1250 414025170 414025193
    0xf0c01030c05030f0a0e06090312010509090a03080c0405030a120314070f050c070504150810060302090a090501091a1501050f0702090403020703081801080703050609040308090f0304031a1b16 84
    0x2e07a42107030031f1401c0c0b03214483e42d06e8004440b100c402d660780400200d00380c10314054490040300d00382e0040a40c815a41e1f019a90b0544c02060034181c0203080c04002021755040180b103818500408100c040c50000b000000d058464180e01c0307541c030600311800c0c004003e0707110344d814100a009162054172120415a202e007050310b04e5000c0f96005003409103140450500c1d001e68000c480c02402103a11800d544500d11064402a1001a50026184001403222103081d0010410303180304100000d0035001564916008042c0c24551107512509030f4100200707030582c64200e42410382c0908080d400c1842d0305003404207911940380024018a0028086400c0600800210000d03581c0071204a44911603868a41c05201c1d490141a0001d05c0d0440030441103800383c46020b01031100584001b0f6260b8803134600350789401c0058015a51032003505101d625004090011780091440b680e404a0900380c014603001900d41e015180f9039a884e0120640302e8a03080318030880c1e50f00502442c0603e050000c03410060000324 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 414027670 1250 414026420 414026441
    0xd050a12080a1a131d071415030403080a090506040308060f19051201060509090f0d1403130503090607060506030f0f0619060f0e06090c04050d0818030106080f0c01030c05030f0a 78
    0xc82c402d408806417601244002c10764212030f005070842100b013000c0042c00c2210801c1650b404000308041008a4490f12006030b010035202c002203800201540c0d030a180103021202603000400d41c0b001d102c40762400207820007200600300c44145290032660103c184142c880d11034180702c1c096100180e031a402083d00408006c20f001400d560551030103180160f20f0b20100700360383d00280112200e501d80e150240b0b000903074902c010041715055640342c4181120b07090190005580610040c02400b0990b03495100800c0c000d0710411000c150750404130249464012080441c2585030001260750004d9040054007550008003401c440d103c1d0642258100001d042e29008201c52444a03203020401c2c0350b07040c0c0c40300d000d05000d0b0307840c200aa8883d41c0c40e0126000324001e080d44841d1071000b02c0003040d4408081d003009460840c064082042d120700080c2101d40c0781d0710044a90b040500600e01554003800300f07103403880d400c0c01c007030101c10306800008225100040c00d0307844e944065401320b8000c0d105030b8020070844 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 414028776 1106 414027670 414027701
    0x70f020d1d13090c14150702010e060d110310030b090d020d030b1c1a0901021204020d08130602011b020f070608060d050a12080a1a13 59
    0xa50b081c01d036003805152070318408000300e1200300f8004000d1215000114420880c04280301b04007050b4504180b10840038004800540d800c560400301c19401105c845a54036008040f900040c84e0030b11290103400404000c111300c45a03204074500580380645c00c0e0fa03000350759441460b50b58086c1c510f1035600581045041e800c820b80650070803000f50400070240202e0f910018401a882003103071a00356240102c04440c20b06150715a0625030f040042c00c0b00070340c603020401c1045440c1143c0680024001c00c1c10349101c9042c8011b680aa40007404c01c480c0a040580d0758841c0240a061070300401d15184003100c0400c42414000070381080180f048202400415207001d0098a50100060802e40c014010340c18020000d01c043c4201e00089104a5686551001d0300c0b40c014802c00f0020403c0d00c203146407058a010010b46a100041049022108207080403109000100500314992106445 = true := by decide +kernel

theorem cover : BRFrame.Cov 413848920 414028776 := by
  have h0 := BRFrame.cov_init 413848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 413848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 413848920 ≤ n) (h2 : n < 414028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
