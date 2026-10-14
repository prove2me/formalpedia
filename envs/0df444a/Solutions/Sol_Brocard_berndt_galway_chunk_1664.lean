-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1664
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:07:12.085144+00:00
-- url     : https://prove2.me/submissions/3c8a1206-bce1-4768-9c3e-ce756d661f07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 299100719 ≤ n < 299280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 299101969 1250 299100719 299100743
    0x1309020f0c0c090c07020112090b070c15020f030c030405070f0b0904050109090c050108130203060f06102d0c1a0414030703020d0c06151e0b0c0d0302090a0f03 70
    0x1204007003103076089040c0d040b100f00840380307401030000001d40145100a81003001070030418504580c554000850349030000c145e000340c3e00c1c041e14090100f020301e2400f02c03034142c1461100c01541c40c180c801d9428003041c0740d07900d501d191101c07071605059420181c0103071003030f01842ea00050f0030070716040114001d01c034128400c0d446d192030394100001c851050f849122a6420b00d124440083c803241403080c2502d40908194200e610381c0c40e0429200221107a0007905071265005200f802540c4400c0140700305012a40441c100794891000c540d82010100054400b4001c90380d00b40078000b410f0701410345000c051800c3c4110300303060b03103078910140084074010b102500c400090106022010003012542c8404000642c5020025034000f1f5032103800300c02d59070410400740006800c1009a07040404c50039011107109448544a6070802050b002c200242480d00c07011300000945602e000e402c0d209812a5070014003108941002d055010394000a03816903c0030780310202041c04c080e82c1032001c0c06140036103921b00d40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 299103219 1250 299101969 299101987
    0x1e01091b020a05030910170f060405060d0302070b0c01240302150a0f0513050409060b0102010b1005030103020d141e0d082701060504020a0c0203010b180703021309020f 74
    0x415004010040031900620040800f00d0740000881c0c0502d00300752659800040001c404880c0701a1a0701101c0b15151500300380305c0ca00000900c2c8501500c0d048500700b020384c0300c45041000c8016240350050140c1c000400400082c041500a407120100c4900045490300b1590300c030500484005100350100900120180150708103030310050002800365000c00c0c5040b140310000b604d1030100040d08410010005a034801111f81140c04500a080240c002c4c03220400074603109000d07004580541b1f00542c600b03417002e042440c1c0005040c42552076034a6407451a42181c0034405800a0a071301503a03444c1d5a1070707260400344000c10440e061000c2031003a50201140f29504503041c00b100c207040c241004070303020a1206031650845d00010300c44d0060f1030784840c1c4d850080d00b01d002d441240d00c802d600c207202181034818a5044100114210701c2200200b0000c00a40c1c100107541c207000000c0f56034080c1110004003410302950080103820489036013003403000d43d101c8010050340d0040030345c1d266010b808a00b000c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 299104469 1250 299103219 299103251
    0xf11010e0615040c120b010c060501090902010e0303040b16020307030c060c050601090c09060e0f0303130f08060903030429010f06030b030c03030d020a18030f021c020a0306051e0109 80
    0x182d0144126420b0010f49003103000140391000002001c0082907450151814584c0540c64503c0b4141d03114078140019a0b40e82814001050310000503804145c4c5491454501d20b8040300310390070b450b40ca5400e5420041c00000c0300c0c900c010410303000ca8140c07188040100c040f41a69203084001c1026a40e00c0110514525040341130450680c0300b208550308182c0301c1c81015420050000c01d580d4a0324140440e84010400a884018200255605400b000074114014070b4628402c4040e03031200041422401c0c0e4990070960388050031a98000590014070110340081d01c040601c0c4c00c0d074600840386200d0f0080205c40c001d80b0360420703804030310500c2818408010068140c0611140d2440032005018400030b418082502ea1003981842c030185540002c141c4410303130007050314036200d9103000c01e140591910fa103000800b000e041ca83c241e1117600582c0d08014011040305401031042e502424202c4d905103150b844201a01018212250021030824243e400d40f8004062030300800c1c0201003c5080c00c0d000d800d0320 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 299105719 1250 299104469 299104501
    0x12030b130e0601180207051203270c0a0e1b0708130902250b04060509491e09150c020103050105030f061f05060409150603020315010f11010e06 63
    0x4d032102d00501482c00803403000b180802e001000c040d8070643d640e655000f503c6210019800c020880100325480f040c614500144060b84114296410802d203900c840008c901c0c240c1c21610902c04d680f0304d81e0f1500c0b0800c074480141c240c4501c14803100781001c241a00f24101c00707195401c10800c4a0340814141412910080c031905a03200d010411b00003583c941d111b40440c0140180050005912800400e100080810880c00b071307083c041c6901c102c0c0002111001400790000602901c0c0d0b00389030b1030b07070091404aaa00e40303201400c041d01c515288800ca035801c24040811140d1041c2407001d20f80300020049001d114080114130596941b02c0c0e410881c0c40050101d844c1a0095030080d88003012440d040840080c4007500900030303c11030282c92501f50000350105401f50401070700031001180004855220382c11503c5c40314141902a01c0e5151030b4074088080b40803c0300d18441900c00c40024110950041c441c840c1c0300b0340a441c080d40f0542c501180076003036500400c041c2900d80d00c032000308084c40604030210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 299106969 1250 299105719 299105759
    0xd06050607260a0516030e18010e0a0b01120f0605040606080603120c0c0402070f0c0605030108060c0a0f080a0906021803010b03010e060601200a0c0e100312030b130e0601 75
    0x20350501444540c000c100d0300881e44110101305c0c4401821003450700400001856030002020580312071410944144040c070280325000c101813419022900b401c01e01d000e0384020703150682d1a81900051280d000002d0040072505a0716250b44980200c1e0a03112400340001030302a580742c0354146e06190b41451314001c41034007180c0c40070b20f05100d1002c0401700403945010b060030454015803290001e041c000362044c1103400040410942090010389150420040c5040303510384002e49040e50b840068089040c402c40603180c2c0014104240116614095104950800c400410001d407115080d86d4110480e80a40c181d804555103100f00d030310040c41e0034007400e6280380301580203210080a620160395105005000d8a041c130003010100c4419030301241504014110203021951041c0d81d80c10401c2950029014a090740c07024400010302170706c6130a4202c41100e906c034103000590810210220000c01c800760032503034080c1c10f004090751624070364058020218044d0b0050315141d49041e088150300c0c60b82080c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 299108219 1250 299106969 299107043
    0x10f0c02010813170a17070201050609040303111e130b0702240d020f04030308010806130b0903070206070c06080609011a1602090a0e070f0b0f0d06050607 68
    0x10200142d9002c0503081e008411150b0f500c0c0800c200b40340200440d26030084078030022401207058826a0303400011500f881401d05070148640c0c0314100d08030300f0703200c04842c2545c202c400d442c04100028480d03885030900e07440b41c000b501c0c20b085e40151050800c40008410040c00764010038480100c0c105812001c008ac0040440145006007540c00f05005002c14082d807207524400b940b640d020020960121900c4040354102155102010306828000c0d070000e010590006030800008204031400190f45070180c141151200701908995550409400c0020701826050000b44001f400589900b40070342107462148040d034401500748500104281401000d0f40c9c490341008004100d021246200428003030b040c4007406a07074200c02c0080c880c041d04c08190094002208200700000803240398041c2c18050550710660705800e589a00c2c85105030180d025501d54040200130455162024100411a1011320300d0040f480b01e589400080307958020081c15507a9104080c8018201506120350101502031050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 299109469 1250 299108219 299108237
    0x31f0e03090102070b130308030c0408010b120a0b0612070b030f0f040c060c1a010803030f07030e0c09100b07030f02060c070807020d030c0204020408030901030515031c030e010c050306010f 83
    0x70000795200c0d058440c00d941c2c3c800008510300e10b407601d05401006150070504050381e80c00c02c2c034251066544148600022035103484010202454030034003004012407050018444d044203503c95800301d92000d4096580a581d218401e52046001e1280c2c5000b418049203850b03c80c901329440c50040c0c0001041c00190007008d40821000460740c2205c0410788a0516107400e035402e4500d4210b050380b81c00646214500031300400020a048000300961251808269401c200d4503800f400750199a201d15408032190461411500b15042140707020703a10410756000c00c00407990351001c0c00060b9224040c00d07000105002080c01303010b5010051142c105001d00101480d00e44030341c541e12190f020310640280720b42419403451060502c82d4040c28005a0010400c564039555564855a070781d00140b401d5000c2420700f800511640d03140c114094107808041c020f425010324201c00300c0384849071003203100b0515503148d4081d0351858027407140c04d0420304140c445640d00d0a00c50700160240465109410070000381ca6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 299110719 1250 299109469 299109487
    0x15012c06150c031312050c010309081608160b0702070b09130f0b1f031a03120915031e060409150b010212070f0314030f0103120c02031f0e03 62
    0x1040714054000540e07035a9440d258840b1000d4198811913a554003025001c00010440084e41101400500c0c4617104607403002c8007600041d02a030b61480d00141c00d940d4144004003003245214086a155403042044c18078085a148264a0b110328500055640080c107404010361260100850030240050b481403038102031810700016a60744514140d4401c243d281d2001244840c0aa082004403040003030201e042d14001380c0b0007100740c1c410720000000080c02d010100648040c03203044549100c1001e0b02500405004141880b000c0d0700284102e604a4086601c607403100740d20501841c0a5030040604002120348074800720306d10b15016108a01c103919048100b800a0811280a007070814920b00c08a216071046005030300700482d46000040da0180007074044100003003285082203040c42034961005400506000d51158001280d0920a481c3e00400510204080c41c1a10401c1541407031301c001c042410741c0c00301341041c104680080d8481001c00c40198641084d001c1d03001080e0601c00154140b44102d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 299111969 1250 299110719 299110729
    0x209091b0f090f0d0f03120b03031e070b0c0301030303140702030313051e0c100311030a090f02120307060c0f0c140a0b0702060a1112010e060315012c06 67
    0x12200403242400005580840352603603041201840f80c014040075456110b41401c800104003400100d001903038140112254000b1441060a21840a4011814501b50030340f4800260f40c05404180c24100034803260001444480391a40b0480004100c991030754903501e006400c2d04e503400701c3d4511000358802086070281e40003041d25800440b0264131840c0c05424100700e0f0800c910050381c8500f40254608042c040e8400155032418034605560300038102c07401c0e500403022600e074188030fa80c9900c000c00102c2c0d00807031103030080c4540a000d034a0191084045600044903090b446d012020b55402c0441d40c4014070045104240c601003003402d207043c803924011402820200c0e071101c0140792900c00040c0d00b0380b2000400000c4070b2654070802c03000b1541020007000c1d64540c01120503440d100d0800c41c4504501c16490261136109a041c20819426420400c03402c2800d08000c100c01e41600c0364215044d1400350040f0054020400e1010309001120040c613410704581c91407020086030044c11041c03148503210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 299113219 1250 299111969 299111977
    0x30c03020f030c03060a180b0316060903080d1107060b010206130b011511010e0604210f0f020a051002130f0e0c0306130c020c0a08010b100509030a0f060209091b 71
    0xb9818200d80c4c1c079558100055403203405a088401c1c4d504484000d40d03022003142c0c1c00f4648014080b03003210001e10150b103038184203040500600d0005490404100000752842c0040e2485031902c80c00401c0b01307422041d0514140e0043d070000d603145030321054441d01d0355030140070703a81d00625488002d017102c41c91a1a4121011410712980440139500340d040c54405109060201007501c204000b4002029142c1042c1d51340c10081d03c00f602c41e084044040f002c2c1150903c01c6107800d079401e448004c0e82c644551000d40c1e0320641c0c2440d01c41075000d450840000204140450b89145c04140c2d0b0040e151310b41c8480c10416031916400c28240d03034044030790910103828440d40c0c0543c0512010700c91076403035580501041d060030092209101c060300f070001050200340c012581d008050230680703240c00b001c2d03564000c09003699900c0346015001200720f050b001d40b581c41040201010000a8200c0361100d100755903070030314002030031000d276825580404e100495260901d0040d0300148003090320346462203014004101c0b446 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 299114469 1250 299113219 299113231
    0x1b0f0f060b0f150f0d060803070309052b03091214010b0103020906180414040b01030501050c09010c030f11070605070210020601030308130f08040815090d0c02010804060f020415030c03020f03 84
    0xc0c01184c4100780c4418034080b0748041400240c2803207680d03916404203681e900015411000b14942440105032030520710005401036524043c0300340000c007074408403441c0111610040d800c200403110080341c07a5100505444001c1d00c42c812700e0741d40900c00c90313000d070861344500307059070402d40100411891035440c0020f0307420f0010980c05403446605914001001012090035000c9031303c6a82041000b0b1000308040c60381200e010304000d2003155142c1510281611a810f00940841c101d03010103004244501245c440c0c4000f00d00340001c0001e60017080510705085540305034009800089c0e45421800c0c400c0580a1054050009104e01d50450ba006031400381e0060410b40ba600c10f440e4102e0034445400c1d1203645880d0412440c40d912600c0e00509a141c00c00649008508501500802c0c1c9240000a40820082c1e0300d550f888503101543d4011920848060025a00c064540e501044451b9072403000b00014901ca009426030f031405140084c060351112032102003494030502400c4030380241c1d11b0480342c0c480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 299115719 1250 299114469 299114509
    0x80705100806030c030a030503070e06030c07060f0b063f0c0d0207081201170d0206130f0b28020a210f050708090f010203090d1b0f0f060b0f 62
    0x140da0300003c01c0c60001e2208080380e040c41050040810705030000000c0d4098010307940c0f03030480c040d030b074206001700e600c819030b80380c195254100001404246241c0c0000003800c00d185012800b050150002600e6400030384c55981c031a000d54243c1d80100388414440404a6046410341110420417189210520001080780041180c0094050403440041e41151300c2030380d01400183d1110000340700d041110100b40180722001c0c070f603401c080300c1110001800001c1030315183e004040c01e503500d0070b550140600c4940300315802c1080f44411000505001c64640c866030141124020820440341b4402c0506005400c50302c60501c108003800344c3e50713030010f4041ca02042020104503075044000d8200020441005440f42492030700041c4000203031301401107170040d40720400300c5d8111700031403c0035401c0b848240d98213001e55100454a01d0202c1c0111640d4081c1461290b641c55030f40c00c2d03030f1103200c1c4d03075060480100c440160740700364801000400e00c100b80d525101a100c040c08242c4900124210300d02071130500480c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 299116969 1250 299115719 299115721
    0x7051e22060605031005010516120504090e030a14040e01030b04020d0b090c030f010204081f140403030b0901090902010804030804140706170106050307080112020418050d02070807051008 82
    0x10058200e40503121500c810410006103035202002003a82d042034444a072141d103c003c0010719036101d60140e480c03900d40341e012130f00f03803c505a6520040d52000b2621a0034420f06000000d0082e40c03078481c1034400d010443c059640d498020a0003400800200000c00e00d10307900380402c2c03145000441d43c1da4196039101c0d04200164603280006650029566401418a416001000301c510341c0170ad856500707035002b40c01302e442440500d2089401c0c1d01882c00f03100101c4e0321105801c29501c2954515030401d450b007010004101c7c80d42000307504545c2c2c0072038082d404280c03200c100107100e0501c102294010f1203100701c208505101640002c02c2c0690141c0003404020150021500340700241c4240540300c07541744125082c26a50790703409001c03400050160a12481c420000040d124001c40c00c59218030010b98071a440c1d0307800c06140d504c100d1103801302039030041e41c3d90781c22500f140c00308000960501d0007007000b81146400940020b10300001c45d04800c0e2560000b43c0104890f4440104100c004136040c103100801e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 299118219 1250 299116969 299116999
    0x30303050702120d091202030301181505040507210b060f090a080706171506070f03090503030424031e0209041b0507120f120902010c060e060907051e 66
    0x3e450340311600004407481c005103418200c0103552014400310301c910320703001e140142048142d80324042403240f520403240b00c03528500d001c24070760300102160041406d01d82c07031035407108042003c580084508501041003000302d01224288101c0030360380c03c0444041444600810300101d5450b0080c0b10720041481000316070002280c1c2d40c0d2403410054411030381211007513946c44c00c0041044021b115a50704e64540b01d0046440b03c841040c41240702000581164904503050b0355008421808282c10303020030a9800d07002c00e0300c1e41c0c2130000340000c11411040407404410132600b9050783c803400014100741440c040c0001c41c446c120070452100141b0242006841d00d6401001c5030203000c034868641384c0000918843c8008030740050240005901a0341c44880b13030140800e00303589804000c915a808241502010100703000c3d25080103200900c10300d03200c0d100b41c0f200e0b520701041c1c4041da29842e0f2190440d000f0003c24072402c018403c020041200ca507800d460a0913455490541140600d501030300b580220015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 299119469 1250 299118219 299118223
    0x72f010912141605100203210405071703070212010506010c0605100506040e04030e010c051515030313032d02060901090e090c041104061d0a170f010c051201030303050702 75
    0x1482c1d105180945407103050820110000c829a03002e19481400740128044a5610000640c0d5007841503403105003840d100940281d030380e1030b80200111103610601c0c501054107801c4050f92100059014019a26110240704200c00442401003030a407c0c1c0c5000204041680e2052580c1e00031504601300103070a0701c8032a0300c50440c0085800442d08070100080014000d40c80000c402e120341e00039a1b620304080d141b4001140d80e80c040785405400d81d880b0f900603c44401c071410306070342c010701800c452145281d01030002c2400d5400500801c51140300314038081041c4800307200015485414001044e07080a000c210303129050440c0d14010340a41404110107200d40d0082c4208005800d00e490304004510b0820b031025682c1d5840340d80f6030701450900d02c90480c5170b03205c0402d032001e0b20b4954860244188204400d41a00c580c2440403503400100901d0005011042c0d043e44c444000050016004040c00341d20070b02c0c251041d0f804401e0812a0410040c0f840d032041034601e0307054035810f18010411762a1000200c2c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 299120719 1250 299119469 299119493
    0x6060d02040e0a0b061315060509040b1c0302061006050406031a0306130512033c100f08070b0901080a11030a0603050c04050c030a110f072f010912 65
    0x2c1548034808402090180010040d4841e02d402c0b20079580a185600c2c40001b80e404400081c21441d00d044000d000030341c041c40c0600302d4640b01810014402490600081a0900311481e0f4040540c90209040615a06200032a8000000c035554560b80c0c1c0f4100d8000c03c2071250740b0a00041640c0d0311003c0c1443e450880e450580c07010001c003150114100000c81c07440b14506408101c440d07206151043d03c080c503610054a100340741507501400994045002c110300c4501c2400f881040031107445240310b520b18615960350092040c40c070200301240c140f411700050040d0720307080345019a020300d07003c01c00b0390f0030b031002c9a05007603007868400c2807038617003c609001a0940c0e003184605180044100540c0341615406101124042c0003141c00f04c1e0300034001d000032250240c40724480c6207810030015071109050342040c00610b0030700121625110303407036280022039005560b0848032400c07007018030100c02c8a6458960780b0402c40c82810800710f0078010000e424a2098816008103d61000782e44051000da03030950 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 299121969 1250 299120719 299120741
    0x71806080d020f10052a1204121107081c050d020d140a0c09090b010903150b121504030305063001110f09040906020f04030c03020a0e04030206060d0204 67
    0x140c0c00c01c0584500a51151840080320501d0303c502c0600951902a80c09118041d03c5918840140740d641a5505400846d403548943e0104204201000c0c2000f40034100a215074019140030190404030100103001240042c00c0c4502984952018004c0805c0429200e56192541080c54104207090009a6040c02550044a540c80c0301041d140d02460b03a907005480882c0c5062400c805507680c0078406411102c4084110380029000a0280003500715940301c00c2115505040030070a05a4990f90000d4a0711900318140056442d141b051019040032401000904080c0c8058145050390340300c0c0343c02c10a40203001904260300e0701c0208030720741c45810b1414064002c003e07135a01c0c1032810550514844036980781e5881c4540ca403807240640504007905840b443c0729030074026840c00c0c640f8000c01c40075011440058680340da0030064401420440c0000f440103521a030102d0300c0c12803960042000f00c5016511035880c2c94075581c100000030740c0c04111141e01c010112880d1041c01a28000305000700851612 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 299123219 1250 299121969 299121973
    0x110c1e030109051501031b0b091203090618030708030f070f06090c090e0601080c01090902031b0c06090d0c08030a090302070e10170c010f27030c030317010807180608 73
    0x1303e101884410082a040e24059480111000ea6510908040603500d2203030180c0d001081c44260001c1c07805040c1240c240101b40200e07401c00000b5400107a06901a52042c00100300c07a418065446c01c003806000b004045241c050b6040202005900403a4412150014440c6100303103280410031126a200120300c80e0088550b0186940b1482180001c0c01c0e4010f05014134401c00000003900305001645422020b0f040c0d46031200f1600d4032400d0030181d003024040e0224483d0745a00b1200700e031016009042450942001400581032003c0c00600700444901c680c01003014020700c0d48041803424046a40001070b2690024223240307282412800d054a40d04104003940e540b801f4803031007a145003c20000c0c1d88541d9980e881403101c00d01415510621824614082000300705046000ca00904e030a0101c448200d9401d10028075140d514a41014250021140d060060f04148140f50f40086c030070145064001e04194294102021255200198031440c100320154841d4000f0340342032904214018180f00c02 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 299124469 1250 299123219 299123233
    0x5030408120705160f06050f12090c011101060303050f0a030b0315221a060a090c0201060303032304110d0f06050f100b09011b150b01110c1e03010905 66
    0x8803071620b900840d4256550312a080c02c240904803845040001c035076a1480c000d51013841c0080a440e80e17080240c181220040078403410080c1c0b800c44d80030074441e100880c060018001070f1400504001d46400340c813141c1d0f82c5018028400a40c100303088a80d13030b25480320099118540c074141200a0000c001144d501809040200e9100904074140d060042c3c00100703c0b0980c1d19440700b040c0e1010444c1c0d01c0041c00003221401c0400da103500c00c0c1ca00f107401202c050100c0d0911500c5e440104242d40c003185004006079500d603010018140c0c184200302201458010303516506c8000d075140c01402e00d015201a00304060120f14200f40d5440250400126038440402d81312084d8605082c001854100e51507111400754000248030708030f68003078960607142d01c880e0403400c10b2480700044400d042c0c10041c030b0f06c0300c86000d41c0040c0403c00c59052561105e864140101e4410020800100342a5240100b5410307544002648480341c1d85032100300384542c80203240391100c0049800000d0140c48504409800340c06461 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 299125719 1250 299124469 299124493
    0xe011202070519120302070f06020d200c0610080a12030f0f02070b15060409051504020c010e0f16121e03080103050f19030c0c08030409150e0405030403020d05030408 73
    0x4040f4541070342c02416144000e00c01c82109405a00c2000300040501003000c03034010018109501401d1010b107500c2d00000e0008145101d4204c02115150680250902049a85864000f008a1035001d08104809240c10b0324200e14030780e890001c45001000c1030022021064903920a034000516001c00f00c0060000c90880d9101c50001c0d0301c44c404c10754420300d070b650000350b00c01d42c210202c000e440800b90006281910b094020700040402400751024840c0f107422801c480d81d00c80c0084e0000c3c0760000000204c804460103450302d090810150701d1283d4000070300004040380407000c3d003001c4070300182040c0c1820040d441e0603550f5821404200b0320300c100303070414031080c140d200c14a10305a070b202e1000c440d90700c0103800050750f1f24140c0d98201e4855001d110b0300034001902c15200002480e03c200346034000c0300d449840c060b0031071300540c00920607680d61300c10801c603084c815030609000301b0f044014100d2134101a210315880c1d2180380070190081640c155440c0401004104581c000e1411000740c403407400301c0c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 299126969 1250 299125719 299125753
    0xb0a050d0f0203070905180f0105130207020303120901140603210705030a0806101803021c05011407020d0503090c0603060d05070602011a03010b0127051e0406060801060e0112020705 80
    0x5d4010103029640030f1610208812800c44114003c06001c05040c94917072800b82041400502c4019481d0050707028094036006890420107130500300c6164048104600c0c3c140c1c41542182c040c208001d41448400c403e01c4500d03103010032540004281071100800c0d6080809100d580c92280e150000c00d140f20000d184c54200740c0c0214414041c420486600340400da4107601201d940c0042c5555807041c501440c030410040c41d00003242072144204031000a049002d41d11201e08450140e494420302d05148010405403e80c103006d4030b500c5078594202182141004140b40360744080b0103900c40e016540000124100c3c0c0d40701c0ca820251141d10604544082d9140d0b0780080c003800d40413070014203140540b03050805624040c0100c518004069654180100d4211a0740b54000c00849038032000940e005008903c540300c42d01c903124000040401c21600020403010310086442c154044010404800c00500071103512015642d40b900091900e441c00c1c0300904026002885100c40040583c4108902905100c3d90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 299128219 1250 299126969 299126987
    0xb1521160e01051e071509050109020916120513050703060c0315030213050406020c0d02031207081332060402040e0102090d020108040501060b030c0304060b03070b0a050d0f020307 79
    0x46586110307644402400540f0540144003d0030742c00b4041340c2200c5448a50300024000301030041c6605100d4103401216041140c800c910151002d0751640c0002c01036040260046802c03c0e240c01400407140844000100304c24030341254414516140c401141d10305900244003081c4a4002c1c05031030b80c0b1a9246409001050070700b8203180800d042a1900e1001002020309008407a0003410b010f000ca051510884000c003001072003107601c0c0342c1c02d000d011040c44040000d2803100006800031541c070740b0702c080160940301c0020b207c8010041500c0400070980040c05588000a80c040c040958003444a10802c28181d003100145d42d07a20455110003109540000300180518004d41c0c08000040f04003118078245e03c0354118440c0c010106206403801940318901d001c0d0f0082c010000010499144c0202c0c203455070047e2108036000101005000511801c0d2094503075648045004008451030600012075602810498a0a2010110340740c90f21100725005100001e518130001c55491414220181010078 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 299129469 1250 299128219 299128261
    0x30c06010f0510080411010c380402031c020a0b16080f0f060d0804080a030302030103020a0e041113020d060305100606020106180b03030c06040b010e0a0b1521 70
    0xc03150000603a42088000f58252080c107545920f01c60b40e4907160520000007006078035040108290f0901c0c0801e407070701181d0b200648410403580c0104200078040e1074a0800c80c0107154049040700500c40143c0d00001c0f816024580c4012040320110303c154142d050500036040900510311040400000c0c01084050042140c17031600e50300b4464444201801c1003010449000e0070132401007000c40c0130340ca00116014440b46c4180d404501c3c4c5a12602c800e1700f071040342281280880d401000600461a1082c40c10020701044900182d2610b061b49841e400140b8220b84503011b80300b0200804040801501181c158100303160050003600c1d0340e4505240d40e1038080c0c00f4020b0032860024040b0b00c030703407041c0036071000c84005484040214800c80c41000042030903140041d4903110801c40c0e000510410b00c20544218000c03500600c0c0d0798540012400c03217050041c101440540b820704407a030385964204000b180744542c10300301c60719484e2000041c181c5803880c106030300c03184858008002c1303460b01d03840c02e40006c84 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 299130719 1250 299129469 299129489
    0x70f0b040c120f23150106081f090b0112020a1d010e0901050906010504030c08010f0c14120402040605031510050d050616050f030c0901020c0102120d050c0408030c0601 74
    0x1d580b01c02905400a81502c003c0c01c0d24551441e01000c22001c120203000d0300c0400c0c0c4000d0341c0303840c01004140380411580818114000d0314004201198200020b1a401503070002c203003c4030900000c121406c004180559504541d0710345909403103034800c0f100b041b04026060007c40d030701c00340007001030640c007011420010700d0f403d9290114400d52281050020406010701050743c16403e21080001c81c441c028000ca041200500000000c2003000f515600200094800040c065085085110a9403808018007003403020b0740c01421076050303103041151465400020300084a4549100241c05002c07960301103a41486034001d541c5614101d0707894140140c402d96181c04103250360f441400400302c129040581990003c100088901d00d549688030070141030340c58500d181032501c5942280682040d1018042c1100100300841c1c4d5503010801c019002c1800d000815102070612507140312407080c0c0d00005c290a03107032000300d0105c1c581d10082d00c0152040c1402c0ea03840d05000ba1000c2c1d5924024490300c4140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 299131969 1250 299130719 299130743
    0x21010501030e0d0305040f05060403170718050f030c040608010b040e0d09052106010e010e151003020f0c10150e07020c01031a090a020331031103070f0b04 68
    0x1960003482200030071502c81000d4514941031100590007020f009009941095518144000044052040d035101d030307200c0d456107030341820240340503100d00c18018005001e0005101072880d054110950602c100c034030444030650542c2c51a004241000c14005500b40c016041440215507504190411010030300181c070708006882d4503030360103951800401c0c01007020440c800c40a014606150b002d5501080c01d802100d48610400d06003507203000340036071000098164510061004950a159040c3c01004400514032801d84c00300001703447c441d10311191003d240c1c4c0054018041c07101079054402861580040d201c402d261900c040c0040c0c65101040105a44080703800f00d5580520b0200700d0241f0481e40c0104104801400154010010f8207d0000ca881003090300038015a0741822180c440c41c0d10000140c0ca81c200044001500c0800101e59682c180c907210b07844e584000340741602190250589440340c0a081c8411180d401c510401d000680507241004201c070031b11a140f4003032802544980c01100740 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 299133219 1250 299131969 299131979
    0xb0616060606140f03010b03180307080403031b02011e020f060a0501050a080d0909020906040306020a020a1b050102031207030b09040c06020601051806191809120e060f030c09062101 80
    0x2603c10781d0340202134440107100521014420401441d404a881820700000240e00c0000da8a0358110503412503e0640009051007015804040c010201907041d0000c0c5400c3c2c51035001907c604a50501c0342c81080e00c4182040503141f00b00300c0c508015540c41c042e5440ea0030302c0c00700280900030900901e0301400140c60002907825000824014120480d686e641d001824481007002a501100140e5400b040034440032000c140c0503c01445458550340090042e14050318111824121407401014001101582081940d802204658420707032260030801da00d0742e905409070010030810b500b02c0d81010440c0c081108000e00b610920082d182660200c4000707030b80e0381007080705081101c4c1c0c0c80d0650310501800f10300c4a0a004035001b2120081c0d10421403c581c40e002c0314200c455180b0042910281c503468100c0c14410442c0800d11641070526241045140759404074000d4425807406000c0d040f40000050700c0d41d5180001c0e10030710395004115035955010580a9204146040a44c1043c00200c0c400003036 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 299134469 1250 299133219 299133257
    0x61c030c020306130b0f19020409020304202809060b070515070e010302070c0503060709030b0c041511120f0a0807080106020c0f011803060c091401090302040b0616060606 75
    0xa1300e03800201e000e0256540e89062041c40700152090070b210700400401804041540064006840c51050041c0c4a00e014188000b8601c3c48285050032442c0810108a4640301c10351010201c175107103c8001e4005501c800003c800170b14941c0203e4145240410114040c10408001c0c010503000c2c208036103129442c803010340c0b8491303001c0c1c2e45003010448021071600c00354000e4018001403400384810307600482d61100400d06240048400c0c00015243c18024002c2100400525400408030003a02d41003d0400d50245010801c80c0f100c01c0038402c1100750f44450030010051540e56840342e6002d036403030350f010034076008064121707850b0800890541c0b0000381070144078003a91070480e8480c2c2c0c01405001501c90501641400400041d81000119103107002441440da00307a200a51144a0000304080c113000005c1000185030080700079041040c0c199030440e039000d501780b8240c980460b4005601103020000031550b2041400201301c010702c1d22900400d200b01580320004482c1e8030f49400341d200c80086031030740c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 299135719 1250 299134469 299134501
    0x50106080118140702100c020c0d0615030f1101080702062a0d0203011202012c09191406011b03050301031202070b0f030a06060c050a0209061c030c020306 68
    0x100c624004021880c202c954980060000d1440000c1100e03070000c03140d01c680c2c1c0460748040580d000d004029103100352032058018519407803015000210f440380000d040b0601c1c800d4054089034442e01c42c055901c40106001000303551055103a550101e4510b403120b00c09a90001982c080391000000500407800491814032030040c400481e008a01c1c0c181c0ea11a490f000401030602c0b01c0014031684444404510045010300140001c5d03d0381d1034074a10004055443c0d01b075002c50450004154003152004405400c00c860404581410701c41d076507010200c0b2075041101ea810111410050364281c21420507684a029450a0780c5907001c985000340550b0310400f0070440140041c4c01000104080b8510507901005404144156040141d9900c0c080c0c41d190400099141c0c01c1c0782c00800e1203013450441c82402c004004600301070040724500d4640a85802c200540640150404800103040b40c1d5106141e43e00505000300b201c82d50149428020203001d89450128020300c02d80b004101081d000c16116 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 299136969 1250 299135719 299135729
    0x7080403140702032509060b0304021201021e071b06111507050d05060301150305030d06092904060e01150306050f0604051c020607030806190315090c09060305070503060a0501 77
    0x421341c00307014650f080300d0210b080040c400c3c00c00c0170610216035030515010340c0b030081c101c10141d65104e0510340100000c40c50b08d00e885031096032041000d0168510401d043d503500b05d41e03840074240c50718100d0a20b481030002036848010092403040d03002c99482c1c0c0044882d81164110000c983c4d0004281e0003503108990191040300100d031301440100e03070050341e039044140e00070000740003c60625400d0020310100da01680044640f500046190002d140452054100404291809002016102c1c4520000c0c003840450b680780321010307145602c441c3d20345401441c010701d40d80f2104035196a503001c050303d07001708142608000071708051000070b0ba85043c0c1d4625100000c003e0180d85030503c2d01d4200308018a40130060f41580c52003c800c0f10240c0d59141c0500b180c0c034026103440142c0e06d081d030200a550000d490101c0d00c500c020796814030102e05140780c20500f027400c403540051003c03801d0174059a0440e9541c04070928a04000300801008004a82c01003210b03800c0d4100c9605481d055008025503c0901036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 299138219 1250 299136969 299136973
    0x1507020f0a030e0f130608010c11010605010f0c1a09071a0f030f06010207030f0c051c030909020f09040e031e03010e0a020a050f120f0705040f0b0a0212030708040314070203 76
    0x55001d285444100800384c208000e01e0b0405e409400030f101800d9440390b512122603a55900b61500324242c100080c64040d04401000308481d900b4540080d00042c4c040102c8401c00c404d000561080100c41803800502100700d100b0300055262981503183e4070707a000d0180024010081c1203282c8010040300598814071101c581c05400d69944101e958610000105070070304612488000101240a85058092313031070040c1c26404007541020140811031100c24a1040040c3c441064800866030021040302669001a400b60b9140c41031284400c7c2c5000d16031240754401d28055200780189400001082809030f02c82800101004440d0802c8450009208803460301c0e07001c0380000c0500e01c40e40e0003006107203c0ca0825506100006000c110b003a00700b56035409100e0050420f200101c45d500518039442000b503d4803614050400286204e1808a4418890f0301d403c0403c01007040d500a2082c000d400301d6241d1032546034075044900402071035090310160080b443c0c4045e20780c214601c2c88111045c1a0300a00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 299139469 1250 299138219 299138237
    0xb160306060302120a020f0919080c090105030303070809070b0a0207080d0806010c03030c020328030b04020c0a0f08040506071b05011803021e031911030a03090303110a051507020f0a03 81
    0x43c1d0717000a58050b090f01c450358041040f070600b26075281c4071401c020354800720b02090380d035007000c0030a8640300350503032028480e11406004200655002040765030000c040e00d000b0395180c50700a00286003c0301c581040c419220017180e40440254000380590403a9040780480d5101c0d1018003003520040c81c1642c13100d000480e00c4040070082400703504001000c0031144100c91802c0ea5816070b05040015400c4003801070b110810344981855891300500c150300e00119800c5260541c50321089030740d40b0780302c40c0042c100c1d4040c441040c10b10203e803003545c00038074020b490b0654681d210302d003140300d841c808d03500d00340341543d200d07800304140d40700c2c405d1500c00b031140ca000d10300005c1c11754003049090303440f090860003584809400c044154409001d405242951290f199075901290314020021500391406c4a000354800c0241d00080381d4000d409034100c80e054205501d145000c0b103201c505007404881c6c0034200d40b042c402c042e5080483c003d4050720540095017504c0d1011882d010f045e4403200b4440019000a100389 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 299140719 1250 299139469 299139481
    0x10f0f090b0c1b1002070203012d0b0d08070807170723010e0f162102010503040201120204030c030209090a030e0112020c011b090e0c0403060504030c0b16030606030212 74
    0x400104443d0541002d200c60800100840c285040a80b4000c031030031503004101c500860409018a1602502130080d100400c000740e01c0301a143c03a5070b518000c070302a072106c0c0b04492584030028440007a9400030f5495a1b00d1000341844c010a51280f103003260518464500c2c0c14101810400782d43c403650f8012181d1000249059030504200c00440c1d40c84015561000f503450207880c10032099800924000142040500980030307004e1501c02540201003081a03190900b81d80c2040e2040407411941c2401c02545031f40710703400100d0b00494001588a540e0f03100080210500003003440020840e8800c40301c00c1e050340e80b040e01e2191201d1602e44000c02040f0305009407491580107a90b9031525251703040300141007040d0310700400c0c20740c1c4000c040350089440c8810400e00b103907800030400010342000c0342c1030703203ca017804480010244034510000d840c050355070010034101840382e6042d031511034105100d0301e003d050828000315200400c586403404246044400034210780039000755403149a1804090080d503540c2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 299141969 1250 299140719 299140741
    0x3010314070e010b1606180515060402040303020a020d080412050c030d0c0305120c2709010b0c070e0705042606060f03070605070c0e01061d040912030b030111030108010f0f090b 78
    0x102100c141d6140c047d44140f10354200441a1000d0141c00140412582d0301100f03d41303c24050f00e41401a4010003040c40480d80000d031070302d102c9a0580381c101c9200d14605160582d405660021640c0c038007198401401d0040c005900d80300030a0882c26582180c5890714242c80713490070b40c2d01c01000b040003409030010304406101d201d680059040340d080d1401556841c0310903c0c0d000d0400c1c12440c40c052180b4000b41d428070703c00e00707400340022007851482c12524440459440c1b500c0e11400484220141c0040c43d401d00c01e07c280c40040c480c50041e030091402a54240005d420200d402e10080c0c072501e8001841031a12b00703404202e003640a405010a20300300942100d80e035001c034006643e8000c0041e00060b01041003205103009005030b40d1b030700140420703044071003494440d62541640b25605100d040c01c04910021032200000340c041c240052a506c0250110740035111a07807007820500004000003851040640104581000a01e410800c00d03003440d01980c110f5194100c040c280ca000c1c50000b80c1d0510030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 299143219 1250 299141969 299142007
    0x20d060b03150907031a0609040b33030c0103062318010608090708010c09090209040b19090b04020c0a1106040f03050a141507200303010314070e010b 66
    0x80e0594070702e104071886070405444190b68a865980c4050410814880c10819080c00781c5c2150100d0481da0801c0c070000b032011040a00050318401200012904002e41454800000d00708840a4590240340c0c0e0312042e94000380c4003503c2d00a004100424406621034400c0fa400d4400d031a042005049000750080900126130550581050346101e9541e0001e000e0345c10726000b0314041d81c42480d1460401d000340e05148296000280680c18050303503030400c0d604510454250340740400016141c0c0c0841b80098050040005001c0c0c00001d22101c42c0c4003d080080000181c8006140500900d04004288401ca10620741e0701903440e000142500000f90070640034804a01c8003e11803402e00381c40b4042c000c881115503100b250541d010070046810007100b000620500c4d0742d00009801084424a20030510070b000428a600300500344c25035090703180942403c68140071248088070b0f10f075a12443c0140404d040441c3c0b0b0b00b0f56204680c0e00180c520f01c4126500c0c140c5041c107074a039003000074100030345e441505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 299144469 1250 299143219 299143241
    0xb030402180603010209041401060f2607120c1e09050109090911090702060106020d03140720070b090301150506120613021606050114100507081308030403030e0904020d06 75
    0x1400300721441b0b40b599140a105605006299201500c1d4074100340030302034a00800892042c060001c00ca0618030a00306180d1450048070301000b43d6a03900c0780002c40e142c64140b480129400c0c0741404400e02031b98419810a040d030200d80c1c0b101d0303928107aa03c1c2628035000c40e20a2a00241903410b00740501c45458003c04160b900c50384c0b51304100d0b00124000380074160100d1324040141d0018004003c001d0b4104003400809001c0e080421400d400200007941402006001c58140150141c0e00403114040710343c03001c0e4500701c00c0256015135458501c1d000ca6a805050b140b0b2096080580b44160301c030140c4e03140c0c4202c0300300a0410b8600601c044480c1c200c110001c2c61107a10119105918942e80c9540c001040009140f070906840800355141280c00c03210180c000c01d0b01d0308410240700c20a500c90514240c801c2d03100741055030b01c402151508141c2c81c8034401e11040034400031040041d07164000005042508c0c840c1d00d072140484070031418006550b4007114040e46c080707081c1c0c2210f000308900b40e114545c070007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 299145719 1250 299144469 299144471
    0x9070306021614030d05060603041505090a0203030a090e1e01050d110310050703050901110417160609050a09020c0a14100623010314060f0a0806090a06060b03040218060301 76
    0x100b0340340c5403240c1d03030034024940c2d00068100040d10007421a90348101a40003000f103030414258181500c4016024031100c4440c0d040f141c1e600d0100d03044190030032076400030581c000d0860b540c0d21510300300140b4069091003400a441c441201048034001e000d03a000d080303100012241750180e8070707080c2003202e01c04c00d031482503c10051074285190b0b540c0701072246001600c04020301203058100048018100c0b200185481c03141c2e45007111300e402080000d000c071004c503040681080c01070064401c2c030a00b8141904c0b0410314080380c1c807200107080c03500324484004888003202c204096075900c0c00420164462100703103003a103410a0007418005041c04148000c00702c0c040c1c04a40c0038955013011201120f4036501f20b1700700b074032203100184076100e6030b4240402c80202c03c2c6410301020080a001440320a00540018421400300c10340f103c16403100110700c5c0050100204480c418140b51062903101d11511005990450a02c0300200b0440700e84030449014070350140c8100e0f00c1d40a03804054590040142045502d9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 299146969 1250 299145719 299145757
    0x10b0306040620190e1804020919090606031103190201050a11060a2c151b03131a0c121005030a03030605120d0c06200304110907080907030602 63
    0x40720304074003d409260b420315107000b886003225001504402280c5c485a2190951b00b0000c6000320b50101d0050300320741d065428000944a054884405281d005020050185441501018019142c2020381141d0059144500040c1c00320181354542c2400581d2103042c502a000309001544a10001c2c84641c0079403400d2218108030617441800c5c090141c5e0201d8500b62142440c00138001c0500700a049050840400030f40b58400710700d07282d1500d803072101191132030300743e0000141d42600c0103c0c0a42d06a141c82a1940d03681303084201c500301d00c0302240040d40c800c068a601d03021035851540700c0d42e0040806900303250800ca403010030b5400203c80149985418101c001c40000c00361420002801411b1182c2c03404181642000300740b01c603404900140c005264003a0081000350f9410a2990000c1c5810200116030450517416206451034941d116a0101c0713400010001400306c1000d1400100700e046813600d0443c1c441141c00c07507201d403043c0d81c4850741b500003c6c030810000d0700c1503002349104440030040c0101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 299148219 1250 299146969 299147021
    0x26040b0d020d090f020a0b0307140309010f0c0521010605070b060307030b07020c121504170c0601090615111e01060302090f0403020d09140103021c062303010b03060406 74
    0x103a50780f040040f2402c01c0c044216074110701d4a01d086001500707603680d18904514040400a0400c0c8041080301c46010001002c02c1d00003001313422102c016038101d4070a1112820000c401801540024a110004103034410880502512055603a0482d9800c3d47d407582441a50b032151000b01c940a4003150b45846407240000c001408103810703520450b0150041c0501680c2c01080c85040c0780220008981c030740240e1100407445500240890700a9004684400c101c0740d0240e040c0894491500c020f21203200305000094240040d0b0000301c2a2500210a02c1140002840030b6800c2030071940c02d5045900010b251107201d06580b001080c1c1701d19a00e00118240f5a01c3d0007203150140b090303541d81921a045010002890703010426a14800e10910349142d180380b40c0103440405000c4c0342c600b83c0c10941c0014400001c0b8080c1c0000034100c80203010704000580e507400207600c0b00c02520340180281410400f11341403a16040c03080c024030820160241c0403640c0c0c2d65a4400060000d9034041603069030304c507a8094 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 299149469 1250 299148219 299148221
    0x90b0d110d09060219050c15090f150703230106030209030a020a1d0f090a120e0405090a03020d020102090a0e130f03090905010f03020d150618060326040b0d020d 71
    0x820b0601503e070060b652000c0c00100c4403100400c4000a007800b104100c0981034450005005a035014102403107100c60315074895143c14000ca00520b1000f0f40300c0c02c810499080b001c045e07450300039240c03501e04003c10520703e103510141759030203045e65080700c545031300400116029800070300504100400b0b48007222a240d001600d0600f254001880b110040c1c10542ea51110315102140c008000d0108a0341c98508000f5180c0e80f110600070080402c0485142d1800c9580600b1840c1c40c0394200400c01d0025161000c2d036169074041111080c0c1c010300c42c0d03011001107680103200319071201340f001c0d01080540d41402149503482c2405028207058014000110010445100e139101049101c1e13500c501c1d00500e02941841a503406030001c10096805a00410040c0e4880c0c042000c000c0e80010300f940c00aa4860f0f54000400030f6900c6407140c0300c80180200390000c4241c0c05101600d104140c0f00703404411061000c000300751040904000c10700100301c20310a1078040d802404e11342c5000c48000d4a04101d40340500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 299150719 1250 299149469 299149481
    0x5091305040c0803030903190203370f050a0e030c04050705030a0b09061f090807060f11030a05040e04050109150605130c080112020102120f030f07090b0d110d 70
    0x181120355034000e1104101c0c0c4000000002d103502401103040d81410391050341c4922805c804c0241000340d2111030103a075402407041e20700d400c0d6480c096000040ca4105000d003240f14003141c1e50181007410a044007414001d0401c800804680c0e500e0034140484144103882c18220404429818032070b03105075413101d580b18085e1a1007800d4035070720310b5200d003040e560481c1030b5070722895101d120385404000c0248a8466407003103c0034100341840030403c6000207000740ca084080e900300b80140c0c05a90070108156400003505400c40e5610b0350384481c4812a003c58a2301c1c0e0050441d16030000300304000403c2b801c1380340d40c0c41c00e8201d805003000040740e54059a401103172295945500c8126900d03501c1c10000c2e440c00c0074032040390016400c0117009400510f8001400d40390705010b41401811110320400942e4803c00071060100b28072a1a556542c0c032006a624464004071180c040b0094210005044548038480c402d044410346100701d414074865912400c0a4420080c040c000003809126912941c0e031140102 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 299151969 1250 299150719 299150749
    0x903170a020a15061e0308030c030a15080115090504020333090c01030608031819050303070503030603010b180c09011103120103050d031a040c030219021507111c0509 73
    0xc0841c03038034030008440b007170f801074403e0440302280d406c01c0450455000c5a600c00240d580103a40c0360b441c50a5a0014200026080307091905400e010584406c15802207009180c014020202d0036039400b11002038400841e402501034201102030a0502030200040700341c242071041c2c010502c0301d800301d10b1030000e10480f05228a0f51180c10b504ca042e58040c0308806c09082418007461402d50b0500c3e40c0c4038000c482e00c038254050403024200c4e0400500128004014000c000d041d40d648000302c1c10190360700d400c1038460901c80d5103001c80c0e0001c940707440c940c0076116030f2442825011656a400002c506034008000c020b05100c003208c80c61450040920080418580ca074103010941d504508200f4500303020003c681e01494500910640c1900c10a04440000f41c0f080f5004903a0b00d0321018100e001c0d006142184482e00e5a10120001051700401c96091111070180044610340c0c540303404480c07000d14854140000d030082480c41c501151380c1e4008911008850170000c0c9854042404500089120010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 299153219 1250 299151969 299151971
    0xa030509011709030a110f030417010e0703030807050a03140414010f020901050403020904020d02062a16090c09080610180b03030928120302010b010903170a020a15 72
    0x80345800e682081030b02e0300010108a07182c42a10b08141242e513244103c25649040c082000c0710006e180c01c08100c06a0403180a8040c2e0342c0781e541e1500400d01c40f052500b8401080e5084c50092000c200e40001c0300811240c05a440350304030740341c80100390307aa9800304c0410707000c164980c03448804036050f41000034080c0b07214450289036010320711011801c440700c001f400f9032400c1c0100214001c980c0d1101c01c0e40d0540381c04803a001082d448620000e0340e2040180e2000350400070110740c4984081c003903110305013442500b494250111040891280c0c507500400788545070340c040002d09002418503540403411024940c141000801e0710b0700718140c07030f01104549210358407040490a000019111400c22080e0000c02c5d01440210b000d000025168010700700b0395806103500807444100643c0542400c0c0c000d80741c4404c3c84035850384407a100704042454050580243d801c008980313405522412140340ac80b50007002004610314a46440e61407544072408400452140041c10401b29040c2c050012800c088024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 299154469 1250 299153219 299153227
    0x30c0c030a032c03010c17070c0b1f12050d080c04030c12050c150c010b06090303030a1509020a020319050309060a18050118110604080303010b03040f120905091305070905180a0305 79
    0x507071842040000c08d45e008006000b03d184000401180c605600048280c54401c0c2501c88505542d2009035164000446041c1d1004440c080c408080b4001d020038000d540c03864002d0350f468603080094031070fa100042c1502041c01c0200300340e69030302d0401c4100d140b041082d240708880d03240c0050102d035450b0280c462078000005400034604424820340b044024140e03003003400c05d02c0349000680c5030f00008000d0181540c5aa4034184441c01b4260440003500c1341c8003085446908480000303550342c11514255256450403020b010225001d08140c81c803c1080000800140d90b8407140700001c0e2125440078048134184220807030000d02c080c0903500c40d1045644121038601c82500b0f224950209520115000c0d010400080c41191808012a41915a07005d022962a1202c0c0351042c407a40715074001801d5442e40c2040d118280703602c0200007040300c50441c0d200d0324540702c010403200c030016061001000c1d6130100d074040010508940100390703c0203100070410014107a41d02e0003810500c0c0c1240860010f10001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 299155719 1250 299154469 299154497
    0x140a0e061501050706240b3a0906060f0b070c0e090d0e130c02010e100c020a1b0e0705070501050a051b1e0c030c0c030a032c03010c 58
    0x5034001000e050110070401420000f0344948901d00c1c024082c0c685440b4195480c071894101c0d0041c03500e01c071040960303c03039559442055035000140f0400080c41c6500e0032640300903502d11078070802c0d04602420b148503c55990030320010b18103000115034054581d080080c0541d05800f5010080c4409010321b40d44500616010f228034810342c200d005540e03044024082540800200310110030042d0400c0b49913031800340000307440358034444410740f4403d082c00c980c0101d581e41900705132804001941191076a00940c494603080c1e8500b080014010303031048100324003185505109a0074480891380c08a40d0b5510b41c0f05582175030200b1601800824000554601046400d1060301d50201e5590410041810034000000c14110020702180c0c0031503002c1391510f41004082d0040311206031301109942e54401c00303000c554517034028044110320390003011000c00301400c020880040c90799142c1e640c040001800052000d4803078014428189038510010b20403541e4809101e005d03290003c9485254a2000c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 299156969 1250 299155719 299155723
    0x60f090603090c050909070f0515040b0d0f110d14041709130c0203040503070605030402030d050714060a1505060708120723090a120c14010216030819050a0c02060d140a0e 75
    0x5580702d81d000700c092b41d1000302800b8204041c1e40a0f91003400015a68141c0c1225100150401b1406501c00c00c0c0790016003c2210600340007040c1b920080c61040c810704812035001e820901c01202c01501282010004440f01e400f260018914030310018401030350884100c0280781101d440c001c101001d81c2c40042c05200d070340f0b01000040000c0c00c0350700d0071034558606a0301007034039901141d0252091020105507041002558512101e032013103010116103181c6410076510026103a1000c0740109000f0880d4045628142441200e601eaa04880b40303d10301003c904855001c00d00c018001800c104074035090044a00140b00301580015203400126114400041000040010b5900c00000a034407000007000041c40d602c1c80c40e00f00c400c141083c00540040000607810040c108407a103094105040c800b008110115010306006000980840d403828228142615148030340d0340c0d00c5011459075501c00f00103151200061400e9400c0c000c0c045422445010103445041c41600c1c030507111a1140214a565802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 299158219 1250 299156969 299156999
    0x1407090b0a030309060f090e0907060f36030510050601090906121511040e0f060910150507061409100b360112050601060f090603090c05090907 63
    0x22103040400c245140d03030182200d201d45c407030b100170701424400f0050300070700404003a0001c001318685c100d90340c680300523a0758494110380640b401041c0b460030f014414034400c510144010845036801042400c03240600c2c5800d402c040c98140c44605071440110016209001c1d03019040940c40c0c01103031034100b85001414415440d0040c15029180902c01c01540c1000410f480640f40c0080c0709000049a60380810050824094689808100007500003600d4404291031845200c1c40101c4044a81300d600c01c008a6040694100d40fa007803001c1001d00030320074101d80c9155a0103890a0061528050b603550400ba1521140d00d068001c2620707007000480359050050810490000108101c00c5200340c00090f80f42621007107190383e55150010310411200d0072000400014540100e5010b2507a5a8000d40c600c3c10b0b44100445150280c80000034103180160350300071701220356449200038141841002c60040040c48419504403010300b40000e00c585403d0b4106002c1c10a20024003501c50815005e804580c0bd = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 299159469 1250 299158219 299158241
    0x40e060103061a09180c06131a0702060906030c130608041101210903142b05150f03240108150603071401090305010212190b1813140709 60
    0x74542e944030ba9203890701e00d036200c0c51038a03255031222001c1e501c0e00c0c0743c40d82c540c8089401c5800010004d41c0d0490700c003008c804440280100740034044c1007802e145d045005201000f5040003007031005581d1850300c40c010395400780c103180d00b042c100380e00c0031f1811141c0c401c02c0d408200800c4841051005110b8048800100c400003030812001280c0d0343d070400c0c4107990000d5a4045c81c3c969820856041601c0340c0b10394400200c91341013003038546491500401000780d0342c2c8040c100101804000301e80d100b2181c000c07944246010f0740c0700100c0030101010701c80c2c03000c5104a0307140c0c0b602a040c4c13900307070120b61600d4034501d103080c06030401c08541c1066009031405002c941e1420314000c09074108180c40d5000a081026600c202381c29080384900c0d5001a41c0c00b480742e410040940d400410100c04074880c001001d0302c1004194500b200b800742c0781a80200320b40c0c540300c005401c4043c09494500031a000e0400340e810a10150310455080c4140c0c07036103030030303610620344000d4180c0245d80304001c110218010410580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 299160719 1250 299159469 299159501
    0x3170c1006320a030b06010c020307090615110703030c060e16030302250b07030201060806010603020904060b03160e0f0607080c1b01050324040608010f05010911070b06030a02040e06010306 83
    0x108882c00081d80c0b0315810310008210080840000303541da40b20b80c14480c801503015048483c1591101c1c4004d0141c04640188500b0210400200c54040d00c207502c5244a818003a028101082c2140c8007120165540da0050360302c25103419007a152010108480145032080701d2017140380d0741c21458000d0500c82d40b00d103141030046124100040302d007007837246e2800320f658500b92550303298218502603014001590010045004134400090813a8040c0c0040440d0541280d0400000c1d0311500b101c002400203480700741c1c0e001805840880170074019080c0414001d002400002c001000340001459607104160450350800003051100941070204074200888080350f801914215425000038460b000c000c01c03410108143c103000008802418844610040b0060014807a035901c0d12545406400c2686821481d10302d00400010b50310700038802d6006507404000300f581b0308541c5440391440040007030181e680c180942c090241c0140e03900d10a0741200c04440700070340b4680d8510308100c0101c41c09005404855 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 299161969 1250 299160719 299160809
    0x2010609021c02071e050f070603060b03010b0c01090606140901050402090108190e0a0c06180509150301020f0a11060c161e1202071404020403170c1006 67
    0x90742c0b04245602144500600058441c056818215041d090040c030000d1025106a4804180800031448001c180400002c4a802581c0c88108804944051140302102401480144010404a030051801103034110022400707101079190b16003101c103160f0254100303e81d44404400142010a04540100070485007103007017150384000030340524001442d05040d050356201091401000da4002107003420540c2c1100e0500b04285444802d2590b94010800400c5401c404c126080d1510102c030700581e80054804480f81d16002d0002071001940921103034955000d000020003400c02c40040d0141c04140d940380b82928031001c0e9418107100c0c0142800540210070051880725a060700311903000e00341c2c4100c0598072400b0142c071011001041c00402410080c1036208020460b900040d51410380701e42003410034030885007000f04412807256201c0207000c8414450041e184034407510203414074602000949030034458aaa191040340c1e100e030804c001900039646c6000303512207451300a07500510310210803124 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 299163219 1250 299161969 299161987
    0xc090b070f080f070b100501080a0e0a03050d020d0e030304120c0308040308060604080a050604020f0409050c13150f08210306040b01020f010c03050f091218030115030809010201060902 81
    0x300e01c100c820003529030780d000200401d0f4949030008641071660410784107001c9042c198109070381c4040e180304290018070980080391a07003c141c440d0717a0130085404003c0c031004640ba0713015075080e0800c2d846180720700c0d424401e806410b80c2c6402622140600b18006e503550f4546482c14110740305038996400200318403084d001001170b4000400c25085501414010061780d680030004a0510132508414440d01a560910b010000000750481c001c1c0d100700c6480780c4865207002480300300d0750144009030040d40103d201800608101e6158001a0403213000452031100c1010500d000039003a512060104c030302d04000700321440c41804000101c42d200000881c20030045041400d19002c00360005100301c3c4d86100040c0c1e60380c001c1003806000d0b40c0c0b500003408140a442009801048201c07103601d20f258900000074041440070598074601d0400c80249800c1071050304580815007041000b50350550740ea2320300c045000c080800340384003c0d480381e0f0755165150030303540c002070135a0495444019490300500007100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 299164469 1250 299163219 299163233
    0x108030c150402060f0c010209010e03120a050d0e0a120f082436010504050115050c0705090406020406030b030a0c050f01021009050a0c141c030203090a090c090b07 72
    0x2200e409000408480303510b6900005600d8070032807070784084040b000203000c446c50f40190003070b26451100342c03503403000c110380d00d8181511005500da88540345441040358400380ea0041c000381003030041c0450005540710340e10140300c3c90f04c0c588210968209000c0800300d1032440e480050080760780b449141140e60b0b4204603d0384a9041d0302c40b1403400005001341c0c0e1354001d5440d5071408426481038200e10341c80c0e6011214000c500d94480c1119440000510301c000b0035142002c1c01040e04136070845c0040da294404040045560307070000b070a00c603030314000c5010026480e9290b070403190040c2d00038540141d60b41d203003110140c203c1d0040032085000750840070340240481c4028100508407841682e07080948400440100d05040741da1000180551911404400744100054992140351096480420362621030120030790303140c0c03c894859030111420303804000444141400605140c17081c01124100455140043c0e8680401d0b0003440445507501c452070059540004011300515801410a15009103900d07081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 299165719 1250 299164469 299164483
    0x6010e0a14040803041a01230102060609060d0813140a06030c0807030203102103020105101a0901050424140406051b0708070e041a0c0d050417130305060108030c 71
    0x505a08804030000e070074001259020b0a440c0c070003c6c6039292035030319101000d061410301680b8424598210b42c8000f019400080c00341d0198000034400205986d43c0408c014111710003203411102e020060020200300b07545030354081d02400c0307008845d46048441505100709904a98094010142011265400d55802003145500442149005070703403944e9030a20b00c414001241d0241804000c1881007454804c01c038001c10075194400c0d4024089900c45408e8003410700c40d13b0141c9810a01c5040b141006400c009000b0904c140040c14820f0915a454003000500790761640710a00d1751180c10700d034542c3c2c0c0d0b500400c6500703260720740c0300150f0509042c028001c0540c014485203000d40302c0c1b280d4040c01e014200b040088014181c0c0000c40d410251101d9510f80d407100161006ca44802c0c2a1a215a071141c0d42d4103864400e4400d4000e240c00c10507c40e6051024082c0940705407452301c00032243c01c0d500034108000b480e1071101f40102d607048a20b180340c00b6261044c16400000b82e90018400309440041c046031003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 299166969 1250 299165719 299165723
    0x3090915010e09070e120703050105010e010f141804031d061602010305060f091008010b041e1821080609091e121b1c020d121b0206010e0a1404 63
    0x2440c0654071301c4030540b85150070669070b075800300c040541c1400301c501c00108102520b11420017409266a98000f00200000070b016040224108250a003c8566400d58a030301c8088002c1181c101c00041c80f040e02c4040d401590141e00064880005459841c18425a40c10300c074020750303d46107440303900800c0758000c1e180c0c04402810140c0759004203003181c1d180b0b048210381100060410019007040754002080034001c2c8140d111035404c3c5070010480b403801c0c4c840c800700c081c941861840f6400e021178400009002a0012481035602b400a100200e54080810384013861011400f01503a900d850028144100c010119840f461110003006615200410756401850b450301c1079603c010184070406080400200e40042022008210a1500844018269101c1c403500003607840006040c4100c5100f140302041210242e8829422119038600c40ca40090021040740710004e1007011801c1c51146407a010074a42005034406c000511591981350b4030b0540043d0598400c00c400b5140041c2c0d45841c0300000c0c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 299168219 1250 299166969 299166979
    0xc0e1e0d020a0302120102120702072103021005090c0a090203060607080c03042102010915080114040906090b07081012030804031403040c0807050d0c0e15030d0203090915010e 77
    0x2010454890b095020061035009010303007181c0204286450003900710184050002e0f82070404219000d0010905100b580c1081400314032280c1c0440072414207900542c400c90452060400e000310300140c4c0c1c42010302840b020809811010000020484030710840e400c0000168810018002c840c1c2c1e885040b150301c1580a6026500d650014a603942140a00e40c000d0101c60301071385203000300d40b00d84048842024401d03281d40355410707183d9030108011004d040d021000700d0840c00051020a1a00e00961016000180085041382c0e0540d101c0c425200e0350102110340090a006000c0200d401540c01544548500c10300882c4e2890040c21040c411800203018050084500100b400e251080042000c40c0d421801e0360b50340c82c2420302e8144448146031040000c42d0007808404500707403030700e0010940304c240c010f442650500d04143d15079400260103061400c105600201451060b01c1c1801103101420340c0d0340146485244503028091002802000d90703007210003c5841141d00d03a0031049864040c102907072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 299169469 1250 299168219 299168239
    0x5070e0603130302070510030b2704260a0809060a05042a05040203041401110306060a031e0608100b0609010c08070c080106080a0201031d0703030c03090b0d0c0e1e 72
    0x9059042000607040a42c01421041c5c7c0382d005650950041d000c2c074a0140d45000542c0790107900040041042c80da022450045140802c0c04200612095410115041200b0402c841e642d90400c0142e40001070b08800704d05244200005800180319169000e040da0804ac0b00502d860b0303481d162145005a43d46203d401c00c0403101c0780101d6150f0250002d018040c000319624102820207500211861031103426560811094010310040c1d1402c2c0c0e40074000c003070a400d003071a6290f031080d00070740310b4181042c25291240804200741c0003580035542c01062100301800c0c00302000e003084e00542e007088955078000c00c0100545541c036644401004407240d00725030342c103031215064a0488071403480e0b6403003180c4540c2081c0e000300303e00c0c401080c2e00501c3c038401d032020003501c00021f10b08800310070b03106018401600a00000c00110740180d821840e124407030f107424204240ca030742010780c41e90400d00b050b00d441e6a45034683c101f4150030405410380c1c450b04079900b8100036004040641c04040036002c031401201092 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 299170719 1250 299169469 299169473
    0x30f141606030902030105090706090b0901030209031006030314030103150203060d05070303030203150117311110022a040905030c0d0e0a080303010e070c050f0a0605070e060313 78
    0x1000600001200d2a009003880e5615080200074002c020010391003540f9141c0850146080050407101304c1e4001c0c0c9035008050328004501100d90044140e65041c56000c0202d0316240c2e406010700081520b011100140f801e05609000340441840710b04510030103810001440410705245805011460b00c00000d6a00d644441c04101c0322286100c0050540c42070171404020190190080c2d403040d404c00c0400c800c100140c40046480030104c003c05503880308407074041501115038071451402c1c400d1a40002106620405c5120120b1502203410b450500d03000c00d20041919000a0750350a020719880203204c54400d40712080011a155111442000d84412502400e901c4a41100e040d441d0840c0940e0b46500031003e6070f6444003d288141000a0154040b09040d4034000052005950f4a80d00550640e0308290707005404c0400540164180080b01940400003642040b5030b403ca404650080d286082d6a454882d0540304003a052606002c1c00d508080c0b115240c1205070307071748040d140c000d100f00244d880c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 299171969 1250 299170719 299170723
    0xc050604081b1b042027030705061b010603170702010e180609090c040e010b0f030304060504120f02090405010b042a12061a03010303021c1202071b06030903030510030f14 75
    0x2185d1055030420110b0400020b0042001d01c08011004504410558007542c0416866000902030f90303a010509100c034016818003150107114021350300000007544d589a03214244e01680342403000250b20000601d030011540e011007480704030a0240c2d40c0c003032841c0410307104000950008140900403280480020740000f01007000003031404024004000b10b0559120080c064803001507801e001d03c1c00c0414070720366801c0002c229001c980680c3d9465045c40d040c0300745001403903a81c2c10b0175603044100280d2480980c0d108116140141e108100010341d02141d1024002070f00d000c0802c884420200d02581940010b801e0f4503100781c41d20380e1400b25040d014450b00b000007401c0036001165074078000c030000e030101002c4a0085068902903000c45159011590081c40315160180b100b00008030070f00036945c44441c1c0780e005007066a106108148001c8852501d50440d1400c50380a07500090300c07080d00074103158044c4249500300304440840b0030802c0c11516005603100c072480000704801002c0420b01e10083c0c007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 299173219 1250 299171969 299172011
    0x806070e1215100504050c040305030307050f0c16050118080712021c0308070206241003090209070f110a05120f120c13140f04020a0c050604081b1b04 66
    0xb6030321241c0c80303052a01819200c0c103020b0203501d00561501000c584c0403c02e07070007074500301c0350b0060003540396984081d02218250410054403490120a01c14101000780901001c68201ea50071030040f100d906d0710b000140800c516201078110b054000c03d06128801d400b00d05103081c5c40cc00d0080d0002c1050910200343c40780e07190700d07446c0080c4400760780c6441010341c02400e031030242c195a4202c1340c0075140d83c07500c5181d406819501d07a01520941500315611301700003181940780c2406040001c1d130100c141c1c010030941001183d80c6800199031207035603041160441221850f0300c0e0b40380c0081c01d110b151551502da85644441e10300091350300110b081c5210301420012039401513441a410101c50914148180964011001e010003403070407400040b440b80f40e2100c4061500600802c49002c0b900780c0001c0c480254010525a0204039101d04404c002c1103041005d02c0c0180c1c41990403641d682c11216140135580c001c005c406416801c813105060505440004000600008480024a0141090480c020940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 299174469 1250 299173219 299173243
    0x507030227031e060117031809040317180708070e0c0315060c0a03021c080412121401090b09060a0306020c2a010806100203071b09110c070806070e12 66
    0x80d00402c0c60f100004080b400701d040380c84904001c44c90410040006840c0d0085018185c0c02d411040100c0b07401c3c0c41c0c9140c00b260410302a0420b80002a1482d40004c4410030455400d288440c1c1d004100314070000c00c0014000070030302c0344082d104550400a0388105107402030300b44030804002201052505a00e004c0b580c08005000303113500c0c0d1301d500c120840d603103031044040254050b00414030140c07010b010300b07504004520340c0d1707690b801d0060340ca5076640e5201c90498000d980410004503803000e52026a8031a40b00085403001051005600d01100c10041d01c0512050600071286401800f02944590203500140c1e80d0084000d0780b01c0103100312191800101e1101c00c1c03820a5140b084049103481009814504102070f40d6828050340c5883c144100841c4002c84400185e00400600000c5101d416400ca0707403030405940411003c1d03403030012000341e94010b286541e104000280014400004110800007401c0e00c40103090340b0310300000d000c0d1805500005182c040d151159041d9003103c000c0c020319000e44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 299175719 1250 299174469 299174503
    0x7060e060a030209030c220f18061a0402040f21050c0d170a08010509150303090409030c0b280c05030c090301180b010f081203040f05070e0a0f050703022703 69
    0x8169050703c0090204101d85c0318096920b0a074040180303d4080c02011b0702222070100c5040759040c2791b0307200300050503103200007141b0038121100010107541d0f03400100300401e19440421303003050400300d000e0320340010408100300c0302c010800102c0c001500451903004000c81164082c071070400314141905001500c10003109200d10019285217240d0300080e200e4140c030b8060f2100980790755000800182c014424801e140c2c180d001f880803000e14a000d03001140d05a1282ca092501c48405640740031181c6003c0ea210b4424001c0d18041c0001103007104004201240050014003200a649802a19520000e4005405c0200000f021111605c00b50001f0803050240340c6102c096802504052280e02c80c21300412004890f502c00028070f0000c002000301a2105250515155803100d55580344091108c41013141d090192240025580fa81c0c012064410801c075840401c00b61040c1e004032040702c40041044040c140b051140c01c440340005160001c009581c03a12401d03184444000007480c007500b0300c03034a40c0d1072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 299176969 1250 299175719 299175739
    0x70315090603082a0a150f0504060501090507051204030c0c180b0112020c03090d110604090c030b0d110d060209030d020c1003110d18120806010207060e060a030209030c 74
    0x1401c400100385208400107001d01c480d845240c0f01d0054420300c030021001e91720080d901c40200300820342c03010540b4421040010300300c0caa25640410390b1011075059801c1c0381d0383d000400104d1064006d295201d1943c0c5000c0d450103107001041c0c43e02ca400600007500300410140180b0800c00c03815900c07409040794103000000c50024602c0c0d2405081c01c900742c40d0006080d01003003254245c4074000d8030780841c61503000d503041c62892400c6c07007156800740c181620580d44a004400054031810300070809004a40b001244510341250080c0a030f40c20307960070030b004585410403880032070396003400c00c80450002c80d00805408128205180170b80100c510070f41e814020000f103042c0c11074000400011100c030680c0e0b038a92a003c61101a800c0300c0381c3c1c041c22290040d0070002241f04188d55800b51840020982891080040546131104018140c03840d050200d8004414403200750380411802e0010070b083e1400490818603080460a240a009a00005c2c56008103204174666402d0111111190003e00301e6203030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 299178219 1250 299176969 299176973
    0xc02030d0212070e1005040b0706020f04081608060105010c0305031512030a02070f0506040b0a020304120809030c091b0a110a0302060f090d0f111f02031503030c06070315090603 78
    0x180b8081543c01c8004203854501003031250500c007407500c1407032259031195428039113040d03e200601d0380001c03011501950f0030451100122600000b5001800f02007004000c0841c00386002a044c0b0700c80c4c0c203c120301d50b224100401c6507a0b405030b10390701c12030340c580b909580342d4503507c4800030f48801000c0e4150740140b0064a410004500101609049199074201c4036641d0703541e07004e02807100c0c26020301504400200014040002d81d030008102c0c8411b68070489161a95500c030150707034007a00f0a011101000009148521441c081007088003001c0119601c0116003801403183e8183c80c50a90003c250ba000070595080d802d0044424a1b241400b203002c0d105540002e190086d19a01d045400e10764241c0201c001c6001100c0004010014100035101c500e14101c020ba000c6d905c9445414019095114109245540140c1050f91000c03040e24210003680340d040901601440c81003654800e40254414404007a101100145a5030084420700f0700040a03c0c0808446d60042c0c01c6411004042e4105440002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 299179469 1250 299178219 299178247
    0x203070321090e130503070c080d090501021b12010b150c01051305030307081009180b070302070f260c0304050f0901081507050910020606032b030c02030d02 69
    0x201c80c00c1842450511025101d016079510403039000c2c40b2a2042d421002401000d0383c40018a00c040c060340032a41005020340e98100681d81c0b640003490b0682203002010301d4150089048000b0344001d00140040c2c2041000c000c4001700c010780c065120780d0411969440390351081d404071026400c09003132118844200030007854194060960440b65610389030014000d560390703036800141940d015010350300d503895401e000c807002c10000d000d500140801c40400900d409852140a01c942c180005140500c5058103040e01d80d200000c1400e0181401002071800165800205400c00350340310401002000020031898000d40304504030400d00e0f0070001d400030a280001008d082100c600b110000c1741c1e90040c0040c0400480700307125500c00780e409591105a40d481072211503502a41900c5d06038200603500b000a8071201c501014400980c1019051107036504090250310300c100d012030400340801d843d580d08a582d4030245191141016682c000710f09030305100f441152540417200d0300540d210000002c1d012 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299180719 1250 299179469 299179493
    0x3030201060f080312040b1f060c0203070f0506040b160204050c030901061203051204210f030e0c15130f0b09131e0b1302030103030302040f0605090f041802030703 72
    0x403600745403002e00043d5034200001141c80c42021131210310120789883e0790340400c0c2d01004c1c0611751036428001d44101c00388242c403880300042186a0310903c1250003401450300380f8000da0082d6440c6091640d0038080b03502c03014102d6007102c01500076103075111112451055408114a4002c1d4058100340078084a00440300146020300d0303210000b0490150349100c40400f01c0003945000340451000e11100b0000805118025070042c010b0001e1003c49039002d08c1d003640020a201004041a0b040e82c003001d603d031749407292140c0103201800801d44411541e000580314000c4d4100100b6000000440b600580c90008a010051001002c10081191691390070101070308646a50350081401c000e40c0300c941c03106401440b00e07030790044105034200a1a0310100e0041c0081c80641608483e07a00024001c0d10100d03c021402580a90b500507180c0d07044c4102040002001e90191041006c00c6c0400422603440d40401c00008004480c0041c1c801c40101d440c40c41c1d5040e00602030350500900c0300000030702c580c40b00e80c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299181969 1250 299180719 299180729
    0xe03030f18010b032e050a0203090c1c020d05071e0617060d170702060c06010515040f06031d030a03050907050103140a1a0d03110c040c0206060f04020409060303020106 74
    0x64030032007120000c030a08030341c0c0c43c0080a034564010308140035251540031144505650502c0d4100783c0400421089055520a07648906080c0d4000b00b00903c0c2041803000040d4644100c0320300c04031000204c3d4100341c10070080c3c4041e1045009101c8170080110800171100141081081417404020204030300208155a204240100721036280b035a0000b03c01c0703450113104003801003150203030040c02c1d116800c2d4034044c040040c1d650f607010002c10000d69108809060910003501c020700d2958103080c284040d2204458101100c40001e12041c0000581021003500395a0103140001c2d10841000e0701c02d50182c007450070380d022030000080d411015680f60300030340d210f0108803007100d03a1103a881d030045003103440c042c180050b19070500c4089440d00705681c120103509803850b00c515175009504c40001c3e59030540d010f07045010810381245007500300700038090300c40c0611080b02e0402c04550141000307074443c0d0000b01018800e05036074154440c2c6586550588014110581c2c0401c05d080d16864080d000b040c0074054 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299183219 1250 299181969 299181991
    0x40210030207021c061521030207050a0b090a06020c061b01140a020307090611070320210c010309020d060c021515040e010b060403020904080702060a0c0b1521010e03030f 75
    0x40034008040c1031b0f9178004031411340790200e64003821940c502c40c001182180440450190400c00101a514615103101400642c28080e0741d5001e83e1040281c1c00b00141d0000b415900181280c003100d5496206407420258660702d101d814488440c3d0881c0102901140340040c0030040e0240320001e4650380c0558454079a9407910b085040d22440180d4204042c03441000039580108001e10000b0302e440707200304881d0406c0410722010804000080c02000461107546080351003203c01c250081020440e80c09102002c0c20200007420380703038003c10441c00d084007002d060300e52214002d503c074520800c00d4100000d03440503280d4131401d0480080c0011100010914030481c01c1056040d40e1310b9061049814044000707040da0f15291555081c080340300c074001e03c255018401400040050f0311a003004101186071603454848d0a03803c0d2802d075032644400340c2104624400d40c1c01810315900c60119003854482c2201c3c044071059401210030340900302c481e03c0b0080034080803060107030140d07403204224020004588 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299184469 1250 299183219 299183231
    0x4050403051b060105060a0c230309130c0915020a0b07180501080105180c04170a0209010b1606020d180606060206010b0a0206011401120203041a090f06040210030207021c06 76
    0x40c0b0195120740c2800780e1540688208204441d07540106001d0201c94070450016901c00600c03c00404454040d0380c541085400018001c0c015151100060400d5044040c081115054040009064151902540b202503c104a02d00725a500030462007010581c4465640d40074540320a00900c0045600e031240c0f0204200e4034041503030340c011201a41600c40241440526040d0714103141c031316500203003104550f40b0040001003010000b01c1e400354415045540104105400b502c1480700106050740321400b00d170000d00c003a40700c0d1700040d00719a40c000d0300541d01503110803454aa090081c0403c401c54607103056560000300070449150040c034105c59182d000c0c1c2d05140c1e40c43d00a698180300e410344500c01608568018000d0001e01c11603418039010624100301000100302c0c56278100e904c25242515402541c0f4417124030b00c60060040750344201c03003001030240381805a1500e5035590f4041c0000303214801c407990005045100f44d068078103c0d500104903844a03850107000401041c082c0d82c013600e00341c0c1404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299185719 1250 299184469 299184517
    0x406060911040b0d020702041409071d04050c040c022505030d020d090e19060b12070e01020a06051503010924090309180609020a0306050f0301050c070f110405040305 73
    0x501903500722411400140d1070415031350103080095201351004c990080c2d4810004084c4601c07042c01c00d03c5070b0071801c020401c0f42e00705000c00d40c007011f0319062076a440143c0003c0000168011869030792101c02558086090300c0611420303030405201d0740441400203000c4040c03081250002059030211981070f4143d60303002101740b86c102c0c2c40d208d058261101007108641c0030004610b106c03c1c100e620101c40410301c80c44008012604003a5090303a80013a40326200410300f5180103183c0c103d00c0d41c00040a090803125400b28a00203505c0e8800e006c0d001c0d02c4a5950000103a6100d03903c1c80302c40c0c031f81100030000c004e02c400519201e101d58503503803800f004a08288040c0141c039a41032040e42c1c4840d40580380c0f51340092414469103d04a0781c81a0004020f803103210004c1c1c00030441c0041c1c59a4001030700c000c10074500b013009200f0071041d0244032500c260f042c8001d01144d102d130310003150b52075500040d00c00c0580e0710504051030882c1514000980040c41e08003003006055000300500714200c03400d181048002104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299186969 1250 299185719 299185751
    0x2010305011508040f0602040e0406090203010b0a0e182d0d0e060f090d0c0e01170307210504080f0127030e010305270c01031410120201030902060304060609 69
    0x218500707000c5070091000c9004100c22040d01510148106c0c00946015182d200b4295441020780301110b40c40d468804a5085107401e014940c0503c400740d82c030390109442c00d03000a001e004058050340d00d0035174034100c1452101c402d0180384900c5021b0520703200445500444013001da4120214880d00c1d0080c18038a0729924800d2a90030381c010300007080d0a0504580c1200d803500341e406000c0940d4840941401a80091200b40d1180d00030100c41e412a5815890055001d4001e0f43c200d0001d2244d8104020100c0014012004048207409100c0ca02c050240300d0a01900d09100e0768200c1c4a45210300301b81001c15003015004000c201000075405084c0380e040744402c211003200007a008002c1002e00d0300001095100e940542d87c003200c2c00c60412034003960b101013041d04481c4040400da40360001c01c0315103015609401202a860b611505007a078500e00100528040c030154054070118502040240096a110b40c00002c1c60030340041c8980da9906080c03030000010403071840b034054140d0030807508004034595 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299188219 1250 299186969 299186999
    0x209060d0c030f0b0117070b0f040302120604030e0d0209010905100302060301030b070906050703020d230a0e12060928241a060f0d0e0303040503030a0e0714091503010c0203070201030501 82
    0x42500800055081c03980c01c0e84030f60041001e010049e00d0034030000025a544100c40120441d0303c01c05440e95082500303004110310030302d110080c0510125080d280050f140e0301180c0c0d04603541e4800006143d00ca25010703a90b11859070307202942c0220040004418003400c12000d40c060003603501c554080c9591140140c4081c0104240500903800501800c056140a18000e040f1610402c51324044000c41a00610722a00404a02000110340310183d161906020b034600700e130400c2c124020501450a500005e0b911380c034042c3c3d59007034188070000001d01c0c1c02c4400b2034441c1d900d074000440002c00902c5c00c4000240340302c26a05501150411070700d8401c20101d4128011020702c00780c140c40c0380404150070fa0407942c0c000d0542b5062150764207980d6400000a0018500840c4500003540e0750f410011040341c141ca00582c05442c09030032110041081d0707000d892500041c968203803000600c6a03204400c0c20015051082003c0e095404e110401c800300303601000a0446610076201004180d895142c50a00141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299189469 1250 299188219 299188259
    0xf030a02192d061e050c040509130512030f070e0108091c0504030501090f14030414040b01111204170f0c041812210506010c0209060d0c030f0b01 64
    0x1d00341000400c20041c507211101001d400400d00980d46615643c0c0404840074810900d0b60032202281d03030044000c2e24000c1603007140040345200d04113401c080005c0c0e03141d130001d40300c0c031100311000c40c864041203401d01c0404152403590174107036103070720b001010a90411400c49a0038000344002c000700070030758007981c00140614074160041540c1090910400b00890410810505003d024400000064824015000443d1042c607a4165090701c52503c000c0c0025030603450501c940042c0700c10702c4106c003082090020081c007101d000c921804190010796103825800d200600c1c41c020300c44200c210101500c0180100d441070814207401c4102c00a1494598040b00c004010f00e07080700030310740d44500d891f40015110301504d40310b07006e03c0603441d80d480c0019840c002d8190007145c01458080350303030052406a8440784022607410b01c41890000700007080b41c00c0d005030003071240d9071207408203d85845144144a44941c0100805000354403410b004240c2c007044641299441c0d240400499600d03524822802144 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299190719 1250 299189469 299189483
    0x3020d08061206010b0d0e0a03021209010306081c0210091a0711030406080702160605030f0c0d240609050303040b180619080c030106050d09050f0f030a0219 69
    0x80008002192180409040306a01c24401081120004000d104181c02001080704182e44c030b5105508910a0300d405c004000b01d01d80140c40c2e11004240c0103d44c8800601c2501c030103a6441080c040181e00170300490f080b1501f948a565055443c2e52600249a82e0082c1d080d02101e96140002c034010045d82d03a800001083c440c80028102c241c5814036500c55044030150404102044800920f14030f9504181d00c18070025800c8030a2052498041c02140d020780030703241e0510002420008054140c3c88003600d5400c40c00082000500004941410380d0400721031355a080c01882c51030107500b46069442130085c03c25802400300000d0b101c0c099002c040490354050051030500d803030b00c845c10b803242c0c001c0c10340300002034403100f00703c089559040003c0008401410700007070100901d110043c441c010050013260f01080800040c40129044404d440100288020204900040346052030a003091501c290000c2d10900d07006030628940480a401503103259804c5500c020350394140d401e02041c00c0e000c060a09 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299191969 1250 299190719 299190733
    0x60e120906070b13060e060f161d0a090507020a06050609070f26070801060305090c060f0f0f04090605180103110909211911101503060e01050609090102070302 70
    0xe6000c040c815403001c2904134919071010b0b01c1d1220343c2a0761121914688036001032003001171051024000c40c2d00008200d0800203d00100034014242c614061003840d14009203004611080d0b4411146402420030070700b0a10440c1080d05020b0340d500c441003c121203060900c0000307242400c1c42050b00303105008a0740c94022020031004169410380c1d807160000441c80540207055100c069a51041e402450607030b5802185615044000b421660090102c0d400c0303820208000229a594170184c2e051707021008800359880351107007492241031041e07100020422801090005a0100c6035100108231041907840482c200580d41418001440c00d00004145415650f844022410700440107540030013060700b02c4c0c0c43c100d5441c43c581c490700561000820140e000144556485000842c0c1010310409410407441c030b403a40f000a15100d10b4208003000341540e888404000c4414810b81c84402150808000c124190070804c1c0c142c0a420101c80031800380140d903021401c825014406c5501c1c0e240c04ad405040c003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299193219 1250 299191969 299191973
    0x506010311060d023402181e150a0503070b0307200a060b0a050f011b0602040e130218010501051806251110020709020a020a060603060e12090607 64
    0xd030780c0d041d03501903810220611141074540c940b440200070074299000401c0b0030200d00008503400e440c1c8140d4070304074550040141e4006840340d6410b4415600480345050b0725546000b030900039198040000300091f071080382448503040041009054018060380c1038205a0b40b9101490398072076a134840c22281000410000c2d000a00c40c034511903855419001c001c0d02e000342000c26034a0007200c01c4007500c202d0758074841c0c103034107140c80794180700180401d8a000c0002900303400007070010040c5102514520b05a00c13031080800c45564122005850805403001c140d050015121000340701010089005007003440d10884000c07101203103e4102c500580d5034504e0030000303800c04403941050921440d08810103000c0c4008001d0200400c421010500d0148180d0044500b0851458010282034900550494800500300d513408150341e030035207004e0240941d803003140034812460026900c0c8040e0040d403600c0d00200c20003140382c104002d0324010004a0f07a011010760b2555200e40318030810a0b80c007003810004480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299194469 1250 299193219 299193233
    0x204030317100315050703060e04060c081f03020f04060e010305030310060206150f0f100e03010b100e06070c1e03060b01080106020c0103150b07110916050301030f02030c030f07090e010905060103 86
    0x360110b0383c0e11f4007041c0c1a983d124840321600f001c3c0c0e011124580c90303a00c105141580000010361000007100b038410080b00a010080c0c1030485400080d000e011f0408440c1c0c1c054039241c02c20310081c00380701600c40c81c56a490038101d4403500241c0380b11614030241d1200245561002a0040c014104900103204042e80201000905844110120341040010b054074815944445010781c8420140d1503c0031200b01c114109400c4443e00c0600714440c01e40d0902c5000d4460740b0084040204105a44081d925081401c0c402c0c4c5549240e84118400c0780c01c1040d40b00c2c1144582200742c1100d11860302031011401500c01524040313824000c0130016400011011410742c440d03000060490143d011000c1d0244d200c003880c0a955201e0389064994034400341d180f40540c1030028006601c04800030071200b940e001070724024071500c03045c48040c1030f405c8000100c000703556080c08019801d040041c22102c0c4e0b010104c2c2d021b52581320078410160310a02d010b0400940c4001805071119660740f01016080680c02c40c1c0da034135 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299195719 1250 299194469 299194471
    0xf021c0215061f03200f030a090212010c050a1101140f0705120103060912020a0b13020a1d010f1d0a050703180f02030c1507030c03020f01020403031710031505 70
    0x1a03400000c1000011218100c070070700b03110500c0d86aa005c14020b0700c15440081142410390242d042070300410403489a420420300f900e8110b10182c40100e50280341e0b00000c0c0300d001042032240710951034000d0100700160000010240b900d1140c844045001c007420885088800e6400203090b8000b1020002e454519144d500591002c1c16061150030000001c2904040c0da400345c0007121503540e2281c5907030078803803070f4a2010444200341c402030100f017400f680d9154007000040e00d684030f440940c5a0000455499482c0100504052544601e19140346014003000e02028840c441c0500d00d1080017103541c10704900c0024010b440c4440c0e40d40940c441004180c0205002402802010b94800d610100d6201c0c241140c00700500034500041c081c00d85004140c1855042070b41c59120b07031441240c3d0515000c0710425030b01d40f190141003889002c291401c4c142d0400c0d0003c07000c100b103544001404000c16810410014071500c001901c0000d560341c1c00c0201c0d405440c0790002a280f8050000051500e0080381c0200b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299196969 1250 299195719 299195731
    0x504050708070e0a0807080a1b0609060c0606090c0e09010b0c250b03072006061008070309230f0a0308061002071a0c0c15090d060b0901060f021c0215 66
    0x70004ca160b0702c040c1141810007680145010b90003030b03880c0c00144141010b0303105800b0030b0314203419041450308102800c20b030801d01c43d45080c0721024000c001444241e84c0f00070000c0041c00300c00e10104000110041c24403a10380c0f007840c4030710003160010520308402d006840c60300341800004c0841401c2903560001c88034003084045a000010040400e0500441c2c020f94091002d80d11401800c50407030210755241452040202143e030300100400c107241e40d40200541a05003a4180540c4640b02c000045000d81400c09014180c0d40c0ba100165442c0034184a11a214942c1c14082d030340e40030700b000340007519180f6414018001038440d0f00855200d05d412214010a8600d50046480207a5204040302c0038a000503e20082640d02140c0b03114080e2007409003046900b0120b0f10780e032080e1040b0700320b2805802809100c41c02800d0089d03200040000c580d010303003541c0500030180141d540e510700c00180b00e200d019500d0001030060100d1100741d000942e6000d1109130a40d0050f00c007620400d0984000410700801c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299198219 1250 299196969 299196979
    0x20c040b060c0f03130e0601090504050916060e010314130b27010f050c03190b0109030c0f06090b03010305030423120d020f030421031115010e010504050708070e 71
    0x2030b2441a00d01084103551580b14400595141c902100104808008550001e00c000c1858010401aaa40700502d1015210b08650000305c0340c4840131582c3c03401800c4c2002003001403110b240841d2b11034008204030119207090703070f050240e0f4140c183c4d00c00401500390381340f0080941071500307000041c5400d10820f80c0089081170904921001c2444200c900c0e60440b81a000359540386941c03106007145004040d030111168030f54910794103103006e441004102c010842d050050365650100150784c4541d1902c4011504410b245600e280c65600b910000d442e684502c40101d600004001103003042e031415281200d8006000d181480d04d40b00001c500c21041550b0403014500d03c00c48010b6596940311719860504804005040b81e86610302d011349040040741c40420158014041040700d0f00036955210000c0b5880807007100703030b40b5403441c0c2500c070500c4c181001d8415001d038421a072522400c10f04040d04855920fa00380c00b03a0703643d980c11b0000726030094910400141d845d42c00955901d0150b40e0704402c03090050700e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299199469 1250 299198219 299198227
    0x31c0903021003020f300601021f150e0108010b04110a050306010e15090f0108091902030a14030319150e1f0f03050105090313051003020c0d111c020c040b06 69
    0x1158078519405186ca1030611107541c0c06030700005030348418500041c1c44032141c21030700d82072003c000303507640e4a144c90015420240c500d002c215041e50780c201116079425010700d18003258803600495041070f070900500720705601c1c041e0b440600785414084e007030451140c41c034558030702038204608032203e81c0020001c0c0c0c10700620710f90160007911440700074052090a50390303298071052100c003003000348004c8009036410000c00c0c0c0c0a0200d8144c3c00329541042c070a4003c8881c002c0105440400e08210800f100a00021211101c82c0c081ca0000300055103c1c0b010240d072842134100c64400d0350100c400c6034121019044101000f413200d5065041801d40000c4e1860b866a0001c481091140c05080e090308111742a966100701001001320034040c4c103400040d0540903509210324070090030b0710440540f1a8510030f5250803640c115060099040314103045454090300c4d041440c42d00007401441c103920208103584a20003104164061540d50115001281c0d07028100c1c00d144803042001514170407480a0340580301b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299200719 1250 299199469 299199487
    0xc1c050f060a021b210d09050d02060708010605040602060f060301021b03090a060504081b19060c11060327010213080105071b3305070e031c090302100302 68
    0x42540c0c4038401c00700300907030f4806030404112880c111513913030107005a1001030ba21849240600c0758018070201045406d40316043d0f9460f05026041c0d41c1c02c003600c0360054a0340d181d00309030b0110b0440e10501090711080c80c0c9998904080342c040c0710780d00c07032580107800c840040350710032110500c1d80b500240020300240c1807a42000070b082d80980080101c1003264000620310355035062007514880102411b040103400d2500d4000340e540c481040c01d00100f59034050794a4081c0c071703544041b40031b030f101e40850030b85110040e1103020242000300c0c0660150383e0311540c008081e5451511300f0840784141d040c03c1c4044040d411114198038840e0203140f680460b550244200207040d2802c84211009000709400403d07541420340340a800c9002c441010424a00030300c00810100e08103101210414079403510000804142041e03c9410194032224000d0003800d00050250003588840c2544221808a050341c1301a000c8411004001ca0f014080c40045031051504001500c7c214008045500321800c5c0940f42440c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299201969 1250 299200719 299200723
    0x81e0a0807020715120504032606040b040e0a030c0c0b0a021e0a0f08070f020a06050309010b03010221100306020a0c050f030f0d0e0a061b0806030c1c050f 68
    0x826154001624110030050341a80c1006030030001e1010f003401001c810f211000080c66411002c0090100649840121341010703c1040c040720600d0120180a0000c0c4902298907254501034400b00d21848c20003018506500d4540b00304844078240e0401000d00400a56080d0fa25220410080d1200c080b80480010a040b5400081c0321010080e405020403488a03c03410001501203080c111590780b10f4020702002134cd900080c81c4400384c0154203d85c4504140c5407941800d451024020b4010040c3d02c0c0006060340c01201460203940228001e0111003041c0050500702e004410941040380d0a10040031041c11126900c00d8003e071840140c00001134503610707040113907801540c5500c001151105000300b030143c1480351801c6080014059803406039001c4602001e40036031840301007959a50f11460015503800c00c060765410394011020b001461070b0064000e00b24100907003035004102414005035403450003054420343c0b0080100b00500c28a4074110040d104080d07048222030901c5062000401400b00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299203219 1250 299201969 299201977
    0xe0d0f030e03100b04050f011a220603020a0815100309030e100905090c0304120827011509150e060a03050106081c110703030e060405060409061e030b04081e 69
    0x1c112030101302c807041c0c0380c24841141d200406d06100d101c680e03401413001541680300f03000c171450b0303084c1000e072100302121041301c0c0003e000c90040c01e06045200d0015075141c1540150900b07510a440d031850598404042c2800700300000f0465900144a444096205000c2ea1100c1d1400d0b001c3d10b002d024010700c50000c40c0213901e0074208440030401d0f11100300700c285001d02145030f0094507181c04a041d030070155258090328841c2c02c0500c0900441e100010342249600300c091000c420401c03980102c20840156041c000d042000c0c0d841a01225200f02050301110360142d00382103161070402000c480d1078081000c04c0020041d100c0c661040d181400040807400901504000e405800003518240e8081700100c05017410303080300d003000d2190030350450b60843c5011400348112601400c00760448107003440001c0c42d920441d0001ca41c00b200100e00131805902503403240b01a1200e20b801c2d101c42c02c07680b40007000c0c010f900d071100030020107190001600141911021302110003050b4441d400300c40b50100d86003d207800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299204469 1250 299203219 299203243
    0x24090604080604060c170a0507120924020405060405060714060a27031b0303240510030908030a0b031501061706090105032d07150f0e0d0f030e03 64
    0x1120300240320a00056114100ca1703424a03081c0368081140d1581e8640c0301200c010305004000307540d180041c0b01a8000c4e0541307031101c509001c080100c070300589010310446080500200100101440010400d031451080306c06640000b8015030a0a25007010070245501030b0604a5000d03240e09109014510200690b50007010714001c0860002d250a60420301c80e01e074a02c1081c40182440c03020b0700400c0d0490401012007034942c5050308110502d080c00d90242200d80c100d0b260b9062040040c03a48150b01004440544400701c0d28180d0f8010710840480c10380700084000f600c01c000030408128075983d142d210a03005080039095074100c081e04021500c114400340e03c80d802050045a00410034132809021541c8840200e035440e1042d418140800c0d03070341c5000c8016014021101003888508605450781e10401c050200856850355102d5122407001420300304031101007146501180c0800d400707280340b44038480e03014003985409507068407107030840403001006900b4800064125105902e080c848144108 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299205719 1250 299204469 299204473
    0x1180510090c080f0705090d0b06010c08040f03050f0d2106030204092405010303140c03070204060b130602030307021b0d0c2c060d020402090a08060f070f020604022409060408 77
    0x49044d5001081c03600340200701c101008401c2008455540e540022010b0b01d0303401c007a200885994070001039640c00c8840f8000740403400041f0300002c1c1d901c41e0307000d241c00380e82c46003047d54524440052807a80e030708454418034001c220310051b034000404080b0401b4400a1040002140b040e550307030013040481d0076908080d11800b402c5450324001c4010072840180c00400b6400401c8907601d9034070020310100c40b10707203490900303100003d5042944201300290303140990002e10410490b03554841c504072950160301003400c460011000062043d0010023500d100d40b804c0c2e0094541070001c4424070300c1c0c640718514059440703440300041c00041520030007902d0140c156081c0c14480791121000600003588040382014103616030000300a0140c5545002006655041da00561552646400110508802c0d0040325561250b14100008810310031a02d0303000c0e010989a1000c003615a81003281c880a0442d0083c1d00b0184a440c0c20382400c10f100d00b071505011602c030182d0709160000c00001c00591045c0d02c410015 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299206969 1250 299205719 299205721
    0x90f08030a0f05090c01020a0809010909050a020a0f0219030e060c030a020a0c17120c0c060304050d080f0f070807050904021b0705030a0f080c070306050c031b0301180510090c08 78
    0x1280080c0703d16030704200080d004150035401080002e6403001c40705c1004002c5000803450503120390194000b000031380023820080c4000c3c034060740224000d402c51031400001880411000d0184d60000c900030b4259107584220002005880d00d081e10045a04402c041d0080c100300316010080f032050014101e0842c0b990301600380e4007100e04005030383c8503060700007400b011410107c01d852090001941032215000c80c5025846040281402d030034140d0080b6916040240041040704100020038a40d03820003c90300d9207003154032070300c01d1151041002c5811120440100303001c5440d584c0990844e503881500c0346491b41c9040e272100c002c0360507030f08400055107203440030303222086c0c0c1001d080c44002d028240c10b070011b0009000c181c03900490400c2c0d210001d4070310700c000540e2082c0d09109210020156030400414000c60800203045100ca40c0110380c01d0f901500145606512062035034101c030b04035921100c880300d100000403640e100400740070b0213003c0740d21980d0000043c42c0030b1901175442c001c10300b62586015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299208219 1250 299206969 299206991
    0xa03050c010905012a0602040302030109032303040b0403120b04111c0209031e07080712060b030a020306160c020910150801030203070909050a0f0c050102010e0115030303090f08030a 80
    0x2002c0e25040705041c410100c401c60040001140f1248601040b0002114580b9650802c04000c1c41180c001a4055007081110030074141c0150305201d1640c3c101005080301d00f0302071102c0c1c1c1c281c00162801840e035014203011a0100f4032803500c01100c0030030910000b42d02440c0000250480d0540408868a007802046000889240028590030140390800c2589004210000262202008a070041300f416800e10700072024201040003801800d8020111404142c032624841004228920122282130511a08091508000c5044100c0641c0500280070b01c0d210f0500f42e00750718001190900411468515a50140c0e0f1400d5807a030140c1c05078100000458240750308940b0161001c1c0c07007242130151440040006840c009800c800b200c00300480084c10040c00d03c0e020742001c01c203210141071200c24071a0300007032000319200103045490036002004010702c010342860070b036410240d00040d0020700920401c0864041d030001900343e4401c80c60710113580b84075a29134a8940040e50121240d40c1e0711004248 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299209469 1250 299208219 299208227
    0x30b120610090f0b0913052103060f18010b0904021213052119090801050415180b010302060f04180b030d05030402030a030f09080d110706080408030c03150a03050c01 73
    0x5103c0003c44203121000841c4040780410001800c040e003a4801014803000344503081c41501380026100c003200c10f4642d241c0481c00501c1c0c005840407841540d800c000ca60480c90a40c490100c034109101401200d40e2804221100d81c0e0016204280c00540030080744070056a110078041c4150b00d56407800c100501c41d07017807a03032401e0040c001402d00c03411119041502e1350301c2e0500307541540700680646040d0051000e81212601d0f1702c0d5018265a600340740900c8208080700400907000d6410030420010f1100a890300c0402403c0c02d14003500700c00f01c0f840184007500340100145a2981c524880c68a4150340300c060803100400c103450001c0d002d94880b10245685018005951a92400d00c1c046045003055000070b51107032402c01d03004080c0007a000100040c0e80c0195008802094000260b640103141d843c405020510401ea41d8031481c0981100854668002c118040c09541c20401481c190b036214603c10f1220340c800b0b03007486a17001c01e00781c06c5c00031561080d002c0c2d00075603c6240a0f0005418800c0050 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299210719 1250 299209469 299209481
    0x10e04023127061203110f010b0a061805061317070317030a0b060307120605060a0c080703020c04051302031c050d09140d030212071707030b12061009 66
    0x2a084241144108440048008055004101d040d0300e030781d0701c070307030380b080c030100514403a80616803121244209100745900b0145003115a00d10b00d05494100e403129040701d00700c40c055040c4640c820f4100e070003880524883d1006203402442002c118007903a80f80d00000e4107941201140246120400c2d00902801c1e4070201c20400d01541807000b00741c0c20741150b441d030340c084054602c0320100703040100008038a0541a004416859405009071b03a403401d00c100018010408108044201420100001410308244048840c0500c1503620500c1611083daa00425a409a0320590443c41280090344881e62940f08150282280e150b00c2d00c0310a4440c0f0516040c010403000f40c0900401d54840500c3c0150002e0444a000b0b9141e100010301c42c801340b03000b402030408203418501910031240e44072280e0380c0642c01054614640300b101d0110b541c800d0310803148030700011302e41c0342001b0500020401d0fa9002e42c105124400c40100300c0600c3c86802c915003480c2180480d2114410490381c2420081c14007075120394 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299211969 1250 299210719 299210797
    0x30605181002041d1f061d090603070501210c02070906050105070b06040b030109050307060207020a12051c0302040302062706091c02030c1c030806010306140f010e0402 74
    0x15402e11386404a659820000130102500b90b07180800010020000c22007668901506a052003961a8403044014082801d5034102405918100e1440c451841c14000d018815a0001c0c02858103608103001180c06000c4030f203051000d501c0f43c152900003101640244200c0b021a50b00404e10103241054420035035000707034050303070512604120b01c0011030100d012482c2c0c030200942d40800c6080244000c80e004002083e400b0f4000e00000c0703460383c00c1011903001400308a000b122104c0c0981e45869003207048503510503000b4800d60117105011080c2026800c000c1c01c85031035080050600c4ea40707402140d100e900c0810501201c003e403007000c1e00e00d0300b000d0015a07600d9030305032942800c0003525408a03a50341c4007402820154146460700b9807c6650801c41660030000180c41520322071101809200d840c5155a8200c002c0303014507002400c00d5210707104950407200d03100c105c0c9013021422001c1c42105900844020b04100300210f2410385515140020300e000c0f10450406116605101c401503508803e02c80c0c0c0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299213219 1250 299211969 299211971
    0x105070504150c0804050d06090204050615071b0308030a02030403121b1202280e0306040803150f030303100f090605030d0807050c12030a0e0a031d0a0306051810 71
    0x103000054019450411448440c180f080035240e0074282950203010321351081e58480b2500c40604200b20711900700c8023080788251406d0001e501e45008000540340c0d203c40c00c2507841428401d50700490740d0705400081d0b00180e140d0f1020f0594490715015107581c030480d01e420070181c0010a0008159005103900300c1128902c00800000c2c1c005401e460003002e00d40e00700010402c88603006d810407035466048460545100c0300171003468190881c0c03070b10b080303041c0c030700f61408aa40c400c4000418140070030302c641701c1c540c0300842d9891030b82c1390000c42c000700146040302908a420300307080f030841e910104011030141e002d880340ca1b20f03000d2910140c44e404203c680c000702d41803801c00310100601e4400003500c280003200e17403c0c4611690b803020811589401003810400c1103100d1180300000e188003860003980696040b0b1018042c9500c04a202990b5076980b09000300081c0c03040c1ca4a02da10100803581458812004041045041d0740e503d41e581a07600c10341d10791000851480010ba00d0348410002c2c039524240b002d41c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299214469 1250 299213219 299213227
    0x105040203120a0516030309121701180e060403030f200301061b0c0b13091506030e0c040e0105010501020c010c15020708070b10090608030f030604020702041b0f0201050705 76
    0x2010075116080498148507010011407000141801341054030042005840314200c0d0764824240100942442202900c0c41d40c1d03591401c51b0418440d00c480c0f40108107040c461081a4038041c40c80462207030300ad103801d007207031340ea050b000f0001c03c01842050f00031402a600800c0301d00c3c1c0320714080f00300c40c400f400221508a00c403103005180002542500c0c1118003a0800300380c01064070f620004110000d08006107540c040010208001d8031080c09803159142d0840c2d4441d4141d180c07100b800460b42c868a118a400e07000e03001c00c007d814801d8010f01d00c101f144005039140c1c0c00c90b440118040d03070707030459038001c05946070801070081d940c0c10040880780803824a4509815400b58075100d10b16032050850302c4406400040240501ca001011a45030540c000f110600780d20302906140030303014080c01406e002c81c0c10034600103022040042a2110707030720f00151591458070b54004000c020351000c1c400b280c1180e00c56a0180c04841400174013034007120786445021a18a08100090031118000d00c15414060280 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299215719 1250 299214469 299214473
    0x3030a0915020a020d1104090b0403030c0807050702060d0902040f0f0f0f050c04230909030d110408121b030c060f091902010f2304030606050a1401080c040302030d1e02010504 77
    0x4948000b42c0790041b00d0001030141650119005e03140c01840030b003800c0d00f01004c3c0001c0552503444521003a48035030392111303152034083c011200e034482c4a4003c4e50080d801d12031740c40d001c0125031103034070014801040010b1950802420f0819200103401c0081c100c1d550f00c200c1100b482080c020511b0301e030040ea00c10016032030541803031182c038007440c0106607498041406504130841401400f002d00c2d040207200c0340607071800418595a9a01160500c100c142c18805c0602e5480d41d03c0e0251030a4500540241072a11040f414000594024811000c0010100d00800c140701000f44024002c07280c00f02c02600d0706181824403c480c201000d80f032040e550340000b40d60250300c240101d89607040ca50920b8130072804e09a203003040b180002404241d155144e101000010404951001001200c0c4244030900001d40d44c0d81c01c21207100c40510910180c10030101c007641c0b43e50704c44c010340c4da40240000e0b81b95042c692240c001c2490300c007003100c0e50703030100c1c19210b440b6100d210070603a81011342c0100d1000740814134140e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299216969 1250 299215719 299215729
    0x6060306061f020307150506011b03080a0b1f02070303080718050409021908010c0909090b0f0702070305010203270f0c0108070c06090516060801150c020105040503030a0915020a02 79
    0x120740b0301054820a5a00300700140f084c412926003c0e04901e00d00440140c0c881c07031074000e0a003070340c1082c042507020f80c1d80078080c01c0710310384a441301c0e8040d22500b50310307031f18040700c44003600640000580c0036044e00d0103c9100a1134022104559003e98001c05580303080d4039028001e9040a002042400031083c1d01d00c1c5000075280382501502c4007502c004c1072100a91010a0303000d012010080100070408902090704213056101008070b8215a0724544075542c2d0745140c504640c0050b10203000c0c80900800600f040105450146e0050083e20481d4a0035590791035a85c2240c000341c8518168040380c0d0745a14081210380012414840700340d000d001240f9001c0d49075035492a164407902c1c1030110081c0002d0403c1d01960380c41031581c0d00f180c0140f14103030080c40c04030386600c111f8105002018400c407011445c2d034072484241d4160313042900b00034180f038032046007a00c0240c1400000c034100017082201248a480034000341207148010344810b1000c50804040b90300d009084d141c11700c00c5621160070803001d41c2d14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299218219 1250 299216969 299216989
    0x114040c05150706090b070201060b0c0a02090711060103080a021c02061501031d060420032104030c12020f06030c0f13080f0607020c0307030f021011100e0606030606 73
    0x11101c2c40c40d80482c40072810054068100094140c40c604034210044c002d420207440d220310800d6000f0040541c40d4043c40ea024000d0303628152840e4410008c000050810441c00d6400580508101c01a0b482e90042d443c40c0071000d030001c5841000126441c40c1c0c241e0104040c100600b4105030300d07614501b070800c0085d52110000c041c0030005080d4032100301c1e1030b40260b00044003846001606410590a0740c0c15941d2054156030480d0305000101040600a0144004000c180c400501605144003d1501405401d401100c0d2410020081100100041ca84e49545000706000244d50030704800c240100324038480403030303095800388104000300984100c200084820702c551f01c0d04c0168591000080d40310310f942d12500103d20302d00ca01681d83c0758000340080c034540320301410b5084818088601050584074284d5105c000d0038040107100380401483c000c04556480c2c5120300d80014100d40c41800305180a2113021090144ac0ea41d462880c19a481841020341c002015802004a403c1c075070081014445 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299219469 1250 299218219 299218229
    0x70f08160c15020a12021204080d0b030d030c020d021b04020a0c050105100f270e03160309090f02030c0313080c011e0c021c0315080304080f0114040c 66
    0x1089204003444203008040c903410854019080d0480420004200e0000358410b803100400304040e44011040c3c50b295008441c04584054030390b080300d898569821442d0380005e035a40005030f440784c00c60240d42d10b0800c890395010409a03004a24000300010182c03d1001101580c82103400c0b011000a107038801184000203007400f50390041c0d95040207101101d540900300c1004000c1d50900d0b0901408040040351001a15070000c40454545c0d55030110741005020309100341c6e01d24030500c045100c0300003690b2243c81074101e040d040d03030300d401e000450004140ca0240d40440102d440f626050020315020702c035000601241460451550502d10f2501807203000003492010a502410417010400c100d4600b40d0787d9281c1008000d002c8285402c130b08510300e6110030101e9055a1903d00c0da458424400510210062413403090710b544515908800c402130705000c0805030700c20a9a01d0300040c4084204010001031090001070030a041c2608225825100703079a502214582c1400203010104100c6403000c0700300e603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299220719 1250 299219469 299219491
    0x3030e0303062d03011401050906100804030e360a02070f080307090f0f150c030f1d0d050312070212030a150b0a020c0f03010c051b03040e041a070f08 66
    0x4038400000f5042d1410f01c60126055401c0c084454241c050000025060f960100e541e00300b540d072540c091120402101d100d48001030208008500464051601d42ea44c0190107050001d2203035644102243d2a0b40c11002c4103c4456285c8030342120007150f4242ea0b82100c482d00b0150724140054903603005451507a4800b422214001010851542c022102207000b05814034403500c0c003e40d06c8034000f21051941c4921995165140000d40b9401d100741020b0300303c01c0e132503110039000502c0c00600315000f180c0714190f103080310b42071001030b0b06681d0f4414480091510440c015030380d95489903800210030002174840f03419035212000e0051418401d80a690b4410340d6035500103015030000e05401e0300c174a5035900c211003140f00002c1c0794228039400b040c0034054034000c2d10040300010050023030500b208d500002690019105000d5030302800c040000c00220240484201c07401c00c1d071030b070100f0001d080065808440f0586400c2244002c01a558040783e845080d9040c00700810750540c001400c80a40108804604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299221969 1250 299220719 299220769
    0x150c0801080c04110904060e04030207060305010b03160c06020f0a1209020604030b100909030903030201200d020a0c0203031201080708060601080a05131203060812040302060a080912070f03030e030306 88
    0x11070b5004e410340da00c0660040c81400620381e11759207515488401d940a50040c000c044020480601a0043e14101c46419190a02d0360360340c2c0e50007224440c0c650002c1c100700011598140007162a03030000d00b205100021503941c1d51408008043c00c1000c2c106400c1c0421400c0544400c0540e6400f42074071308a035008411013030150303600b11010341028a00d0f041203014901c7c0c00341c11018154405043c0c400d80748207170020440c092980c460030b079400384550309010309212b0800102e00081400c0d0060002d40005042940f034288503940040c1c21a00001c140810840b55540100403420040240d400142501c40c0078104a00703125000030440400207000e002420f4884e4081500101c05000d44080b80c2d800c03d0900f81d840901040040160540c2d20800e28030744220113440035500001c81c1141d003205d500420306450701907041c0c1c0a841c42100100151401c2c01a415100d2400100400604003984140c0a07a1149030381440e0140481d050902000100e80c02441001200e03220070f081d04846c0d80c4403600344810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299223219 1250 299221969 299221991
    0x9060d180b01080304061b0f23030a020a0b0c03100b0904090803010801020307022103070507111012061e1e0b0a0519080c0d1505030307030903020405060d02010c0308060102031303150c0801080c04 86
    0x1507270920304401c1d40684000100300b00b145601048107036040c0d00c01c8031240050b4075450f00212050106941d408049030082034104449050398005016410001c0c101280d00303445a107503080380340c10036480b44032580d400104002526070305202c001025440c50207483d0900002150303182c024000101a0024488000383d024184050240c406802a030010002e80460b4801c55005020522982c000e04400d03040c01d0020442c0c204551500b0440c40022410742207551801c00b2140d40075040c0101c4085000b03603148003140405045000303108022640d00c1d4180c1d201e1400c02441070500090040c2001c0001c0d100074081c5800e0040102c0702c0040201c9000b04c1d6441d251205001030154940c070041e418400000d40500f05074100060b41c0440b0700841d41004640d031200d090204070001028000d0000780d199000d030700040c0c000d4082c81c0e04001d043c4102c9080840f0440201c5d030324021900151500d41c0c440c0c0080c6001880c50081141800b45072034055110f5243c0550b046d540d040c0d8550303140c4203c3d00c80d042d541c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299224469 1250 299223219 299223263
    0x20d140d02030c070b0c031504020f28090906050f040c020c1e03100903080619030510021b070602030901120f1d0d02010209060d180b01080304061b0f 66
    0x81404030050085540e400c007801d018406600c1080112019205a030009600910b000c1c1564860000764074400c8803020210b00f00320095000c0c2203914800744081c002401106810420f05000700c1c96a03003803043d10010103a007d0010141a0310428006040000a00c11501c1e9181806800d0f5026140030520131321041082c1d041156182c000c1750000c1c110400d40d900804205520404000c0070b4003603580c02100301001c0803d5034a154009004a05480089550b906000d03410507101150442c41480590716070743c1d05410116044181e0004a401160480c032401c50700000500700d8001d032000b003004502e4000302035100e005256080d4140441c8189004002c002500203114a13000b5000c200190740034402c003c02e5440b14440500014850700306410840c0e40140300722101c40f54001c0005040000140d503040140c8501c0c440500d0410702c00504070002003402c95094041e000d07500c059516203080080c0101050b640c11040c18420039510f00050110316406203400f40240c0128020303d04020800000d8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299225719 1250 299224469 299224477
    0x1110d0e21060a0c120203060d020d080d060e0703050109230c0c030c0f160f03060209011707111b01080103120e03031602040605060702032d0304030c0503071203020d14 74
    0x11525025038810058500c0c2c2c20360101318999100d17140c040c0c81e4140c0004640417408200c0b01075410254181d4030300d01500c7c3c02d0b44808460742c441c80300c90385806e40c000509800d450f002e51004460b020f404081c088a9601802403d0242c51901800c1000300050002820180907890782d403800100c07504003159070220703041c3c00c440020358040c0480340d40b03407144150785030b403040700356000401401080c40301c0303030644900c113441c60454a0070b54185060701e0454803400000d42c031440c07140381804108444101400c011081d41d505c102c505441e640701001240718801e0819120b48c29500c845840201e046250342e82003641541900e4111051080b10340001109448481c0c0e07aa00055040c4004034040d11300d9080702e0040f22041e4400e40b410700c1141c0c1e03201c041c00703001c0c045e48000940c185c01c40408001c105d1010b0f2820755185000b941d000700c800b0004150035095034480d82003a22900c50040050048e82000c021400c000c18414100980c2194581c030003d4440001110903c20040581540c683d201181d009503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299226969 1250 299225719 299225779
    0xd0e03010f1d0d02060f16031512111002280b090f16050d0803070e12010e19050613080c0106170c0d020901060c06060e010303020c01110d0e 62
    0x802c0869680ca4010540d40d03640034549080344912030322030300c40c1880441c51901a40c00c0d070035042e2090702c8a070030a401680440e81d0003000c0558a0454110700c40b00c07150038030020801680145092540b0f81403150190140d1003005000d104041c00c0c264000364005606a030010a140d203018400b0288504005608050000540400601e005100240002240c0d09804800c0c040480381d0668210b00080400c1c2d00da84140c1303074015081080d03000805c040800440c1e1110003890004544200b07140002d8150700c001e4110b6100e0780d500c0301c213001050b1040080603a18074080b13650550341c01650f070324035030384034002041c182410302a0410b1100700034503e0240c5564801d100c000340206138640071a010b0324122814461450320402e9541d071010304002d04003283d080e4000c0e20008960782040f0003514058400d04c411680d07541d03945400220741d8100d4500c20f010314481e6000e0030008550000041041c3c2d034010114105403c25035100c10f8403038108061081d051401e42c2c0140318440e0f1b82c404c80316018410303012 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299228219 1250 299226969 299226971
    0x20706110304031a16020a1211031b0c010f090e01030609020105070503070809011b0f110307050301111e0415141605070303110102040f0e0907050a0b0409050a0e0d0e03010f 76
    0x4003040f505544c843e0030300c03031401d690001d150b00e00e40075001c998410440c07201034100b510700c0d10300c9002c0b24030400c690016155020110f92510105205070242d81240d11010842a0003850100c240c66034040d080241020340c62501c1104903041c1400c10f4821801032000801640c0e0318120034085900403004d4900c41c0350460280c070780724145420511802d80c81320a1003800541d8901d017000c0e130305040004e10302ca9a9040002990300102e42e0343c0b91448203290749101540361180000c009051380d000d0103241c00382c00e49075101c0c685510f410740d10160000441c0108217500301e01803005104040d000d403003444140c441860b01e500381906159207401103205100e00c0d01c1030f03108a140c2540503c540000d404045a1095581001715400d69050314200d000b28004c03c0301074490b804080028070381c560909508520030b2810750340d02994076800500340365401d501010001002040800c0301203600d104450b80410848400e114030380710745c1e0314a81c455041c01004014400c0780803125850b40c034250b20901c031075070140d50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299229469 1250 299228219 299228243
    0x9060e1c0503040b030f012106151701021e0304120c0f0206040b190203190815031c0e030c0616060f060902091302120f070c15050a1b02070611030403 66
    0x40d03031013035640125250010072071304a0001520b804240b080400d030103014080101d2a454940d0717078030050908112207404601140d0700110f1030108039010072010b1015280016a01c40c00d10301e1703072041d04c811081001c9010720140304120110f8101044440c04c044185095000c00a03186000c1d42c0904160801a4111a01040104002030f1b840010000c440640298900c040c4440e1401c07030307507403003688128101c2c048840d41a05100e809844200e801c00038815408002410300004a440c2001c601245102a1401c03618108180d8200541e1680320390709802508281001c1400310310700348200c6c1030001c2404c2207103102c6d04c2813151b2613226482a050b0814144a82c0d43d403840300b07601a4200c800214403400c0744a0a00f911800c45108a41c02010801480d040030307a2100c0c80d10b60502d02c0200b0344e20170f003d41c0c0105140090240700d8142200c803001035000890f414449462022200104561018244507140a0180e5600001d900d400c0304c0b00e500d0311640e85145009640e0450140c1e502c000c003040200c0e1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299230719 1250 299229469 299229479
    0x5091e250302011806050f0c01020f0703030501170c060415020307020a09050a140f28050907240e060a020a02030a05011a0303120c091f120c09060e1c050304 69
    0x40e0040003102d00076640d29030000c00820050788101854450070020030030407c02100c0e11184c860262884900310000141080624401d0f183d0640c8854811000a59103a0040c820155101698004040309400a0401c1c0c402d4902280141c4101d0054803024001550076816162003001103900da540e028080010a9a503081c852018240070b41d4407905c0d06040c801c02c0d940140c150300382644103a000180390403940e118040c1c8004c400c8448252a56a0100d1044440e40e81485010307442c050a42c6c90010b0540c1890b0580306280000d0903501002603640c0c87c911615019441266002000c00450b0708a80c0c07124109002d07880c0c0203c100d0000e415015080800c1c05100c8190320107400c40b0640700254400c4a0749004240d02c911170187c507181c40054003030201d25042039540182900003405001c14108540d08110000c592075950400000956419421a440c2c8103601034031030030b998141442c5946609029010386151407010515005110a100007032490000103800e00500d0f4114041c0c1c1c2e5116228 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299231969 1250 299230719 299230783
    0x215070c06270510020a12110421020901052d0a08010c050c06070203090102060a0902190b090f030d0905010503040503070c0b071a01030c0302062a0109140105091e 72
    0xe220b080c0da16015a031040b80c00c0314481d000710b0300d82013915130b2480da81c421009102c4c0c000300314140785404540c0381400046a00403030f807840040c2c0c5d901203203441c03540280c0600c104200c800c0c050700940d01075032030b00200c280700d00c1a0851100c05800302129001401d401ca502152145035180e0200e00c1f03941c01d00070018440ba0700540106190742c007840030748495503101e480c00d03030741d034411004882c0c01680503400040c44a1019405a0b1815100800803c2d0034106a40c854290f410f090f004802240400602110070b0b00d015030007051040025000303010200d01c013580203440d81000c3d02c01d003410300c10000001020440140212018658080b8101c10740c180c543d1074a280581191404444411119032010641d10540f0001d5040b6030340400928481e40c05d603030074003513103801012510000d411300408110144d00101b042190310312450000103992500303400d0028600c62154580c03081c1da490302041c41310021020840f0000002584810032000c800341c00081d28201d015103c0d14400300040410926050320 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299233219 1250 299231969 299232041
    0x60f0706110d24050109061112070305092110090314030108070e0109020301150c050c1003020a03060b070206120c070f15050901020909010501030c021906020702040c0215070c06 78
    0x1040721192010700e654500f00c0b0600b6540c05514007190451004100107841421070b0b0b00403490f4402520030240440d164005a81c2106400320003040001c83d421180781040e03030108a034082d0509040d26040c0d80c8807006511b640e580074107816525115a030250505016403200c1d24451110f83c8096902d40e0741e511581c0d250302480c0a40a00c4c501360000004100c0118000e89059541a13004d00d528000d03040ca0a0341c00210120003114640542040d080550303483d544041d640c41041d803400340c2e03595403818006084030310907003040e82118820b20200e40984c9079002518906400e640d0b00d03110540341d00000c0300c481d020340100180348000c2e5156040422034603001607032498a41807014055500c1d15115142030f405030385070880e0410402d50040081d984130360007000d4100c050740103540c41b485402529036002d0144000a0b10421b40000340641142072500c01c0e40080300d8944050040708034800c20751000010701501050400c400914044140f1040e43e21101c444003002c0048540385603400500d503010702d9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299234469 1250 299233219 299233241
    0x2409060903030411011b020d240905060114010504030c0807081614010804150c02010e070e01080303130606090504060b1e010207050910090e03070c090b060f0706110d 73
    0x141808240c801900000340c9010301e5000c194a801003443c000110383c41c1480d502040e001e10300c6000f10f40050f0702c0740f81c5503517601c034000c911450300300c0c3c5040b00d050458041c031662410414644007170403010070320110355281540c01402e00d91800001010040f602400f076600060010300456000203a05040003c58408462011040d103510a8030b02074a07450707580ca20f100707420246a030310101560740e40c0303d8410168002e10404181501c0e503c501402400c5450407044080540c3d514000800c00e52420000427008140310171100c0701c81e60400445640380d01005d0000c2c1c000b01600100401040700c00d030044400791110903802c00c160f00c0e060400c030340541580c00303201c0d014085080c5102c0219407070180b154203c04060b00281000c3d4940018090100c2008151034040c1c82c50110203e042501405006c004200d018010f40d1036881078100902458196407100347c0a5240c407a071480320ba1070f04c00950b0101c18000d0f00c0e807500c4810a06105000d819450301c503005da40340011358681030501c1907204035000c803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299235719 1250 299234469 299234473
    0xe0a030905010e1309020d050706110f01020f0a0807030906020711090609010b042612040608100f0501050c01020c06012303070b18030a0c061e0503040f03050307022409 74
    0x250754000541d0400c0d071100159410080410018410303140d5030b0800d40880d071014201e14038045050301ca0f0340c1440e005401200001e41c40340072462801a0400035025081c207018021407410340c0104044505110301d4030b078103091000e843c000580e00340c00b0b136100d803d40d2500b00c0401d65413134140d841d02e810106a9080902c0c400d4040038007203001030410175000ea059950543c5183d03c0c0c9800e108414070003011684110000c0c1d281035184d500c2603801441130300c2012803c0b41d04a85c03202d0800d40c0161407828014100064540071074002c02c0300c00e6450003a4000c4034000e00749135566840c04183d440c007900c80d068404107640714080c000102e40406020307801d005000740c12074039541103006c41010b440e1750341442110130802083c04101040303070700000c0500140d0f06c01000c4521000142e80e4000c445035150344a140800c502203180c12620f0114244400500a1403400c1851450030703a5070303a4503203401c40710050b0130440080700051040e4001c0011042007580e0a0b041c0d03040a014000aa1344000c08039908100c82c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299236969 1250 299235719 299235737
    0x10c05150601080a182d0c081203070f0f031b0806012c1507021305040b15091801020405151305011809050403120c05070506010803041203110106090e0a03 68
    0x410b045200703102d203902c41c0d1005c6801042d095110310720001c03030142141d40540550406601144c1115503504e1619200782407038004680703030034041410060040c1c00c07040c50410400c1000703440c0d9800064101c8007141420110201340030040100c004011071030080116069480c9408490398214841902c264026603d02280c1c0848082d1640340182603084103c404410b00707552692841c211090490014407401c440f428004d00b50002181c02d1803c1c0100d2004680d540180018840f641e0f41840e40300811701d882c80b80406c0c0300004a0f0880c00c1c028582d2039141031108044081c3c0000b90100e400609004018150049219440c000c155014000e52911b05100f5200000c02e5401101d1820501d40800d042c0000701d0316001041000c1e00001780210200704510a004060303410a02c10450102c4040c1d81310f0351036804e41c0c80d03c24907141c0c0680155403158002d020030418400d5100c018145140d043c0b4024032031066040109015040b50741140c5041070406031020b240480014004d0003040c080d0742c8000da4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299238219 1250 299236969 299236981
    0x1b08060f0303040b040620011125030c1b1509090f0b010c0210020f0a06020304122f01110301030807200607081c060306060f090b0d020f010c0515060108 67
    0x50b9216501c02c401040800f44010424240503004101211410072901e003035115444c04440d0071030b40e50340305141c0030302c501103640442201200d04803202980e540030203415008030358401500c07400640d47c00401c981201c0200102c0041c4100e00040140708103280001e040c21440d10103000044607000300002185032a080c0850340b14140100c2c4050481a1038941a1102907028484d41b44030046a5106500c074200400c0b00590081044071140703406190010788904186c41c0007078907203486800c107000f08460356a0903070545d5810018039401c4510040da10180303201d078240081c003524210788210300b40d90001c8000010700c000c00f00100070803407058190280100c1c1d82d10800d0182e0070703500ca2541e08003c0030b205410001e1007030310041282070707000011107031054089111001910080d410031103405480b85420400f030070034010080d020f42a140c00a0020038120350105044101003074004c0c0c030131010501d048500d6405410380111041d003003015079078601d610700c1d080303804046c00b507a9a500281c0002c0010741 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299239469 1250 299238219 299238223
    0x50409150f1a0a150c02030f030414010306150f03050901062d050d08090d081207030e0c01030603031d0103020f0d0b032404200a080601030b06060306061c1b08060f03 73
    0x2070f140d0100243c000c1307031101c0300c04480e8020501d8003260144600c00c10210710001c00c1000c0c10051114040c050012120000014151403865110183c85504404501005900b000d0303000c0a400319481c0004440c2d991f403a0b80382c05403600d9401011110071566080c1081c001c00300000c0e41650000c8020038040307136900c1c140015191518801b80c90403105012001d50380c0382402e5000035960045291500341000a0b445201e00c060690740003000c01d0f556410250100000c0c008020000400d0030700304940391540d00d026240a25406c0c030150240f400e4034684041380e0007907050340d83c20031400f0811a20b0300300300c940c0000140503000702c0034424840c510700341c00c00c108800010302c80c04244061040141d1543e90700c01c104060103602c50b00580d408000c160019407200c0c036084005256010080145500d1410074042d0038001504031806000c1c200200455174075038804581450728085114408540240350714001001c000030f0010f04031803c4003206003802e03400b0031654052076088506d503c0b400000ca007015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299240719 1250 299239469 299239489
    0xe10060e071409010e040e0d030c050c1b0a0803070803090f0706170411151308030901020c06030403230702100215070318060e030a0f020106030309050409150f1a 71
    0x40004002e2045000c02030125000f40c100600f042c18044814040080001e080c0c58041905941c1680038202e480d070315544c9030040410000c02410854038007400002c900f601c6400a600304d0503c00d0548440705443d450745001c41c0c00810070b41e81629102e01681c5407000140c0e00585804625118280302d11201120200d4424129819521480b0031812415001c5540c601c00070400e0b191446005440031365612030707000901a44070310140d12a501c00030b521144019070095000803800ea402880f1220f1a660009102052800b044440b40c2d203070395903441d0441b01076400095503c848200703e0801c250380d207803010252201510072116540d0540c2c6140d0100c0c3c0e0b03950020000e001621700c903004100c0e07241c042e90000c0000c0c0f214014101000c42d503030700c0d0681030341c0600e15064003d07400014246500b80c0c0c403150410100c89148024444140b031510020010a02802070030703ca036542d2003440c0304001d0138040d059508692854148000d5003454100c00082440280b10310910000784245803042c64000905 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299241969 1250 299240719 299240731
    0xa1106010509070e0609040f2313030302030405100c050405040b040b09190609021206030c0303160803070c060f05010f060c02030a06050a0b030601090905070504090b07030e030405040e10060e 84
    0x2c6907580e01d0180840d143c0803560401364014004203c000115203560050380109458090301040405200307540500d00310340780d00d0b00301d106108101481a02c07050910b40c04c1049030140303030140c3c0300d4989040a6003030403540e00200040c1840d100d8513050039030f00140a4000c030745044034100300c82c8001d07505100513070b89032000c0c0c1d5912841e00d03000103140224240c17000078400e01d1550002101c90321070036144d049900203d81c0840c629980c9040244c039150420a10b603c00d14250041e50402d900d81c120203d00c040da0020003081150017100084080d842010300c0d07126590468020b1044280c03045854000f081c0a0045800300e80d00c02202240c854010101034907042d0f4050000d004844a503182c0d18000d143c0500b411031700c9a104c80d0781c2a0f803682c0070481c03280078140d100302c0015019440c0c039015150403d84d40c00340d0b02486c1845590b0020440e0001d86542c411a40c0c20b01044010001003810b00354407864000903842440d0180000c90b50000042250341c0503145041041099100c0a10100e860301c22102 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299243219 1250 299241969 299241979
    0x230a052203030c0203041d060a08030c030a03051b031303021b010f0c080405180108190b040f21110f1605060a0302121302010201140f15150c030a11060105 68
    0x2403030010744298070550010001c0d00c1500d05054480747c1c03011252114086044080c140401484203a141034442480184440f1009500c0c1c155083c40315600ea00075011f4290902d076803240007a5602168035030070340c802c104101050350f90f440c03d29214000407684a005a00603c60701020400c198500d2034141c0010b081611104004000c209081744c0360310307203080101c4903664103000001d481d444c1c130012030a203050244050030381c942c1001c03101c0e03141241441c0300000b58445110030401041d40c021030a60021342040c00064003200c0c50a01c40f55040c8100041c2c400c91034544150b40105500041d9412040401d0054940500c20144101e82d81c0641c8113081d0420950305408001519200000b00740c4810541005401d0071521804000c02050403280d03500780880e40340400c030466034203205201850129030042e25003030408000603908603000600b40c6d544407c0007001c10005541c1e401109000361125442141e40e18021034402d40ca9030001518080030400b601a401c10704040420305a050b1040500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299244469 1250 299243219 299243281
    0xf0b0f0d110306010815090c0114090409050a0b060a0501051e13090f020a170f0105040507020f06130210050408030d0504020d02030303090703110d030c060f230a05 72
    0x4004040034801030032203080c080c0301c0c0d40d1a81a10140103041c001c052400140031242078803e1400da5281c0000c000b291260010700742c01c0907503a0000880d100681c5000c8a581d00c1d00325440204e00141040e480203011445075180c22020411518182403251005448030207003640d4441c015101401380d1100c10304c043ca2800307820041e030305400d00075011844541d42d214403c2c903a078070082c0080700c05a840c1c0d41039a6800240742e00150f45c100c0090a27040c60b110a4862051401c56840401d10340180910b6100d00e40380d00c041204c075442003082d5070081d41d410060350080d003000d24011240902c07441c0201d002d00403c49940e031301c19004070151000c541e60200130b14909040c40701c0d000b005000041040b81e01508400401c805602c2c100041d5200701c2440c401485000e003541001446e41a01110151240b43c4130024440003d90007a2020a1658041800310301a0104400000500050109003a11000840c01c03075640c01404454207001e2000c0312010400c0b0349070200718000d01c106400e0008c620389401c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299245719 1250 299244469 299244499
    0xc060a02031315060f0b0a1b0203100e06010801060503010c05040306090503070f1101111911040207120914040c0f0503332e1d0303040b0705010f0b 65
    0xe002141e01c090486194046000259100107000070005560088660303034040510020140040300345c06020665550390a00000d1a4010403048162501d40306c01d0204a140c2c8003103480c1001042c111044a90051144a200151656940d1402d01c00c0708042e41c00d00100040f582018480d03001c00e50a103580701d40c5400e042d912148084c1c03080c85001c0301c0c50302c03042014502140300d030200036001d5841500c100c1c0b901d0511400043c25219021903d80e1300e07801c00d90b50090b840c88a00c3c05020416400303018900b03020300c0200060001c0c0038000001d000720094081000310190701c5244081680c121110904904141c0d806202c100c071900141d81021547d01c5044e0400e1500507401b46600030f1010004600c3ca02c0c024456480048400d80700e4607a0114885c054041880c08074006030b00c05551010700103103100c0d032003c500072016486900a00b0302051810a01c0e4121107101002011000542182c0e038a41c1d50b8485490180d00018054074507519001140504c802280208102030a00401c0000444210 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299246969 1250 299245719 299245721
    0xd020d062102060c120a031d0606060a21110408061b03040b060607060603050f10050915100b0c060403081513020a0302090301091401140702030f070c05180a060b0c060a 74
    0x141460454034407a249030081c5c1141c442d40200005a019500420b041d544091000b801c1c40c001045a0b000d41c101c0350801105843d84402d0700c40030744c0b07140303007041c0400c400f80001c070a6116207007118a1640d040c594800403950000000f0000c4800c400219030362030340d0b000c0028180703800d4005401c0c0d0605041010501050820401d07036000790000300741d030f49000c0841c0d40711001c45a660b4001c90301a0007034109020800780c00e120380320307009885642c14022481d1141d560b5440e81c452284601c1c14000441c04103c4a0340c071082801d025042a09450b907072011011469507940600b250300305d00145403507001078410280d510615901301d50140c1260781c0060a0900c54001c0e41258540394102b40c0c0c28407004400742e0f0240141d1101c01c0c051801050b248041c040701c2401d42c0c0c050100c24039983c2060092000482e4000300b01d83c00040071507140707911100070746054050746103264013003a80106a83c601a00442041c40348a019826001c0c2c1005011758964500005020300742c5400507130b810101c000ba9641c0380d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299248219 1250 299246969 299246977
    0x70b1f0303080c2b05010504090305091203040f0e0f07090b07030c170a050903060a02070c14040603060608010e1b0a061d0411120a05060603040f170d020d06210206 72
    0x1c40c0000f403c201505600e8413000840c60035680b0b00ca20b880130100b000318150311485015243c282d40900c40b4000944028160744141010a13020300410340c1003c80c00102131060340c002d410050a60190256034031690840d1240c2030b6132200c000a41032010480e240d000e0740042c0200c4418612207400c1500716107003950301d981c0360300050360b0604412203042c0d070f0b2546040c0100454105902d03101d841d40e1844c01030516000c40101500c0140344104001030204e0048402d003409c0b580c03c1c1c50310340c01e50011031010902030f0186510060140341070280110300490190080a00c0340000c000b101e109028001c0783c1c145c043c4080004e20381009030b044080c01a60700c55621050418507103500300c15204580c4010804559034540140c28401000c070364583e90340d051090460300b1214110040c40b40d03003030807000503a45120280005006094058040042000c0b40c1e030b070f041c488440d00c080640c0310340e85420404080c0d07010420744460b031407500d0130206140b000c4290504001c0020326128400300c09a42c00d01c401584 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299249469 1250 299248219 299248231
    0x20a06050309210a0207050a081c0201090804031208060306010e010501110106030215040501091a030114030f152707060309020a0902070c1505181c08040308070b1f030308 75
    0x9000041041d03010200e4689460fa05100156a40e440e04184028141900741d00000e1040411000400ca070000000b81e2450030107081140308105181c3c09016801050404c07030041c47c0c260003140000030310400040d103038003001664a401e00c0b01d650358000c15482d40024041c2d52400d405030001401254401c1c4c0100307071004101000044c3c1d41d51241c000400840505980582000d00041c1c14400340d684109510020020710218076010207100c809081c0d203000502842041c80039445450040765002c100740c00c941c101d00002d480525051b9440c1d94690501100e90440301528407150902440c03d0b44403003e9600f1015003d0524241050022409014000ca0903a8086424117001c1502d404520080007054450617244d82c45a1070031500303540790301c2d24011000910106003c4000d1122503510b0085803803030100c2d4180f00c0c0f09a61a1829150380030440003070040b442c00308d0040700300055540144900c0d4007480c640886540d402c0161200015681088120388040c0482040000c1c0a0310702c0d907070451 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299250719 1250 299249469 299249473
    0xf180e100e030d0515040b0a03050604170403060e1c090f031101110313141219080d090f06050105121c0306120f02010e060f0f0d0605060a091e03020a06050309 70
    0x850f480484282e40040d00c2c05030584441078a01040c5180030310814066102c1500d0500004e491038642035100c3c1c00050010300000341c0c44c8003001c00c4904243c102c401459114200f00300c054270000c0d250365601040da03403503503c00100e0036290352000d020702400c82c11174010900042080313003569904500d154921058505005000150700e00802d014800303040c900450380112500540350040c1000c05000d06c2080b80d00485500721032020303503540480c004081c0e00c41100c403001c28a2540c80c001d1005d106003036552100c6881d00c41d1007002c0140903285005045c0c019041030100b40d80310b504201c0501c7c0c483d4440d1003207501c03414038600703051a216450802113119060001b01c0344d0b9a00c501449160f00c000046039086400f8405908640c1c014052007141c2405440b16030a001c0b4404000d140c520910740c4120440402050146450135103410441c05090040e25050303c840750f500015003004260300801c860740f0005845c0314010a041c8541c00d040f03980061400c15924a09402515950300140554103e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299251969 1250 299250719 299250727
    0x6060f05031b0d050d1d010f0f051b1b180601020a0f050309090106050c0d080705031911070f0c06140304060f0b18070f02010e250905010f180e100e03 66
    0x70604c1030100041c00b5041d0303180c40014480c01c105800d150100c24542c2c07414000c98040c2100f17643d030b2101c429000300669081459641d2030030b41a003444183d0450300c3c6400c0788500c42d54050240441100c200403420b06070f0b400c00149103501c00c841181b00084403443d00507845000307400d001c80d1103c0e1128940c80e0041095914208884001c20b00c4a882600030202003840040c9031001c804040045180034806860120140d08100b0703c024640d102c00740064800c400302e812400c0000c00320750f10026800080189455030782d00c2d14174001c180304c0c1c50001c00792555840b4100009645004900070000b0041111440d8950743c1d07107a4504004040c4c008030f0b0032900d41d41d0310420a80d501d9042d40002c00541481490106151400c0300919100040c4409021641810011022414002444148044070102003801221078a0741d1803e10096544072070346190500c000003880071610081d000a40303000d00340343c00d1802c10f000c1028003a60170144882d152a03012058813003441400c3c0e80400034040c60001541d2030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299253219 1250 299251969 299251973
    0x50c0114091305071412060f0402030601021b030304090f0b010f0c0b0423060406050603010501050f06030604020a140a030209030105071403060d032003090333060310061206060f05031b0d 82
    0x64004100d0301404103e81c6c0c00740700441c540030107069060b810071a000e525500c0d0140c0000c3d1a00c4a03111541b035244a81388105041c0d60303080c4195000351541c04000c10016019000d040d000c3c1c02e00d0f10395140410b0040300007440032481070f0342000000c2c1e04006096488d03241c075510810f1440c06150701740001410003907909000c0c00b0034008540500d00448000c942030828004060840c0d034180d005a20a090810740741000d900c4040950303511a10442e40181c440d050090292180c04d20b04100840300000090942c5a0315059406050440340c240e00803c90b554030600c01782c41c510700208807045c010105000040e040c3c501029807014440c031034684800d802c1034494072420401c1c0160030340402c0360808140c4c02040c1c1010414170b18051680040000c0c0c0a1040d003490741c0903c60703020419040c8100e0340000d003160b10100608240c590040b401041056903e00c80c1c1d40c0311480c0d401049a05600342030001501c00c419044001c10340300000c001d40901910710f103440520102c41c2c0101500002d1454000c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299254469 1250 299253219 299253257
    0x90604080a02090a020301080a020909030c1f0509161401030e0321090606010806010804050a020d061a01090819052505010215070c0b07020f0a050c011409130507 71
    0x400011000701500c403074038810001224002005640258414401001455800100780b00503c0c1c0542d45d01e16aa1034000340c05055104110030207003184121040c441209403500c002545c1100c02c10310400c2607032203520003142c946c4988100131020f040090f0043c0000c59291510704080441418005001d02003941100e086411590000c02a1b4000460402008031800b80c200c0d4071810000250020745050000a0500c00c3c004c0c003102e04100884000408100c0c0410982540d180c0090460801044514294001d000320302c0714120004100d03c0380307503015402044e00740181c8114030090203101000642d48441c020040009851b40c2c41541060300c610815850700c0164070800c9052440300307070f007460700280c90b0007001840e5120b64480c40741040b140d9035018014104c00d59003c940c005064503030310340c220b1134100441c2c149455030003800b102c0700070050002083e1811030401e072a20f2448128803092080c0e0340c000c0110072a000b0b504400e803420400724513444158400040d0500d01100030490000311 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299255719 1250 299254469 299254477
    0x180b09041b031d0106030c17100f021b010b0a050103110f0408030d1503080906030a060e0f0709140306010e06030715030225150923060103020a050402070308010b0703050906 76
    0x800429611085000015808010080f80c500c0500081c4005484d40d07840d00049421441404c410724080e402c0e41100c04824404407001003078103c0d0900000c005520450025401035402084490009480158108c0103001d0040c181c140240f4000d5814039003001580a030440e03902c200e0500d1000c004014001c5400400b520141605030f0095032203640601c80b00003115210b440305039214041c01c1081001a40441c00c913a03031040181c400350380381e44580d60404041d045540003245044405400c20001042422034184104103a0761380e52461552046000c0782444100081c40e01500540014045081c04100d0142c1000014044401d441c3c3d407035141914003500581c1c1d5100207500081c1030406421400628805071f901400f004e035510003d0fa0710782180300ca14052544c0042d40f1040154188903003000f0f0f8130b14a4010915064030240307241101e580341e08090101700c1c07244120544c082400d060510980798071a13456180d500700f5900b041c1c0050740300d82006500b1400c101c41040010504c3c0c4460003d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299256969 1250 299255719 299255771
    0x12060f030c03140c0616240203040204050c030601120e070f030506071e09030b04171c0f0507080f091006092a0219080c01050f0610180b0904 62
    0x25608160441c0340802c448000c00c544840540d219819413403003990746004598a1682500d264254080c1d51f2801d01c1800020307440180b440603603241101e644165070780066100340d1084408116030f83d0340c14803001041c0800c1c4c1303400740003d0b1000d21010076201c00c0c1c0c1c00000c05480e00c208407040c035030f9540301ca4007240c03806030000ca501c0e030000c0d410b00c8200e51300452468100000790850203161150104e000f81021107501c4081c1c44640100041410300c0000741212800109070480c069071000042e164507103034030300c1c1c9442c0ca150a16045107010002c00c1481103e0017082031741d841c240d06444103401e01c85c0c0c060015004007128002d40e64a902084014455180100f14160010494592702c8801e042541403030000e0050b10700c40d01c5056203609034086400140c196442e041d071050800c0d1030600300406d001d4200004442d40c41c0500344804e003816000c03040d11031794085540b04a1603162001c201c5001100f442c101ca00079101080c14400e181c100d00c003601d0102d001400004031804205200040b14158640c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299258219 1250 299256969 299256983
    0x30105010603091a0601020309040f0e0a140d0207030224040b070c03140303070c12030e01020c10060621110c1905070b07080418090203030d0b010305060405070f12060f03 75
    0x845001c1103c690f500b034000c1000c0051113a06071a0160000c1e481c1d11500c2189442103940303030654400d40b41d03141e0003000010b4040342100c482e044280707003a01810785500000d07040c0e4842c4911003204280700080c0142683d0303015003003d0950381451000d01981142c284d50b000d4006091001152650551019000841c05800101491032860070520059180a061604d0070f4204204003d02c0e00e42000ba041c450715400780100c101d07454a14001c178004d004a03109100c0c194000911401003000c0012160505031400200b00302c081d9481c001a0f482d221038000701c03048041200100c44200000f64403100c14040900040e40ca408146600241010b000c090350b1350010381c1409040003070020400c4030300e001c0c100d1031108500c0d004580e00c0f0361354940200c1c425000d201104c110201c419400301e40101c140140c0c0501169240d000c007104141c05018101461760000746000c00003903040c501401428040d000301d803170705032000c21007407000c44424070060048500f40e915100700207122481061a07800550180b89 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299259469 1250 299258219 299258231
    0x70809030c0d0827060a0e0301110408060f07020703030906030e03040b1b0f06060a0306050414072301170f06040b0a08030c010f0903081602010e01060e040210090f05041109030105010603 82
    0xa920700c000107140760b1600404180d200701003001d1700d502044405c6901207080c01c1000d020f030301c00083e000d8400301c0500080068080f074005005400025668001e40c00040700649070f43d20b170041283e840c0741c00d1101500203528020200301241c02684030103a4a82d24109492809454aa003142d055005903085130401075402c2a07047c0b5998180409811940d03000c014010600b070000c0012040c0c4454080a070001d07949102040800603140300460000f00c0100507542595034071a0748070301000352500401a418914880c0703007220b6225405101e050341700300e00c4c1d44803140c0311580d110402c2c02c0018100760304269110059180360341c0d500d000100a02c4580b00a41d56070107001c0c8003a00355284480c1300210f44c0c2c100040240083d4000c02019030041d10a15100e0400754588000c90240420145262065280250120350b4504912543e0320480c000e9030b54036083c600b036200890780322115100303521029904c0b090501042c80c0542026154000200080342040700500c00603007111020303800103002c031755910 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299260719 1250 299259469 299259487
    0x3090306070e091e010b0d020c06070215070c02010504030308070c0f0b0901060e010311040e121216050711040515040608033105010c03050403050a0507050a0902040b070809030c0d08 80
    0xb2001940724110720b480d4280131620011603102c1c0d213010700480e13441c1540451018010800342d0f05940610b078400045031003c2c1021030019450384074422402c0c0d0300c00b0005c2c0000304160301030001c0d14901c45d8103a4400c1d14082c0303151802c8502c400080c3c440020061007600650100f02180705c064041405910403003041c0c284912201e003110b40503400f410b519030422004002141060501c1c0210400549000c80e91b052000000c0b4181101f409103245807001c0458030340f00c9292656a0203200e42c5a01c0c40c0c0c110000e481401c00c2e110f5015000009000180001d902d0b546400c0a422039604100c0481444013120080000242640c0d2590840c2a00e03600100702c0d0f111407007040711f00d00c2c04c03501043c0e1503034407400e2005000d07104428035004240c18428081c0f091010940f090088400854001c030580c0c60304803103450301c186c84101604c101c600c00c10700d10300c0215070f0781c1642c0301312400c0758400300e8021f18159981d6160036403500180c540c19454020303403541a03601d8552159200d0b82c28403d0b034182d0b036035030640 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299261969 1250 299260719 299260729
    0x80c1605030d050a0e1b04020904090c030f020f040b0609120f01020705061603060b1905040b1207031a0a0302120f12041e15030b04090519050f0f061803090306070e 72
    0x17601c001c9503103511980700c40c0c3c000c034985155a4060036040d0b40140c2c0c0c51688402040151500440050824154810000c05c1c484514007458903103100700d91a0040112900c03c11050703413012500715034030a0040040c0d10403450141040301e400303440d0006481c01c85080d0001c06e402ca801040044d201c5411420070452410b40d00e0740c90162205483c02d007000850300704100c100c524025500b0303140115203800b640c118000d0080041c1e4004012603400d00c1e549618040605250700e400365550350100c0e04003021246c01c1141e03c40748038140d040184c110086145540c003000303101000750070224024014914800042003080c1325481c121600c0ca802d25584038079014400d10341c403c801c0c21074507000004c4001840b141c2601091503001405524010804001c1080014024134940c1c60061080c881c05441d07428145072040480c003868015001d45081071980718a95480751001c1c91401b0198100d0300000300d50041a9080d4030081d4000e0045070f05000c10040401c0c900f031740507100c01001c01c841806040c894500 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299263219 1250 299261969 299261981
    0x210090e0c0c07060f090f090606030b040504050c0d061e05061c11101803030305060109091a061b0105010b1c0c02100e0a1a090607080106080c1605030d050a 69
    0x81500c5441c2112400b00180c03180101d0280000704a00c15520f482403a20400703500e40a4041c400b8003807c04d55882030050000d104611400d00441d00740790201c0110b2400b0304c1a50b22441e04680a0050038085800300b0081e81540030003103a20658644a807a451800c8035901c007030000701110000703024100700d400c0000c00341a50745034906500000c2d03404c600140550018a625420940d10310b01081490081512844205401c1e01848038128000209056050304031500500003a01c4242d03810741c64400c0b82080c0d40c03403c50344040006000d04c101c043c60400350001d14400c41010116184641c48030b10003401e40c0c0082e80040c0c0e01c64000304186e044c81d01400c07100003400300341d00c00030040b4862000c0b001e9160400c0310261200302e44c0e5001800d610000505c0101011944442c03441c0da8031004024800701a08103072440c038410b106800014404500034034025040e01c141391128640c030ba480b0120301080d43c0c031061a9100c0c20880b210388c4c5000900800213020340b10310704840860380e40f900a201c0da0850701 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299264469 1250 299263219 299263231
    0x21b01060509180307110d1b0906080706020303040f020409020d0b010806063718090c0506030105010912170c0105150109140103020d0b060a0c0303110a12050703090210090e 76
    0x800000101c602c0f60f8000201c601040d4011401082e200607a00050340d80c8610500c0a0b011046d140070b0190700c43c1341600151b040e201054801c002468541d10030b150303114664041c070310140e8030410205000c65600c0231040710707051008001107240116640890212000c44104444200342980140101d00c414408981d002d801500c2400307621654140c80070a00c0d1a6121140b52040707a4022801501d1400f42490003611194031400c88450007501c150000f8400c0e40b40c103840d071200038503000c1400d241550460381294816940c210559081814442844c01c2d0510102da0070401c1c001400945200080036001915200740006800e00d403250a0704102c00180c20518104004080b0030301800d003211903110a200002e20300140c9460442c10030030014200755006680c0103001040ca8040503500c0302440b4800c80c03003903030284900e407a612240d903014011a2144400300300070518035010001545d01641d40480035140c08244041c240e00030800703e00e012030000000425440007401444088190203800030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299265719 1250 299264469 299264491
    0xb030a031e17060f01020a06180c09150513141311030604050601120c0512030307020706032c0c0910140a1503020c070305030a020307060e01050709050112021b01060509 74
    0x850b0025401c10b1a8401840a0301c503651074201d1210903442044910041e640c400d004011200f46019000c50240c658001165220440b100c007140b03009440c040c2e1030b4103040c0e00700c1641e038041c207000400c654208140c0c0d1690303816544603003220950880c0c0700703d503020303154810b410614420182440f2131166520650540203a002c00c0a200000d00f0014070705044a00200000128000514051b032003160550b000c15445181d22942240c688004401580607840507001c03035400e540d4640301601030f40c6552840c041001c2040c4c02eaa000c070016002018860f00e41c0009441100d2000f60000d1800c0c141a00d40203141c09a000d0188014455880030342110314007100d404e4010362915201201c9042c1d5804141c04041c0c0100c0c9071500e051040002c580a503501805030398403000c031804000d6586c1c02808040d1860350801040304085401071040b80c0c0284800e5441022990400b401544c854199040101c440c42e800c10407411203500c40c00c001c00c1d40c6c81040d000480c0c2036142800700440c0701005444a801e203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299266969 1250 299265719 299265737
    0x50d32071e12020904170403020301021305010f0206010303020a02010807050d1a010e010903080702061305090103050a150c0f0f021c02250b070b13060e16060e060703080a0b030a031e 80
    0x9130761800007082d40694040c2d81c45c480300c80c500c18511840d008640c002900f543c00440c900416009040d65002611000e036180c200c04024580205c2c3d51351000c0c400600960000c441e000b0143d4400e034103252380000c0600300140b030450100140c0040392035001805090310303018404a903a030341c0d1054180501000074030301749041d24119115050540316078480284205d10001d0001c200b8070561407444000c010040c0b40310300302d6a49007881601c0c0d10b034102048440c05c0316240c40c0e120a016902c550410f01074150380b103100b0301d0710081d001d49018034a40400c006610480c0c40070356085113240041003050383d1a41c05407560804c00b1801501168000e1410105074607880e409020068a86091b036460940004d1060826125010300342c05030000c000000c0c00c2181001c600704818170000821032209100e07078202d004099a90081102c82000000409a016800f0090340300828442e145607500803244190001e4490304200010b0310f49140d0707003811804540640108d0020140c201109072032486941081802 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299268219 1250 299266969 299266973
    0xc0e0705040e06120604150b03011b030b0a031707060e03090d081803060103030305010305190302030f0c1203040317090a050a0308041514010f050d32071e12 69
    0x10340d01a41c003a40d40b2041d603510002d51079645901c4c1080200b410a0255040c1c2d003400c0c100401152410b0098003030607410302c1c038410702c00e00f4140309000c020f99007030202c0440321001342000c402a00300200d40c10f80c082003214010000c160101141141d11805007a40d41e610400752a02d5400d9038410794410184d600140551041c030b45078803031144502c030341c006000750b55031030000c180030803401410b2103440c0c041c8101030000c010140c059101c181030704d001c4d0007203441c2e40041500411204440090042c0140c1041c811400e004403020054200c000c0c200b0203489000c00d1841d050580f58108a505500140c9040301500094249508150b084034410004c0c0401c4071142d1107282d501e4001d1701c8024200040b09001609010104600a0185030031900a004494108007a0024070074280943c111000600c1f400003220b242031603a0714500d0707500144503400403e0508494210011450b8200c11142000106121441050140d14060107580d8100300d0203403210070040f1219451a04141c0c0d080303c1c0e240e44680 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299269469 1250 299268219 299268227
    0x10503060c0310031b05211b03011e02091c0b040210030e100c0f050a1b0f0b040f030905060903060a0b0a050a0b090913080f0f12130c0e07 61
    0x10780300100d114540c1d502c2d11020a9020f8810301c5520141114010b02d03140460780d4080c4002400b12501144c4508034103502c1c0d0b98444048004080502655012003010411640e01d44094600031340001d0000800d804005c4024100c0c0c442004000381c05a40081e9209103460080a154800c100281c030408500383c02c2d0307880c40c13000b0b84040c0000c0c1c032403840c4a442045882c030075084204a104164280d0340090b0b50691144094013106201c1c1d4089441890040903240c032481c203480b1503070b000381e4030700c00342007041c4010400d00c07a4103000507140b1a03c0e0804200109407142c045034000c6104001d481102100c40c05c005107003002d283c00840c8200e02c00c11040c0190358000035942d81104025800207502c1d0414030008205800c036500c01a000301d02000d00203181500a03014050011064480c0c102d555030b601007000c010700048034010607004003030007804009980400074046039003503a1852440d0413106104c00c07001032000c03540740001c01040280d131400c001070950914003c001c02c18010b90142842c860140c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299270719 1250 299269469 299269471
    0x115020d050d09020a061206092706110403150e01051510021c0207061205310602031603180b0a0b01050d020d32010302010305060d060e010b1801050306 67
    0x104100000ca1241d4800c50194032403c3c6036a4020b00d018203240d0790749400b81040e03181d1000100350904e44a40000d2001c80c9018440792a2198240c0744c1d08090401c044041c04280311100f84c03480c40c2e4034400e001008004100400246001d022a822504080520340090300e00114142420340d0609051000c0201d1204148440e80c1e412160b25002c2814144100d15105140944000319800d10f038000345400d03000704440043ea10140d9801c8520003000c14000c065943c00d45030502c0401c085100f00070111441210800806100c041c0d441030200f164552200707a82085d40c0304d4103040010070740a00000c1e0144150340c000344250445020300c4550f500c820442c1f00d0003c1481011070344074a000c0169030310580440c1e0b058000e0b04000c5407941c1030228a02e0044ca1008120200010486448541a082840d5640b000703c10302c1400f502c43e81c02c41e40110040c20018000340d410040414505000840a0080e2103500d182d601c000500c05084204005406001018125001c10f800f40140f10a0b200841d0301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299271969 1250 299270719 299270743
    0x30c01050c0717120711030903010f020307020d0206040c03030c05070e041b09050402091b09190816240c020303070f0308011d0c07030c0506041208060901080319050c030d02070b011502 81
    0x51b0780400b440d8540b282540b24000085070705500e0013118a400c0a200c1e0701441c0690100d03402c4903141d20701664181e9030750000b03650141400e000804100000f07440345402c0c0700c525101c0c0050f120b0603683c44c0010717840500107036011600010003900e0001200f083e4a50803008240c0c120040c001c0703007440d8011030140e02c0040d094903d0742c003403200d1190310105d029040b40c1845001600e1030001d07543d50021000c03c6805070044100da4011039030502c203141c40d114602825a01c40c8400000708a51801c0d01141c081e0102c640c59080c8000f1348805005030340d00707001525846014603c541c1004007145401010640140c204140e03414001c4003045660300418805076001101811440d501d00710350800b82c030130081d01c81c40104180f2882c0104400c0090f00300800c42070010702d0311002000d4403020204061590240202c1d0b45540c010300104901c1101d4044038191001d103418803500d0050041884c0c0e003164020100100e1440d0001440402c000c441c4c1c0d420340c01819011800451180030304c5000352102c844c0302c0c1c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299273219 1250 299271969 299271977
    0x509100203160c050a14090703090317010306050f0c03090a08070c0e190605090402060d150b0d0225020f06130504020a0f0206070309051905030c01050c07171207 71
    0x10025418020000c403241c03028441c50030080b5202919000c1183c030843e00505000e00c0c070300d000001e03100300d2411510882030402803903102c0035038640380214000d01c0c10000c00e408014521003c20481d02d007048030540a14060540400c0d24584031860031214440580580b00c1c4c44010020018607aa01003078195506904c40380041ea601c00030f0402540c062844c0e00031562130302c42c01081c081304058400380c40249500f601c4040c850309546400b00024442c084601a4100e0740c1000403500c5100e070b80e4040c101a204c220180c00c0000c0d150f034a0910035800c0071703d94200c260360002c3c0300004000c00041881502550b11100074070a0101d03404030b024210030200b443e02541010601c0b140155074050394070b01500001d0411919140d070f81000a2411041403005005401807001181c41c040c40303030040c6040039420a001b0801c00480c401d0039010703803515400541b507a01043c400c0860080c000c0c01101d01944050303008640395001410216088401314043c1d150b08c8000704078500300b0700040c8500d21b901501c1810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299274469 1250 299273219 299273239
    0x61006050a09050a1d0f150f030f0a0b06030f06010b0d05100b0715051305070b0921061621090606120c060e0a031502220609180c0509 59
    0x80180e540c1c400c1500480c3d4000c044520104002c000c0c40030702c1d0032035808172401c1400c5485004900903810020340e00503c105541c828000c58600740783e030f030a0000100280c01c96110f41d0040d8001030405159000071246e01040c0c109011192408002c02018445c0d80005032099502d00408911203104079004c48023665282d50000d5490400c0f184000d008000e041d11450f550841c07071404607421814403240320f180b98039050114031920725800c0307038a4002c0ea0250080911a013043c4d0820a00c2d08100e6143d41d000840040884800c10700b4445140210f80c0308005154030b041880008091034841d601c1c2000b04024160380340c0307042410703441815440f01d801600060407a40f504010010709800d40002090401c4040204204500c4818050485815641d040900900030b4200036048815100213800580c050350009412502540201820620300c0380c10310607929094180c0001c52519409407001c00c0c4447c2c010010341c00145162016040c0c100d00400880d814500080d01701d018414171a402000007403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299275719 1250 299274469 299274487
    0xa09050703140d12020f0a12110d06030605010b03060a0608090a02151b031c15050d03050c0c010314070f031104090b040b04230a0615050a0305070206100605 69
    0x20114001554204400318924003000c05540d6507003c03140d181c24001414140c00c2d00a41c10144241e4041c083d11104061800e12840b0003114034031000ca04800455a0300d006040c6019000001811a012840c0700895068510304280d0201c42050340130301d01d13160040082004a0382c9464a140543d0081e0928a042d500c422503031714607200c0c0c0e824009400c40c1d540070500003c814144068500050001c2c040001035000b04c80070350b180c1c068010311203020303442c2c042c800810800703503000b810a0303800700124010070540c1c0b500050001010541c040c4e000c2070380065192100441032005600d80034003800c2c10306c0440100110140d010380002d1503801008640040700500c9840380e000403004070100020340b9140ea4548103000000d200059403075203d149400a09481e50a00d8000d58201c00448640304403898943c0a110580244c001c1203050410360351840824a070b0083e5207001486ca480c0d035201d507100c00c07280e4406011200050103080540d03003d81d08001128032000f440600391041c5203481d9880c3c4401e1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299276969 1250 299275719 299275723
    0x3120302070b1806070c0503041703090406060302031e04050c2107141c0c0b03070908010f0b0108010b090a0308090d050f0d021608101107230c03150a0905 68
    0x10700c10082c400d108403400e000145110303911040300300c80b5003402e403121902d80c0c440541b10103450b004000e1490300140010061085844507200280701da11003581e1030200400009011600360f5003042021039404804d00624114a5100d00400c0c0d510020414007820300351610b82d503824403212801d01c180300d5455020842c1c1041c0222110a030303110300454850903220919140355220044103203000d000b5080d4203403000b034602035850100382d401145507820f0074100803006c1c00304d034070052940b0284000c040d8002490002407140250810096400042a09500f40010842030b010fa01141130001c0038044010103a80300040306007180da00002d0300d0317955880040030900e00d00032240050002c2c050810031105045011070301109804095003035800041b00804c2c07454007840180600701c696481104010700800065110158200010000504001040d81c07034540c1c031030101c5e000101d141039884410420000811000e40c04c90380440240c110303010100104061f04c18000d000e5810191a1750800c1e0900c101 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299278219 1250 299276969 299276977
    0x70f11040902090a0b0108060d030c0b04050c1807080606040e16030f020414042a0503060a1502010e12040614030c0714030c0c0103060303120203100506040611061f03120302 76
    0x1000d8444400c40c5441c01104c0020700c401183c0b00c2c0881c0860000030054a0410707044802258952601c1c018aa0181c0700d44a9100c0c0c0148210340c01e204444480305540c0c0c502c0c41c1007030302070043c115004807446c254400901ca50405084a401010705002c280a840d1694100307503400039484c12161608551180f0441c00f400f50b5040c18040c4904c0000c010071086100300c685454a181554240400308212500515410007500d8106410600310720140800e84181c0040d908000000e0032085403d071284420f5410000100704840980c1d5a808103aa40748803d03c2404804402e01c4c00c17181c142840c24101030114608075911071001100080011414804001034519907600315000c0001000c02d131341c0907660399001200001c2240700d0780041d030517250f21a02402d402d49a040d51202c1401f00488100d0000c1d4101404034000c00504080220b00c42c2c581e1f102038401040b06a4031202c0b41000703403031024140300024106500079030105010015045d080c0b00b6500807203034002c4120743e5a01d80c0800c1117009000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299279469 1250 299278219 299278223
    0xf0b120a0b040e100b121905010e06010f14030a030e120102040e01080a17070f0b0601120c05041d06031e072d05010305070804080a110303040b04060b0105070f110409 73
    0x45000c2400f25011400528512184c8040e0410850902008208501016a410728414951100c1e00c110350110b07070014035600c2c09120b100045080d00004102c641412426000700038070101e0040c0812404051080c0c1a0419000381c1c041c2c00e01c3c110a4074020440c01102c4030481c0540c08018511152501c00d604031802001500d80170026035851b03031000c544035540e02905481d01100c03da018404800882c040701c048692214003000d10340c0d04d59446010841c0d0081034a07050100c011103061801c1254003425030410155514942d56505100b101213040003404040101d601c0341008100d003503140040c040031488144100403801f03e501c024410714013110354100e0f80e400c10b40d000001840050307201c0451008028004254001621500114115441151820000380d000d00100b408600450018030340c2640c04c2c82d10426603130301d24110710700c0c5920a071803c44d000207141e0100414003240d0300c40e06040b240d092804d1460000c0d40d440b400c105080d4660060058ac840040c0521a0745c0c0f26488503601075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 299280575 1106 299279469 299279471
    0xb0d0e0714040c12020307080f0a0b03190807140102040306060911070f06020405060715050a110f1c0f0e010b0102070f0b090d02120d090f0b120a0b04 66
    0x4628000e0040c030903005002d07040f1030b01d20f000447c0f240e642034030f586415060510100070803083c0108079252281c07604d0265902550085000c54440d141280580f0380b285041c00d00c40c041c0d20030349400a20b14810781c0000298540190050003c40b03025540400802d0780d00c4044509880381c840303210b04202070810204000a241c5083cbc140c0305401440010300306074a490202d44141d22076407003034400b0920501041c051a80c540034060380314000160034401d1410281a210031030084c40c10041142a02080c0c40100f0490328440c6c003a0448503000500505500b0310019008210b00442000c095003414425440d0303500000e034040413194540240000c0e549002e10050060b0465020141c1c000d00340304412000d41e50b514440103d01f610300000d019519502000545078401590040d600d12070191820404d40460754140c6103c812001030b5035546540300c0b22920010300d02c03110b4103940701f = true := by decide +kernel

theorem cover : BRFrame.Cov 299100719 299280575 := by
  have h0 := BRFrame.cov_init 299100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 299100719 ≤ n) (h2 : n < 299280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
