-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0841
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:06:32.853698+00:00
-- url     : https://prove2.me/submissions/b42b16d1-90c4-44c6-a5b4-cf23b9506766

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151079136 ≤ n < 151258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151080386 1250 151079136 151079141
    0x604020f0d211707091a0d050a0c0e061303060b010e06070309050906040216020108150a062001140115020a1401090311010204062a0b04050a050f0c010905090901 71
    0x10380c2d001411220010304110210302d03200b0b254005a0014200307040d6441c00b940f6114a450207011150b4404910701e04001c9000d025120312240c04080c0d00e41085820400200740c814030340030f500c6a0300041000545030000074800421010298403a45082000114810200c00d0040c01c49078400004a480d00c01c6000507603000402e6065550003103800514641010342c4180d10b13400b61001200c0e005101d80340c900502040b4049c0044800c0700d040c2507a2120090b602592125038800c018042c20107005041c80c001c00e0071400603a1100010491202600443c0009044894032190258008114150151400f81e01c00314040c441d0003001104501c400b03101d41e10a0280607181034000a03c0712420b00c01d100000d000705040c0000fa0001110240c0e0754491a806008440444e40f003651002101541d000d4004c260f500e07450f8010303403000f240c000400c0004401038040d51089016201800c0c0b15191400c19600340408021031107401c0c0c222072500340d11aa005040d04044d11804e5a0000465684a000a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151081636 1250 151080386 151080409
    0xc0d0e2b05060f0117030a0804150e0709090303061a0301051c06060f060f110606100c21090e040507030305030a02160809010f02030c0703080901091503050105040c0c03020604020f 79
    0x1850041c18100582200050f4510b8100c64145005130520719440b140d2544900403541c219001030600c0000c00c007c156840c10741c001255a03440009500c590701d0300c400e031420725654400c0c100d071600c0300d5006040c15050b21980c4014180000c0d41d07545e00c01140a0300c00a4441402058412101d40212440300c4a1100c045501254002000c00000f6200c00500c2200241881003000107040345c0c0e400c625140c81240703010428180c120082200e0388030503080100b140340d00c2d005d00e02000040441180032800e90154140800100e011042a501c000100205003c0d43ca8020485141c1074001b80030028000180a40c00c07290140f40864680d11008903c0001e03124042c40d0200701070709180f49401b0301c020342008000601090320f078112621080314050f13071240160440070b1080e800c401320400104407580c005003a100c005141c522a042d80b101d001511003c0701d001640c0020b580c64006028504044c841da031305207005800c111503003111641c2d0081d690f00d402000240034001f88560390743c1940b1600002e00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151082886 1250 151081636 151081643
    0xa0c2c010306020409181a0c0c03131403070b0307051e030406060513060f0e0903071407050319050a2402070501050a050609070804082a030c0d0e2b 65
    0x4896580d00d04001010350400d01514420b1403402c920b0180c10120301d240d102c256a4422070003016015403103002408250010b0036035a0070f000030884580b1600c0203100505400701089828100107040c049809000390344101240d00a41c0002000d00009a84400340c0b607101d00c032807618950714115009101c8030381e80090200094004081309000c1048030365002941540d10541e052034401070003120210a4420301d20070180c907203c4440b01881200c49103264a82d0109030f010440b4900b00042d611582c200b40c103101d242082c2e4200c120180481e00e0b041c0440c110408480360060001000743d22a00d469051040009103401d00b40c42c0c480c0c6004d00d01079001030505810b10411900d84940d420014040e2004a0703242d0007840c60400040c010345082c0800c54050420395464031860741e199a10a491a44160203005424100c02508007100c002003c83e0104c1c40307002c4001e152183c0010b15454605a2108201e03424050300702e2202920361500c0d007100c03884100c001d401c5d6903401060304500141254070714024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151084136 1250 151082886 151082969
    0x813050d03020d021b06040302040b04020f07120905010311040603090309080613061103150d03030b030712211b0201030f06030303090213050712091a0403030516020a0c 74
    0x100e05160b00460a01c4003e0b0403602541c1c405044580c1807484007240c800140d5201c0d400780010300250403e07034841c1030000c2001d030005181041d9000714080075044070004070307030905450040d0045560b000701682c00400c000e003420301c440194140400468003a43c00b0394410550b031104484140f5204001c984000d020090a407103240c01c080f00d0301c0b0404030b0102c609444041c01d01041c03a200040f4801128882e40a80e03400c4513064005034100540511500d009500301905c4403c40c8a83c0ea40c140000c00081c000032412200e41d49107450900ea10700c030011182041d2800242061242c15000700062480540b9011410b00c02c0d20148016401811000b811040062801324040200f40d01035003c440170500855007405a041c080d142c80f020f03140c04a0301c80c170014121203403248002c044c50300060840c0d40301e060450ba030200c1c0f0030801195280b0803a02640004e8865040c89001000e42412080d00040c910162201209030340303c5192202d2684105100d5000c0391850004c00809503806017501040c00110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151085386 1250 151084136 151084159
    0x20604020904150c020f0c0a03050d030c14030c040303030c02010c020a030e04090503030f07170907030f02060c2a0109060e15041214010c030203010e06090a180f060b060412081305 79
    0xf51b031240010115880740c86000071050b003500d0851801e0007107960140052008a0103d04110040c1400130000c1040c8011080c041484400100c007462040300d80550640c2c40d03134590700300101a2002001103205592400c600c0c99611a4003142000702181c140c104020450761101c00b00e00103000c0214040c040340030200a000c1ca012524140d1400b40c0401d80d01d55200360031410030089240007d8803010240d03403001c41c0400c0000c10120b000c10b0410300041641d030138910200380040c1015103042e01d0310b50400c41078801e030800302c1cad4100416400b05821f207131840d0f403d4101040034200b815840c0d4040c0c0b0034601d4002072402c030700c1c8480458026040c4002e40c0d0a0505482c5000c0b00d502000e0301a00b1510b5003070155595000d480792090301d04907903050f054428a92550814480c0c800380280041c410395882d410352000200d00c42403001d410b58802c808811250f000d600f0030404681c245c80000b48241030410040000c1140400000301e9141c008008170750fa20543d10940c500985164011504180e42620 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151086636 1250 151085386 151085411
    0x30f0210050d0c1e02010e031e13061808010605060f030612011112010e0705030c0a0c12050702040f0c141315050d0f05010f1e050a09050402011403040302060402090415 74
    0xc4c0540042a8484200c1c00010a440d051382610440301c0242e00541c800d0007001e20b025065809616403501403a490307413411401c01007404008e0f00b0782e00300a0105080c0d0406150b01e4610441850040200314003c000e968100342c009801e521800341140000000400420800e543d90f442d43c10f41c001000380200162448002d01003c10f400044101c030b689003001c1c00010f41c1070131050400d0b1181e00d070b551781d540c0b655031802d480b012a5003002d03401d80200440241d0020000e0301d0708065405d6105142c03141d41d1292540c0c810402990b031a074559a07c0f50382040c450288080c3c110300042c43c2004805003490f1a5001c0184103101c07400c46511002d001d0682c1c1e0802003001d41c211380280424404a541408483d2104503004142c80b020310842e000c1007801d0004000a02c00a8004040c810100301e01c2440a41c0c1c41002456500c003c1d0000c1c11748542d40c9041c0700441d078020410001140200700c00170b00314586902c000c0d484840042010b40560a504001030800c00703844401180b9686090301044446032801 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151087886 1250 151086636 151086647
    0x10909021f0906021c020a0816050d0e100201020c1009050a0501061509060c110603090304050a031101181415090904030201060f290c0f0a03020102091009030f0210050d0c 75
    0xf141d00c0c054080c18800c0000d85c103402d1342440480310380c0d0300104081c00d44ca0382c600c0c0840c0d10000c03203100d040600081c90b1000a01c1408800000c104e5a542d01e00320142c06030411804000802414040d0f80c8104401007214a01043d243c0f050340540d50700050540160400f42c0c1080c0203c04001c10340e51034044041454054140c400014480560301c8100594031410240e543e1041c07401c0c00341c0a0704001c1213000c104c2c600500155440b51252055034205656280031888025003a0402c491100380903c814010303507482010000307080640d114001c072151512760000e10410390742c01242c3c00748a0707013411800c20a1000d07080700c0464001610aa8980c5410f0800030b008007814000c8003003400220034001800440d0b410704254402d02c4000c1441b18000280c10f1081640c03080d14021814000c441007540c80070820f000200c4d070b8a020f82c00140e0344c2c4184c1c40400401e42c1459051605010f61503e090000c00c10708800f046005506a82139124803201c0b03082551980200a6100c03c214208081301c0d0091358000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151089136 1250 151087886 151087889
    0x1e0803040821030106020a060f06050d11040c0305071e090f061205070302030601020309040b030c030715080702070311040e0a021906031b020d0c030507050d090519050306010909021f09 81
    0x3942c4000254411010b5106a11081c4a00001a4030492810001c90506d0340095400c4410310000900305a8540200c2d1400300c80781c20644185480388100085801c0a001e61001c001042c9810841494006405402d002092040d41c100c89a03035462407409500a0544101401c004d00302c2022079640c4002c01402c0d002d5901d8a5a211420400401c07106070090080d00d0003580142c0145050010603400c0c44014090b21000d268180700b1881400604d0300c00b403010304050455100000c81548070102c001d40f280740040d10f10750842d44064400c0000c6002d082c81352951b0941140c01040f0604102d20300c9103042d52082c006544090b15050030024400007020f91022600c1c07039142402244210341201c40c481d82e9007411a40541c100241101d00d91b4130519080e00707000d00c242443c6042400d1902d0702481c05c0c04510070013010800b070b158107020070310b8610414001c816501c100d00c8001400e2401282e00c501041c4900500c076610340c14010215a920b0b4681800804240c9083c12101d07004c0340010205800c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151090386 1250 151089136 151089163
    0x703081801120614040207020607140a0506070c05030717130b04150c0b01032301050c030f01080a0309060807020f030d050610050301030b070f2708070b0c06011e08030408 75
    0x245900745240446400796078100c4034030110118440c444c0c00c0501003c3e40c407019007241d014004204272400114024410b40381150000000d0482c04544e1824500d0701101605404c180400b0182c040d000610010460700e016500c8030741c500241d03400f9180f811841c01010004145290b4650000c108908040c02820881d0601019010550003040c0182c1c0c4d54034100c0d20240042415600510101d0505060198110050f4012165003200343e00d106084071002d81d8080c0301d080c40082030000341104246424050882100607120071030031a074014054422601c14042070040460006803294001c1c010500f490b4041d1040e2580c50507a00c80c18401000103e8015105d2084920169401c07486072064038141c03503101d100903a803a190032005644c441090908181040746804045e40c0340009200603100d43c42030840c0b80d5a0150800103407500f481d100e608018141a000e0082401d00c600001c4d49904459801d804140709600404210340c0015880d00200b0140c1320000303000610040004000105044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151091636 1250 151090386 151090397
    0x150806130b010b1201090207050f060c0409050109020f0a030504020406051305040507080109080d02090406051c020f01050a170405070503010204060f03180f021c020406080a111008040308090703081801 88
    0x2200c2d052550f050141c43c4612505014840050200c00081c0e0f000303144140c002d2045407545000d0440461a000e82120058488500801d040081254501406015100301c000c25405d1a40960384031a003406440101000c064990307001c034055488583c005070103007102034000103072860308034408409082c040d0f50864041c4206600090031510601c0703469042c40d8041100c919065030000c410001e90404001d05911503516a0005029500c1d403560190309030302250b83c600e9075005801000381c1c0350070400c5028148601001079040c409c0d4012446078480820f681c0ca0450b5454030704180b841c0c10016008035030558030004000ca50b10340c20201e15002d8140c203682c180000c80c5000c0103904a106800c1c0002d0481420201d44001850400085600d101c0c41c4814101030035801c1e00050195840341c0e20840954202504107014045030722075982d0001410343e00700c0921109202d004041e44001000501001060070214040e24810f001c1d8800854102c40c50345c2d1640800189083c1c0c000070300913058003150 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151092886 1250 151091636 151091639
    0x30702030a23160311010507120506010201060e0109091e08041e03020310020f07170c100e210d09120e0d05070b1c0203011203080f0903070303150806130b01 69
    0x12460102250b990090424040c01c3c1107182d00341489a06114500303c00380701390380e00030001c0701509105481c030401c125070f560200e072145016202c08450026103642d0440e41091414021441050001030450711081d00000d10480d1509020001450440d0320a00b0030481c44440c0f024004890043c1c01668a00310700394016000a0f011507150802512009400d508915400c1e800078140c1d0b03026098101e8820320051415081e031303541e600c0024894140c501030f003402243c61007034407404100c90354012503011802c100f030802228000d6a50400284201a4044a99a00d4440550840079100c021840b42000e00c295003151400080c40c1c20340c040f02e4400550380720400059860810079407004d43d500400900b0b005800c00e010302d8041c3c0e1004014481000020b00e0303680350b242c1ca03880254000c0040150190000c001480d0042c541c0c00e001e00300e20300d0151980203000c400c901c04001c0f03c24942d41401d000610260a4002a0000714554800782c85070048500700590703003028400f20251070344101400195a03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151094136 1250 151092886 151092917
    0x1030506100303080c1806070311010b0301022503020a0209181515040e031306091a0408030a1b080403030c050d020601140108040c09110c0d08010b0d0b0a0902030702030a 75
    0x4454800507000510240102d0307495100c42c0000c06c4426075040c82980011081c0e00070440c84d50000c0c808400042e01c03240c0484110100388240304001000300c00035864280043c1826000310200020340d2604100e416003001018003c010540d41190302400c1088180b41940c2650b20680b079560500700c42d40102c007407448080403060702c00e9100b401030802c40c5202000503824000203249044d4a8041403100b0849140b01110211501000b098039959612100341400c0324201c2c044c1002074030142d480b40c00d000c20b204042000c41aa03002d40310f5031401c0b40b07984900009030300f080030440344041d204510006010042c9a03001600f8030000d4040c508660403012560000c03039580c142407107481c54000501e6141007041d8800e07480250414040c00714000c2c2c0d9501c405928040b03515480009603203402c0000d03501c3c00a4401d010310100210141004500c1c0d6160031403003038052041101258081c3d0317071042da6003440e541c0c460004000d0030980038119140e241c0380f60040c5d88d84c0c0c0240740030030108901c104941500d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151095386 1250 151094136 151094161
    0x605030d05040e040201030605150706110403020603010303080a0b061821030307030e0c060c010b0a0801050c0301050909010905070308090a0e1603050702071a07061a090105010e0402070501110301030506 89
    0x14030100e50718507182600d8190b84403603c243c0548200d04042d25800300050b5980c0d0702c1c10001204c0b41098407656500380c2c5117050300c02c442ca420310425100300280000c10169a401003038034116905402c05040035590041c40000401c992280300d40e0242d004914014501584400c50030b114000345c4500245100c8540b5660005c030b40e0201b4500f10354404c0001500703441c4079400c00040800d01c40219140361341781000098158100411107080c0b80e541700c0350460303280361051410b03001f022400c00800c5039052180c40c03c3d40fa8401402a180202c00d4070700800c040300c0c0c0940c01b032441c940c1c028041c1e0b00e130a51207181800140d400040800c0c86442c0450380820300004520601d4020303401e10364254514120b9403030a5002d007400420010071f501450000152448240c1031180c03003491001a12a502c20440c03600c4021036100c030154500068101d64103402c0c075280d54040e1030566000342050000034924a0000e03005c1c3c130551600030150750a1000070b900d40d0402101a60681e0b00c2181500d18555030071a13400300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151096636 1250 151095386 151095403
    0x80c071a16060c0c0602040312170f070c0f0503071209050402090315070e10020309130911130e0318030f0102120a091b030b0f010602010501050109180204081c0201060503 75
    0x454804420800001030782d00c1e071101c8a02d681e181458081c0480c03d894000c02c9070001d500c1035403c81215845541c52071740c4643c81101500400c480b6503c0da0504102101780e0000050001c401e21180505c20300070701c82c02c8803041c6c0001c0d0744901201d5a889203803170503028168002c0070384000721b1710740c80000c10b4914150080c0d40760b414000c2c00424900390002c8442e0f45400016090780240055440110080c3e01c4aa59a20b4108440d4004503500c40e0071400340008038a80c001d00c0d1480c01d140107002d000040080c80310b028480e000b203440c124840c0000c2c24403401441198400d55070b43c8400581c040e80c1d0110949241c03c1128101c003034481c0140f0302c040450a0388260702c40c6604a2401d200021904a21075000c0b11300c01d801b03409132883c600084540c5518110080e00251074500c010400c000313580120800440c003400440c4000c1c01a5403410740060b2025007640111320145040b10300d010590811541910024500f042c119201400541003050040314400c0001c0019400c0260101c0c160078001a80c4a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151097886 1250 151096636 151096657
    0xc10020c0a170d050306041b17060d1a06030f010c020109020f040903050301061d0a03031d030a020616111005190318030323240909030304020913080c071a 68
    0x42003083e0008111041d6000410942e070180d82c424042c00c503098081403088010342151101e4a02202804001c04203a000400d518421403102d5440c400003090b130540c407448030500f04154001c0e07844060020f810090070100f4044690701c4d000000c4440c0303605402103007507a802590b041140340d0f030810030710040e543c121402402181c410401044007603c24020030707107138288150203901241d012000041c0300091550082d40000d8000c4110b4500308400300852041c00c004400800079080242e02042043c0101c2440e4821200828241400d204003601c10040d1140020000d449045114101a00c1a0050304003080c0c0306c1e040e052241d0707445000e88101d5501744040000c13680c1c440e005035400c401504d111b103503802003842c205c02c4054100c11010b00c041e01418215400401b404d0750a04c14031080c42c8001d04261144041700140911030b02c02004907a049901541c6e041940c2d95100c001031188015081c000f8629000014015104000496542d007902d0300103006445985501c0e8441c1403c3c0201c402e141c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151099136 1250 151097886 151097893
    0x20904020f0a030803010b0307091d070305150301020d061505032202011101380a1703040f0905040c141011010608070b18030127050c10020c0a17 64
    0x802601d4810784a4010303150080ca400d031031945130f81e2030209640085e4400c0810644c00300621221070780001811020f460000c0b99001811030740d0081604070140902403009041d41d820225441030605007c441c2c040b28003400070765441c5407102c1640300a000c1403140804030098192091102d0340304000701e074010010200c0b0008025032188961410844401c42241800340201c42100d0b0802e081c0079009540d5512030401170750100383da20141c42440c10541c0e50142200c0210032001c1d9613280110b00050319000d00d440001441d141c4401d82c83c1d40b1403600075074002d8559400002c1d82004c40e4000520852064407040d482030369515414111f0300200c17452a501c2262040c003100789912450020b0a008401400419000e54030003095081c08480d4020590401000604a050b4010703002001d00c000010380080107007407503000440010042e05d100d03015000401c84480030038090100520a1502801045111148071100c0003039030300c684a03007805003d428050000039501296282008060b81284090b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151100386 1250 151099136 151099141
    0x12020307090b0d02041d060f09070902072a0609090c05090111072706081b060a05040506031503010e07030215070501060317070302070b1801140702121b0405040209 72
    0x1000302902e95458050381100c410800340025948500580303590401c01c1940010200b903645845017400350081180c01009018405d10424010010320740c000c81d1601c1400603240e2281d4548603501c1d0301d550f000f03a1460b9038a0f0001c604040c104401d210304a480f51380700ca100890f501e001e01420740e40d640d42c070000481c4003805061030035401058424a0280f12000382d03441503440340d0318000c0e0701910740c0300e00c440400850304280d100c00043c420031000e48418401081010f0410000e10028109840c11300e0181c0300101f280382c0340c0c50041701a41c001e01001005240c40b4600b01903e0781c03003018400d07440d40c400d6007042042c02c52000003185a00607250044d01c412141d04e103114100302c00c0d900185044519651b0307485d00001148402400c0f581113211803041030740d103840300e0400074a4417006800c0025029405c01800c42c45015120b07d5101e1b1030740a08040302d41400601a02e803140c000e10030080d4122006641c4011042004223260208c889d080d895480c03400b044406100489004039402500040c1d039501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 151101636 1250 151100386 151100399
    0xe1c0e01050d1805010b18040f1211030c24060d06150f0305010f0c0906020d0f09150908010f14040f3915051804020d0e0303090712020307 61
    0x415508600703641c0822143c051014100e60340250310410356003a55a080c0c600b0152600c0303451042c69241c81142051581480e40328440001c407140710003011034407140000f1000502900d1a040444a5038095a4071100c0c0d82d49004c1c3c545100802c0c2208006520400b4080400300410140c054200070b03085034418640c039034074003008100701c1e20001000c100343c80000649800080c040c07409103105070008148200c1c041364810a41c2c001002030000d0000014042c01455030000e00802610003e1500700710501040710181c1d4140740a42290b01c9160611403500f07a01a009124241282c1c0b140c0001c11100b4201c001810455103003941094902e0300c0e010100780030940c82030358040744030b005000d101c3d01802c0800296400300e01120941d040d40103101c1280d0142c40844208800904c011000301e400e0050307600005207984220024842f460340201d40f0070a454555506940c4080440042044070036030b05880143e580d001218040301500c80d07000d000c2240c45068107100c1800c0d5010700104545401c155 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 151102886 1250 151101636 151101647
    0x3090503030604051005030a05010f1505010c170d06260303060f13020c150a0c021b1207030507090204031401060b07030f05130905070f020a050c010f090b04090e1c0e01 74
    0xc180e0035561741c16980c040346039a418003201c04450b20541c0009942c42e5403110344000ea403007208410a010350324100421050340c005065010003680000d800d1a004079001c0c80c00802e01803100e00f503c90525100300030581c84030420600c64100444a400252041348d00c040780d580c1c1c402210080d401c00c0d8079007145c1d802c60500c10b83c010f000701ca01c01005804c1c250b140c9280e52510003d00c0c400c43d00c2114000900c400c45002e80306020740d902c2c1314805003000c9141c241006401c00429020719001e140080c1c24298070110602450000d03503441401c0c0c6181d10360300c02e8043c01075001404262002100c0352810702440c08140315000c1240c04060351142800e5160301e0170364a00481042c294180002001180c415a0168100e00c01401c01c50200061030b081144008241f0004c44403808155408514401c2c04103000007404841e4400900e0000c0c0b03645100002252a81d104d0b40c4080c2149002040100390140070760010504403a012040b140803000746080050105505210f4070007052041c0c03102902544201c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 151104136 1250 151102886 151102891
    0x106080a09120513150801211101110c090114100c050706140408010903090905010b091e040603050f010c0201180c14010c050f100b010e1c11060304030c120309050303060405 76
    0x30000c41c1c8038035030700c0028031750800c503245000340040c080c000140010428181c0c400c0019403c0c84400245e0381050b6164880032100440c01810f1043d100124008030508100c0f101754844094180415540c1d10225401c40c018403580a0b03201d2403001c80c1e424181e601c20109203410ba604103001313214a6190540540d02400d6103541c00c010400200b0000c6481c400c24022480301a1181c0d030768107401c40c07404401c1c000722030040c1c100c4614103004000b03107405035642da501c0101c50039010050f60fa040c1c202034001801032205500041c07490081826101c658041907103d0a21742000f0303002882410507881c10740711502c2d5194070052201050305424400c0c4101c02c244844100410305040f12011095200d442c41c003001001440c507680c0c0103a510724040240b0b4000c0e813008820a003020340504248200082000c84101d1040554100522008081c00050700407118602006464141e807401c00e810001e002d1a0803030000e40d403560b9164000070009202e0702c42d29103142c1c2c1107005141103807112010440941000f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 151105386 1250 151104136 151104157
    0x12060406113906010b0307080114030c01030b03010e0d0e040e030909070507020102011413150b0f041e060e010806061e040e0708012c031e03100f0308030106080a091205 74
    0x80b280b50044818104600c034043c0c0801c0010300d4891038400f00041265031705800c00c0051050440303000e042600d00181c4503032200001d00b004030719a50224040707401004001c04c0144184110040e926260703801c402d07104060a01a1030503c001c40e038401c4080c4d6284070b00e80170769811005000018440600c41c0e009051754520500c0042502ca1284492035580c8100303132031045100041c9035076041085000c2c0541c0c203a5040c0d510007840400011400140030100c7c05080601582e240c40140040c090a0341c00240c0300c0c01405010485c1d00c0d00d074041d0707600360074003402101070318840c007004201180b4020f00c00e0303288034805090502107100c401c0e05010181ca00146008403502c1484000700e5581e03030a0150317907510001c0300301c02e8001c1f9056424810700194002101c07140c64000300810030760324859503d1414144c0f82c440c002c80c1d803500e503900100002d0300164400c1c22040e46d000008010880c5000003141200c0c996540d4540c980c44800d10401110510300001300b03128506d5201081081c0a20b02402001c01c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 151106636 1250 151105386 151105477
    0x108131103010c050307030e060c1e1204051e060609130809150c01060608090d0305060a03061503020f0402191b0b0405070e0f090d18051206040611 65
    0xa0300012a0a4581c10038024012900100400c107032a68144969001c590410b0020301160400701c0060b01540b01d042403030485091401d9a0b01075202c103030700c05c46002e4007106640442c00d1a140c01c02c50307141c0c5009504408800d02d9004012551500021084d000d180010040d00c540d40780d01111507480c2d00c02d18022a4600170500c580d002035aa94803014410b00c10141c001c554074880c1680403804c54450360406030034410240e0500042200000c3d11002180b0f4030b04002446448607800035a4040490344020b00c0e6a007013000c518503410b0301d540c54a084034401d89402c40e02c09810340c03c00c8107034050601d142c1c030300e20541300c81030209074400c1541c401c0d440c0101001c500c0041072034035150f00c14241200c0558083e1f1282c0c00422003c02e46401181d071108000c1103038103c60415104054440b180e91f0042030402c0f00100c2c00400e103081301c46946000348002800c0b2010083e061a1203030700c0301d4044030151142032a1040f5500303c942c1c0d60b003c85002500c1282c079008100012241e980c8883c21022000c0e00302807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 151107886 1250 151106636 151106663
    0x512120d0924050103020906030f031207090f0803040e010603050103030f0c02190e09060c0703051905090a03060f0e03130e1308041205060901060e0606031b040f031103030306010813 80
    0x14070503441e40c40301c8002d01c2d4000c5210b604500500000b07010290015010340d000d55000502010040f05840018000d440145203580314070342c0480302034520740c020242440c4001000a40c984000000f03204646070b5060106031603907580e81c16400c5801c00d11015000c2911100c0005900e4800c101d07100d02c042c8010501160800d550020b4800107280340c2010b03003071140201c184640c1000070840c0c7c943c8031100340c542902c4c104543d5001811742c014040c1640700c2c4822000c0900c00240603800740c601580c4080c101803602540c82c02c040313020b0311038402c1440d40750b4585a0340e4244250080301315081c0110201c561258240307822008000014002c001c42c8003000020a6500080e15110040c0010041a44110410542c6003020380c100a0068080b04150789003480400518201c080e2103a0b001c07108984090b101d03030703a0713041c0000c01c80342030412400300c03a000040102d10544214040c109503400b461482410100c04024155280300035100302e070128991500003115440000d4800a0407840b4209404100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 151109136 1250 151107886 151107923
    0x10050d0b07031518060509070c120905031203252f1b0a0e060d080c011b0807091e1406040801020d090b0c070b07050a09030209100512120d09 62
    0x44209400008001c1413011a18843d100310340107074005480129580102400c0c480e01c081c0c40212a04001085505140042ca0706180035440c2c070380c002c11016003034030100d0700c1000740d4050ba9842100c209614401080004980140c0c540311004c914955840740082c151003540c8070310400e69602d5420522100f180303030400e08150240131320407116002455040344020b4a200300046d40110f5040000014641e5040010690f01e0000c2c100c0c40d590042d01007981c0d00070544606007d400c40c54611104000e81a80750a041075010200d944261180d03602c0c3c0449a403a0000c0c0e184620142100c1800d041100000b444803840e00c0e1001d03441120002d04031454541d48001d480d0076600321082e0842c1d1540c0d034074801e50900c01c20161040e0301481172030516140049598502c4198440903001004005010500d00201406440042c001e1030f00108004160724048003400401d080c2c90003598060380b51003c50100203d0005465580300c039a40140b035040045914050300107150502d010384d2511030b141c0d0001200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 151110386 1250 151109136 151109171
    0xc02132d0b0a090c0f0203030c0f070606050405130c06020109200a1208120109090506041119080106140303271f0206092a040f020f03090f0610050d0b0703 68
    0x1c05540c08003081c00b40304000040c5c04030111001c850700f950001c20800130310180700400c1790200b22000a8450302d9096604141005060507001950064a00402d22800f00400102c244615101e0b00225a0594a91200301d0a99030b90079070040c000401d00d20507421481420800c0403c0040160042500556450341403404a8005905995110300021102040490692001d000d42050030044c40303003840315039681c1d0341c80d40c00620103866400080b06000c859541c2c0300702003100c02411040c8440158407240742c540201003922500043c03900c80807668507141000300030345003600307102d51885580c401d4004003035440440c00c3d0030041e800800d584000a9008154581c80906511640280230038548031484070f1514003146181c1791404080114490907012200c03820130703181001e403000318040c002050300d80003a020701e5040155008001c01000240180020452000c0311448115032142d01d60740325600c4112024010540c000241913240f00c04144001410b9403c50b034140f03400a48513804091000c20f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 151111636 1250 151110386 151110389
    0xe0c0702041b02011a090403050c01110c011410030c0509070201180b0402013b04090f06090b010b09060a03020c151008010f0e062a03070c02132d0b0a 66
    0x6034000100949090b80d07034244644a5111a60f4518011a0b050040010055400100700504003e40002d480808220039000000b0038400f80d05001e44480348640d00c140a0150100b05c400d022100c0070004903103116004540f42201e0300100018249401e00c0709109016070020000410340d901c1c0c40104414001000000d4100d90050b4009c000608251000404210041540825003445078070032684c070410482403000c0100c099500001c03800300110210b03001c0c040094014090480400c0b0200c1441529040008038601c507144050750340e80c031103064000b1402005c84141d04402c2c02d0240c1e01c00b05000b903006040c116040d404842c40070390000e0826024030f0040381c0501045034007803020071800c0024001e441000b510520148610403002d164250b5070b81004082010340b40401c6128010401c0c2018241414a14010807560301c0c5040350029140ea001d08004a000344582512030100c00d140b031203603190302162449a20355005046032800c0300555034551075440c0c240d0707803400a642642d41680c03500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 151112886 1250 151111636 151111661
    0x2030a0f0807020907030209030d110f0f0f010c020d141303060207060606020c030304051804080c070b13050f01080411210f0c040c0818030423090108010c05040e0c070204 75
    0x1c0d42c4052a2041c04004000940550300345401030040000954000c0b4070456002643d2400d0404061100075251801000c0520b54059010f003840050007040003107205180e10280100a02c0328400d50035003203070340314040c16100000584030800307503240725041c0009181001181c512810440d03100d40308c000c01c0f40c1c0702c0320046580f48da0701c1508104440d014000c0c5e80b801c9100720003442c1810301d080e010850300311040789400c007034034032002c005401c0115080c01d803540e20380610704480400f0303112003900c0101e038090080071484185803a07000a081c5010710702c4402030003041e51000030781d071680d82e00c0050885e1070031000b5510941c0321108106c1d5003c034140b40031801c4000c10041c404803854039281414100c8146000b4025805c20101d40c066030703000945590404040c050385071001100d1140c1a0a60185400c000f12603441441400741c4010181d1440c0000c082c1240c40030901d9a840700c081c0e01301d8199003500c0b0301142d4144800c1001c100c04401303c0b6800300b811620b543c0b03014a5580020300301c0d5000d1041a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 151114136 1250 151112886 151112903
    0x4110f090405071d0621010f0609090c090e040c08030f0414040e28020901030c0312080f010605070203010912030e0f0a1a1e0f07030b09010f09020702030a0f 69
    0x81880d20745809001c0d00440103091407501510b0b0404141180002000054003030900011035140c2a09170202c080d682a1844248150a50319200b01030507034600c0d0300c82c0300002031800c840850403407040c0c030409030203820f55201c1c0b409003440c1c600c503101c0082c401401642c03002051717800016644d8050009103c0680310b0400c803a82e850034509104110000d103003455014500d018150000b180000035043c402040c0d00320302c00b0540d506400c200e50325812225009400660010000003041700d404140c0046d03a101d140b100c0310072803455004607110740045506090400003000108100e80c010b00040181c2400940003060b081b01c035440c3c03903885048002e4071000107551422940c801c5007040c8410f1800250070000382c2146241c0351606540344000102c980c280380f0803013001c0f41580700505065407460024a800c81d40ca0b203000040000c21680c1103640c0c030042070800b91401e0082c035207246600c0c10ba500d05280c00c14240c2c1084040002034010100880c0c0501c22030320345402240707040c0201c120961156048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 151115386 1250 151114136 151114147
    0x150903070605270604090c05030708060904020a0605090d0606170d14070b0604020c011a10020f0307060c050c060903180406123302040e010b07170904110f 68
    0x9240c9400c055501c8081084800c3c0700300741c0c50040c9108060f03508960060802c4036042e904002500c0c520403607015401752860071070000b8003941c00501131031280c0741c241c5491510390b403800c0c14000007850449000354042e40c4120144145030260380542745008010300b21400b123102503501c600803910344d900704c0c004000e08170103400303600541049004030503002440d1107400804407204140c21800381200040c07262924500082d003e4460b039040e111710484200c000e1210300240e41c0c400802505c0c5858543c01988802d40c120b10040c0009030002070143d040b0000e525020aa85401009011444200301004420070446001c02d030104882c3d40981c40e401c000c0c44c0c0d60301409918000b1410b0242a20f40601d040420800458030400b40107024150000109454000e60414200c20007840d0541c941640c03810100c10103400c019a40540196403184c00f802d01da5903204c00d00d0b120180900207000b00301c0501c1e842c40421012142d07026120007003000e030010607940c20000691409403c03880d600c3c1c09415000c04c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 151116636 1250 151115386 151115389
    0x4060e1009030e09280c050f0a0e01030e0d02100906090c030b010801060e070801060507020f030d120506040b060913180b04060c0e1f051b03030105010206090c0f0f0303091509 77
    0x4440c5c002c4404540e4203520640c2c1140300c0e0054034040c00c040303082581c0b01a1044118081c2c4100e0b1110f185405a0f00c2c0c2e60001301202600d00d100402c030040c00a0701c0d0020840c0d03800000070b810b80100480f500202845445850500c0103042180d00440d45c0c2c2e43c46545110000b10440540b0000d5841071444011035130610002d203003102c01c6944400c0c04c0c03080410901001940148846055440c90300e00260b5545150020480001100c0b40868151090b8542c0100c03c99200c28041e982c00000f040c24081c0f51180e02c100000c1e074008806891b03101300300b0400c2c04524942155604e441000b452004074040c000b41c612400118080078040c0d48050310300040101704540c501c181a00e8031110b0914514124415011038a80080225800c00030801d181280c01d000c1d0188050b03500b0544404281000300311407080d015160f42081c0304240c0940301e1f900c0410035180d030101d0002c00c0504060940400850709004202c03441b483c0900d06501800200301d00c0d4043d4551540c9030580384411040c05c0c1d0346030f50460 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 151117886 1250 151116636 151116649
    0x409050607021006060903080c16060201020309100e070b1b0312041202010e06060103110d061e050a0b07080f070b2a04080a141c090806010b090904060e1009030e 71
    0x82965407500c0002d0245070780011001b010b0340d42040c846c80d2200c21120345c0c1d51528142040b000003010010400148056054004600c2080e00301c0a5540000000714140191446211081d01d1500112802d12490040030050000b143d00700300b03003a02a1220900c0b41e0b0940d030115142400200142040100303204d4050701e0f0b001c40d15941d1008205941e40300e070303c00d500d5407009000c50341056101d1030b100c000c01c2c09030002c1e94190143d2090421145071344105c4541c0b815580d244100d2000c211180001e01840c01004034011507280081c02490100642d50703900319540143e400f41603664050105078045280071001d94800d40c0780c00c518003090840f04400c1e1a0b00030103100019140ea8040006100710075000c02d23641ca41950000d83c1202140c01301000c0d5007000e80c45001c07c903c5400d4480400c0180e6440141c400890700f07040280c2380356988540042640d4030a032103015070444000301c0400d0028000f9031040503070320740040a4400c6007503008119029202200c50680014001d2030000d0520b19040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 151119136 1250 151117886 151117903
    0x50703080c0a05031605090a0b1b010203010e01060302340b09010e0a020d061d031312030c1407030804082a030d080c0d050c03150406050f0d030e040905060702 70
    0x104040340c100040010003d1041c440100103003413a82c81c54500401c000d00800035180e4054006010071040c40e12900300c499103411002400c6200720080c220342c100100d06200700ca05903101c540f10608a41c0c240b1000382e02030760020107a0341c590140107814044401100d105402064284062980c0f91801400c2250742c4030b202404020a0340d14200d01440582d1000421403d89a410754000344150071508080000b04481002031000c03000000c1a0398404102200034500108150f001031401900d4111040f502c4481c148010702254841c42054046143ca4070030b10610003444040341d4090340c607603071144e0446d0810707030044889611101e03040041025240880c1313403060386030414004003096800006e542c2c1c081ea4a1100c01e02c81c0c0000410740303000d102c104507445562404014000f40c00c01d01111103a550003100c00301844a100300580c0d00782d11b481d000703001c1141d100505d00035024660904020100030901821400d000300c0c134544d55025110340c0280381e03005004402500301032030600e50190501e0360302c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 151120386 1250 151119136 151119151
    0x110d050709020a110f1c1b0602070b040308181203091006081f0522050f03190305010503060f0106030b0a050a030602030108060106140d020a0509060c010912020a0c21020a0605070308 80
    0x2500100c5003010303034001d18500304d01b40f03032506001e000302034901e5a15041c1c08172000350109000181007400d11820741d81842c0a1846035071052000c2e640d11042d2604034100c068282030540101442c3c1d50490342d044042c64121003a134044c0c0b00301070905510030007100c00c1d07540a0041ea8001041c8103180441100076008242500c00702803010389440301000c50746940d00080c508078440300d01e48540600408018050182400b0b1044a5944441c0820108040e1503041c182c40000e0500002240d54200803030898003e0078042c603035030341503400c2c403109401a190b40345c5a10340007003100703a0001d141d035100d030480030043d8064080166070b1350620025600382401600304005001c582c04043c40d070414041c003180d01500f00c01e10010703202d400001e0102c40d18410909140d40c40384000c910b08030b100c1410741c810b00d6105c2c4100300f420002019010140e840da0807114010340b203054500010400d0b03070301c0200c00c1d40b65220341e962030503181c02c07103035000901149050b0001000200c0c0480c0c5101010b4020304e00d00d400114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 151121636 1250 151120386 151120393
    0xc04050d05070302040c050901050405061803060403031b09050108070804110d03080f06061303080304060209120123070e041a041b030506040b1302130b03010b09040506060304110d050709020a110f 86
    0x80323017800030344244264071800740541c0d00094a0303554060820705016000341c0c001c05445042c201400d0003006440c040c4900c5101c0e202013149001d41c103000b064904100c07041a1955121540e4104050350031041c010300c04d890009051801542c00e076120030713041c3c070b1240c403c0d2580365107410241614401c01d0402446c240c0606400c014051610b403a06142400701c1c1c2c1d11aa196550b0307a02c070301c0c01c0000380c001d541070707a900034405100211400c90103400900041e04034000900401803500d4010081c040b0546d01c070b601107400c080c04192182442c0e0448030783c03404480c2c0359901001503800414211204003c00e400d40b2041407001042141e45400740507044001250180482000b00d00041c003034411421000045a80c0022001045411600d82038020040b000031107440c1d40c0d440c100140903600031021180304904d413800142e154a064005c0e0383c020740d045824521000050b401340206100545d42c160750390710501d44d00060344100340c00201000d1180355030360129410f0382c02181d442c044640e12169000d81 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 151122886 1250 151121636 151121647
    0x100f110c01020718020d0207030903020f04052401030b030f030714030304081207020a050717010b09040f0308040f080a0903020f031c120204030c080a030801080a030e06030c04050d05070302040c05 86
    0x70b90000e41d0609613401110804114551440070000a2050f414a0148503001141c024145a00101883d040764000c0d1182581043c4000801c022034030116004180d201044c444c01441407100b01c0b5468070702406040000749151002e0000e4500b202c5003e111800b0f5000080070000c10040318194092804100000e50179414140d0300d101d00ca01500c0342c281401c0e0b02d03110026100034420803262a10642081c01d03034507441c0d01c603a1141258210035500340c45546c00c020002d1300310308144544521590304a4a80d1180d24140e50b422503020702c1c0504151290080c08208401040302c100042170702c0080d507128120314611307610501070000d200503002e82c480c0d004680c45c010445007100e50004981414030f450404000e024540b41c000b40104c0d0800b40500e03030900d00c0801c0b405000100312040ea4040c0d100c1ea840f82e80d80b000e10581d05c1c000302130f00800007680b20388d1081203414400065600014000c2c1d04138105521900404e01c80c08050742c2c1500e07640e11402040045d42424031035004915401d280007031504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 151124136 1250 151122886 151122889
    0xb030903030403050a09031b030c0f050d0f0305040509150102010b060f07230a030e0a0b0412030c020612040f02150a090605030a02040e0c0c0106060309020109050405090c100f110c 79
    0x1d00000300050700b44840091016292441060ba24024580c08491502100300304003041d034907208640003c8403032904042020035940c1d0805a0b04040301c0c8018081544072a441e03a807111201203051080741440001d000109844d0786125059100d00240340c2c500552020b07034400242034842048007140103000400c0560180b00886007114103880c0c001100c403500752005441200794140803584000704c5c0c02030074800c01c10954404440c45081104a07103980c007440d2565600700301c0c0c1c0309a2140035041d8840f039801c140041d02440c4442040c41c001000c85050940380484490b0042040740d0440301c06191f811511700710308d44988503e00d28484114841e0a10001803005044209103016050a01c8004030000f0780b1a00680c04803409170900d0070144040741850888214a900a82000c1c40c2c99400d00f440400c5042c46072040e1a10035030141d599074096807401c424030008100c0030b00601040c0c024000e40e076013542c03103c0d80600542d509543e285501c0c0318441c00b000f40740e05890b030760591094000c0011a583da = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 151125386 1250 151124136 151124143
    0x60d0c05040218060c01140609060907081803040306020405040c1706060903010b13090209160219030314040b07090f0308040e0702160b03071119030f0e0603100f0b0309 74
    0x35654241e07070042e0395042030700f000700c80302d0a004021a800400050f1101c99003c06401465164441108a0250307807201003c01100600c103c0724280c002055174000791f4200c1c41400802e41100e030352a90000c2c05c6d0a01900103082d5445078000b41d81720381c1c000a04101a050612410b400f80c142031500200104040052015001000e08501e00c103820209900d602941c0a5210f921107a03401404002000b0203282074001403c070b800d009a104d03030780c00d00006140c90701e024030760080500b0b61b60140000d440c440e09440c0390003805d240258105a030b51142c00c0024041042040d0166015a40b034043c2450003650050000450360824100919004004c00000742c50b1000d8806580c1041c90094080d52441401c078507000102802c070313040b4401c04800080b0500028000c4d402441030750b60b03404841c5061518907980702d20004400b500140500c41d600d0201e48141c0b18500c2c070001ca494082e000500030000900103420070385003103084035132803107003040681d413400c071620700074049507503454194030b03002011584 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 151126636 1250 151125386 151125389
    0xc04030b0c09101214010806010303080c031003060c14030a0506030f0a020616241a010c0b040b060118080102091c0b0f04050a02090108030309011a130f0e06070215060d0c 75
    0xd0140d091302009100b441500603030303030340f03103030300391007404560751055001c0c0c2e03814003840140c000c40e180401140400b803e80c4100c0380f0a128002100b800c0344d28540d5200010135084034044200a041d200180c0002803010095000e010307032078001328290811070308140c140142900286030039030220701c2000050b201d42060b9a8072542c0044c088000c0e003514201342009030140c0100c00c0b402d01c064681c5120b0081d281e405100420500d0410600e4404075200540300101c4145014002004100014000800c00303503049900a0041c03500d0516011310121250540707413150040a1389940120390451682000c21034059041d141855080640180e81c0303a42035079110203407400a402404000290610074100900360b02583e0240200c6115a034620130503031139400990f1070030455420448042c40440c94000c11607003103240209500c032081c00d81743c1490002c0502903054040325131100313400c2d4182c00061154610600750b5402801c0c800001c4e00139850b1808000300428840d410758400d440104421000120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 151127886 1250 151126636 151126669
    0x209100810020d060503030c030301091802061602010e03030415080903030f0f04061103040b0f1b030105010e0a030b0403021509011407050a1e030b0a050d02100e180c04030b0c09 78
    0x1650f400d80248000043c1140d41c01c0541c25200024400c0341d00d6a0000085040702d808800400c100105101c0140560f0b0003608083d60240b4188800c0d4802404511203d45461050620085a5050a001c42d0654005500ca2060120f03150b0804145540003a00654080304a8002e5851440d00c01c0102c6e1045201030461030350070180b10001010018907510101101d621084016180d151a2030090000c0400311545464408503034007103180840c1d41c20b8046c401c1e101d00140e50f801c581c00e00004407070180d05491001d4dc45408240000089141d10440600a5003c0e5025151112010f0401c258140700500761501981c03400610701c035881203c0d1340040d0080154500b50380e039080c1340001121801c1d89820110f8100d00803090f140c140580540c0b11010f40b6030141c0d80040ca2650700c404010801d40d51050180d0441d003d841e46c1485d4074800d402c0050048130081010060906004500c940f1400c120f0700603500010015062051010b002d84083e031004a1800241c904241280407031758a186200d144c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 151129136 1250 151127886 151127891
    0x20303030a1d010204030b01060e100903020f150f1e13030305030a0219020f0d030c0c0b060d0f080903010f23070e030a08040f05030106050105041703040909050a0209100810 76
    0x50000d6040388040c40210b8064000d5403075a440b407c0c1140006002e00c00c80002c2140d0440b940b08506100c18804d04205040e00c4101c901d0b4a1030302448110403080022176449540f46290004440c40c490103880b6900d40d50016030f450315010700549000d40222244120101e0782031003103c620120410850054030340c145400340d12920f959441c04d01170301a014406d1600e11762803880040d6136600084a02a0300d02c038800311846107503041016001c031100f150142c0000340044119601291107403c1c403d0301b244000e00062900c1109480d9900b156a4044084072078042c005600c03a43d51609006580c0807200e46581000329030f0380000c06004a42443d000e558501051a001400090013240c45000518010f000d550035039090b450223600c40e6001c5c1c011642a131422002c003144034281440781c841501d0b41038607104e10305802d0101d0300c03109011100b26426288020080458982101c2c000c06034807034403e400511401c440b0340f040101d1908004c01381c0c00c0c02d440c2998200010480000c820002840c00c0b80c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 151130386 1250 151129136 151129151
    0x40203030a0302071703070c111e0d05030c0303010e0f010e010518090c04060b0a1103040e01050d0819030204030b061e010e030c0913120509010c0303020904021c06080d0c020303030a 80
    0x2080117400c000014a40c00b44c0d01008000034190424100c2c400c69101e19010074004100350104842d002c20130f40104140c2401d4980000749003452900c99031143c0c00ba004076420312002c1c00b203c61440d8000d03041a20120700c03a801b401102c405d401c41141c0580280c00c986505503042c500440c403540c03404d031507030300c0d2295150000c24002c0d10240405c06034128003410900c01e41da101e42d21481c4550050a261000407a0078925000090000c010340b000d9484285610382180d00c3c0c0f908020030600e001d0000e0744c50040c10460083c599403010301c54400c1414a4402603115031541c106030445180062900e030182c502170040400007800c00f99200c0e5003000900304245403240f4800032a1400942c0c544540d04030f040030042c072600c07128841c2500521449440a5a5075400c07101c0300f21000d000304201e07680820107003860440064082c0e00500f200c0e110151006060695016403892800e00c120f0118061a0b61140207111116042c0010340d041400ca041900c2030001ca41c0c0441e0390fa110050403600304590311b484 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 151131636 1250 151130386 151130393
    0x6130207050a08030603280210020f19020f01020d090621050a0e07080703081207030f0c0e0108090a0807062a0302040f17060a0b01110a03091d040203030a030207 71
    0x5603048650000210390304140309280c80581680140d0700c0b04e03c84c0c4a400054408406440100c401300c80310700100e84441d130203690038003007200c44990040c42580600c00c40d508200703404001e80b040c05103c125001e070049130703107005000c000c01400881c0d41c11034000e060b4491180390481400d41c00c480384e40c83c12148190300360300c1210703440101c0381c41543c190f4244802d1161009680e0000118000e400c07007600c0d4250303900c0a0342513450000e03100081810109000d04203110440b02c00099000c6a981008210714070181d6000b402c452640308440003144081c40018060350b80700d5286648480400001e041102c85901c07240303420300030f1079402086031340c135030058407a50101c1c00700304084480c00711149031503c1c142d25400b4019404c06e00455144850030b00d000516006074000206965814002070917080c1c40710742c1407501034aa4160024180802101003142d404410024400624040d40c7c0300141c9a0900140b4480da01c40c4801a0081c00400e5040c80056070340402102d004940b50f00340143c3e01c011925 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 151132886 1250 151131636 151131641
    0xc0d02031906020d1803120506010309060e0a031d0109090e030708071a0c0301030f060203070e06030c0d0e030906120907051c330c140403080c07080d0203030613 71
    0x48004921140c58407620040082c1a0040e01c5a45503005007031200113171760201022005010413000e800550101d40c0600101042d83c00603400c1801803601150f950541e0321036200703840304185407940c80d6101c0140c1d102071662118102e24100d11f040306158170f2441880000784900074a0140b10851503450440303e000d0b003000c208070740f03107294003d540316100d03201418229468454074580c504015200400180c407982403d085034162a441040d034407900080b6140c98009400c010000c000740108006041007654982d0041e502c28410109141c2e80c5401d400310b0322003510a050b4880d4415071003480284100e555041c00e030344c2d8040c0d800d1000e21907940c604503524a821511ba1045030442020b030090102501080101c2079602e0080f12994103440ea140c0c00e141d00030304800842005c01e0b1246401e584040c2803078000718113070a204e140045c80816038502d008031a074010740c4100c2c0e50030780029502e0080c401c20712001004180c2a03018292415100001070b4623440020509441440d4031100480c0203640742c0e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 151134136 1250 151132886 151132903
    0x1401021c1b052b030902090f04080904050115110609190302030f030109060f0b09010e040c0c020405090609060c07031d0a080a1a100f052709061504020301080c0d0203 73
    0x20301200e01e030300190110441204440b120080c4400749104003010742c84c0c02405200d0401c0d501900e00c019640d01e0081c105401c05000c2d00440e40f0820800c0702104541e15800303428046c11b103010b01079281c0141090090040002c00360b0f9854a82c00c00f40401c81000c20128580d02580f400301c8158652542d24a01207081d4441d400980b8034209002c00081982020395102c0d4069039a41d0762084034954442e91240f40601403422900c0c0013407455002c00305075003800d41181c403c085003800d01a180f04825070000e8169101103401a5140e4060410061680e400b0404107800800710864640303400640d0b01c008018a0410680540c01441c00140d81003946422000c031004113810f006a40b5681c2c803601d0044045120f00c0610401c081c00d15011860f400d00e0182c3c864101e91074940e005050505d000180441c110401628000720070b00f584080100d201085801d03440381400c01c016120030300d0050403000300d24041080c0c0500451041c401400300210009496100740001c44032140c0750102c0348000b81c58800b02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 151135386 1250 151134136 151134143
    0xf0703021e090405210913090524040203060703060b0d02090d0b0a0c1103030601051b070302191703090a03020d0212030a0f030f0e0c0d03090503070f1401021c1b 71
    0x29001004103002d0041780c0100403118018513004401ca52052aaa00303000392081e0030f5110b00381d500c80c1e00244c04103a1204005a1091040d03a48000c01c06085580d0a04078481071410782c05140c00b04411032609115140c0d02509500701040344900b00020381c3e01601403804281c191a0f030000b0b034480580e503a0141a04603942c4000010300700c0c0303021049000607000c4012070f200407414000501c1c03130340c48002c42640c0c46050181c3d21103040100b403070404582c1d140040009142c5d4011254080003680356a1101040034002c00c200d59206850140c1111407003c032044030300791a4105101c5558155540003030041100d404440032003101c0c80070300010301402d020741e1040f1801c0c480082e661091076003000c1c1d0018480c1a903102048005a10101c600076101c419800c0c0c142c0d600120301103000e9140c120000402103010f441c19807001c942381c0c400300c0e2600049811001022119020070082511011607814000c1d1083c800f03006d4034a03040d106421a080d1341d841c0602802244039000c0304a44270044860410f542 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 151136636 1250 151135386 151135399
    0x30c0604080c0c0111250506070303060816030b010b03060301240503070819080f04030f03080a0609150303140c2d0a080f0703030b040507020606040501080f0703021e 73
    0x4051806101692201468032110f010f54841140958003464000c00505c800e20050160340c1c411100450058500c0086801184109a4040340680300c043c003801415100782c500040c0b103428654028500101c0c1c1c81c400d100032002d000240005030422200307504440484407070580700c0d1507100000e8050008224641682c011030302d110702140d011424141c0883d40141c05855045895003001c80d15001010701d41411060018501000075a11400408544c007003200c21605040c0c0b80c0d0b035402641156941b040d000140032005210020095105e072400800c4441420841803a182d8056081c1c00d199201c0902403185901c1600149140801155800c00c211000c0d95000304001314800400c500000d194102400d400c0c020b40e001c010001040e9005d182c00c4880316040a0000c82083c0c8554841c1804504140e141d080600341c40e1154090540540e855401511580c0351200c184012180140d01090240d4400c10400510000102c2c40320207032901035820b09904028001c000e0703401800400e01070b4203c003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 151137886 1250 151136636 151136641
    0x309230d0c0b03070914010f05070809040b06030405010501030501050f070f030515041515020c0102031602031603030201020a0311090f0607080c0a050609010e0723150d09030201060f030305040b0c030c06 89
    0xa9002801c5001c6e2480da0245080700c0490703500465407296492000b202280c010803206c0042480a005020014401031000c11f000100a01094041e00140c0b4100d885039164401441040001c0c0109940403a070790210284030b290268000b4020140c141b400c0e002c0c19514400b0603d5034a0f41e040c090410702002c0c00c00c0c0986015602c0741c1d003c90700c02d80301e55841004c00350b0084502c1403012030102441141680110304013002c0369000d8a20040980c4126410b10a2418103500c5040c00c4039020011130103900010784609036220040c09031201070b400c2809004080001d94070503911080c90004c02e409c00e94010751500360510b00b50b01203210b00421508907100355029182004030000c2e180e480361600100a1000c80c00c3c00401c07564030905405a1040d00d829030700004448a4000c0e0b070045020401450340c13052003001826803085078020a0a42010f54417040310300141502406848002e040100110f89003918686008182d40158002d03c0f517042d00010b1207615010007041502d00541c604e2040c0c84050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 151139136 1250 151137886 151137901
    0xd0519120c050705010516171810020306100905060a1101022517030609160203090d0b0618040b0c070302150a090303050906040c0e06030f0f0304030309230d0c0b03 72
    0x2c0c2c1020380200d40a40c240000151484480c18420444c460310f51150f076007a259240b0048e55401d4000e2810280341407014410300c101c2004c1143c10320704d10507600300580d20b0410005004c1c1c02080287d103c03040c8250040100141e49030707a0100c4181c9401c505d4040542c440c0103031042d019100d90301080e01c01c811041c05181c0800900050780c03001602c1101d108400f400c0c0c40030245042d00046420f654001420000503502558403680440141158810399240c800301130000b40e40480e520500352400c0700031030f04010541c245051500500402c99101005a2030540d5414002c0200103200006059012541808060081052151601c80340342802e82514103250340344014001d9000590000341032601103409500b0200340e041c000c07500004c043c49198144a01340e410420080d10a540510441410740e0181d4400d00c014904030203050055035440c1d2650070020301400c3d003038009540b8680c0c0c4545c2d1700c20030041032107900008501942c00c0e5008105608140036803c034203a005a202000020820484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 151140386 1250 151139136 151139147
    0x90a15120507110a121b0c03172209050603010e07140d0b0403020606031c080601181502030702031c02070e060d060203010605070c060e0f011b020307260d0519120c 72
    0x20245c8655a0204002c1d426030f44210000001c4405400c40403c01800c1c00031921841c404881162400181c528040e0741c0c80441464070280e400f044003400d407129090042d54018080c964204234210002d100c0804c2600c135058032400980f08000404869444091807500c441ca6402c000c0340d00026441054501070070060f44510040f136485101c0d0042c402002065080e400d410340c04007085558007442c0d42d46002c019030700107840b00c000c050f1803943c500c8006240c10415541003800c00c041e5003d03684801316031040c18039112502c81d0320b036810b01140f800c08810940c0001c103a4100d0303100402c824490388480300030400f000c0300c0c0342001e0061400080081102900318004146952041440c140800c0d900c0c2c40c212203400807400616800303144050b01c4007242d841140108440720741c42e200142250010340c0000c2c0b42181aa019240c1d0b40c125a010741401c0109940c0d0400150300e0700003902c005041150003c1c042d210740801e64440820702115840e4582c0300c1d041084880301000d00c02c0100b1110700401401 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 151141636 1250 151140386 151140413
    0xf030c060c1c0c0f0618050f0c0112060b0304171c09120c050709021c02030f071806020c06030711010e3d021605070b090a15120507110a 60
    0x1540c6800c41102d00c01845416145a6903401004007000d4221503039602028151114098841015500c00d50300480d00c03e015410000d011341000380085034801e0005480c0510140d200d00b44203241410401140e014241200d074000d0340001e03038905140c010700580030766001d0b945412002c0c48412440e17810a04941d402015801c0c0200d0a90f0b210800b030200c1210350070328105008021760010380c0d08022104c00c41c0c02600a10011200500c1000070746e40c1c0d2801240c200312812200640c0d0402403001c60b6401144913258051b0112000e010542070001c003070340d5540c0c140199402290b00000113068244200c1407000521a01c400030300401c4403800f00f141e078981117035051507004a11114289c101c02c00c102c01141c0283c1518100b06d0030010f581c041c200003504004803d1410704078551440c000160f0038402100504039880c40705894101c802d084c00f8820820341c02c403040c6032002080c284800303904550400d2500c09040d80100e0296643e100440c0c1c1200c0401f000511841114034074410810280c29150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 151142886 1250 151141636 151141663
    0xc020d2001110109020307030b090c090405031902190b1302060c061b07050705100302071b080706080f06090402060f120411010219060c1e020a0506010803040b04050f030c060c 77
    0x7030b102c55600181c42e08a68403800029415402400200001f800e00c2c02c01e00c3c0d0082600c011307905201070324000324000c44002c55040b50a6040098411410b05c05c5206481c1030f55500e00c010421500104840400c01c10101d030043c0c08038030b00c0700000b803805031400d1040079504e6018001948654450b162617594280c203071000c500c00840700b038440f4195101903060300c20168000300107051040c80d0006018085642111000030141c00b00440b03c08104500046111002460f00360364449241c07001047c2440040e400c00d00030403800d101840355a5a1911000350000003c6503000300580360b500c00201c03184142c1d81341c0343c01d2090204051584c42040d100403807080b405071342206040c0801d0300049845458050b41c2d5003000c0003103910301000c511260b00c40e48900400e030911031b001c1c9030358000700007601c210400315100592000c045403040013030501010780140b41d83e40046080c14100f512010081c0a20301456004584d4840641e42ca59030411900d082e0001c0030b400b05903a8000c4401164541c0600032061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 151144136 1250 151142886 151142897
    0x20a0806090606031e1b04060f08010b1e090a080d031a060307091206270201021c02100c02030d060f15110606040e0a2f0103090c060c020d2001 63
    0x301c103801c1c0700085920030101c000394464585154011040e0204014003a05031004810302c1c46c80301215400001d001400315a129115201107000c001802e030702d4140c02c031121103d010f00410300703c0e0469043d0f241d91118a0300202d070300c0d07400c2c07800818400c05940c3c7c0303c3e46551007144490710000e505030303003d4020342e14103014405803005803900b480030b40e11066506600141c20800100884000901c803520828420100410b05140000000760442e904e449072a50b00c540c4190604110341e010010350700b158000c12044e40e0310030f81d030300310181d110040510000186526070030001c00083c0700344105c40c2d00d10440c8108001c2e15803510707480b442a0080d40524110110b080070086112030140403d074540101200c001d00040d61042d0038000a8034014500c1c214034031a600c01c000000385211101c0f082c0c0303c00545c1160380700180221100b1450a03c1e07101c18145031802c0c86c0840400c0401c420765083e105241802541c083d074610101c0d10321105014054002580c40310b00714000c1c0c900d02d41f0869200e00c00d80e44e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 151145386 1250 151144136 151144141
    0xc020a02220e01020702030615060c01020d0203150906030607050a110313090b09010b04060e0f0d0b0402090105010c030903080304081e0702100819050403050c010908031006080601090b0c10020a080609 88
    0x1c28205d210f0301d40b000e945070f1b001c20005101201c01c802c0340c054445000c0d100c00d0600c09480d1200d400c1e0380040c00030103552034012080225a052905541a04400031604542281030000200703450700f202400c190b00300715002543d90350850050046080410200084a68885004444001050305c6000340606070b81050440c40b15407a2201c800c605948031800c01a00d090310700340d000d40310030704880340a6401030800391010240c0d5881d20b0060001500416082c085442e040c030400001c0d4005800060511440b50704034400b082c1c2c045c0040040d40d5204d040540d0325141c42c10f00400b80e001307450303112480c2801c15080548801081014000040c400d544c0d00d940c585c041d420039502108104ea94005104144200702c1101c0e610b81c01054003d4001d0074086e103440c0c0400221070965034100f5051711400d9001091107913801280b980c80e80104103902c0d01002e0b07403d00c017000a02d404c1e4284140140c3d4035011450b04071784481031102200790303002ca0a0443d0f031950004409031042c1011100307071b44110b480400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 151146636 1250 151145386 151145411
    0xb2a0a060b0a0e190902010e090403050904050a11090d0618140106080c061602010e030d0504030c05030a080a0f020c210c090103051c05040e0405061605090109090c020a0222 76
    0x100d43c0904c910b601c901c2c500300a198010310007420310301016030401c96108004509a00e03483c103c20b0040e40681e9510b42d41d06060b00a000540390080c2007a080c03d4a0320351025020a00302c42a02d801c540c00300d5a94215045900348040030308241c002075100a200d440100d000c000c2031040700d45003101410000c0c8070f91642c41c20001d881e0019030401c1c0381c2108040106c4c2807001c5504900c40e04103441414668422040c0c200400c4c6891140c14207000400c400040c14000d005241c860100203100450040c40c60315038541e5074012600070007230200700380568081880b220a000f402a4010ba8001070718100c095032441c5403031004162240d441075024000c882ca1000103081080c0e2803070607241c0280043c000841042c0310041850b080707041441c2000000e00c80450840360b039030405401280244010306072420030780100801034940490510034014100f042000b42d9070030944034002c42d400d0710f0000a0031034149000b68108252554000d42c0076100d000c500085010320003800c11205100c0004024041c04e00c613 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 151147886 1250 151146636 151146659
    0x102040e09070303080c0f130920070c0302090c0409020a030b1206070e0603070e0d08070308100e0109050604060e0901050a060b09010512130510091b0b2a0a060b0a 72
    0xc00f1340011070380000508600c2e0b0410082c0b0344180c000284602c0c041c00082c1c5903400315641c4d00920400303611002404a1911444a441e000d03280329a0241c0c9400107503a5150030b040d40520000b03000e00b542c000080c5d4000c00c000c00f968006c1c1210b00c1c09640d11100d61800800611040b60000d10900d0b2903101d8104070000010f206205070125183c051078100100e00300002600010f03d04000c11100004080d80b949a150a60417485d2080741c8075503d0380c5080c68084e0007510020600082500c034044200080c1410080d80d504440010300300282c640c4485000c0b030003409039604107445411382c010900045120551040b8841d28400c0004c2200d2911340309031542c90f1085e0010345000850600601181d007100041030780c3c02170100c1d40c100a00002c0c0b9500c0a04212440644490076947c4060020078003070f09120030040d591502d00204625803c1c400344807061300070304015008014000c008002c0121494030860340c5410b003c400c65440e0011803074214007501c212400240507010701240041c040003000b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 151149136 1250 151147886 151147889
    0x91703040807170c120c0106080607050703030c021c0503060906010e060f1b0a050304030c0501020d051b070f1401030e0309011e050d061410020c0307090c0e03030c0102040e0907 78
    0x40c20140c9004400c0e200c40210521031903080c2c031070f810108402c18840d04d0070461006140358000140e82c0b9424880c0328107084072071036446000d40b5000348042200c2241d204003101c501a034035007800941a0b0805208174a0100d811101d20340c06220300c13198012090304000614031440007160328000c595600310046500c1c02402e003420780c200780d041c00b50b4050465024058203a9440702591180d209480604013840d0440d1414192096000004d09100340312150300031101804c2c0a000074440e2002540c802040d510a07844451419a4000742c4400003500601c11320000b4481290304d26645a10380f20031100d01d032954681d05000c2841e09944034034400002c0262424850140c4895440c2141420414000c1e80300320850400c215080002100360102c0c0d04ca09000740c112110840d0307080c2c0101e03041c02a801da00c658604199070014a01c1c03142c9580001e42c14094420711000428846207503c000d0f030724800041490784d45800301181d00c44100b0015405001242e64900310f00307425480700e0103415101c401c1c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 151150386 1250 151149136 151149143
    0x8191517010e10020d0b060a0e0310050f0402040f0b04051005011112030c13230a0803030906011806030c17120f0a05030c07020415050111011e0903020a020a0909170304 74
    0x43c07070400c41c0f0a20560103004040300c004008500204144002022903114680d85000b14640c0040d0003280e0074200703c00c11003141c00c10001c00c0309060940b0b101070345240087c0b0091045403554148507204140e81c00158950101800c24042800c0845141110148078000e031130000e984650a48944840000c01540d449400342c0104e00e151640e40c00d100b03882c0d03c401d40d40b40340e40541200c001860b841088103041d8045210b68a00840b280074401c02c04250940d40c48500c42d41d000744180f015121000c038060341100c6500c501d501500b8403200c1c1070310160240e9800981551426600080c800000788440145140300d0344c00c2c0d811246a0950481050080c0303011003038a800f091021080160080001b1900315042c00b442d18203040d01c942c0020182c0d0720136400070245e084840b1040080e540c02299161020070003500070b01504108010113018a81e14400000d001511001c009061600a1203e0000c035078014042d151240c0e2981e50344000f4000325082110014110f8200010203801c010641e4016a403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 151151636 1250 151150386 151150393
    0x1005040f021312080c1e0105010617070f180f08160303170406091509062007020405040c0302090709060210020a0804062301090b0102100b01080708191517010e 70
    0x20043c808031420603841045420300c81c10450190b101c0d0041003184860414601344048003d900036000f807c1d00c0c0306074810000d2000030000c032500c004810214a50007001450207103c1c003115010301303d0b2a82c222842040441512040c0800c101400207003010503903510700d0440d903500a48920a4040310110320001e4001850005034400d0282e00d00e0105070024020341d40032542c0650354583c1883c0c1300b00d00040041c4140e55034800d0040150703502841c0b65501c0a20b1040d0300341115040803820904c40d448000b0710450b903546c002000c2000122422010310740150581d003c503e000f10010b0880003046c000e02d005485203950707040e00702c06940222802c9034030300ea450340d10742e4507640e50300e10103852202041400440701c0c90004089009081e02d8600a110324800415051075400001e402d018582c20b00501d0a400c01e034203202c2603608071000f60741041c6a440c08680c25542c06401603070132040907120000007400c250000002c10a40b004244c207851001d0300b0031040b69000c14446089481410140c2c0c0d4540 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 151152886 1250 151151636 151151639
    0x1f030e0d0203091e040203101d060f060702060f03090304210503071709030a030503070e060324030a150b0a050108100b0a020c03030415030e03070c15030e061005040f0213 75
    0x1044500036202415240c004c0d040d0042c041e00080a036001214841c1090820490030401440114400308075101c000c141c52101c3d050840c0428001c8410300d0791f0314001c010009074542103450740422a0100711100a036252a8184105229101d900512800001c454000e8964210f10b404410164245034494025850240a075507003d484940c3e1420f1007441e88814444904a83c0f81070181081d018400d0740c7d100d40c0d915008601401c401c0caa480c0440c00b6807024010809041102008070030500e02c421680849d0940d8034001910b44406524000d00b100c0381424842c145030140d130021000b1000c101c40540e4016150001184c21074030482d1440320301d6a10810412a40940350001d0407080c41074819542d03002208008170f8555440f5134044000705401091703901c601350b41441403803140c02c14070b4040c61501102c0d440710b050442107405a4010007020940c40c1007204d01036407001036070081c14016600c4610302102482d011440310302c6044e01842c14003440c2d41d080c030504d100725109042414002a00e03503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 151154136 1250 151152886 151152889
    0x1504330203040e06091e090d0206070f120e071211030d1106130201050c011505040606030b030703031b020a091e020301060c0f020d082206050909070309111f030e0d020309 75
    0x10b020151188051250006601c00000c800c0a801e80c1f01d0000d802c0100115180343d10001d16222009260000300410041071550307444d842112401365001c0134402245100e0031700030b100c1c2026041e900c8000071220910007901005001817880481d000101e060311140004404141c40942c40308a5655081c0c02100006803201403020014a5582c0185045410020840052403c55403c4464444403041002003009149054020342014040b01d2406204001c7c4007004a562205240001424441a560682140301c00803c1300d51005400038051103050f551525804024240e110400607000351307417114080700c01124001c1301c0c1201c4071641c03066001c1c0340030384414414181d1004100e0b1300c0040e4411013004140440007400c50a40b46e58030b010382d69032900510402d410b050742d100f01c0600c88140310002c06561a0001150b00805c1802d000c41c14118900e4a03148840018880342d5200340008000809800d150240741070040181c0c80c00c00c40c0c2140c51055990b101840440c6000681c030403c4a07a00c00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 151155386 1250 151154136 151154149
    0xa020304031b0501060306050c090a0503030f040e07030b0a03080705010506090f01090c030b030601031407090501031e0f020409030216090203010f0621090b060103050a0209030c1504330203040e06 86
    0x1800c1c040c5000003000d9841f0743d21101038400541e00f00d90642404140d0396114900540c80900900c0114000d500d49941400302003030a0042d0b200d0601d040149100041e0058003d070000c03d0000002020000350503204e241c1a41075070401e0340e003641c0c5503103010002402c508149140d140980f11141d0400a41c0c1c0c070f0a40e5102c06040f442a424041540b03e00c01c920030742d102000701c0d90107144542006900350800c5000c20f86014001d9014145580c10800100041050302c10001c03110280c44440c6950740503141071010300b010b00312800039003051418a9820905502203510488041c850115284040d43d583c40a0f040e4002070090006102020780d0802c8458024061182d640b0140c205100a0304040016401228030112094030442020010400150b81c98400d403030340110000d204600300b00c0d0308400700c1c0c2c0e03501c078030141d841c020200025000051145c5000b5900144240d0341d02c075080c41100721500008882c0702d5031460414100e151011040e5001000b0b580c16501c0c50812400203a40b40c9041158 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 151156636 1250 151155386 151155437
    0x22050a1404031e030f0e060708060d11040b06040503031207080a1e0213150906031512030e0120030c010e03040b07031d060309030c150601050a05072a0801050a02030403 74
    0x14165170308680309181040f8040e850000b40c4080c0900034038a802c04000d040f2000050856114161124240c00040c14851340d030307140510151000102d40801e0300205259100d6604256070501c400310312584081c4400c1c09140c4920156a03d80015864020040003611003807002000d400d40d4940b07c00c00c801b1b140798080c00b180d400c600e940c0800140d50b04202111a885040303500000b0320014810f001c81b80e0103004d0003c5a0560301070009400703240c9010b01e40c8012031000c0050400c05000620f055030b070711a4880725660708903040c1102441510800341941c0e64000b0f882e028141d401c00008803196034001c0203803412604890f017602d1130011655030440d0340034a50043d00da265082c250402d0065105c900255200c3e0402000441c0d845101c0d4000a242c8010b04a05490a4950070100012660f1010aa0f844640d40f801e18a0300c64a040c5440c0c088650458880300b480b2a0485414104e240720758410000c483c0483c000b0000d03901d40039140d2040c0c1c0b00444010f00441d41c110b0140880800303030400c0c1136 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 151157886 1250 151156636 151156697
    0xe090717090c0d03050a0801050a0b04170a05070801061412120307020a0807030306030219060f0309060605120d1e1b030215010902031803032422050a140403 69
    0x58079101d502d40000c1041201500a80005801243e012080780e0840b07041409081d0484034905201e05d0201150074034800d600444402d0030108185042c40176041016404a03680030f0180c445071922589028000c12491003000021000e81c6070095050501d4400c3d44078001100003d041000c80c0202941d5040c0d2010b441d07082107215880d1840c0101e030384407019100841c429500407a20350f1543c0104a00354141e20099880d41c001c070078040100c0e5400401c07025001200b800c021031a645079040480090041f030f4405d0341c2061101010515007280410100b060441d29165065051198200e519841c0d0710b140217032000c140002480303501040701041040c10544244103c4016082c04000308542000a0340a01407030354000c014080c0c5030030368004055042000c0c0004500314a0720440ba00a1021502d40c441074031152801d106103140c071014500d0120085492032042c0120041074a18000c041c1107501e003500510300703e0744104003510340c0d17030080c010780e01aa80d003480700d884030b05202c400614008501 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 151159136 1250 151157886 151157893
    0x309030b010305010c08091b150f04030b01150807090311042a1409010801090e0f030301030308100e010501050a1107050a0b181c1e060e01020306010e09071709 70
    0x994060106020b03610480010542d14440b20001d0001304d00130b81f0f01c642c01e801c4101c202610303400f410b48a1201170011110359605616902d0006014803030022a14120b807400100030082c4a05403024904868004000c0c004010900408940c5200c0503150380340007400119041011403107a43e40b12218001c014400980d14070560500c1409005113215131a00d0781c03019000a81403904a01c030044621200e85902d4a8000c200300001c251040502503d10640d6807500744100c190000c01c1008040302e940c0046a9503540c41c1e003000303001031900f25131203403a50303500303002c089014186075017140d0488a068648606103281000262003522aa14414640d03100d001c100181e10368402c07042c3c4000b000043c51081e80c0e20310707110701c50390300c4902966410300864050529961903d6409112107001c8d401021002d400740b252420145507850603c0003400d280d00f80a810754a003403042d4020750080100b40c03100340050b215502808904102110190040f495254607054800d1812400b503500452078010f8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 151160386 1250 151159136 151159139
    0x62313030f08090d0b06031608070501140c03030709090b0307030b0f074b0804021011030f04080105070c05101d03030408040602100b03100e10050a1b050f0301120309 73
    0x100720ba1303100304c01d41034a456422106000c80d50400f0b001c80d03003940100700c03114001103050042c0ca03907444803c0d03c0343d5810070169244007404182a4401e9031040e800c94410349540382005440100205002e00544840c6c82c03400c04458641d15000a409007226849507180e0035698880c1107030100c1c01002803003081403251380e0705c101000140841c0f98001c103034000c0701e205222440200041025001c42c5045010b1060400390300008a070b0400d0a0b03d038002c0d41118007030b426a0301044201ea081604445180d080d02c8045000e0000242d548058001e5030a480000c0040c0d0380c170f14a040360446401140903000d070b009011421044d003101d40024400100b524021004030440c0110f162541c0d204450030741d00c001e00400c0501c43d9550501c12000800c0c2200c00071701143d080b140010351200c5c89450701c1101a030f65250103158400090060030310007002c2344000c015030b1409180c00b2000d864117511034418088040311142c9410300a40541d40180001e10704075065a080603102031046021080540078040702400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 151161636 1250 151160386 151160389
    0x12180d02070302060702010e09180d03092d1b05040b041a0103050a0e03040305010c020601050d03050a0518060a03060906090606090b030a09050319170c030403080a0f0204062313030f0809 82
    0x60040c050b10740cac15030542c00c40c510b5500503414890000d000344101814501000d01042e90b1503180032031070700c005005202d0031050100400c44142c2401d8020f000c0744d05a00361000c4101c0b00c41c260012280c06450034060045883e00b08403c0310100c003100c440ca0b540c0b00720b544403603520940c041680921744001c0091810b00d111542032860304039610440c2d5aa4549514981302641804100e0040c0403c0d601417003441d400b564040c0180c040d603000141044404501c20140d41c1c05c00310f501504207000341c0b80c00c5d941c24000600070090b21740ca01408043c141080e2001520f4181c0380701e500e0444d02e03140d59002840303040c01d10b039103825070010b0110002d403038440890784003181d0140700604224450014401e0811031441c00500100ca00059070001c41d03850b201042940c04502088076407165240c41e001620740d03203550801d001042400d41e110800780c804140072800350380108149103102c0101040b41402c500010300b89130a44920014400f07040c1088408000045580e120425402e12902c04079060400000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 151162886 1250 151161636 151161649
    0xe0409050307021503010806010902030408120112200f12010209060f030109060801060302150c0106080601091d06090a0f03030f050c040509090111031f03060212180d02070302060702010e 82
    0x40003903815410006042e400c501c0c0c1085001c001a04034140325085600d402180c6407103d82c1449007010607a0000300103001c20140700100d0ba60500b81080140203561501340100d803a52696500b181c4003800700000208043d0005060026014010701000e010070100051152107960407009000d6513400744171915041c1c1e03810020703200300300080c0b040035201d600d0314001a065841d07076400280d85074980b400920242c1c4503001e520140ca03481c1400369680d03010080b80c0a004000c5a4450361380c0d8003c440000c20348002c1a04030300c0030090020000084525407040140d00c8140560710800a58010201400003071050300c8940c0c0c08600900b000200d035498042800309880044400000c0b5400001d003e00c03907442d0010b8800d4010004c0002000300c03240c0507000150030b100140035005065124868441010f075800c0900300990381c09003081d515541921890b407001501070303a000c420280050308280c0c00420009a40014201380d90003030403818596024428035510503c030a81c10011500403a02482d210407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 151164136 1250 151162886 151162901
    0x10f08041106130b04171e101d010608061504060b040510021c020d140304030e1c0812070908060c0a0e011412070e06180411070210020d0906080115030c0e04 69
    0x61b00c9607000c072425950701500740341d007408030004541000d035a030320700d171a800294602c0d28002c800030009400a41e41d14034644440300c601c20744007560030014080365001d808103802e809403505000744000c01d260142088140c0308a40202c8480c010284010051840c1003c600c061900503801981c00d00f88954503074002c24690784410002682c0003010001c844c80c0c0c0a200302d02002000030415085007400d9400911002806103d41e104000f10b5405001d00e00d5080304607081d450307000380e080b0b65415003241785079000b100460750b207804aa008400018244804240c0c24891140740c100686441c0c0c1340201603801c002c50141070760401a0012800b0907900ca031400030b01c6903410190346000907141c205001003071003403606e5066004c1c01c000e0200b4040f25046e0f00d00c0300a2190215004a03603074090301c0c0c3c50401e600070310b03002941c1300c1140a100d07006190081044550100596510300c42d5640b40c5002741c880100a100300f8039200d01d800181402c4900c2075214070604041450413686148491000400f6203420 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 151165386 1250 151164136 151164149
    0x9130c110d09080616020307030e010909090b04110307030201020d0809010902060f07060b0307050102030a05162a0509190b0d080a0203040e1e010e040c0f0b0405010f08041106130b04 80
    0xe40400d02007a43c081242e540d014198410341101171858405c001c0d168000c008005040c001c02070001c0d08540e00803c0a03e026002c4010104080461410320f81c4a0b44000d4130161035011413000c2d40480c40c20f012a0364425a501a002401040969034040359250401080e0881c3c55687d41079410050ba2000010030b0340b00d40140a45d91910500c0c1000000c6030110030700140720398010403003001180d0300803007903c160743c40785d080050719004201c02103407490ba0030b803c00400c8180241c02404a284802e80307144109480c0c542c42a04258844c02804041304d01994042804c0072104250507151042e608410070030103000e804001408025503408105070030001009016030004901400340d160159002980b02c02802c000c8554082c4041c41e2040c8600c06010309510100850001014000304034210001442084065408035a841480300c01d5034010340600707400a00004c007070f080e44601c0713202498000c3c0c0d0001c51760755040018108020283c1c0c48400020f8108101000000b10f12a004002c1d00080c0b22 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 151166636 1250 151165386 151165397
    0x3050307060c02010f05040b130614090d0f09050a09020a020102090d03031a090f010603020f1c0506010f0e030c091504090c03110901030c0e0c0903030307180b09130c110d 75
    0x2c2c1d610207820340340d4002050f84040c2c40e000801010075080c084e80d613080854040d00c203481d130485080c010050000c0d0000c8854241c401018024081000a88030794032881540e50000740d1340040d07200300e601007211711070789030702c2000c9150922001c0d440743c2c01041c0365141c03800010324292503600411002e94000360290040795030350807070344881e410081d40c407464210212004105840c0c1024040280c17003040c0106010140d001c210344017288000800c65003041b0030800c7c61400c100d0824100d601034130040783d001d40000c8819043d9003040d409600494000e00700140a8980c4140342014889500d00c000c10006070006040701d10300058941344a142038260050103840c03030182c01c509050b0303440000c442081e40245141001040441c003045403440c150b442944128001ea1601103660986d4040c00d410150705010001c00e114000750020034005912220484000e52075a5641c2450b480e405144a0550000808400c0e603061114651200d44e0521180c00c2003840310440c041d0791031030034001030351a001165 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 151167886 1250 151166636 151166651
    0x306050703050f0a0e0a0f02012001090302070b090f090a020405040e060a0c0806091b040f0b030612030c10110403050105040b070e0402041208090409050f010204031704050f09100305030706 83
    0x1000c51141e10010384001071141709819441d5580e1503040fa42d016240325000f00c0d42c082160311030487e202a43c100b244c242e95640340d00c0000d180c000e1000304421805407013800f02c005520b032180d8050b640ca9030801000c0310301d082400b0040c04010a0000c0030040340325400c01c004034099031148141441c8200a00c014031051030a8111a400ca800d480c0e01c900034803c2e00d8041100342e544d03d8040d15030040d1040c040ca00380c890f18203d000d4650289d50842e10140e40303400000b143d00c3d900341014601c02c140480d191070803800f11b088642d80300d00c18541c6100c1586c1081903c12003009580e0083c896003404d43c18080d103419900c1d19682c0c21600283c8046071601036139070a10a041754010401c0c0740307000c001c440451070217103002140e45c1035500c002801041400d000c2020070702d41c2d48039070000102e9130304101543c200e8000c0c07845640c004d5006000486420703002540702000514600142c500380c0d6405001040c0f021101c00c100820424000c01801c151b0525010220010b5400d0024060440c8107060200707854 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 151169136 1250 151167886 151167901
    0x2040e01050a0302090103021c0213240e010902090a15030902130212010504051914060307060c050303150307090903032307080402040510030605040807051c02071e030605070305 78
    0x800180d00c8644505030b00b40c03081c030150b643c020006044aa044420f0b00801c0e0034039441403a5000c140070301035072150b919140d000a42e501900a508081040d5030110013220104d01d1900d000501809007100b503406c80d034010700408500e60300070609030400800091150f582c1d07440c2141451400360a00c0e0000e91601d906a003103040060b0a982903460202c1d065084c106203805400b803211051003082e2166031a030000ca0107041211021380722404071036405004031841c0d0005402c00e040140e03034080c060701c90020001240c91141030900102e99106000d1340c59500c40300b929440700c04a10300f5a5605004664001a104c2849d1203080c070498441e03100885c00c000c5c2420101c4241c07000a1b1099240c1c0c00c041c041000e510343c00360807107600c5541180c0c001019103c07071750015100b00300d039040101001d10300810300c018001c540015110562040c001c48022210040c041e0300c2c0b1008111040001d41c0c0300590510030394510400300c015400f8120001e011890b40c070784070f41c410303600d094501c4408280d540381401081c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 151170386 1250 151169136 151169159
    0x30102120712200d05090f10110418050907051806040e1e0c0f01030b061210050a090501090e30070b1f0b0c0a060b0a08010516080702150403111f0204 66
    0x844070920150000101064420748c4480b551098201181c0d0b44250085038900707404255405002c100c0c1c100807010f113880010000416058840104034070480c0c0c000039181c45c000e42200e800904000204000d0748418003408040e01c0d100400d034180b1300541d0200c000321103003032111a0602144c4401045032810b00801e00030314500c0302e00301c0360404d424510180a65120b02c4d04844054410b035651130241e9032000c55103484214560005a40f2008000c00040c40c105150003660680d103100408000300c1c000340b41000e5440700ba5000341c000c0c1101003103040c2d175101d03820384044943e040c410b080d29203020381a0b550024000421124044181d01d145000c941e200c0940100b40080d0400b074501503c0d00d50600c0041c0c1d030b42e2a44040c020b08007903d88406000039154078800728010544074000b4811402c0c0741140c070503000e010810207400140c1e208009410b061000840b54122040c1c0c440b4500c654543c1c1e01c0440e0b102448281c0041c80780710390340c1c90400e40031500448100524040400503100c03405c02d00006507 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 151171636 1250 151170386 151170391
    0x30d0c060b060304080415140408150a0b0f0616020603010e0f09070b0f0a0c0605070203030712270827120f060c0c0f06040f020a05030102120712200d05 67
    0x2c000038002c202c00602e10390210350a540c80c0b180c40310a45a00c0400440300b1890040c0c0100f0070f80800f0500007144000040d00800c95004501c8114442c0d680040580480304014103a46e4003004401040b043c0342400d0004000d01c5065040a80c000030298001c81c106a00c2a40245e29401065080100c0700c44610031107504010814041c122417450b19949480c51b00940181c5035107100d001601d420414014041181050b81c85001030003a4a0100c2c40a52213400823545000440c51195018950b002c15200352400100d0a0480e4162090302c211603600e0406040d604580801003008100820044030490082044200c031801d01c103640000140321000440c690180c04c0ca41c00b0140e850300c0b0040218000e588880d40700c165503210b102056002e0700d8410a034103804c80034040ca2040c0301c14030003040701c0424041d00039210003480c0395440c02403500700c1c4100c003c00d1803444503850110f1860b6100d100d42c001ea092040402180b1000b240034254134042206c55010842d41000480082c1840c0b00c2c0034196 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 151172886 1250 151171636 151171639
    0x60103060e031c0c020a021807030b06041d060126060f0a080a08072406081c0813020a050a0611011d1e1207060e0606030d050409020702030c030d0c060b 67
    0x505281001e4445420300b070f000c60400c25015242c1134900c9903a4420880044001d800a2141c1d420742c400d40f00c108041002525610002411701310b4000303840c145601241c040303e0808010302071700e52050b1500f00e10000041d01d1141082600211000145041d44000d668600d50300b500003240e0408801f0004841c41c4e441c0841c3c054915502c2c2003000f103001080c43c00d005500a0001543d03800203140000d80c01301011340f401c000c0c803034032035004038204110b078001426200d40034102d800480f541c481c079001d625884542000081d071381130001094540569010003586102078020000b00ba111000034440c01c07216080750000420b002e0824600b11401d025114103d801c5043c00115140400c800703030703203038132410204510070308041c51041c032103003c20840c3c103100e03542d14a0b400c1c0d1540810b2400708084c10031420b03154403d1080300040342c5645008286008006e0b01c94550500d00351a000318000650421842a640b600035803248802c140c03418810281102604d030398044103a00603140c420125035034030200703d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 151174136 1250 151172886 151172893
    0x10209040605150a051b010c020a03020607080c03060d02010c02060d14060402250305070507120b0f07051c060b040603060518040f0b060418060c021509070603050403051b060103060e 80
    0x16800004126206040075262080c0d45461100480c410074601000e0030706e03107601c0c1a4494034035941c04107072000f00c60b01c280e0a5034225100e01000311000030301034034480109003081010810300d240420b002c14405106040091040115800103981e0343c004006100701151039800315080303488e990b000c03940d00046c21a0118144494031402031107190040d500980c69102000030301c42458003541c260b0303000380c1d13009040382c00c500e40b0f5090211414002c580300701c800d4080407011030400303a05d1701c0c0364a1049003550f13a06810075540150301c0300c440d070980c402150043d0781d0b1100400c200e48614002c00c0038249544001c1007aa00d00424803044055903515004840018024440051881500b10508c55003200a24400743c4075400010010035481e02c4002e00031310041c81040400085420140e0a04500d07000e0b161044000a02ca50910004071621200360300005002e0110a0003a48441e400038080d14003142007000e0001c000c100c43d654469080540e030f1100004200704283c9028a20f002442503015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 151175386 1250 151174136 151174159
    0x30106090801060e010905040c09060308190f08070e0d0c0b0c190b0103150e03030a0b090709030506010302060f090604080705040f0207110405090f0a08030f010e0702030a1b02060c010209040605 85
    0x598201c1113041c05500c1c0038940b40c80c00f1805104118942c0700103421424420400b00d5134a02e0111065845403003000342da8625010b410b06464001d07815001c250f0210346440d001d82d0399031781d012a400d01088d00340c2a40000b15000b8240030882c4950b1450240900034081580c504400242d5450b1041c40715821150f1a80059800c0c0003440d201540360440e507101c1c1038240781e9a41c0c21401c0300075011464644850340b0012081040403515504140d424000c26110200591514401160b00340c2003400083c0841d482a00100010b0401e9001005002110456603041000c400000b56460303105521030718132a8031540c402c0c001c903d064814040c0c94800361030700b1486c19101e07648403260f244c820070f5254070407561200007484165013400045c042c00303034010a407243d80c2d802c0d00d407019254100b0303a150550b882a840002c2a85000044c8903809800c840c0c00a60512403100001c94801c0d0040380a200c0e05400740e4954401600d91901902e004214900056100d62400080c40221b03001c42d4400d5100c0e07442d40d41d8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 151176636 1250 151175386 151175399
    0x8011a03040515190e1e0c150d18050d080a05060d020f030120070510060b070f1a010b040806090a1214040506030405010203010807090c05250f03020303010609080106 73
    0x80e241034842040041c3c00c0341c2e0392510344039407a0201c01003150504a041c01400e40301148007252a0920103c0410301012050100031940d42d03034034000030560b8200400c140000071560180000d4607103e00f04d14008243d114003061106080300d4030138011202a840840311102854001502c1640030020324820003151600600149807201c1140b4064000d034000345014007130703880039000100d0200c80700030303040c02d00c8190143d855211391160350260703154007803100c01c445440000c2c003e074803c40b421140041d0030816162280040c803d01c003070040341d0412840f1040e0340d5100e000d108542c000c0807000202d0392100d00d0000c034107061490040c135075902c3ea0000140f5000050041c1300f00c1d012039806241c0b140e0320301c410844003140e0748034503046a80d00440200802080240c150001c40c1660780c1d403011745005a64901c1650309403078800d8416000300c1d406010319010320010080d5007840d040c4012004400341c070643c0340c0d4800f0070100c14050f030040c2c10000043c080240c100211000900b0a04002c201452502a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 151177886 1250 151176636 151176643
    0x1615050601140901020a0615050f190b0c15090307120e010f03150b030a061401020a150209010909020d06030c15020a060b03010209031603020f01050c0d0c05010e0a0308011a030405 79
    0x159070508110040f884030003c2e4420000d200b080740c3e00410800c0306003a044211000e03120300d4410640b0444034100849402d060041d0f042c64a400c0754120b900f080c60030101e2051042e0481c80b2500c240380314010390b5402000c00307540064001c100d00300c00745a03611010704201200491001d2030f5002e0211400b07089079140da10042c0b4001402c0359140014241c050700902c0301200e2031981c01041005008410f200c80203940c1da004804403804268245a003030849001681c0740c20706010f000c2e01d40100c00005259050b81c5800608840c4014500004130a480703e08490881c0c129181451440381d44080a2003041a89031a01e0040e2018140c01c00743c07000c20b0703640250303100e02d1810b00506d283d884034201402e0740c40940581c0c59142c002010360352000e082410740481d010781c0c2e12090303214201c070540c98a4607501601c2240e1140c0350040c054015080150300c00d1310f680091000484540d0b40c0c0c0d1410540107107050205000b0300744640d64141655241a8101304908107094054615503010014000000c0001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 151179136 1250 151177886 151177907
    0x1e06051c050c01120e010c020303190b06030411010203040902030f3411210c06010909020612041703130204050c090108041b080a060c03150312050d020c01021615050601 74
    0x4d18000d6003210542240601a004078107102c041d56090110820420b50080040c1d442072240d050110a80d0428014079016210407884090300000100041004200240460340d41e244040c01124901030f42ca04004040740c4c8111068a504200f020902c246881d601e40d090703111540364a914000c40c00c1c401a50250550420300c608140800b2030400d582c0080b0601c2110384404010303601503c2081a00c0940e46190304c00c00c0481071a002d840000300d03001200e445241c4100360040d000601b0302035512105003031030034060001d50301100b55400c02502c6003100c5008500c62040c46c0180060406a441808160791000d03040f00303c680320501642500d0703640f10901036801500068180c20041030344240e1050002d45811824140c0603c0000c0d40c00d002c0c442e00110000c041658003004a8040303d03150801d4a1218000284801c0e0603001d4401450306c95006001380112074140140f400020a01c414220307444202c1070b0030402c441011046c01d119821035401071000d401d14062202c0d1801000013810a0801e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 151180386 1250 151179136 151179139
    0x1020c040e07030507030305090a0927080c100e070602150a110f130303170f010303050a0201022a0601050d0f03050f0c0105090f160b120a1e06051c050c 67
    0xc0e8080c1c1e9008610412000d001190082c01740c50780c9a490381801403603030313000340e46090140004080004002d02903208102a00c0c01541d2001d10303000b100b4101c440c04102034402504e524400744243c1e400034a0500010b000412200360000c0c041c07104055042c02c200442e40400203640054150410b07583c24030804581c0140b400400040c507000c0c015602c5040e0041c0d00c080c511281001c941d00c4030b200300f5101d405068a00a80303800c800350301c805000310b00b00031045400d0040c0078810030042000900580160981040a00000d414144080b20501e12480c4540e041019001078000c2070f80c18000c14400c035409054280c5081d0107a0001d5101c0499228988400808101c40003540800c0e4141c0102918048900c08000b8406424080780b41e6640c1e40151a82c10507500466000041100c0800850301c122101c13011320605003a64031035911100c85004156001c060307210b50030104000b440c000a50320070145400006070040c203180c1404130500745ca243d4580303281000104200032a0000503006140e410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 151181636 1250 151180386 151180391
    0x50d0f080c070302010204030804030b011d010302100e01110f06040b06040b0105070f020607020405010b0a03050106020c010f1107051008010801060f050618040902100c020102010b0604060f1124070f020c01020c04 93
    0x84520f002ca00a2003194000307001848049004020400c1d1001c4842c12a0100c55548421480040b441c154101080c80000d5001c00b581601014190044034420b9186070141044403544201301681380c1050000072003c0e20641041c01044100b005506c03166800c68001c1e201001000c3d0048000703841481a81030140c104c1125508d840c1c215503c0b6000c4504580c0d02900600c49565100400205074118980c2000031900304000807400034070000c3c1901c1010300c160348004644541ca00d007078070f0b00c10180080302803c1c0500d00010450b500e94242c180d9080c0350a5075041800d41c50440410708540c0a50440c043d0088840c10402150307481c401928503201c400d2103490901211000010700400c2c000c01d0094003c032010b01c0c203480582d040015044040e0003a0021300409965804000c1244202d009010114015804900c00188520a56049000307440308070340526180d400b1007443e5000c0382041140302c860002c1040415a8003130030810741044075000030010400702c2c00002c1d44a400b0058118011903 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 151182886 1250 151181636 151181647
    0x50306011206050607060204050f100504050616060903052805030114220203390f0705160518041205130b040b0315030a050a0206090109031e050d0f080c 67
    0xe8442d4884001400000c024a03656203441c07a105000c0d400608c81c9610803580b05100c1c002c54101282e07031640a424540c0ca507490706041608015003500150180d450360398500f131160001481502c81d0420040c040e40f500e0340c5030007400d0401e800880e10348024680c080ca40d2890b403c0a950840e0a59044d15030b4280450b0b4200d20f40300c040b9181140b1952156118465138070348445928540d4029070017003201410b62030407000c4030400303010020b500b00c2101c41072108039400504185690006400c510f0040b000183c680112501c072a490329401c1481150707140038003941000b6a00d40a04120340b04107130910305041d240340c2621101000040e07956007400b4050001882e200391490702d11071350064190a466107440341c2d03c50405003e035800442d0003022060b04403803020302e03900c1d000038001130f8150b0010090416460381c1d070130302025403c0702c401c1605001416001000180c51038080c208491070703a803100c0c804181d290400d6864030384007182c40390a2001c80070719102d03140d6100100951110a540413507030b848 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 151184136 1250 151182886 151182917
    0xd0305060409021807020705010203070f0b0c0f03010e0105040f0c0e0d140703050115050102150a1e0203010303020307031701060c03110a06110301032f0103091a090d120c05030601 79
    0x3050760a0000f58080004c611040310240300003c11805041181d08490b40b4546580042e42e403480790801c050300421880703e03000c0000794031058440d030058500120f9401c2802e0f0004184c16a0000e8001d154040003981c01030105082030f10646081d100008020302610540c2200a00948400c00c0101d004055040400c0103218050541550119200d42250317409070340da0900754000d08543c2c91072041c0c1c00340c002c2d0000b0b07150b100280c000c00c400c8000c19061095180c01100302c00500f40c07080c008102183d00341503d541d4900c2480558000c0d80a07030080c69a80c2da0304d25000f42040d490708240544540d8010051007a19841181c03180482c1d85418010004240b100c505840c182d400b00c80109401d090410364481c048000020358100c91146164500100b4112842c10800d50859403120b021071810401034a258071a4021400d150301030107000790790703110a800303581d694801143c2c1c0300910303444840540300b59071744160f6100900503480000c004044c15614000c0482c4006825103040210703c0f0201c041e038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 151185386 1250 151184136 151184141
    0x30903060c0e100e190509070813021807020d09240203090a090605180c0307050d1410180203010305030a0c1a09100c02150109020d090804140f030d020d03050604 71
    0x602c00010b210300b04081a12400500c09101c0319501070281d50251204201c00103001340c81025900010301e01e00b0213941c0d142046a540030700414004d110301c0d0514111025882c0c1500d252a42e800c1080c3c181c215103003545000e450240b86c603042c130b403c00c0132401c020006c0307400920003a50800360002c2b6500454403100000c034030714012440050340c03040e009031000600d40f045034400d4040b94400c0c0c4070301e81c09941d940c840c0340c800c10f41110306007a0341c001040018884c40c81000103000c1c00c0702d501000500040d0103044001a2002190340c00c40e503034200c2d81c00348450b480700e454510841e801404203525560650317070f80a0301c070f01890101006101c6015003c10800410503110380184070020825502881e04c0078001da50394801d40351440801340b81c20203032108544041105540c038140c03500c0c180a01d0346405642402584000071231784076540d6810108000404640003040100b8040801c401c41d00009010003d000c1f8104003c948a54003040445485580205401e00701c60302c0c900b400078075680d64a010802 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 151186636 1250 151185386 151185407
    0x11a010f12050603070e100302040b0607031209020d060c030f1104060c02060a17070e0f0a080604020112020c0102040b19090806040308040203010216050124060c020919020f1b0307030903060c 84
    0x80c411807007c2103000601d81a0403802c6900864007032051108103401c0c05918800c03000e0150010b85403842005411010341c022601051016205819a5915032520320440b24142031290002c1e4490a008141d98440d0248950700016442d90901d440e20300a0003912207020041c00034050000824038a907010700a03681003908040710b00c0100722503e07000300c004084401c4118007038480d07421020b02c1c1d000c07814100c0304070095920000082940d038032542c0065500340310346502d07808400d07020000415a400c003800584010113602c3d18442d21049400300d680d10041d4030384411410802c50400800415000140541d040741c2c2500300705050791038034004030740684207e513412464280311075901c0c01081415808000242044800c10011184190fa800f6809145210b03400014003000f04c0c00c40989420114a40c0020001c101c14000c0c11003506580160b07008a10307601089400412200d1a000c0d90200038400c04000030090b5203002402c2c1c0d00680304400c0c6000c050080d03566500c045640c0760140e00c0340d40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 151187886 1250 151186636 151186649
    0x4030b060312070f051005060d0f210207030201080115020d080c040506031302120c010f03020c10091a0702030a20010e10020c01060b03060607020622030302011a010f1205060307 78
    0x1036560949041130740140c440c00008541503c181681111401d03a0b070b20036035003c0c0d40020140007001015403204245a0340080c41501c28410b0582c0358504104103031010040ba0b5015005407210304d01d18000501500c80590001d5a01440701c0101c4000d03aa010a025000700d000342059a4130b92505c2200007054011074004a40040c00041031000100c1d10301d00414009100f1144110003020011400c0e4a5a500d210b0700d5020031204001c48100502039006052181712000880d200310442403080800c1e28a541da00740c90f505140402d40c0450310290603025408245400114906000240c0081002e10808000c03030600708803c885d140c2c880820341090322826034240454050800b0017031a01d0007948403842d9401250302c2c5c8200050300c0d00d00301003941e01c280e40040401d81480450307000d00c11150b000080000810740c4a00080b06200d00010b05103010318029800040d000007003220b0310009020a0724003130305101e440a03e00403500d9001d100b50801c10100d810200e1140c1f10750000c03a2401c6071941004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 151189136 1250 151187886 151187923
    0x3110a0602030f0606090d080d0e0604060209011e02060606030406090b0f07120b09060d060e060c0a0810030506060d05030c010608100c03090f110307050603040f0309050901050604030b0603 83
    0x290511030540c000d14090182c100080c0307101d4640e081003107600d100311044c00d60400c18103000440840c480c3d0300503101011040c034000c6004030103000d00e0350034202c0880d01101c00a60200b036103140755034403170840700344c0c0038086036815400700080304c011b5654440108081c1c881c1000200007010820150401115144e000c1818440c505210394498844c004c2152035000158a1003580d05001440b401882d00d000005011900103449100512040400901003510711070b44580c4084400c40040003550301c600f50902c80f081c9c4841800300010407e00002d0801c5201c68486803043c80413810202d140f80c1c01140c00c6070384515900451918500358007405c0c010101951802100250540d004503a0603c0100880000c00425101210940441d1640400501810030f04010380c00001c48075214407451440090407078181540e94000139006600403282111111100c00707034102003580000884028100840700004d9a40c10500811000d008601c4042c0030301c804032021070f0007600c042c080d61000703a202084c070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 151190386 1250 151189136 151189153
    0x70e120604020108070915180314030418060317030411040510060305181e07180e0c04110910170a0504050d09030c030803061309210815010c0311 64
    0x50549a9104407400c0e808500303c1800103881e0781c0700340030020030303039042c42070080c000c800c44401215540d401c5100c0503800030700101d021000c1a941400e420421844c04000c0d41c0d11800c001e00c20403000e00075003c292000342400c00500004000c003455848811214890a03102d84e01d41c108000c41c1c021040c6c600b900039103842c09014480f1008050202518a03503141400305855045500741d5815100b031080c10781b40c101c000107040d80368034503451140d02d06141080301c0c0c1030f58681500b00d0003600103403103035a400e5640349070640c0304100611558810600071a030410900f03851000c070200c58403461589a11403040911013a2569024801c0d005691141440707080c4689000c1014030000e040036507069805205211190750b04504c5035820348281c82e4400607500c02c0a02e50b41d10032100381c1003e04a1540507900250321020b842c09441000580340c06003c044104144880b050010006169210000c1100d01e2041000b00ca09541c864150700710203103014005030038582006ca4000e110300c0c41c201003d000c2d1250 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 151191636 1250 151190386 151190419
    0xf010e090c0447040306050106030c0f022a06040e0406050402030c1203190314130312060f1e0b0a02060106020c0901050d1401110c0f01061d01030b070e 67
    0x2800541d0841c4030705020300c0c0782c215440800748454000c0d14818440c03007200d9841d40d0f40040d820f030560040c8142110f043c43e40344d5039074006450b8260040d00000b6500c10740145120f40c480d444500c000014005070100c00004003c0c0c401441130a03209045c4071403000d0100740300e603c48a084030b00030702d03054007400003609007440d01d98003900c0e05840c1a403207032040c409501518504803035001040862a8011f619100605144104d15212030a080040c550b035159603081d10060716004030b1251000400c9000c0380840ea24010b004115189502d0201514280007404400301d01408503040c1c4030030680d5402c8104010100b900b00080ca50401c6800140114010740311940000350541070702c5a98082d075100008040c10b1015900c800d125140d80801041109000f144032401e0520304410454004102d90000e00107401c4e681c1e00204660200d07031b1042c11090710050080c812200500009509001204051f00140301003c00600024210400f400c020443c014007031880400340b028094100c004500c4000c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 151192886 1250 151191636 151191661
    0x6150f0703080105210a0f021804120314060f13020d060b07060c02120909070e10020706080901020306180a1e060e092814120309160b090f010e09 64
    0x2042c0c50081100d100b020341d0413501751315800b10030301c8a10004d0a003000c503074072403004150707001c40143c0c0c01199034400404200c1e0001d940600c11409008000000d6020307040040466011040805800c1904000d0002e540d8809403006018481210809030429079107007150000d204104981404514100380003601401c140060b200d080e0058008006058148c901640ca64064407020483c840d000c200d600031500d0a0210190003801c5443c040c03540c4200c3e0707000f144411400c0c0c43c1500c00369020990400c613480e84440d4096010310300d85c3c0250f0950a0500115107891401c0c4645180e0065260000f960040c165015000c4040c45c405c0d08201e20002d0f41d460f200400c00350150018040207140018515040020201300088580e00501201101114050740361500c031181102c0d401c0c8031055500055404010440490100c94404e0b41e490a00c5691585000760444030802c07210a20030082010780303034960a880392600c0c107a80704024052003000488001c40a4201c0c20340c03004015003130043d072101c00c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 151194136 1250 151192886 151192889
    0xd0614090f1204030803010611030d0608030d06080a0503070303021c0501030807030807050a0e1306050607140616050d1508030c0109021e030307110303251b08030306150f07030801 79
    0x1042980d400404a019800b0240b0a40c0006060a2001c200400c8410300c103907541e601e0100e002e410350303081041c035000f0101654001c3d406150b9503440410030b20a0900b50303110f104001e01000008010030f1003269079040e206e0159860242c181540450101c000501d85070350081d101490382000c01007980c6910703002d02150000401600004e139001e001441c01030103581103d003076400c152140c40d82410704100300840e94250700f000e1144c4503140e903400034450700c455000d0540240706210003103600030000c002a160000c020000d0314061842c11403000019001011540c205400010104041c650103c1c030211a03103da5020303661522000820004c0c9460641c01f04060340c1c0300301c81c4111586210440702d015410722082d001e505404c00c0000000040c0203c070040903070f409c091300340c0b42010b00e04020340d60402e080d50404030650050a029008101e002010003407103102d402500c0042c0c60420901c540e403800010641e40c010150b5002e002606c0324a0400d60741c07100b414403c1e260703030703090a480c0050901f0300a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 151195386 1250 151194136 151194163
    0x2100c0509090705030a0c03110304020415120605010e060607080a0c0507030b07030903080903041a09190f060207081204140d0506011401020c0307030f0b04031205040b0103021903020a050d061409 86
    0xd00f02403401f514032900504400180d24251070f82982c40d01c2e001c0000810307aa01000400041c255800a400032101254560060084030001959854648610304800c00200f03420320501042110000260000d0140c2ea40d407251441c1030b04d0710030640d1603e64a400840d40026000700d080c0c10030024802e038190090039000348290380b80011500c4500749555030f80540e0103440020b414800d01a031904a114004d054000001031a1211104002c903140c1c0c012012508a0b06207809201d905000903501086603070001c1154400030b000640f00440450780d14011801455002040c281803101540e0740c0c403440154454201050b6034565a4901c01c1354000b8094204a501501506242184074030f4003040c0700003101c0e00402c45e1141402c5681d00c181d40765034000d00c11000c0c024520346100e80c07035590740b00305441113200e600c001010b541140100240761204038801e15011400b030000740010b880e44618402101d81c161403400c2c9100003490034078098280c0784001600d0610f00d07010001c01c50000030b2205424402c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 151196636 1250 151195386 151195391
    0x902041a030c0405070f0c03031503030e01080907050d12021f05071403040b15010519030903091202031c021504050601060e06041406090f120106030213020a02100c0509090705030a 79
    0xc0b450b06001c25140220b0b811000b0590350b4805100785809186400749803842441e0015a480504074000980405600181c2c0003c01340040b8540a5800003502e680102d8800d0080684500c1c0c0000550029000e4138010308054490b0300010540c2d0003000001d03910008180c484642a82266500005080446100002412000080001c0c48030f510480e40a1a00300300340e40c0ca1507407100410441d504081440340e0421804118000a4803406000880815030581e404a0381c145542802000365a16030440e062070200c064070407005a07000100c0c54018403a00107200100740c4121000e070300b06410608440b0051407144104001c210340884d205041e80c1c03107511100c1291a805051000c580550b0250710100b42c645003000c12a881c12001800e58404000c000d10b0340181c2c4140403440c240a2021103540c01d03916800b0920840c034240144918008007100110b080c443c00e50030095403855165255420300d941c96600d045800d1040084030701c4180041c6c40c140c0b19081c1503000078540e91084501000c200d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 151197886 1250 151196636 151196653
    0x3180103022a06060a0e0609131209080705100f0c0302011d010f050a090510050c1c0515010201020a0c03031802090403020d030b03030a08060f0d17070213060f0b0309010902041a03 79
    0x160440c400c50a42e40040707462000347e5940400d0052414001d080c00006030304086145002505034445151109420750380e6140c3d10380341c000b155261103030076048280f1407002003443d000000d0340800400311a003a01e192104501c5203500301607004080501c00703031039600c901c1c00c210b0314403203030540210704001c0c0000010483c55803801e030700600b07d0f2060b0000400d01d0300000da0403400300710117800443c0c03c0090203010740d00d85a4014140b00300b01c80803001944c18940c07070b00100003002c46141c014412580c400e000940c540840044002c0c204101c01d48010207040e55103001480d1014035034040150641e01504e414824149814040e40e600440514040001e0900b00c161916042c04000d42d411500c803a129089c444e01d92404001c11581c00c0032031103820000d8030301d0b0304002c00d1410841441c141c2407002c025940742914014040103020416020070344509005042001c2d20345e0540d0441100d00c10340302c140e00c0703886101080d0f004d090f10740c4000c2c0d0701034280703107016090396044012403107100022401c0322000c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 151199136 1250 151197886 151197889
    0x807090209120c01090b18131407020a080318071502013213110409200126040201020f151503011401050111010e120c0d05030903180103022a0606 64
    0xa04008903a0742c000780c1c4c11841084001d840c030000d0000d40b0544140c55402c954450017040c6890208c055000c01ca544614412844402203544181c01003202d1001d4060903400d6110031f02c5503c80a0f00030400c041c11601c1c00010000306100c2003010b0841407035520104160303510300038081c0075540811800d200008105c4d100c0e012802c0382c4040c82d0002c0b82405150b0342c0c5c480041840044007000251000040c04030801c4a41e40c80d8880c400e0001d00c12088890403034005601c0501107a5010342c8241409280341342c40f8036070102c102118040741107400ba40d4803140e6a03840100d013000c0d40d076500294603216030052414950340b00f582c035038421404041c0c50820300040608240c02c0e05c01c05031020f0044100361005006551003030b0b41007101d062600001040524616100b03520b410401d0304040404140070400301e01080301480400d40d2139400d46440d5096041c100407254492103404604440c04484114410940e40643c05031a1040c0307d101440303a030081c1c116039000e103040001022410900a280004159 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 151200386 1250 151199136 151199143
    0x30c080712050c0d020d081b0601061b120207050a0e1906060518010e0a08031206060306030712060f051f0803030c0906030411120d031b050d050a06080709020912 71
    0x30590880c0c01403a80c83d0030107041c0b203090464104185c2e041030314080c00c1d5012410700c1c001070030038102420308418601c0b02885c419003020010f812410800100750360441221201c619000401c039040805042c8080d0125001e07445d01405500841c0c20a182d0000000c80c90f0441d44400d1007000390440070200d00040400308400c465182c042d00c804240b09001c845209800e40381c005a5080c01070404041081d44800040d0b1000300c15840141c0780c1c0d000061b02c038991440b103032030350f82c0012090342d1407400c5080400020380c5801180c003607080545001d04542041c002c440c0c00c200018156000c0402040c24458290f1301440b140015a03011080b82c0701000a4070300b8004100d034031a07080300850030f080c0b982000c100700651344041d0054a200a5124a01010341d0312103100081c03411214009054050a040c00501071b02d540c803400320307041c0707a5401000c81141c0c0c2010490b00e103e01c0d90900012640d59030419900184100d420144c00e900c12404040303500c42050307005200c0c0e5142254200140314907031020b0b030303036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 151201636 1250 151200386 151200419
    0x5040f060c05030c070b0612010f020918010f0e09030f04030606051f0e010c0204021c0501030b0108031806070206390303152b11040b011706010e011404030c0807 71
    0x12079180400c510004180c2d07a04200740c07c1407000f418010305071901e5640e5425070b02480c040c0c0450030380c000342d031403441d00c0e103403910583c031208040854500e50715040d14039110055600c20030301861080400218048028802c80c0c034007101800c10242c031070f5101e0401100520766406240e0242d12031102c0300c0035801c1e00c14400e41f112405da590b00d211a003c9a00110f8801c040351004a8200d0340903c20f410004502d46280703031100b54007010003d040d41c5141010490203406074450390054004101c5031003000c1c2410002503202d80107454103581d681ca0361010030700902c103e0320440840c0c017000160f0300640307210f0220320740b140044002c08003094604c1c101c0030b52648015203013413805452503102c24905042455466081361604444a552843c107410340d0072a01940c0a0102c3c1c40039080703100b003262846c041c0700b09820b070482880d0450746603d4600980002e12030103403205d41802000c40c50000d00c3da205801d010031046225202c907032220ba03245080039410085002e10300003400b0341c0b2030101c0c003a02c02c00304840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 151202886 1250 151201636 151201651
    0x10803121605090603090d1404060905060f0909240418110114030a090317010b161707061b0212070f0302030f0a020a1202010513021507020405040f060c0503 69
    0x46a90311621000d50420342006080c000b809401e1001100b80d40e1210041e5200342ca5200282204081c403140c000e00040c4413620602e100c1c1d5040c0800d01c1070301c1e404001a0103443c02a1484c0d0394640854030310054600410610a610810314810000040c10444121055000030103150070b42c0340803001000180c0342d000001c84440b0102402d00004168101c20501403100103042a140e070071a80c2071084050b0748110b0b9403c18036611b075007040041541c03261011280c4848105a0440380d4100b1181300c030300d407190410480d003c0c3c0c2c0c8105480c0c280841118003010142a034012a0744c0d42c0c1d424a0942c001d400714102c40504980408070b00d00609001103850841091104207003490000c80781e0342da29020450302030aa086120501000d00ca00300d41c0c00040c06100754680013088504081d191003203540348406614070459060009000101c841443c050b614241d04841d21202d804c1e0055214019005080000c2c0d03000381403005000074070450384501101c0e280503040c03c0c028081030880c02d40d107a11080d034196 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 151204136 1250 151202886 151202917
    0xa0605030d03020d091e050607090e070e01090b0a030902130902090412030b030a2316050f0d021003050907080606010203030402040506040b0a0905090c0103091a101205060f010803 79
    0x301c0e003282c4242d0040c00038200b00c07070000075004100d440e1038203010320014441d103408190030821020f10504001d44d590125440c50841c031100d08120f0210300c654800b6000000703010303800380c5081d020382c002c081103409480f203506e01584a14070b01c20700030090032250700d00b43e00035003006007400d500b1a20b81c0141414030790003426070f01c05c2d03403210340e40c5042110440003100d0400d9034848900d020340d074047c411210094090001071803006201c1d5280c846680000d003078030484e07501003145644401da0790366581d4110340701100c843c483c2499103000f0404000038010025403020b104180c116040e42c2540c400342c002c0300c0c10412240c3e1a91140e00c00c1d9605c9505440c85400741e07005000080c01840d041d042103074081c80281000c2038800d000c0f40807a18068282d0000e6030011b4480301008241002040400c0c84e590091038280320300c009a0301c90100b100620300c1e03400d40122580d400150442c01811030240200b03105031462003003480714205191224030a483e550710030140c1100001e00000f0000940f038510506900303c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 151205386 1250 151204136 151204153
    0xf090906011103070c0501030e0307030f0f02030c030d02040f0501260a090609030f03150f0902070507080a0501090506060d080d0b01110d0e030f060915190914060a060503 75
    0x2004041040104031a04100b06400b03040352400050014180c5a48151500c101c9142040c0c00901981c07440c08200c0724039070080c0030351004254411948000d1207194101900107404049080f800e52068000f001e0144c4800070b003d0b2210942a030040044902c0002c0660005840300011108200407901c140c0c1100f0089004441c1080d40070b074010b410600c0041c00181c40902039032000152041001c007034000ca072a804621007a16094024042c10b988580e404c000820b040c50320440401c80c081c040d2aa40b80d0f808107003542003000030030000c00544045c5007181c0342e40c155840c105001e0100941e00300c999010b02e0002c12014101002c0d004602d030b510281c401e0500c24024207010082c40c1182c0310794104000d45400c0300030b01a0600081403d42656606d5540f100c2d449000c1c9841c054000b2030158240e13212208020800002007174a0a4100c4403d010524507280d40807060b0085000054003480145055115010441ea07020b07050840c1034040241d034150741e1000d20f0131044402c00e104164250300030203071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 151206636 1250 151205386 151205389
    0x102040602070b0c0c1509010305220605190e060406060902090105030103030f02070b03070c061401030803060d060605061207030b01020a120e01020a06020d1409011107120c022809020f09 82
    0x9441c03401c201508680b440844000020480e0031000741c02c40c18035100186031f80040d40d01d13004040d40300c9125120b900d040040ba003000307a6900100c00c2c0284c406941c400c045298114850102010720b9502d4000784400e8000d8110203481c3d01058034100c888d1441d0150002c3ca1040324000c1d02d46000d01610b0310307410340e0701e546c6007038030350600c039039400740442c098420040382008040380070710b0003a21180d0b21074406084a00e054000c030f403410b20001c0a20540c503070041001900000841c1ea00400503644540041c01c0d918043c0081e11154004076800580130502543d489601030005205180da5a03040c005150140010780c0c071b60580010141407080a840300000035405100f400d44400010700c11642c1000450701d40c00226009094a001201d840c1c4003150641c0c3c0302c4050711500302040c0002044608411464240d40c1e200e1b5400081c070307050010300c841c0e4241e80607200340f640c415000b40452900c3d4075404c1414102401c80d8001540d0088403100114045019109551120128600052070804001e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 151207886 1250 151206636 151206659
    0x111507050c0313170c0f030d03150b07030c0b011203020c0103021e030c0d0c051303020d020406091e150506040e100f09020702010305010b16020d020f0d0b090f010204060207 76
    0x742071940c1d510041045191604841441c1002000c600303034070503841010448650304003502540342a11a9006250000e04c03944c011070340f43c603420f00e0b600340040c0d1403026015107074402003954080009103802140070b030285500481c510200c0c510501341d00c60070382e89403a42070761020110b178006001640840010340c01540242e00426101c9250719071850942039085c00e10286600440703013911000d402264125400c021401140910105400d10078241040303000390751282d01c1c2e10b12000e032223a10441c508a06640b074552019003d49540203092000800c01e00350744401e0200c60b4100c0714032602c0c22030800c03042100e541450081d01c1d00186181c4c036140c585043c0e40301d202009400640020840070700001d41f41d0110260400400c1032031700140c0c541c4668000501160380c142d01200340901c4c00c102c0d0801c5051b0070010858081d40c125480c105940321800410f4074895600f03210b07a08403020a400328140159400705030f1086404100319100400b103020a01d090b409244684d20141e448082c041c0040a90300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 151209136 1250 151207886 151207897
    0x10b03040f0309050a06020708060f0603061603090804030807020f06030112080d060510081b0a0903030c03140408100605100c0f0f0206070b01060f030903080c0f16110111150705 78
    0xa1401541c5244c0711000109401c40700e5000c500568848001041400010302000380c0c000c2e00502c01c503140e8a0074401294803020002d0407080b00d142484101951a03011b0390100621740e03008602c90b038555459141c412460340c00b001059200311b840c180142900d14002c01268103864031440e28203e071041554071601031340c104d803000e4680030383c4500300840c00f62641c01140e1810321503642c4151250608850300d10842d050615a01c1a80800300000c0118603002243c0380201c0b58035151480c00814030307080c201d68011805103550403c41001500199a80d8006003075000a440100300700245a640d0701009940c0b001031080d01d0204603241042d0001c5100740007400600d600490103c02a40041d50016900b5402000700311850481c0324010301210707600c0780111030740759a90b003020812070100380c8000d400d01000402810044a0001e02030401c0c1c1c10344400e40d000841e0590009003143c00615208001d402d510030b60500081003500c206103401000200302000340c218842210403a190488202c1d82540072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 151210386 1250 151209136 151209143
    0x50103020a1a09041a12010903050a05071e03020f0708010209180c0403050105130606050306061e01140d02030a11030c030402010806010e030f0c12010218130b0a062303010b03040f 79
    0x3c0c414100c55886900910400c06070805040c0b003080050300030480c0c40000c03904420400c3c0c3c50005003000194010080b1307880020301d4100103444001340d180c40350741000241c140c512280303039003d0b07480100358000800c003003048429000c0d40c03400754407014003500301d0140500499000b01c41c01100903ea81c03418501c0e94000d80c2850b40c042c9415100d456140c20350341706a40d50a26000604201f0080c40130701d110303660107001d0440c045c1859040c00c42c00108203011000415143c040043d450030910382c0501001c010400040c0411900c1e0124040e484000390421540100c0a6041c0170880c01c0c3c1401b90022680b08030b16184100c2e0542d00ca6400449200348014401818440406440c00c0c456608020001d0050001c41c000e02c2c12414000a01c030303c10703c50700981c0e045680140145204100c002540600301d0b1010349880f0311906410790910042c02081c4140c40d0051a8150082140e42d80484140540c0c0c40e1541010449015019070070110701c401d200c1d15000d07203824004038001480a40020391820701 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 151211636 1250 151210386 151210439
    0x1e0909030e0d11040c031b1215080105040c0b09011202222402011a040b0d0c06110105060d02060301210501060807050306090106030507060503100801020a0f030f050103020a 76
    0x48107000b260700401000001d6541e8520b9414542d80d5152034010262002c44600c3e00b84031420200c080010103080240d0f41206000c64101c03000c01d03100b000d910a24400c00756803100b1100b41c0d41c401809000780001d68044d90b20180307031100890080c0c9110220b0741591010303590340c0c0c06070b10444901402504400c0a00071041c1010019200141082c100c10001e01071500090501102c1c3c3d080311040000900b0812095904001d00c400040300342000d440401d4000f61000b161421030140050440102d0420003407282c80541d101241080d4848178170240b01c00c07000d008210684411f0100030000740084e200039440101000180141c04002c05c1d91040301500110100305012240c1d219420344c0c040d60407a007159400f01508001c0e910f010085940c002c40c0c000000c20102d030039610f40b039484203114003c44051100c0080801c0403080d0140450303008000000013103403212580c880041001d01800c51200000c0c0c241a80c0451100852003803504981d8001d0440449a1900d024861400101042c0080114 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 151212886 1250 151211636 151211657
    0x60703020f0a08090111060709090207020102120307020715080c18011206030308090c04060308070809120d170f1e0901020d050112020909031201060309020604051206010303091e090903 81
    0x2410000c182c0214419984240c6814080300010541d081c400f04944556000d9000d2103001a040744840082d60043d0f2005691500316000503450513419500450b072403c00003041216451f0701159040944040d9000604040c424007001c54090000380c407921101c0c0c1c401c00911001107208249040e072460706041564400c0301c085075100469100354010b4012a02500c00c20440c42c1d41444080255a000c4504008050641d2103c5140c1d000f000c00c010040d01d0001840c08480d07945000d40406c42c50700740101d0741030b1b0301d070303040001c0c615500d01070014104ea005002289030708010b10303003c82c4986184001d0300c01030800f21000c0c0840c0500645240000e5600f00a0100360b48401d00401e0f001e40707a003039929200c2da0030500c103000404c130000340f03844801e800034001da50b0300d00c0001001a045483c02e282c040740c40c0c1c41a000041c4c180c0f04a51000c0d9221107003111001c0898400325007641201d019407110b06070f241e940c88815140703a840508242c2c100c02e10920902c124042c40c0e02001205010b46407104050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 151214136 1250 151212886 151212913
    0x309080a060e0f0304120209040602040b03090102040914070e01140904090309050a09060b071205040b0721300e030307020a052a09130501020f0c07170a0206070302 72
    0x1040039026900e05842e42009403101e502000958201590440210b140a1505010400713071414846e0003441000540b003c501808610b0701130710090400d10200a9490a140c0385e154000d50152107284100e90a1031405040c581d800011144101444d44489071003804c4280111400c9400001400e41c01c4001d0144a200341c54900c40d0000080c401d442c4c0c0004182088204041045d01e54406036409042c420140205101b0b030055035086a070103644040d190780112001d0702c00b80074503009000640c0c80880c4600510003150100ca110040003000c503072984107140750845100001c0c5c034003a600303902160300ca8a0165400507900b2800b41035040001400d03001003800506580c400e442c0c00e8010ba1000717200c0d00071300030140603403003000070110429420100c04411180e48400e00d50310f420312130750310700300010800000c0300c807114650766000c00219501d07150702c1d04c50903540e000402845d0503449650004604024070841c804121003524004021035841039081207800c0c3e202c200c044085001e21030302181d89 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 151215386 1250 151214136 151214143
    0xb0a09090309180c080f01063015180608120c10060608090d09300b04030518040e0613140d020a0b1f0501112a0405070206070206060d030908 62
    0x814105200070502c843d40c40c0c4024080c40015101501b009007180040040c2500701c02c024940304103802c0d0315506800d201c000c02402801c9803031040003042c00c02d4a1038400a4550380100c003520088901940103000c410419000c613840d5010700c03130150740010807102114090b00003601d034600c6417408403009842810056820b40e40365030b000c000440c25400034450885c0050052044840013880d00d0751016141c2010b003510384d41808544150310030322450341154041c40e510f681c411309410a40140260030b1516000f00140d10413080c508101c0c0a84420680615041c0280d2030050802401020076032165950002070701e0142500700c0710080d4284014121403024003198010b4812500a4550030069081041210388020442c60b403150700c40481c500324410210940003a10300a19001e0012241138486c82d1401a4030b5010083c034024248030a101c00d080e0700417031052080156020722094039540c07001c3e43e442506031403c0c409030700000001190b40c140843c141300030600034640220229540c0000504 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 151216636 1250 151215386 151215419
    0x21e011d0a0606060c0c05010e120105040c0f05030f1b040204080f06010501020111030723130e0406060504020a091e0509070203090316050a050409080904050c04060e040b0a09090309 80
    0xc29802003120101401100e125100003800181070080826105540d40c0b403801040d4018941805a0405841043d0301d130800c02020f0080090002c002e5414241401900c0c602c442c4030300880720706143e0001c00c3d54100410340e5800040010001c209080c84281040c4081c01800c01030754105031300303100024858004024004a82c0c0245000c0c00c81d41d4102000242503420300024194040400c005204800e0392010101051607050300004410f614590030b403190342e01c0f843d460b01024900e500408250b4560450800f030089101c1d401c10031040b80c1c0e5406200c01d80c0508821003000c200104000c216106068015140c080d802c00080e4202c1a180c600107426544191507080050b070000c03a03281003a00341000418102c8219592512070f0900d040300180841c0c6450145501658880d001c2400b04901030094845004006105200e9403501503802e0109805c541b140030000351669001c00c4103420b01c0d10232440f40309800303048900c209d81061880070141403816421010020050400104c9800c02a0f000310f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 151217886 1250 151216636 151216691
    0x9080406050408070603060302221418060f1e07180605030a0b090115030c0203040305070e040b1e040f1109010b0d0b150d09170301081e030a021e01 65
    0x3070b200d5080500040c40c204507900090f080c189041d1007072000d60b545009204803a04442000e0a4940c00707400d0803009004a44a20200000b00030103018a0000c0300c2055208032a0440455006698810303200094210a80d41981300d010304416018174400750a9840303030300c08070381d007003200c0c80800c07054840b60b806e4070302d50044000680101c184400c00506000342c60f04000c1c01c0780c260060794100040ca801001c101d00100d0f0a1680d10740000d8801c50007402510000d40c2c0100540e1001035840300512041c1c1c40882d400c5501c0040c0c0000100c42201c01c0c1002400001c041c83d542d130465030b4a50714020000e000e840180c031a03021000c0740c20742587d6240e035028040c280920040c0c0d1a6581e25410702c0c180c41d409c92080d4829400300013100780340c050300300a0310040c004075580490003240600b0010000150213400240c0c1d4900040042040000000d85034441c0506541010b81d00c1c4031105142e40368080d101a003801a0410f150540c58000d03031a4103202107040400000803104070b00b101c01d084c00c0e4138400011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 151219136 1250 151217886 151217897
    0x4120c05250504060902120a0c0c0204060801090209070206010e0126010c020c1c020607060203130c1d060a0303020a12050f16020a0905040f06020a050912030310060e060a0e030109080406 82
    0x40c8054102401510000c001c800015070400307100181404407201f0050110221a80e15030050f410240b06041060710281c016000b0491a500c80d11807501802e490304048c0e0003103030304a000c52142032001800d40c6c100c0e1801d401400e0541d00340304141404443c40c00f000f040f084500851703846211820b2060014240c0107400400c02403510b102030115403000c0200c415503200b0b40b0300f0f5250140c0c0f512800c59070340036803100300181d4940e991042da0000015034000585100a05400452054403e00010010085046e20032005950f00001c00c01c0c861402d0100a0058102d1501c500008581031040480c003030704e0381041e60600e0220900495960030075145590710040c80307801e0700d05505000308004081c2000c1041846549003548a9091045894800514095000558008452240c400c0c1c9240724002010360f01003a8889160702d99030340040d2640070f001c1603511000a591070251142500c07140700034000a00b4960140400e9811303010002d14550107548400c1c0110006080400a1000c1c140f0b6443c0c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 151220386 1250 151219136 151219139
    0x2100204120b0a02040602032b02070515060303091c0606080111090415080a0f140d080103060e010509061603110a0801150201090302100b0f0405190e0604120c0525 72
    0x10342c1506030003609410406204000074082c80e41d0100c01c07501c1c6400100030310040100c044041414400f400d03910980f031184040b40034400c1000c041420900841c0c0c00d2140035290702e03044101a00d034842d815982e50300595a1205a120402641c2440002809040000b071b9003a41c842980e42134401d1481d40d450781910004100b901890148a00038400144000c1c2e00c400300e0400312040d45d01c005800c1c010f030600d001500d58508101c1e941c800c0c52025980f6805072150f007074030b04401400b000028001110b5440c1021a6044031a04c140300da00d209012450042030561034101038802c9070300107020b054003003580315540030050141000c01005100a07954594000703600d4020701141140800d02658216410086c103c00403a80c006000e490b1a00325500004000c82d030b141c00202e084201d03004040d0071508210030803500074120003152008d100c0c0c070070701440418007400200e5200d507000c640007089034030b031180ca811392284a007421204041c0300c3c03000c0b5108611407014800c0d502940800e07044004910010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 151221636 1250 151220386 151220393
    0x3030e1006031205030402150d0b040e030307020706180b18030d231b06070c0314040506030a020304030e0306180d0e011d0102010b0409050a0b01060c02060406050a0210020412 77
    0x60a880c11031044100500d50031607882d40c00c100e800501410401901102040555407240b82d8900c1c492248040c1d030790b40f00b9260980c800540a1000c4040c0308a142c03d0031840e00e054044110380c82207105070301078540b00d4200442542d000800980c042000010321901050030f81c1c98030700a02c080001045e20300c112900810030140b8110760700c800e020400c0301254411110356004d0750742445691002407506c1e110318844224200001038810400000d2040105010005810a9002150718083c1d0340d0070b0600070001810380250301c80c1d48180f540240c800c00c0000c002c50145e5014607009486480c182c58941440e50010786031020645a1552480603655220050241040440148882400c1601c40b80d010000042c104121115140360084940512801c07603a00c00c3d4005403413004d000b482049160760509086994607860082105d40d80320010006c01d03c0c900441400440c0d6600174600c910381818980101c3d5190480382051065215005c0241e021001070700140c8040c14401d0078141d0441c04070305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 151222886 1250 151221636 151221643
    0x509040908090405100303080c0702030309090f0402010210051524070c08060105010314071b1203020a0e1203090607060204051503040209060f03060a0b150f03060a14010203030a2703030e 82
    0x610107551503401105c100006600300700201da101881d0708125448800e1030001c20306600c2506a85039001c0b11076010480049141780180e40603034001c2e801c0b0307403000c8003034515030040314801d607000388000c0d1501d000c2c014246410218400c5e180d41c210031880e40ca0703050b40a00c05071a00525402c81321200ca8800900c1718030700c10085a40140070919050003802c1903280382c440340b4030b00a0002c904000c522a080038002d90010115041c1580c0106002c0c252400030000500a40040384c0e41000201c40c080c0ba00501d00d4445444480000700307001651401d01960100001c40d8451035040711159000e0100141d6980c400c20b4100071070b0885c0000350750b2881c041c41000210706c0c00515047c801d101ca10054000da40740021090f5003c440040002070f542c1d132100000304001c00003060415000070025040d001e03420f11102079030245800b580e41c0e1401c151140c0415210460a04403a1300583c403c0c0005090b81c000c0307410107110818082e42061400c08824501850840e41c14815000301c2d45a401d107044441041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 151224136 1250 151222886 151222891
    0x150201060524070203060a0213050102071805040510050406090201090b13090b0a09090f06060e2503020c0d02010501080601170709020d0b03030d090b01050d1109070509040908090405 80
    0x144000c20400d420580060b080c40b2240300072210745216550001c1030128003104072050360b5002400c40703110b442e009442001960000481c0d8201a410071400501540005101c005039450888102d021a030040c04040042c54018000e076040e02c60b054120390b03501d01521a0b83d0080d07016040100700782940d03000250440000e98400d4820101c100300c201714440940c54460207894400d00045412407101002560030030b40c40e0032401109140c40209010000350030b0902e10700601c503040920100da580d00982c200702004480000030640c07016031400e6280e41c00540f04254004a08005060401101499190603600407020000d40c4d5664014445070340c04110243c010040808098120304100c40174a03100c0e441407240440c0702c3d030003003544001c1c503800d5003040f048103801030708032a10745280c3c1e05520094a44400c06660650f00707040085071a0421845240d40700340c11016030701c200d042d8607082c002c1845006110404101c4184100e10403075607513000e003050040c0103d104580f1800030754204812510b02 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 151225386 1250 151224136 151224179
    0x1e030a090f211d0f0a0f1410030903050a110a0b0108030307140a09030f0f0f12030c1b24050903040825150302070507030f12020105061c051e030301 65
    0x28a030380400c1220315030001c0c5104403d403400140001904c000c80c941e0030756500403041c042407020703011a081d0b1000400402c108012625503503584003001e016402c413161088090300107542005110302640c054480b101e01800b414003107580205031525050007030f40003a004200c10b80c01c00824481d0584d0f00c200d240c5c6602d00c04124080c03078003180c40000b41082460344802489401a4000201401b07510321012000c0c1e60040d9140c42c640c1c1840c680070040c04100c6941a000c00d1802401c181c89034441e80030b041080d8582d010864a400f02500e410702030080c01c0d414140503541380a1400202c07411401128040c4030404000d60300c0341d081c800d110341891402d02155902030801b480d16441c400303c10025408883e1320721a0f40e010b2003e0644100c0191082e2100a032403442003030340000400c00440c0d5505100c5000d030100541429911100303c2c01e0b503505641955102000a00ea41c510120903043c80c8003591241d030031194901f007000c10138140710000e80390007000d5030004401002020341c02440c3c141903110b03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 151226636 1250 151225386 151225397
    0x50103030507031e0905040e160b0406180531151403060f040305130305070308030103171c05070c0519020f01090303021f0605060c0c1201021e030a090f21 68
    0x8200c0c000402d45c2c01544507181c401c41d1281c286c1c250000d4144655003000542911031404141c5501003290342c4c4c1d216104410000c1e00542030140c03400d26004240054a40081034401185084021070105424005e0124045050310b07401040894181c40380c01050043c060340070030201e00e002410305d0740d0000e9040140c0681c01550801c1a604500034000740c0c842c2c0e00d410700c9600c6101c0c44461240042d00da0300000c10901c1003800110500080001071070417284259800e40301c4600a940d0350006000b0034805051207116404007110028480d0043c503403102ca246068100c000003611103601c5c080c4400e00c4413140307040c02924a4294100f40ca01c03003074901c034282482c1c20900d146560003503491000780c42c18100c201d00c10008200200d681d4000c80010705000f00400c3e103d6500c220595110100d007c200c501c2001361074455071803410b040c000c0c0c400c10300a040c0110a903040400000d5000d51004000c600720030b542e0100003001030080315044031070501800151042050b0390800400d000341460a02c8240700c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 151227886 1250 151226636 151226687
    0x803040b030a02071a04050102131208070201141c05010305010509060601080708070504090e03120117070b0304080c01060305030d050c1219090b0901090507120305030408180405010303050703 84
    0x1000c090490741c1128800340016581d15660508005501c4a8030360b100604207003500340400d1000540207402e54141c03000341c0100e101d1b07a03000c6c080b94140a5840040c480c80040c8440c001644c0640840b802804021401c01d2405005c91400c85409000b0004011001d948100500c1070089c2413040e568000d203d0700c02801d6900740300001030503183c0d0081501d8100590740e4000341c0f00c10300c500250b400410009905106c04503481c40d6841e22038101e00c11030f81c0000004c0000094031040e11040d41d940403c0c0f100500142c505280119940d0382c002481941c0c00841002140b507102c100344a240011405200035549490307a410b600003d850300906841a02c1ca414004807042c188482d050540103c1001910030800348140000c001401d4050405130a203c4200b0800c0320200c810b41141d81c5103441402550600b5442d8003c102d001c44007084081c00181080c0000b40024003107000510007100030031131032800d80170301d13070001820b84009070000c07000118003182180415402941c03031401182d410714a000b551 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 151229136 1250 151227886 151227899
    0x91033050927030310080c0102070b0301060f030e070905010825060806040f05070216060809060601081003050a03020c1503070c060213050d050d02120406090b0711030a0b01050901080304 82
    0x55801522108500d500c2c84901c2c030408580e440000d40c5400c1403020740c0d86910340310800b0307903401d03142d0701c1295418050580807040640c8003040b650156098030281a045908200b011150070b40059400c4041c15500c102c2c17140403c2042241800500051074082030302e60404443c82e05100105411145a20600c0b600e09418981304041070280d420324174200c0007039614640028041d041d030042d0355880301d04d02802e002c1d909501003254084070420002205d062965510112707490b1004568481c001d421103400300e601c5600ca003040a03004a810018040c5042e00c9480b103d0a205c4549811005a8441c0c00004503e041000600300303a020179040160562030b00b460040c02200304044014210f0780c0c0001d1f4201c05010f0f6040c1c0d10050301c0050b0039034011348401c2c0750141d51503a0100510303002d40f141010700300f0401c00d08411142903030740c1582c501141d03500e015860000d0f42c105210071074040004401c0c410042e1070410810003401d000301c10560065150500307000d610001031700403500d5030300104010f2248 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 151230386 1250 151229136 151229149
    0x50307020409060b0d0b07030e031312050c03060702060906010b04030b04060c11010e010204080114040314090310020a0c020a09060f0e0c04030210050d0e010504030903020103020309103305 83
    0x4664065801080100661a200c401802c510600903441041d5440010038001e01e50f029901c1500b494400300280590100074641d2806510401000c9840d441424481c3c1c412111991a02a1040702284c0000501ea0002800d002c0300b1211000140c4c044420400600030400141e40108400c241c580c0c58076007961244005910014409003280b03466402c08100f0522643d000f03204500958000c00080002d401154041c1d8401d110301400c0b03600b491000e0303080040510140307004580c11b40310136615040c01601e04070181c008441d0346a00d03000d42203006040c942d003400101502c003a42d50350858000e2071441008413000d0950480c034240e5160280620582e42800502825505861200da40582d00d4900919052045410003900030783c90750101c0c2c0c540c0b90410f01401e40c0c098911024801c04040c0e400b400d0807507000b103401070000f81c24a00c0070009540268011500305106070192641d0480001c02e020030b4622120080424a00040b841030440503a00041d823914652241d00305150341c500000900c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 151231636 1250 151230386 151230397
    0x201080117120f0705070504050c09010f0c05060a0b01081e070318020301110703080a0209030615060903060705031e0606030606090d0507120b01090209100e0406260c010c0503 77
    0x20340810020704020300c10200a510360040c00b01500303556810040390b0001c201c0d00100002c84440c800c460000c1110306d41070090900c501000e540403410000481c1c01150b80360070010031402444025850304000c50b00900c84144100000c5201140341d80407113000410354000240410f2410200b1103c3e5004003005101c000e40142d41894003180e42900010651103442400d44001c0d030543c45d00780e0b2203841c43d54900180482074003e84075507000d580e411540600ba0310070100081d6058012100142103800b54144041560300054040750400c2040e002280c542441a9500d001080d000710070400030705c0f010040b00295618140c2e0103a118100341020600501000e0302d014819040400d040000d034807101810080c0c4e075001000c440b421703691007030303203042c44c9805c00004e45101880074008075188c40e0034002c07292800c201070090301a8100a80040759402c0c6005540c03503000344c45200002e10031004494104000142c805007104219282982da441d0406078403a290520140408100118001105030354 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 151232886 1250 151231636 151231649
    0x20a08090a0201120509030f0315190605030601030510032306070f02060f040303020c030a0819020319050c0c07061e02010605030a0318050d030302070b0a1116020d0206221202010801 80
    0x400d606d40040340b5042d4000c0740e848804413030000c01049140400d1000702414013000744d40b0303440c00040c0c0701c0201c91481c90600403140880c20400104581707512a42c40b140e4131a8000258449003505c23540d41183c490009205040007101c2c217510b10030022414401203800003102d0410740c929030311002021b520f981d0002d240011225900b0f000070103050280c2c04036400605814203690703507082e0001015001c08000e80c0c00c907459504000003003d6064441c03003100d009407040300380d80c00c0b40d0303d000901074050940188600700d806014864420003031b41c10011500030740880c5e19a1030240740c0510040c080840c800d140d8104681c1410030800103500c02183c16000c4a40501c1c1840d03103072000c0300804207100a10780c0100c1e00503841e00550421305034140d001d02041882a1112199911415000c406940c0c1d521400d84030a8010410f105009284a07140340c9031a1025000d25141d102da41c0000b50607030031210414014101c072400c1c8400ca1a4140c1500d0090b04500440c80390b002e01c1c40c4c000070304900c0e0502858 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 151234136 1250 151232886 151232891
    0xc01030b041b08090c0909070611160b03040f05030d0605040e01050402060702090429010509070f1b0501091a090708010204150302031f0f060f0c080d09022101020a08090a020112 78
    0x1601c240d20900c188805c044019100388a14200040031a5880e40c1030b20800e8001038180303072403129001c17010034550421640c441508011038103040d00042c956001501c2150000c02c01d516400000c1c005001a240c3d41c103800b40005422440c01c070030301056a4a010203044242d14000030440141d03074110036111030701d40503030300c0a8080d40c840ca030107041c0c481198801c52441e2050f00e00101c0b220070888095050310340603680520306440b80e18059401144588004000c15a6491a02007500102d010824040c2c090b41c0007143c100d210f03444401e007810114580307500c46600841004052001006410000d04c40507000710310305481e15203001014055030100d00e040640000124407584000031601c8580b910a90b0051000340ea10b0075000b02d1001e45100d04000300781c08980700700078a0301614554043e940c2000805140c5500d21944000070203422008030781c807100c02100510f407401200c07084d0240d00381d0321000507901e0036070400c082c00000300100700003a5035010b0715030320f00140d03403003202c001503102180b101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 151235386 1250 151234136 151234141
    0x10e0310090c03050703151a03071a041e05030c010215070c060608100f060504061a0d0e030c03040609050405010b0d0510090c0c0606060207030b01061407140c01030b041b08 76
    0x1c802e4918440d80040c11a10a583c1d010080c89182c1c0105120f4015246040101708008020740407110b80c81c914040c0d0640080008014004032100003650b441030002c946480c003a243d0a8244444000d0444c0070150301030050300f4442400c00300072540c50324509000901011410107071405008500a001c1c2c010454420001e01c10072050741c122a0243c05084152044080325178200e000610010041d04180c604040300041e050515104603815240390700040b030307040d010901881e1800c0d40480282082c4580d9803480c03551062052000e0000c600d080d1000c0d5985d58030342200200319225a8211501c90391a00004108032003034030003104c5004130b0b03038600410507548000302400410742c2580040390460170709082d07581060b8480781c01d0303500501c0b4070380801c141030b00c0e580100c2e910f2070580402840f15440d0030042c4034860080d200340700740c410b05c525014036041d55a0741e1104038100e034074100749259114003032550566070075018040c10341000356003c10512960002c0c0c011041c0c0755580480500040001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 151236636 1250 151235386 151235393
    0x12030a0216060e010b040f020313020603101a03090f01020a091401020f2d01060501080408070c030c120b0a05060105040611030409020c0304050102070b03040b150f0409140c010e031009 81
    0xd072550a60300302e02c00708112502081118081c02d010464140b1035450142040c1ca6103c2034400d0340d009130611351310a0f032124002d03400d0001e0fa91002d8003404501112041c001082030313156a8441402ca00320303550a440303040000c00c441c60101c070500442400d90050054810322544001544211034071f0300a0003c000c5181e0300103034142600002400345500820388049004202d0949842000d504154018070880381300840d5401c9480710702031507001603040c00c049000b0030300220241c4a030724051150b441802d0703980d80e9100c0c035214950740640218030101e80e02506001d05884c107640c0c005904501445645884170008010707100f1801000b061100544c01d9130b40c541c01c1007054901500c00f1501c21559050016a4135680360014420540188075600c004100c100540054902032544a00011100d0300c400c02010180141030500540010914a00200e95a5140074042003503018046180140e041050618107156811860b98140032408800300c82d15180001d44034005001ca80000840040524 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 151237886 1250 151236636 151236667
    0x30f0b1c0210090e220516060906030618050c120112060c0c050715030b09010b040f05010546080403020f030403020a0b0a14130801061d0a0e010b0d0605090c0312030a02 74
    0x320061b00074072803241c8a00c6284280d00501c010384003d40c48501d0503070b030340e020124191003860294891b04403c01c000b02c004203040342c00017600400d500c81064103060000e44000d40701d2400343d00162466007903040e8403090280078820b00ca0703ca100c1d131800602151a503200d15030307104180d00c00d111660034201c650811030b41c46944a540407060090120f8901d580d21415a14540c015005401c0c180349003280020b5035601540c00c454150100b840c0c442d0009000031401e240350030805010844145422107220b42071046e500d1952410400398440d0092400c003400c000340ba0112155260310341b0b9200b0001400036940c0d800d003140c12200c5800d68681d4410140804580032145e840300120072400106620b80700700c81c1c4402100075501014001c00419a66a00001c02d11050715800449454410042031001505801801141a003d8004181882c070707000403e5001c40b0341c0d0800d0307429950322401d00040034802d00020744003000407002050300b0001c034003416840c1d1002401c80d010b400d500141c483d135444043c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 151239136 1250 151237886 151237951
    0x411030705030a0f0203070f050a1202041b030516020706140c07030227100303050d05060d0c080a03030b100207061b0602030f010e070f050406030f0b1c0210090e 71
    0x1034183e030003588083c90a1070703484070b088104a01c00d01035a0780110318401c101315204101c82004051681d00780c030b0903c1e5407a880701d000340180c0e009500c0350b012098800c0000700d01c010708040c59a00054919094050207000600341250b0000c54004250800541364004415070700c91031244410b603501c100401c90719140183c00d900003074014407020704000d030403841c40c00000d241c045142d144580d1603503804251905480d490200a0128105004002d07006c021507119503401100a088001c40d10b540782c55481c44508550700c011000e60281c0c401c14200f42d450f004842a48806450b031921142e5090000380d1207501600924040088011807030700603c442c0040344c00820b8101c001156030342480d0800503024042402581d0030784040074049403c0510941107091541c00590310b650038281008022005001c03190300c03603004a80c84940c413840d1991000750a20a0a92984400003030348991b1041c08103403030039001c46400344051060100120081c0c2400a40c2c408162142044910b440c036001026682c0c12 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 151240386 1250 151239136 151239139
    0x6120905010c0512010806040308010b0705101a040c020102030126030403080304060b040b060702130507050408011b08010e040c030f02060d09051506060c070b070311031c050f070203030411030705 86
    0x38201190030254120008242c4c1c0201007001d620309030380b10400141d68140c1903800030002540c3c500100306510a0402400342c80d4421415221102d499507034080588410360044480c02c0c80c0c0308401d07070f198a000d100350000a10303180025801c56240403140706030508019030440e55086800004e0403906070500840b405954807103c59138481c1864181000184101c2c2c036441c2c007440c070b0100c46408502c6c10070141c900c8554000c009440d01209401840050080545031100b440018032002c50504801c1c004c041c1c0d2031038000c480840940d1410070003804e0000c1a032280402000d01c48c00e21020070881c1003204162900300010600141c094070115031580f06409480c61820301c0c00d80090300700074021a0155143d40415429101c0d522081c0c20090300d03225810701410580c2c400c0000708582c44040010b407500f0f60203410701c00d8015010300703007031800c552043c60012104039900050300c0780003c00d4865140c1106e034401140b4086e00d04000c000c1e5403440003400c0a0108051010205125901040608040d150 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 151241636 1250 151240386 151240391
    0x501201c0e0907050720120307030216051f0f020c091509061203040e040206120f010602010c09030317060f030304090e1209030d120f050c03010302010e040b01090612090501 76
    0x29031000c024003510441188a1055024802142055100780d059414191700008544165424226486101c1a102d01019004100d460426040c01414400b4101042c02034001c1c1075980e01c2810a181400110b80020703104500c20460700a5030011006280024009400c04c0c141001b9040340580c030b8500040d508076482484001045003480700ea01303038400785407020b0303e2041094480c0c0c007c010301001d103c8000756040c1d00a000801403c45540e801c42c0c0c000740090691031071718541c8045c41000e003c0444101c0c02039070242c401001003c1d42480381401c0c0e103845141119000e070a6650040000603c3e81449202d01880d002082055a800c0005507440c02c0c0181180d50300c564032144280a01044403100005005624000c1007171072034030045450300b2100501406020509560036524500103110800409030b64880d0034802210700d00c40e080c0119100c0700401c2d220742c5544001000400c0001c041d6001d24140300043c3c030141d0700070380c0e8401580d81c0c0b0b04000030410300d4140201d00038105280054255070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 151242886 1250 151241636 151241683
    0x4230609040302010e0d030c0f021516090b0a020102210f0f18010905010606020d030608070e040516141c0321021c06030308180705040b0117071107080106050120 71
    0x2030700f503841100c4230743c110f0f1100012140084802d903251008140382e40890004180013032200c0007040c40d664000720b89814203542c00c6440b18080c4025420a4801c1000341c0c2d80065030f032030040c14000419443c02044c5c45a404503182c0380c400204600000703400c003440e46100c100800d01c4019152003803415206068001c00120368582002c5010304803900c645800740c01940030080c2c40c24420301a59056841c0364000300040b529114014941080007002513455000d111450384c0c0004801c42d4480080613022054200020550200820001000c80011055480031001e0340080e420005603c0c015034842d0441c4007810802407050007070720420300345507030703100c3d1413280c01c082c0182c1f95211b0b1080da03002c3d17514201c2d56507603407180c80700301009100c80040c2944410f004004502c2d082c0c01040c2c03c840185801820a1804414002d03104030a0303a40300042000c540c101941d03240f00b0004d9030000c1040754000e000720b611f0318001070040c00044400004400d5000c1500f001c40800f0007010a00109003094100c159 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 151244136 1250 151242886 151242913
    0x2011b03030f06080703170a0e1807080c070510150f03060f0506060403020303030c0904021e090102010b1903080906040807080321012105010e0f0c04230609040302010e 74
    0x1820410840780302030f440d100c00841e4140000480b10180c07507219408007465034036441c109013190082162001049902c3c0000b419940b503118000791a034504d40302e40ba1407420081c401500c0400020143e038018003051084402103100007495565882001c0070000720000c08030070000c605034281d0401d40c080f07184480300000700300f41e070341c45402c89020036001040607031200003c106d42341c885e0b44400383d85030340b081c000b044501115100900c03c000004000600c0c0120010840f101d0383e07280000d103940744601040c04509540c080c01980b0f003c540031688420840e0242101110410003404058610301000c2a100000c6c2c546404982c0a880443c0485200319a5010001d9480d4020030244011900d40308a070f0407818110720015060320604c01418054900480c140d190a41c0e5074601683d8943d01c442903100400001c0c404481d07012440c034080c00210303030003d0600c0261020500c021155814180c45004c02c5159481d0145d0000e808450b00c1d80f041c0c0780c80c24200c6c05014940d4049442d80944203046d520b2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 151245386 1250 151244136 151244141
    0x9050402160c080703050a030f11010906050702010b0a080601090f02281103030702120703020307020d0c0501110606030a06020a170c030f0703180318080a0b01030203011b0210050402011b0303 84
    0xb407007880c454010a49452080f600d90480f480300078407907032204140c840028060400808050b0080c034081c8460401204000c2c01c5d2401040161061585c1c0c0302802070031036080c010b044401605032120f40326070b494017a6040d90390700d051042c9112160b40d042c8070081e40040350101d8004206034041c8141035400c03007070519070300100d001d841000b00e504c04030300c03500c4214080f05891144000e80c0140952100c1a409407542e075001030b4003203045010400010340181d9445105d241d80d01d001d124447d9145060400140041d28020021086940440204411560700098001c0125441003015072900340c0d07440c0a441070320a801c40c0a04203103603a1b040007280740b418409140b007014158131010103034440c5001a0b003104d0b044545004a004080e02c08000f09015000f403480c884010302440403d15074418a2a05043d0a1a01118401000702c010800c0d40703800d000e42c1c0346040b00c80309151409202e121010759182000600000403070385541c0018156806440c1c04100940d107203028000203009890300800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 151246636 1250 151245386 151245427
    0x5070609061401230906060c0102071b090204081b040b090f070e0607032717011e05060307090e01150e0403030e12091203090a080307140316021009050402 68
    0x19460b041c000000340c40010741c0c4a0a0042c5202000e103602000400c1c00c0c0b00d03920344000c00e0290021300400c42e282c001a000d10003403d11501504002e40e000c4180c150946000c0c00300d40c001d2a0450041c001400b00f1100803d81c0000d41400030b4044075061841313000b04010301810300b9441d41c04000c800402104650140a640c440c85603540ca00e1014008401041580d000d8540043c00280c01440c140d40f0310000300907a100c62803407541c0200241c540d03800403400d6040c5541c2c2e0706811239458040c904440c4141491040d100c0e18a40010301803440c082d40425500e015071708c1001032180d110411004809400c2d40208c20324039942c0c01440109482c0d402c503502c0201d054800314006842c01100546500003c40c0c40d0605611619445150a0091041094101c0c0c00344441261740010440740520f940c500e00c030704005000f13003005903803a60520308010742e0000200544000741d420420016040d000400703840c0c2d0718280e04a070441d00c40b00d018002141e0b81c0010303800203908103200244144e0140c00e100500c01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 151247886 1250 151246636 151246661
    0xb1c02070f1208100b0913020a020106080c04060e0c0a030e0a03030c0809060403020d0302090a08060906040b0c040806010302120a0209180f03070b0c0a1713030e0415050405070507060906 82
    0xb01c0044040c60202e8a01008650103040d400c0e040380240b08900059000340900c1030010100000100a054640c04a80c4030507602c0300175039520042088500002e101c0034601401c1110100805460320491880c00c0000403c030350000000007030842d190b580294008007003240741004641d00c1d500c0c0380c90054005c14120340c000e0f01044171100051031103000011180d10503640743d400ba21000100070b00a40294104280b440c0c2c1c0a80003060100d2901c4082180d0342c441d0700d4000007040035040a04204042e84c50291a80342250020001441009400a801070441e03034143c500051f04045a10741904110340d0480096100e4030756410311024064140041820508130000e4035415031170303000420b90b01d20605000034120314150001880131080c90703000c0c081b042c0003814050041c68031540c0e07140130b85808442c00301d2081500702143d824940d000d00d8a00e00c105040d039040021100e00080d0b00704038502442210b201c0c6840da03002449452088065a20389648000d09000110880c68244040e10030b4900c040d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 151249136 1250 151247886 151247903
    0x4050601050f061305060f04031509031b21031d060106090504060e0402040e0a02030609010c0e0a1805090f030a020a050c03010b090103080a09051e03070b0901090b1c02070f 76
    0x142c41030f150480480702d481c1405002c1050061901090114a4024001e101c4154034103110010118001d50722101041044103400a072031442481c0242c206042c00d8100c441c021902d21001e0b00240c40b003d04a0032802d240c41c50030340035074000074044003d0f1240380c8010000f075944051240c0b60450006c2c24605844032625402203180d161402d120032a1024070031b4080004030702c2c0c046409801c155126841986110055030100601600464a08041915580800d0307540e6034400d601942e220013841113030705003212001807207854061031001e400048110044020354450210300360344010051121816903910940307444000070340010703482d180900800e454600600402000b05c1c40e0621450b04c010b40028645d01c40d40e400c640f150700c85070f0003003020706080c44103522001c1404c0c1c0d80c0e9002141c001c0000301c013941584003224141030400c4070b59800130220503014004003c85030780003101d00e030a0380d9500000360b8a41d1500407028008829207865110034a00c001400d005000c042c580c20501640514002d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 151250386 1250 151249136 151249159
    0xb0a090c063f050402041b09031b0b03010e15030706090915080d0c060e0709050603160608061c020d03030203070f02060709061b020a230402090d110d08030405060105 73
    0x50004030300c8042c03109401d0038100c01d140440d61a140d010303541050000d0800245140802c080c900c02d407812108500105102d28030400c104400b041e45d2a182d610400d024050543c41c0080d444010300040c0141400c82d8844400200c2d405c01d0805190040400102180e80643d40c0f40009844039004d80660303d02c884c10a0f031505015809407494604640c25000200124100d81c181260303920191402250f00b1501c0301041649000300b0003140b406460310110000361818841e08051605200301010340003281301150800030746400c1010745e80d101d041503c0395018031580d080450f002400141b070080d0b020f034803150400c0034158035601651003030b1256104c24000c2440044240d035160303000c58032400044c440c80070512105109001d045080c0b5004da0301e802d03134104140e000550603001500032003040c0b1428100d8034034501001d0140110110192000c502e064801808144070f4455084058180071308488292919103d02c1c07401d500c610340001c107003501e07401c0c40d2608985462083c4160351103201c52080 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 151251636 1250 151250386 151250447
    0x4030f0e030615060c1609060501030e0a050c010e0f030703050c0109080a0804120309080a2114030c0714060703050708061804110a120308040203160807030b0a090c06 73
    0xc510f0700500200c4a0119800f0020b010440294000c0c0051060b42c040d02129040606041401ea4043d0003042408503d042c2007000040441e40403c1081400707600c02801030000c14408507070301d14151002c1c40c1c810400101d403004200c0b4046901c1d1030541504c60280700005004001c03c0206400000b40e0b20454165034903078401d80c0d614801603020b46000010001000002e80c20944400b14910a040000355581d0b02c440c0c843c1040000d06041e10103401454541e01d0074480f2200b00072072141c103407c0128252172414010b9056000c0207210400204000420200740308650b5621080b80d8080000c41d0914a000c020080160005860040201c0ca5010225405c2c2c0307800d1b04840c0c42c0c030350003143c01c1020365100c1d1a00105a02d0b504100340c0c0181d10083c0c0172619170036204226070300341c0c002d486580c0d140c1440e10502d4034060012081d900c0040012205100c40c1c5d0300424180c0440f034021106225686441c0601001084034002c0200103003480ca0340018115044200411100d80c007015212664107141c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 151252886 1250 151251636 151251643
    0x4120c08130803070b09070317090a0e0103080a0f0201060b0a0309060603020405070c0b0f25140c070e01050301020c03120c04051905040f0c02061f050907080f070f05070f150504030f0e03 82
    0x10043c03a00f90414000c8131040c40e000040d050f0f81c0401040c2f401d00d02d43c0c885514a084100b80c10503100148005a10303e612074000b020709418072510700c000c0100c0361030804070103401d0042c10660010503449030750341824804a038111001440c0c004104110900380b004020b4580c010900c42210b000d8180030004490707008030b0a2880c03041e02a0060b805092030524000c10400494820450501003020b0007403024100e0700022741000d030010001000c115007803034023895040c501603210621a038010068101c501001006032030480005481c0d0580716118162094014003c9030403180d0000e01c0c040303c140c021000080341e18111042507504000505944500d4010349408a2254000d64041d1002c43c40039411440c15011014241c020603027265120303c001a4090426503100001400500c103208040c0781011400350000100d0a1001e1481802e01d07019045014407000a880c4044c60015901403140351108000c0c9000d03480400c001074030381272902400b15002c40c41040005003000c1c2e1101c4044c01d001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 151254136 1250 151252886 151252889
    0x6020a1205210703021309060f0605030c1b0106030b01120b040803060f0409050c0307170607120902030102160b180703110d02060408010507020c010804120c08130803070b0907 77
    0x405081030040304030406035030580c00218111006103050490101611154542c2805032000ba80c01603030710f0300c01034000c129540f86034200042c01403401c0802c2000e0004908283d04031b0b14103080658a0380d40c1d6000c11000e501417012804060340e121600044c03002019404002601d20401e08981c2590321801864501822100700030403840044003c070303021038494805540d0280f00185214161103d41c80420151203680104403031945c81304407465514541070085074040c00e5440c1880c042c50130a03203007195844074040d01d4031060056003a41031304c5046050300404440b0341c0250003550b83c0c2079040c50074040035440500c2907400701407900c046010000c1410040c600002148001e1482c00d00316240d040780719550b003840d181d00c4960300200c00c00580f102c40250000f4030148000140900d03011402905000881150034108040d01042100251211607002880d51071803804200340800352070300451501ca501000050201c03a2600013407140c10000003001c00510920425030300c1d442da040d420f50303038035200e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 151255386 1250 151254136 151254143
    0x50316110601060903121e12020903190203010f020c100221180d090810050a091e0b0a0207020108160903080c070f09060806041b090c030c11061017011d03090a06020a 73
    0x200d6160604841c45440c1a9408c40f02240b0014981021140000e1407d5005013074803010304c2004103c50191300e02803040c00c5200340c1920080d807421015000d0251100011103400d02450f030701254841c00020385200b02c458021003c4041021030511407003c00c0104130380318900d002d610900c500c600d961881345803588102d0b40c0343c00007414080c00410362980500801045500081d40d51283c0c44045483c0309145c0111800c1c42c44659111320244c2080161001c00a107071031180e5004121440050340e1100e507103a44100070840302055800d81c000121029512540080c0c0200301c0443c1580300828042050703030407605880028041550b4819020050303a880c5d00c60b09026420040c006070101d1888044000040d8143c08a03082090300e590300481182c5401403480006a5103107034844585400201d4040c0081c2e211008250030f2902d0002216140024000d0f18040c0481001403070107a0400d4001045280138010043d4681c200300c4031b025940c0c0c1064050074422400810000394483c00403401c42132440c1c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 151256636 1250 151255386 151255427
    0x5010c11060a1a0303030705070b0c0a0507020f032104150c02060d020a02031e0307080f060d060f0b130b0102060f01080303160c05032d090105031611060106090312 72
    0x444a10180003011094181c450f05a000d4030041d09030b5400b800154401d007025200c40ea1142207506002d0030b4414000c000d20080780003085181071841d00074007917a0074203604840b110858810311000c05e0412645030f24075050000950304100b417000d2180d001e4000e42d101c10800e00c0c1d110340f40c40800c45511088440207500800b08012220312170003290003c01c2c00f40900d00440c0d152080450f18202542c20003d50040101008001d001045038045041c942042d100d2120340b1050400100003400b0110051000b0221503584002d01c10100030340c0c2040022410050010424010443d42c14001d40300c00340c0c900d07005000b540002000c69203e001014140d580140055082d0340e54040081d0390b61041400b000c0c10304c0070541078440010010130007018081c400d41c0b444044504144401040e9504a140020b0908800c0c09080c10710390303110303055940c064120700c1c20091003e03540b40107645400c4245600c008034090303440045091a001100241100d01c118500400c03d440d401c0101d031882ca03150001c428400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 151257886 1250 151256636 151256641
    0x2010207081c090b100e01063f0e010509070501080405060718030f0302030d1104050f15070b0f011509030c0302060715020a230c151e0703050405010c1106 68
    0x81c1001c6000c2c0340c1c803004010024050800d61a0b242d4200000c85220191041c00740060007036404030030445005040d6400c1c00e0000d00c00c2d104008400c4070742695070300c1070368030704020000755010907900c000d0301d80440920800c8180c4400c04d03500d010788800c850103070b1584a007540001e26035224820700e61145811801030070081d00d907040b0446001d200e0382d1348503030600c403980c0000c804200c024010508492103500219a60701d1320110403030958816800c0e85180490900c401c01c429198261000001c0000302d0341d89a20710b165100401c42e6000f408000741c030a200b54020440c5414184140b82e06940f003e21140c4d5810b110044121205151800020b1410407007031420001810700b9070103008030a100d00e0a019980a04021000032a003083c18800c00065050256140c150030f581340c2400300e419004107162070504182041b40d904d0300d00c5000064140213400c0060241440507008641d5400210349600e000c0c2440200100605029a07064601d540f80281c010728460044032124034080d4444081d10807035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 151258992 1106 151257886 151257907
    0x280b01021c050d0b040f09060c080c1801030b06091002010b011403100e0613090302011a091e06030a050f06011e0e040204090c1203080103120201020708 67
    0x1003601500094280740d120007180c049105031200800c504d1103460200e00101040d915a00c2c00c2d9107810f00d031500f00421900003aa042c0040e80d2064119100c182090a4610440c4001c039003d4540d092030081c039501980219805400007040f0707906080700d18000c60815001d004c05240141d41d00c2c19201800d40c0c204501140300f417503249030217045182c01e0f51003034926045402003810074090500002d03981c1d6a000701059000424981c207200ba00c0341751601a000e0701c8440c500e0441240710407603031145030a140f0440d0307114142c03075120000c4181a1250410b031001028000c0b64160140d150428040740303003081140342500403000208000e604d00021031103400c040e4000c0d11521902c40908108060803140c0f41c9030003139011100013031000c9151400b4001c12681fa80302000780311034440500f09164004010a040b40e0141c8001c070085820711104900300c0c442d00d040140740f40424010b140c02e6 = true := by decide +kernel

theorem cover : BRFrame.Cov 151079136 151258992 := by
  have h0 := BRFrame.cov_init 151079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151079136 ≤ n) (h2 : n < 151258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
