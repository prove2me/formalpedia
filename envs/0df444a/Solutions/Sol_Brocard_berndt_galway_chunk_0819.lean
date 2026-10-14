-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0819
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:58:39.808833+00:00
-- url     : https://prove2.me/submissions/4304453d-ad92-46d0-851a-4d8ca8079cec

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 147122302 ≤ n < 147302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 147123552 1250 147122302 147122317
    0xe011703071106091503090a0b06030a030906080a1409030d1104030804050409020a05040509161508010e0901090203030d15060509030303061026040c0602060408030a02070302010f1a0108090706020a0611 89
    0x60b90040204101c7c0c3e00045410b9801c14010618000c09640d072004054550110b040001d0228142400500c00140b1030584180d1001300c403000041c3c091500c10410b9201803088804190551000440329400305540c040c860041c0446c0091030f06050441d1346100160180e40180c0c2c0c01190fa6202d00340665445c0000103009001c050000c01c9142800720f00a51507441c0f40c071608508440d0000c0004400e451906402c180b0f0300d00b591161003a0b400c05442000c0743c1d0020300035100d06d648500903071000d42d400740000c110341000c85500090b0228142036030103d0240c2d9520050130f0200a0204540c00e0320b0100849500c802e04072044101c100c81440c6c01d43c0d5102d100c500d084002c540c1000c01d415888004000c01d4003440c0200d580c10509a034a42040b0f81d81c42080310010304521007400400d40015042d009040e00500c2400081041c00c0d4003001217003244c4000001c0702c10004a04d44d22680783d6000315050381c00904070b4005e007250358140780c006540c400103031100074209a42c4c2c0e0400d04d00100c028050b078441 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 147124802 1250 147123552 147123589
    0x60e01020706020703050706060b0c1b0411040806040c06020604030c060905011401090e010f1505090c1c0f0c0c21050d05100816030c0b03090102070b010e01170307110609 75
    0xe484c1d403810010065008548200c0c1c01c01c5c40e00c200030441d0380e000d4082c1c03104405120010110f10000003a0009010380c551500c41d00251a1051841e9a9620102a1000d401c10310700074003e52500c0c0c140081c43c50300c16131121b0b055400030b07420b01000c41e900200e036140c4250451004145d0040501c3c0090060078031106084403170b080c0b0310022950b50126004030707804640e40300080c0f0042511031840c070125007005c0800d02082c03a6540c020441424500d002d41c1c0e000c81030700c0807a4242800014008a207141c16070410b048196200b10320000c15000e4070969888201130b103041e9500307880c1079560f4181c64030111584221294001c200402291140d0121100070402e58002c3c8500d0622140e91311081e407060040d03000c98045d4540c2c059610038810b2030384040740e4001004803001c5141c00228081030744007034083c4e181c2d950200040c0000c1510a80c10900038002130740079003075641c50581d00090440240010140d180c004004100205800d00c1c040c0169140c100c90340c0790394958440c0011380410903082000c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 147126052 1250 147124802 147124807
    0x6090e07030c27061403060f1017040b0103020a0b2b1e0609180b040f02010e031b03060606120f060307053105061c03030b032e0c050403060e0102070602 67
    0x29460100080c0100722183c51701c0300c034030020b45d2606212031404203c549503080f003503200d03200002d4130b0b15509185030340c0030070f0800c0b09d080c0091041400a4040898003985c501c4503c000400840c24450000d42c02081d00300c0c8110706020f455145140084c010b28040c0341a01c0418a1660200d6401d0b8082500d102c20301c42c000a036410442d161101800340780c4640e0000d5450003100e00c904024002c035180344541d01c601440c0040d602c50755900c1b02e03540d4961050f13042100a9410440307d03141004501000c2c0c0d00c00c0a20182c40d8000310406d03207441401405140a80424015400416154092982c03c80343e50341d0502c006a81d8940481d02e004d03950b0380000e500a059501e1040070040c1d180c0019040c01d4907000c03104541c2d601c420080140c820642d0045e0300705200701d20382c0c45850181c0c5040f180d00c1d0304c24600850131000705000a490305030b00c00c1c60403082d40701602c00254030820044040344c0c000c1c20174105208144a03208080c0460050b440080d000c0303a181c260f00140c212080d030448400300d5100b0350454 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 147127302 1250 147126052 147126107
    0x1030f060b0a1815091e170c0a05040c09060c0f02060f0309010c0302040501120203060a0e15030f0d020a0f0c03080d050a0f0b220204050301060e07020706090e07030c 73
    0x814a461503c0f0007042180070860103c0c03101101c50201c400e40c0301d1915000c0101e454161203120301c0e201141d408101c40c0094030007061141018140020300910351000300900c4030402c0402c00400e03265449184114a0300c1118007959030000c48120880b13003142802006030141e42004015002c400304001d5100d60b0006121284980c400f024600800d9204020400e2001104059040303200318000d15000c9080800412031100e20b0386c00a41d40308030f016000700d0039141d0b00c00c1c100c8140c0405640b0503081044800a0900b1400e00f041001c2002d485d06005088406240b94040d4130b6801040e0040c012030f1a00a60f002807000303003c0e0002c0295400181d003035407480d21110020080c6000e5615003007003402d107200130007103032154010b45040b540c4c020301600e20300c0056005500b81903c20711042540701e400b80000a856542132240e600107012030440c5050b42e2a0441c40242000400e40020081c04200f02c010300c05101480c00081d481100b505000030710040c81c1409a41c9005078550050554074a0481c03030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 147128552 1250 147127302 147127307
    0x50d0201050708010b0304020310050c09030a060e0c01320f0d0b092401111011040911030103030507020d03030906091103070902040803072a1202030606060a020a0201030f060b0a 78
    0x344125459650b8070404d90f00d8020302881d80c4070503200690301d54080701c80c02d40450307415400540c008601c038842500d03018000020078102006030206980c4140d40b0861011003820a100020440c2e0003464004c1058814180f121049100020002c2c41021400d2500030b0603110841151352605080c60794a4450840d01c4900c0040d04010108500401d61180407d0202200d4a0040140e089840c4a094481005401101d111030113048107003042c0b0035004401424480c0c1d104880700505040032040d600c9052044510580320100c0054240c130004000400c08203a1007010b417440554102d030f40000001c040d0400f10003070701c0c545d0005052186030114203820400080100c10030301d4803c3d010303500001e0740c56405000701d0065226140380c03a0410040c090000b407443c02c264840721120f2090025401b00e52902c00320f641d403070784c000a1f07207101901010025032504008144c0d218004849061038010341410094958840303580080c1450340311101407a0785800e5401c040301403c1c1503540c65855100c8180300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 147129802 1250 147128552 147128561
    0x5190302040c030b01080619170c0301060b0f0f0702010306050a080318120d0e040f05160e0906010507030c020a08101d060c0403200409030e0f0a0f15030207050d0201 73
    0x40344594548400503601d82c1c081d020b01c18139048140c481c14503550b54002444071000c100b84104420382c1c04000c0100d03256404503012500100f0001c000c204001c8100141400c449458000c02110042480301c0317040000038504843d204031103100c8081c0c50b21014130060300948101e0b00160391180f0f2408000c0f84400001010300003040950120680308001a03080c440c83c940305090300301c12a002038040801c5240901c2a4102004c005000000c0c031012030750204003200c2003901d0302807030740c60840c00da0044140d0020100d0b01d550f204440b01006418031000180c210b110349d0348001d0a010200303c4c2c9005554408103088004c0c01c2c2e03101035903100041c0c1010040100405507007003240c0346c108407020501400010b00e2a1264011078846441c182c1076888401c0b10380701e040460401c0025a0290340140d490701c2c01045c500e2842a106d0250304002c80c0100319442c0c2910860701d000b100502c804008004480c40c500007140c03030707040010141c3c0f184404100c01a108000002c1c10758450b010700c60443c261f05600c03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 147131052 1250 147129802 147129809
    0x3011803030c0e100e0d120c03080c0408031b101407260103020d0c09141b03100303180b0f0408060903030c0a0807110604060e06090f07090b0a0519 65
    0x78100881c81680d001500e28240b1110302a41084144001c5400c49000300c43c851040e84000f00f070302501001580d90001000c001c8965040007511213070019082603004a001904180700134460340c106403c02d245540d0b039010b51584046100c04290700300d0201e00d420302c1820905519024140181e280013150f03401014000d441010024048440c50724000301080c0012070740b14880c801000300c903461502001004100e605003500c0c2041c0300d8a000841400e81d105009900c080107000e14182d00d00a904039000742490ba600c9042281c0c01c0040001e94a1819a0038003a2941801c00d0ba90040c080380701d411001007503812804000000103200c100d90340030800500220382841003243d0780d0340da0318840180c80780015100040305540c1400004040d0f030082d0200ca41c000514513080c43c000700164011440c3c1802500e056400c01e50b03404061554500a010980d17000804200070300615a4402801d0303500c9010b44504a00c4503910001c43c001950341c4901c110050100030f10b009c0c10b031003078a1040c0010114612 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 147132302 1250 147131052 147131057
    0x5390307031706010e060d02070c1d01080d03180213020f0a08010807060302040b0a08041a040303020c0f0c010e09090c0901080d02100b0a090b01020a06020c0a031404030c03120e03011803 82
    0x140d00e0351721030105440030400242801e41810400c02c00340b006908a9807044919095110700800c3c4080084150402080f200104c0e8501c4d5142080c01810b00d81000803003001c1500304105007403440c1c60710081d18a00c40d41a50038940e00207004000e98001c1c050003110b444640300008001c074503542c1c4814424142e568050a41d41e810366503030800e50880c4602c0c80388485820040c45a203088900401f1020380c0640215505080c08900030381030b907913244044800314003084c0c1c04600760384080d00c1006030074000c8090350700400340313403201d400040c3c20091013035071403441550800e0020740800405d001c1a913070700f00b000d01210302a503114030702ea82c0c40313403480640f2500522950340880742d50503050003030810b14a0042d00c0d19100034180010b01d4040c104a60340b160541c41643c10400008509200a00d20740700c80d40060504159646401806210560002500000e051005102291003d43d140046a0f88021205295a4080401e03900c0b064020309083e41340d4a4101c2c0c0300b007a0200f10540500c05403096 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 147133552 1250 147132302 147132347
    0x1060c02090c03040309050d080904050a020a11071a07110a3308041106090306010f1508090c0105091f020114060907020a021c0803040c03030e010539030703 69
    0x2c01d0b500080c1c0012a0050000b442e03c40c1c00b0400360406050340c003034090090704402d151401101c0480d06a400c180c0d4086a5140d001841210315548403580525440c900300140040528181c8142c40d455030103211a4444080051018200b04003600080140c02015203009038140d070703d000c0200c0c6403245a428040304049403013040da04c2c080c1c0101ca00d0300c01049403030385240b948030b586966140c800c0c2040c545401c00c03410080c50380141d030b0070081d4a0003002c041c1c00801c04a41410031120b1000044140e1005115080d000d100183c24081122882410286842922a25404001000c0001e00c000c035038602070301085580340e1346506410142c1c035045118410705494980509104008008461a00058005c2580b01c070040c44d09100072440c81640030003000c040402d03522010942d03402074800312403000c00218104200340c0c10400c208194070b003d00b00070b42000c3c4d1148124001c14400d04041345034a4042d040412508100c07026180320503c07210441c0d4a40740180340282c4184080340400b001c0d1380d0381 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 147134802 1250 147133552 147133561
    0x3010b01090f030f030c050f0a020103150803070204050405070b1909050a0509070f02010204180204050f03010b090c070f0b0f0a0b060a02030403110a09020a080115051303020607060f0501060c0209 86
    0x1404144112058219814001c2e8616201c0c41411810404100e0812048100080210b0010044a14a800e20034060030b520101751001504552650007681000f180d085010000684044142c41c0d00a80659000c5460755840c075140e0b0174800246c202d14440c890114100c0311035101c0d071501c0c00c02c00755240c5a0b032411a40307810400040030081d12900d40e2042041c00003500561189116140c1940c06000150401d529890946149844101d240e603001d41e021801300080d142c828850071030014240e000700103028424010030304007034008082100c0c080f000510390040000040d02c4681542d040305e1504041c0c2004283d105807100d098982d2a0f000e414010303102c0c01803600e4000c032803013005250015480d0a1039683d0300c0c0442080d142d01c0301d5225508060001d20309050b4001800c40c2992a40c1c1c1600c0b6604045416003402c09888005040041c1404180c0346d090554918000f5250121800781d04e50003a450400043d02014400030900d60500c80005000381e04005007150607071084a0b1543d49a98 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 147136052 1250 147134802 147134807
    0x1091205130f051c05070e070c0605250f0e0604030308150907050d0b0f030d0305010611070302030a03080901020913020d1d060a050403020a0b0f010f09020a0c0b15040f02030603010b01 81
    0x1428001c144e48068046481c8002c1404440a40d208034401e80580e0100d507031f1114049045032040311460049000034829004000c414404d05074482c00c06440081c05680c3e540103094000401142481071000c1c900191001c24041e4400001088008000568540d2645401092680152802100500707000212244c5107409030311184600c1e800d030303036650a00020842c2e04003e400ca40d42c807190040500004100e403506c05000c43d050b4007146403004100c0e949408001440820110039480b0150800350003400103a801181d00d030751140c2c0510341030f905c0c0e48a0440d8203009118280c826075120800308890034688110b50050007a4a04000c8100000219408252100242c6005400981d017200700000e000003001d0b03001c540c01c00d00910403200320300c0b410303503c01c1c109110690342804050344440c0108201c40454005d5030180401c04815402c02c907850502400040e08914000d05010f2040300041000c07001010700c1c400c040004109000b468140d0380d4010007513000b995141e000354240b0000326038650 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 147137302 1250 147136052 147136079
    0x513260a02090c091306030803040b0f040b0a1109041508160311190305061504060b0a05030f0603030903030d150902070b010b0f09060c0f10060f14030109120513 71
    0x150080c01100a90383c422807800f070070360301a40c2c2484d40817840298070f5010140d1881440d0180d40309110a503a44c1c1003a04009001c40c0e00100344c065001c2c985e0041100090314214400c0d00020500d0300444c00c0300f00d800b01c2c4002800f03001c41c0c07a0340051814031091895000409500c0c2180e0004094954003440c804110003603038040d0102503ca8900500440054100002902e6521240c55040030003141c51b03075111800c0000541d0007605047d65050341c0e040030b203007030322030741e0000e200c100c01440ca00368000c070303001c1c2ca113000c010503415001151303a0010312183c400780700711040c081c001801e4998a07820100100005c044a051140441e6052040410110910b1003120b145640286104c98240c0ca021341e1144980c1c0100b10780301585078140304a0b625601e50340e0203869000d011034058601c0318901a110b034a05100c4080404046040007000c10050382c8100480040d00c4420444c40340ca83c410f040403074054845030301c005041c1207200c50710840c244e0b03220f000f03025040381e0071136050034280d42d400b40d919001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 147138552 1250 147137302 147137323
    0x5010803090a03150b06070b0a0b040218090709080601060c030201050609010b1b03090405040c08100b010e19080304080606100201090206090906010c0203010507030209100c0b040b040201051326 85
    0x2c18450018008210790044582c251014032001042e080040008100342e80c0001c0c00860b40e00c0031803024400401f480d4054440040030588045040c8020640007003a004082c88941e4014948900414905407040d032a05c80904024000c980740c0c2c3d60b50f188004c003840c0407400240d00652a01011070180c0c600030300303060704880c0310f614014103040800c800000701d80b280f8031041003a40310070024a1400d890b00d000d168030803401000071010782480c2101aa0030020354200c82c604c20740c64580c0c0714410381c3e006098605011020713907869200040040060160403507a400500040c03101040002d440da9000880350300c6040180c41c0030310300715103620040e801e862070940020743c016414081d01c1c21509280d04a598840d605141403014590282c022a00f1213805451400c006500042c0458190810940790b0603402020310349452010701c642c48813600d00c04050710041c154050440400d09681c403d1003514942034143d510385d03210558905520b0032085004500800d504285140c0b441201c502140348bc090 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 147139802 1250 147138552 147138559
    0x10305090309101b03171f030b0a020702040e010b0315010f0e0c040302280501140d092103060326120403020f03130911030910090302100e0c040501080309 68
    0x60181d00003c020900c100400c5000800285420001201403a400030030321207402615200d40344d4900700c6116903044030080c8141035071200c50414003d0311510a6000003102c0d04030722100407540303039160184081d10401401962282c140741042d580c5d01d206601801180d4011400c0340d90603840c00301115840300b400d11035100d2402c41a0410000d80b200f40f80341d03c3e03002c00034190f0b4030702c0c241d12076002400d00e00e003030301c0d641900c542001000e496074507a04100307101810003400c142c00e01c0b4954910740c2c502840b034805c001c1d10f82c5807901290303420400d00103034032840701c02d4445003080e590030705031001030041c0080c0c8415138241c25071808000d2004408001e07480c000f03810240b00c07072511640411000c400000644101c045100300c0a007113a519030284080c0040880180502828614082c4110b05941c0710701180404641e080091048117000000c26840050f04894045649030b854182a8200480381c060604a2030030101c080e80541c40210310000b043d0320803241002140d80760041c850303803401101d4140e0740 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 147141052 1250 147139802 147139807
    0xe030d030b180403020a082b020306060a050d0603080c030a02060127050618090124050622050a0b07051006051005070f05011406120d0e12032b0b0103050903 69
    0xc0ca00c0b580060365209010303004644280205990702d0856620090301d69201814620a02e008070680c0e10094010b0012243d0660a43c100072000820380e11a81500d00240080000c0046100c241600841e0040d6003000c0d4403900c0e1119030032030329200da0000e0b030368000501801e400801e00c10842c1203a00d003240e0001101d08001d890540103070f401448042c00c026400f000c0c40d400401100e8041030014032039111607001186907110900556000b44500c02240b02c0414400810300c02d640b19107040d03482d40f682c0c1c20045280380c00b842d9001806c0440315000950001e18048000c502c5510340383c001c0800724490411520a102c5200c419000c82e00240259503000c0d0140040160f2144a00083c0c0b00150145c0e0320801e258080703580c2c140c01c488941802600d00416001002014075101100c00c5202441902400c1502100c1400420707080a00060030301c106500002032403807420410960788480451680601540b0070042c521000114100a2410300c40c01c00007055000d510900907140034001c40c200450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 147142302 1250 147141052 147141079
    0x80d02070608010317030604020d090606050a140904030e06210609060405040b070f051309090b1315020d06050907020c0a0f030507030b0601170c03040c06090608060d080d0c0e030d030b 81
    0x4186d01c00340419a026400303000b001c4019030184255074650340320700400542c6034540400c3c8500d4401c01c0d480b14540801501c40700226031901c115543d4031a5140c40c00485c40700301070000500600030700303400264003624000e140e0707008070031101705501582c1c0c1194480840e9550f1010030080e54030850380100507402c0c400101d040c0500500c440807288802c1c0c104075042101107460040310f01c041d0b500401800341c9031107080040c090746c2c043d5640c01420420800c0341ca080561203032804a400c9290420506a00060700c4051201d10b43c414005040e00038041070260401060003540c0c0c0780c00742080f910804d844e080020b0124001c0c0414070440f40e209028001941ca5603c1369800f100006164a040c00036102903940d5500140c000031344a42c0d0691201c0344c03a42482d00f0481d015040e603400043c10f0207182601488860b4000c0c030303280d40c0100d00719058020150300c2c0c40c03d00780710700944203200d9095003071820840415030001144000042c00f035007160200a00a1b504a090b914002c10381d40d000311108400d42c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 147143552 1250 147142302 147142343
    0x30f071e020618012718050709060f14030f070e031f05040c17030c010e03160809030a12020703021c03080103020909030f03040807020f01080712020a18080d020706080103 75
    0x50f031400b0050420400004c410b0072601048441c800406044141281c02440b410075585c4202511700c078124000c004503e0040005030210740c141c0100c4081c0101c051844140c00c1c442c10811740c5200342c003501c03942c4a041c03100f15000b03010400c1e2900004503100000a03441e40c140000c1041c604411401200c1d404d12603545000000c0102403c181c035410180c01010541d9206041d11420010180f801103555a60900c030300d40c2103401500044105030001c000f20120802318014540085420030101541d40c0600e10000703241100300d2000500c02500341c1e08080025070082402000c0328025540c441c0e4800310901800b1a900f080341c80200030441c2800140003605220322940e84c01610941100c0c64583d00302407841e001d0b001202c0864440c640011400210300b400c209661020b002801c0c0701e00e4504051a0103000c0319491886c0a031f8056020910300c0f161442940d1225030300c11380300050401c25460f00017154403589500c80704005841090f00000d44e50b84aa141356040340d4005074514851400480301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 147144802 1250 147143552 147143587
    0x2e050306060d05100f02071205270a06030513050601030b010515390303090a060f050609010528151709030a0c06020d1805120f0313020102070305030f071e0206 70
    0x17000069500b40070500000e03a20940e285440380c080c1d00c40a480f285010200101052a0401104445064014841580c0f500300c0c0071801d58201d801c000c03030300e40c0e10180c40726260002c42e40040c1103032081d617000200780041c440714036060716800d50f103a40524401c0951050184500e140c00c0020160700141c81011101001d080030b4180310040d860b281e086c003d50711207459504107035035800098002080b98003c010480c03050055144030420140182e00d0200006900a00140319282c01603501110342a6200084210075035a4011114001d91890321070342c8110b106181c514485020502c80b00d003020000c0d211111942c81040c4c4c0800039490041c8082e42203505000701e440071a41c40f5001c0c0640c5104c421607000340c003824410061005401007241c28224905010341c00d802e58111002c0011070789011031035044980c04444482c40a1401ca06440101e24058040d80302601d1400081881060f1086600017440c4070f900030300d100101d0350801d8440b0403400a0f03650000390b0040c2d040010344000100d0100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 147146052 1250 147144802 147144821
    0x20304030b100b0a090e15010806010c080904110309010f02031605091f020d030c030e030703140403020901121101020106050f091905010b1e07020f06032e050306060d0510 75
    0x1d69040150b5940d080c044035040b120318180400c1850205001100c1e241120747e0780140440e038048400f1805c1000640800409088035040200e0128150b0910044030f08645880707002030402c20442c80c1e042d146140c0c45d00242e031001d8047d400c1408182c0e01900b14001c1d240982a488504500704a40c590265815401005810f4100ea1031840c4103400e641d04d1020300c1005000c5401038401c9100c0b4020080c1211500e200500c03d041ca040303611103107818000156221a68541420140c0000c807144517803c9016030383c002540702c1a1800045040a0942c1e10b00c00b4040c8911282c06152050f50010f90030386405010701c5400401c4610415650301e4043c00305a0008002c006000440c041c4400480036100d00340c0040b8180b0000081070300d160640041d1704021090020038030790800c101e5500180340b035000d4403200703440b0380d0010020407058510b040c2c401d000c51042185001c002d9003890203904001c1814401d20f03103c3e00a100010b01103040040035030070150b030701c01c000e0244007031054496001011000b2 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 147147302 1250 147146052 147146071
    0x110910050c0c0604090507080708090d050a03060509070309031d0315070e1801050a14060a030c3c050a020a060c030b0d0c080f031e07030e0910030b010510020304030b 73
    0x30b021030040e4480384010405070108003004507113441e100724040c255810190010040140038410442900408240007810002c94505540c0d0f544a0b414214040c1c1410f8102e2a4890240402e200e051a016842141254482d84403805410b52801c8241d1508003c2010340f60103400209031000035000031002e00d42e02600d40d00b85400e65083c0840468411280283c00907107170110320740144000e00e40031501e603004100415244002e2001c01001c10300302c0c041c403c000d100f819140c0701d076004060f0141c0381494110521500080062090301115610320180180550803214120802400c90f4403c804071544a580c5400904208509966010040075403480910400d0303500c078009070b9030707544041c0500601401034003010225402c0c00806403c02d10603e608140784c1e4410481c00c80761842001914450140007000c05803500540d0905032501c0301b10022440d4002c100c1c108010103c50788408520549002d8802d405041c0e072100d05105030601c03102d03142d0000d40c1c4244401c00009200c40c3d2400c1c2e10200300d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 147148552 1250 147147302 147147313
    0x20309010807031b20070515030c0f0a18060305010b0a0804020f1e09010603061a07110604091e0c05070f1e0c08011506271509050103110910050c 64
    0x18040081c5016120303910100184070218001401d00240c17a406030215000800f41020034504800101d480c5488420312240900110004500802d08400d0358500b140c0300550716a218043d02000b42600c400744000d0b282464a2031021030603034841d102d15030590b0b4070003411a1038500c103401d003a140181c00420480c0c0c404003240302c103000c07034076500084400414070082e4011401e5a940403c040d8600c140c011208061426008201c202d4845c000b002400d030180b0f60361b981c1c40140e401c000440c040b17290000c43c1c04c2135001400155a40250307100c0303400c0340b021100f910354911903114050140c45815594100146060060401207050200c0d21044c0520480c5140100d046009580700070003010174068611511401003084226800c0c0034020510401c0d2091481c114140b1101030b00703010800d01810f051100345400d18510000c6240c4c614081c0042062004444042010043c034a101c68080c1600180c2000c400342c40c805001e0301500c0c0c6120700201504540b07a441d0700111426004501a01c50b103201e035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 147149802 1250 147148552 147148571
    0x80f07201002040b040e0108031908040c08120304031701080607050903010b040f0b030f0a0206030c03040203011508030307090501020102070c140118080a030e12210d0218031c02030901080703 84
    0x2103200610013020703420040354031645498600d1183e8101603100c3c0c030050b0410407403890090342c03446080311058001d08100209440364209402e90101c0d98106056a01c20044c5180d0341c4810407000e148a6032203030340c54210350380100b50385048204081c402d8000c140c1c410804115403034001d202902542e03130060000107401d01100001010354000c504100a00303603441010000d00c0c1820300410a100c2d450b00020202c407241030b408513080b440020603602403040040301045c1150785c2074000c402c0302d0710010f041200381520390765415103d5006441c5100803c0309200006823550060095032a055000600d00705100d00d40701034420058011030301a4100b040010141c01032500d04008240a0b280c00d50060200882615024180e60303500e81c080d80c81042c0303488400c084e02100003100c0d05c1c0d0030700b40e141d49921404200100400c40c081c80402341c0c143c0c2c0c00441c9078601c42d02043d44c0f0f0325009508070b0440745840d00300202c2c41101c800001c091001a00200b00707008241d4007816016400140f0381c1790000e1088035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 147151052 1250 147149802 147149833
    0x1c05060c0403170a1d120a0b0604181e05010213080a0309090501030b06040b13090501050a0b01080103150209060f070809030c15070f230607080f0720 66
    0x20840d415194140007040c01d01c00d00036803080b40f00b810f001d00c0303110501e40014080043c00c04480d0201d008458804516200000d444100c0c404021300301d59012a50b03c01491300c1c2410f54604e0855103a40201c2c03609615055404c581c0340002d40d0719801c1552102e8010442100140d4401304030001c0c0c80640d0200583d03c8286000c0198600800000c4060310040d54149401003801c60a0ba21840401b81880018404681c0c4094043d420507000c880c0003540e01c00401c04030b00031480c4014410f002c2c0c0c3c600050b032801d02a06420181c0714050200e000c03c103000c50311005542010003800060011000d4a01c03401e0006015801031140c20801484203081180c81c0e44401340943c4201011500b0725008135000016042c02c020003003080d81d080780d1985080e07400410146160260380c1028082d6403000c1018401c3c0403486115101c2a50f00c8928038083c03414140000c0d9a40e40c05407030810010b8842e500240312241b90f008440d00824103a030368a1b140c1e441c2e0124688165021303600310040d5004074031445a0a01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 147152302 1250 147151052 147151063
    0x50d0f1a0103030807021015090e070b04090b0a08011103060108070309020a0906080c0405152403090c132306012d030c090e010e0c0c0109060207120507030e1c05 71
    0x140300c0d1341c0d01030a0385029080203041611211848a00a0803d0201c401c3d07901c45145440031703682240000a4241072056440380303050300961200c01c2d980d07000200400c404019400c0800610310a441c114901591085c03098221459084982052042132011a003158480c40040e0b4200100745004204883c4a40020b410900c4a07031080740311566444080010f00b500303004105220104860070400e85c0f801d0b80e0130131554000901218030541c8601050620802c103485051040c001406400b40c6030300c0d094906c25520345403141224454100b03140c0d401051002401075141085904448403150904c040e6081000c8030302034802414800719007012802c030980300c80804203440c1084188424110300042c0941160042c4010324104030901c4818080d4903842c0d04014116182c106000703280f565000f41240c214080d2202606403542003154030400e201c019000b415086004a09203c03c40c04030034001c0e2118800e1410080100710740c401c044200346001e0b01070040c1a00b8000148071441140d940e100e0814 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 147153552 1250 147152302 147152309
    0x70506070807094703010914091b100e090901050f0105010c0b011521060f050409023d20030a02060f04050a0b01030803040b0c04050d0f1a01 62
    0x5515181040415070740700e070400d00107040c9405809a83d8005034a203807185403080303c000e020450b044500c0450201c2d420044030b50410700c4d070001501c0396102d80703014000d04000d468043c1e0000c410000318281a07008620000007503500401c819515481b6000e018a410700c41120307506010741802e8426890320b034658014414120769000050301e2810002d031503009241a040709041001d40480c207800a5a810590303415900105050000c01001a030200e0b4100c51500740503005908040324580c2c11780041d045001a00e00b01010140980c0d210024001101c0300440080d520040c4600303061040001c400324140c0103190305444052801401c9110244241c2800ca1040004d203c4441142610078580545000c0e03814100510b01e00b0040b400700941d10900500141244507044000c01c041110420070160620341c4000654140d60307407420020340f160401c07507090f150b804140780010102c1f0040804c075003d43e40c000704028021a15500c0702400c401d00700001b1110b00381c2c200c0c81c01d0441c00d050019a4000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 147154802 1250 147153552 147153557
    0xf070509012c0403050c120418051008150405010c050f0708160206040807051e100f050702180a0f0605030303070f05070204050406060305190f0f020103021b07060e010e03060403080c07050607 84
    0xe0740c030765441d01c1f072034584070992200001e101400140000d041c08440d01c044005200804507103510781c240c680030312418070b45c4000c02901c202d03002096051000360000f0311a41c0a60000c11034840342c0d801c281d035640314001e400740034400c0c00c02c0031100151044020307011001c440301c220440e4030b90341e0380480e105034410b82004510380d1041300c0800091604205c0050960f0440b91801160300702c0303801150b2a00f2451042405110050507083c0784170b4891400d6072041600106107600407401c6007054a20080c013610381045c602d082a8028025194130b0042c0400c0720b0f4040d0040d0710315524240215a590030000d12041084070030008034016a03128007541c1c0c00399000d540002401e9203107107841850041c4220001464820040d500f5011464502c501c3c00300e075810125007051802c191004034020f104419003445d009802200300302c410240022034801f541c03030580320a030b08016403030010b40b00d03055808499503040d80050000f4001a00c142070b103541101c0319000d05414041d40c1c0d52124113003542110349100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 147156052 1250 147154802 147154807
    0x801081203092e151202090c120a020403020901080307121101020d060b030f01230411090d03020a12090f090207020303160b07031a03030313020a0503070305030c0f070509012c040305 80
    0x1202d0840780b24200b26620f00024804c1102d1903c507103403c0341c0c00130880281c031441c00b4100060b11011203004988001d500841c0e0b070030385481c1540246000707411030b000503806007a807c00080744241c1e000044410303850301b10103600020121100215001d80024102a10382d54080c04680e05c42c41c803034040c0d040580000c805c400d8503403411341d11500e01540160f220803500064050000c0134400080c0006413103440a4a012034001000002c410440c070a038141103800101d00c548007070501d80d0200f0030403000c0e03105101700302c0340e043c40200844108005020303400240b40c20243c00c101c200071a40c001e05450344081d00b903a060038030982408409042c0f0ba80150b44d10488802003125013603041c42008030180c2c104131030b9141c1c00498404aa581c0c00000c1800c028440c0d41010f903070541d81c851000707500401c0024110381e00c01d0380b02d282c15916600800d607099400d01c40c820154882040200707003142034400152984100360318107950041504041e080201402482c00950088824014121881580292903095 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 147157302 1250 147156052 147156133
    0x61205031b01020f04090b01020712060b100302090f0f130903080910060f05091915030b0f01150f050712030c1107030b0604020c0f0304080109020a06080108120309 72
    0xd124284000e000e000760348104005180030411500782c6040e115400f0740010720604403030050345082d04a400420050321502c4452040103c0f03500104c2d46c195082c0c1e0100442240c488041c0c0c1680a8040c0c5664040404c0c442184141001001c091121200a005020a8a07107486880c2110409841a40021801c90410680520401403401c00d400c010100b003145c5c2c1d2405030303070803140c4049000d03107803003101d1a00c00701e4440c80540c8071110090780d01501c100b280b24445500d401d005d0080d0321089410100400000f94544800c0050504071030300107410202c280c0d4180000c5646c80307c070310345800600c541404100c0105200b400e8600c1503880ca6280090f260118900141c2070f080140044d1550383c0c40003500740b0008180a041070782007803041d14050b03150845000307804c1c1060301c07440c441060f0384000b20700000d483c1c0054104100c040d00039103545c0340107a100c41080304c00400034020004a5801404c1c0d00d562040400015540000c48109880c2e81daa441c001e8003840d401d0818a41580c08415580d10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 147158552 1250 147157302 147157327
    0x6020a05090a080303100b03330301060b040e0109020714010507090f38040305161d041e02010509030d120c1d040b0609030a0804030b13081c06120503 66
    0x6402904000f001141546817001414a00d008607002d84031102c040803022500740c1140d20384800c4507034220560410344544140015610380c07010418030744650b0038440001044440603080300d050302d01c1d10f04200d61507030800450b40060751100381d0417120000e401c50745961584c020300c01c860003950b00c1d64428808501e898481000c03070803550010410b50050071080030702180b191561f50044001c440800c1c2c00301c03c0c00c80c0718000074041c40e840503006004181180d5000880501c140c1c05442c1005400e5030910b1071100320450a2208940c0200100400086402c0315100d0000103101144140f4004c4d282040741c1b00460304000e240521140810300881013410080703500e001f01e0200000510b06000c060324450500424424904000f502950392211111026100d10f0200c8200c40d030090b084500b5101c4510344100c5d581d0061100341e9203207400340045000b040d004600142c0311508110841e0030011007034031a0100c0c441c2c0c4070070750360320640d903820014420821060110149001c1c0c00950740b26002040309 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 147159802 1250 147158552 147158569
    0xb04051003050c090d140a05030c010c0905010203040911090409030201090b0a02090a05060d020d05010806150a030c180605090a0209031608060c071a18190c12020301060306020a0509 80
    0x4040515003804100b01d10300340c83d0810b541120800302d81c0d081c40b01c2880e00340307100002c141d52406c6c1894081d10141c1d8042c0705000005100c00602c141c020042d540740c4080c101c580480d030340070341c9005030400c100400c04030349542c0041014000e030b101d00610300703d00c00340014102d9003104002c40140c2d44512004c810b01104140702a4454804081545004e10360720001d4450709960044503c215004101d0018403c1681c0c1580c8800c80032110400039541c41d400d40307560b20181242c0300e055050313440e032541041c1e00f4003045180c2103039804049801e5841c14000c0700382e207400521075102c001380e44d12500000c482e5501000340e40518840749005a5584c008424541001c100c03a602c1c040882002e141004031110008a5582c40002c41310095100d60343c0d4680722510400005030100c0040c01c0d101845800400b1060b058001c101ca80708480a1800f0750b185d5840a160380e94015201801102040245140548036440340b94401000096143c0e10385e6540b0040360001000c0c8000100d001c107a5117098207183e00b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 147161052 1250 147159802 147159829
    0x80702150610031107050d090305100c0f0806191412060c03040605060612010b0405040e0c010c0314130b0712021c0f0e030303180105010510050708030c070c0b0405 72
    0x891614519107107000c00d80103400000d01000f0150f503030000c05121411101501c032125802000d580406080400040442455000c19a154040c0013020010581903200702848d000c50f944a42c0840b1140310010317591504028003482d007101003d01d5480c0403840d40004617015050b00700d0342500a40042040c4580042c8400d410b001c1c960048061140340b10043c02680d40c0300303900c16000f180c146c0c1c030040881d90303d0003a03032a812010280341d4004075403200d0340c00281085c2c50b4155010402c14515003641d07541c600440c840c0e140450003840711500400c1c80303910f801080b2220b0b1100c0928102900441e58034810329a80400c14540d00402c01d0006c000c080c80c0300f814074103030620042254001d100b03200108035088003074a1080c01040c0103100c0c1640e000e1000c42580c0d0300014241c035160f01d06400380303080100728012441560b500e08000445d1b2440d02032401c0407442840d039100c1c0e003400556951885582c1c000b0748400440c1600f03220b0f01c4002030810903148042c00704142c5064032140790609004069840c000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 147162302 1250 147161052 147161083
    0x305010807031a1503031903050606041d0403090803040b1c06030b010612060f0b090a0812070b0a1d0304090f0c08130609141b0d12120615080702 64
    0xd0301040412903e0030a9044903a288a8200554072a09181001d0981c00c3c0304190b014000030a0a1100210384819080368494548083c003260b900c160400ca085e11440c0a001030318544205800f070081c00e0100f081c0d61061090038032442c80d07615180e140303207160040d50054032980e01c000307020482d901e44101c55100950b488402404414110364a51003920014000d900402441190004248002d900007800905015042d0200151148400400b40d07000103141070143d1540c03c00004e516200043c001d03003820505807500d00f0110b86179a030359204a07000d44118507c5454242c0b03585000a0100220178183c0da460045a40b58940a0444140c0b201140e0144800d40b9009480c19490b0f003006150b640305c8e1009550301e108202e9482d01da401030411210140004c407a644040203018400200325034a4440c021410358560380300b4040149148200000504480c0740a0101c584980202c40745805070500c250082801c507181c000c0d802c16845205007810020b60608240005180c06000c44a101c40018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 147163552 1250 147162302 147162313
    0x308210a090c0504150b0d060302040207060507180303050f072907140a08041104091208180304080c100903050604050304030b01060309020f120721060b060c21041805010603050108 79
    0xc10401308171481c418554101d40002e0031088850055001102840c0d0007001103446150500380240200000c07100e50380405c40340c0d00e0440c0c0c0660801e902000b1698955500c034378081000303c1d0031a95030403c000455581c038503841c00038100d2071902e506528140303a001080c903052800c031000803d071019003050520104020801d4140f420b038481c0f10142e003c1d8004190001d03c0d10002c000c100180441c0a0180c500030001800c0c4001355403102400703014641c2030300c4116415511090480e103a20032071127000080da01601405d01c3c0f90611541c3d4960314107141c02c0c021049966a120241440000c031411504ea4000203001c1c001c00122501c0036001d0034941c9810800050540d0108041d80e0b03264404030321824402001c1861582c00700030300000b5280c0742800d000c8400c800d5147c81c000c03050740320017120260f04041451800c2d081490980b20b10301b00f0000241104030818482e120264070f4a072640140c4c640802010401c11306207440c0d50f40e482111b61001078103624208000701202c2e01a000382c10140c110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 147164802 1250 147163552 147163571
    0x3090c060c0a02090c0706020a0201060519050303070b153c030a06050901020f0705010614061303060209150a0c0201020d0801080d050319090308010602010c08010f0308210a090c0504 80
    0x442d420065410346801c90070b1745032182c1c1c03080c06000d410002458240005191000c0c0d640c103422941c100d5105035204260000c18007450780ca18643c9000ba84cbd09640240003001c00b05501003544c54000d049000700454480c1c51901080c11113900011001d0410081e05500c0d0303440510101c150101c0c80031b4892101c4030480440001c0d1a41c401d94009480c1c151108040ba880110a41c101c403986000721004554580507031400902130300b0184915140005103031032640c99824407500f190081300f00d1060111555080d0755500c0c00035040302c2c080540100c16606107500b00b40c1000000e11981e00c036a2074280140429200092918902010703980801036134100410680d03800140704801c01c030031800c000c0c2d103c2da20949680003030042408141d10340c0d400c011a02d42455000303201d05041e103603181e00920044820344004d561009013071090051045106000300007107103510707010380403c02001c0c589031040615440a000c014070141c90748000c00b5a1130b1140c000304408e0280200c001d2105035000d20040c440f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 147166052 1250 147164802 147164827
    0x11a0a0801060f020c092a030105030d05070606080a0b04151103061c021c030f050304020a0612090204090b06030d030e0d0f02030c1b1c020d080901210203090c06 71
    0x8040c4220030511848001c6559154001d1118480f6018040e0166805140240e42800c2451f03500c000692050454092a041c0309040c20803a81625400383c02024000d10b10001114170384c0c840b02080d15015941c05020540e19010300c081d50215001d0f000d40341c140c2c1054100410f02404d00c44083d80b02c580740840c20030030408003400b942d42c81802155220b01103e98642403109071441400002c0d4442d415241410070744416a403560021400395071005980c03211010141e941c3d100c00d89000e5032140b800002009840c0c4141203d151082c44280c0105001c00340e5400b0409840c00040115000203480c810080f060804201c42100d00ca41c0d85801d0046182c12005a07403100d0b008100d8500b0007412100b42d04005008204070f41c8a031700030100310f8030680701c03401040300c01820b581c0c42d903485015866941a801d610f0456183c040780d4005140c00031850301d9a541480f2a48019a050305012710380c1a4083c61100c02d0014003019070702c2007005a07691421030a80e80c141140031855600c580030078090f4190140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 147167302 1250 147166052 147166067
    0x303090907030b120a0b0a060807031115090d03020a02191d10080d0305070f0f392012060103060509160303110c0102010e0c011803061103011a0a 64
    0x41c2c1800118a206800807a4002400c01e0350070840340300740803402042000000b1003612403003e40c6002c20010340c0b40c0342080c5e1150503c0c0b05c0a0075000107101800d05c40d00d400340018040d174442003100f45c5000800342c041404001c0204054016800c684c4c00c2a0540c200106040141400c2145107502c4608145840740c040900c4082851281800000140f010380304c80b40c550b000e050094200c506034a07290310000c001d0041212a10b00181c104000342c082c050041d0300e113400c0c1080f584c450030f0181c00a00e9a4000009141c1c0180c000001c2c00142001e0b640303503a50303001d00348c0381c0641d10820204030020007082946c00620145030148081f2405507074002c402140c0c050560b6446503000c29151078401c000d6284c000c005e01203ca201c3c2c103401c80001010703085082000c243e400c0000360340c203d1250500580c200c0d4a001802d440640040e000400c40c4c0d1303c10f49060407104003505242242a849071124001c8030040b4440e040d00c400c0000050080125a02c00c1c1192803030315414682ca4818107142c0140782d074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 147168552 1250 147167302 147167311
    0x812010603022703030f031003060b04050408090108041109190e030405060a1107051914010807081302012c0a080f0a030f03020d0f06140603060a03080a090b1303060b03030909 77
    0x1107030fa00542503107503800e01c102c449403860242407d03102e0911540035565040305101c12101d0b01d00c4d1820000c21400c0c640a20380c496600b0014042c1080d03000d0005480c1d4901c01002100c000002608444030b9948a89225010b26031112308201b0520784442020100c801d44c5610b081d9903401480108034036540c0070102c4082004525000c1c500001d0b005a0610f010165080b0650001c0c0b0712928644c46688200c90400302c5048450040001610000542d020302c030a8483e800041d010400150510030141c0095280c20301c103151440340074404074072201c0c9007865080c030340000d40244403000ca6030f8030b03041d0300303403009008040050200c18444d084110799600d01c40c0d40040c20f005600407040d0040c0e029a0540323103013445200d010300c601c80d4080000801042180211070000d041d07500b891400e0b08040007528441c1c07101921812005065440d000b44d160087d010a404010810b44081280089040608003451401e041c0d400c5840c158603110085c0c0b007900b0b198501992040c400b081c6a070f541c038903955401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 147169802 1250 147168552 147168607
    0xc0a05030316140703030c02090606160b10030f050607031b05041511010e06040b01120b060d020607050a030f0e010327030912050c090a060503030a120f0603081201060302 75
    0x20310424a0302021144080442c10040c3c0906140003050580041f04090340c544200c423050529656042040018061090200c1c0f80c0e820107440c03480002c2c940b28200d9080241c90030410b00d403070303629650310300c1c088140841268903401010500a041c0c1c0c140c0243c1c1840b07054441d4451100d4104d0100803c0f600861280003035409200a100c0e03140ca0086505080d1001e56400a114202801000395500c0703405540499801c044007000054511182d40c8004885510140d2204540c40d08810081e80e00009802607074032203020044140000c4040000c440500d00c070b5142c2c1d0b8502444040047c00c100d8086007403506050512180407950815254100349003031002030b03142c0c604d1a850604980d000c125801a0100000c10601002405800103008a003488120740791084d9541d0340a085041e15498451541c141c2d105010104201c6d0164803c1d800400e248540021944140e00b24541a0f50550303105580c9804001140e803001d270342103018a8050150f07410b09510f0160510388201000e80c01d8242c4940 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 147171052 1250 147169802 147169837
    0x6020a080904200304050f0c030a0b0405100e060406050121060915060609050a08010e060615070f03030606020d020c151c020d0204051905130b120109030f020c0a050303 74
    0x70595869002c002c140f603162601c41c030842103400d0700c44000c4e8000c2d44d098800384201d451444441d0320006020b0700703864011f006400d43c00728a039035401c5e140402600444850180340002c02c800f452a1080510301e0304550000e007030904250410104842041e0012400e02c0201c0400c880840c0d4240f0b45200c4841d8041c000245c2c0c200181800035070000e144482003044c5040c9040050841c0d400301c01c120036641d00300c900720b482550b00c0500e54202d80092100c0d070499009140002c00e107280c00d45449900140074400d842ca420360035a0f0b203411401c1400380440200c1d91f41c20f400c1c0b20740c0b5810480e500b8902c01600040c400c0e460b0a0300029099452031101071030100001a158804c903030301ea00c050b00740005d015400c2d929010030012410294110780252401000300f10a0142e241c040622804110345c00540380104074407800c490280900701070f1f4241908010040000000008248030b0000344034000e507500402d4800c01c6000a003010004004244943d0400c001400705a4021045403400c1003403522008 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 147172302 1250 147171052 147171067
    0xf03050f0c2d031b0304051b130c0206070e0405091b03010207061a01020d020a0b130809060310090f0c170a061707150516120504120602040306050903030106020a08 72
    0x7a40022495040c05074089086a605102d03071040165004810b40075110384400d07003203010310380349010844010300f030381d440040300000d50040700c4e0350b0f80562038024090703d55070403604104005407400d1440c4800140e0044e010400e4899008024801100301220f050105041080c10039540740d80052111400e41103030042004151f41c254111076603181d101c0e0052244030901c0c020300d40180202c00d60540940600d1000d500400c0c8049242e880c080c0d80034214080710788407440204403800321040101c415690401200c0d2060791004040d5105200d403000c0340301100c2c00c014400058440c102080484142005641905250000302241101e0761000010101d56034501c0803070003910242e44845038072511903a01700ba26110101e000001d0f119098045101001d03240000c079400d00c6404008001c0743e1481a9410018001e02e00c04240100d5518202c3c0c102500c4050709084c040e103d0344c003150100e0b400901001008000c1c0915688620b00308003840c190343c5018800385d200d810340980107060110009509 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 147173552 1250 147172302 147172327
    0x1c05070e07121d25120507150c12080702100905010b1011030901050d020702090c0d14100501051e0a0c051005010303050f07061404030f021b0109050d0303020c011a010f03050f0c 78
    0x304c000303002e0070030012211100b9080c115102c034218000c1c1845041c5070b400314080c203800f030112020070b1070780401c059107150310799101103400300d034080e100c40118054403003580400301c0c0c580140813015001300000a0512404c8040000c10080720743c00c1420b11400b4001e80d08900008800c2e580c4900d828200300d40d665825028000080c0300d5080b00039800b00f0114240880030083c64060141c11051100401562004008035455001c0444100d80d5103100c2403421300082d40b00310b028105464140380ca03c00d13070340e0710090040341c01e411031a900000101d404041d07100b4000104240310395900c0f0300790104400d50550700d00070480d101e640440001590005062020404176a0062585e440c0f011036011050800d40350080a103240609680010b02c501031000703c000080d8240c0c10701e02c080503103844554915103414040704520844065007490750900c608002d02d4000c2c01440991200c1841c0042e94811003000540300c84031701c0024404151030a0100014420b00d46455900055040c2c4e519440d00001c5000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 147174802 1250 147173552 147173623
    0x303190b19150212070b010614030112080c010f0501080c03120408190807050a11090105030c0109030b0a200406082a090f0d06050108010e0c1c05070e07121d 69
    0x408280800641707102401090070700e042c140d50b0507541e5482c002610301e118000d140030a029041040310008096000543c0f20720040011460000001c583c1e050f2040411003103c8017607201d00182d801c0744201d44407a240612850400c0564108468200f40c2410082540d910380c8400301a00007011201c17002c1842091800d07104180e40c800b08035461b801d4603140c040710158600001c3e03401605601c0c00402c1610b00490074504d20302040e1750750705005140d81c451503620f0340c0151845020710b944046000c89401011000001d40c400b0016440d5260300e071280040548a008040310604011510b64030010b0945200701c5802400680102d41c440220500142d407007401a00d04990158072101658100b16807074200504940491008000311074a0881d03e03500d13450780c426401d81c40106000d0200c500c010b05110090000d00a104855030692207c07048038640d601924803201085454054038070f100301c2d034000c0351140e07040b141000c1800c44450005a603075806540c81480b03800c130380a4283d102030b03e0300046c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 147176052 1250 147174802 147174823
    0xf160c08060705040603180206030a0903050f0f0315010504030b0103030c0614010e090d0203181302040302121c030b0a05040207030e060307050403060501082107050a050303190b191502 81
    0x1500c1d01414140ba0103001503015108140202e030614a05001c0840b0303080341030000300c0e00500903520395070b9140d212000034480000100c092040901c1903001c070800030f00c05422000f4400780403542d281800200c40142c150050101410000200b03c20b01c0010101c401490460303905046c4490108501d107420005411845608209054844000144424403150b0640100402415200503500b884003ca03102c0c4038888085555881c904d46d110250f04007803068000b01100340a005003400c1d12a40051503103410b144410700d043d440304000b01038a43c24400982880002c070704042100554500126414401a1060a100300d17400b00e80d103800c1c0741c040c1d40ea52114180c0184403c0e6203141800004e0000e40113400700b9950746284c58008505514000341440011800b03440700704580a001d03d080310070340d200c4002200d29015456400340000c404001a43c025030200210442c1c0441581440301200e1406a4140c0304103a08411120380c03d0003c09410191040300c608503e44d0450060260300c0c0803030224 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 147177302 1250 147176052 147176069
    0x10050604062109060605090603070303020319050c12091c02010e0618030106030302060115080903030a090c0b0307032306010c0b07030e0601030b1b03070915210903030b03030f160c 79
    0xc483d07004001c3d40368014025a1400c031910012900d40005050f0343c0c17420340c0001030250340100404068490b4184100002102ca031902502c1c0010917990241007040750000043c10724408584110140760225409080302d8003003501c1070080440750002003107055400f0724980103400004003000007505451429000e184003a0003071110300d07524a802981c4400910031002000b03481000b440c28244100c00c83c030b004140c0f0000960650f00c0f2211100000e104420044402d280c0c0400000350301508030001c0c40c4916075549000a44000300b0080318100c1c150f442e17407072400340000020000340e603801205c4003155580003a0f0300c03c40ea40e00e04205030b004100031400c0800500c2000d000004014240b034209105214030324100e00a000d8141407081180025244103000c101c6800c4140000071f4417203e00422030640b031801c60144034114032078191224105004e13000042d100c542e128149a014090341c044001d00b54011460024a0f2065491744d0040103401007009003840020700a100d00c90101c40040e001c043d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 147178552 1250 147177302 147177311
    0x19060204031e030f03020705060606160c0b0a1205010302010f081f14120609060c0309100203130203010e0714041d0d02100b0105074412100506040621 66
    0x146191401c2d4007100b00220000340600103c120300038480d001307540d030850b8060014007054403a24104241c07030300104a04400541c2c00d41c4140d0118801c070051000804000c0d0f1915540c0060000003020240200384800c801c500b40f8004000507640440c0f840f1035816103250108190300c0c2c108074144101010f1030b80c1c00b10b03d1540600070814148044094600340d00440e60010740036008901c9d03548401c1c080300d40d400d0381d420980c00241885065001154030045042c2a103540b000101c58400c1260025510034134100180c03202001141804d01c1105664010b03200140815482c155114040c021030848003806184c444061040d0b6020268208110111010548601014070318000355070f01c00400041c0609820300703403003180310350240089510181e0400c00040c58511402109003204040801c82e40e5062001c412074402d0380d00e84500b04400d085907502c01a80c61481c41c002c103002d0070000d415642445000f41c01081140d8404089a0440ba041d0818541d0002806103480c00030002d607112049035400c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 147179802 1250 147178552 147178583
    0xb0a09060f08010606021c05040504060b0309010e1b040f110301030b060918060a09141006080106061b060b012303060a06030b030606041a040f0219111906020403 71
    0x5800c9042903802442103405440e5a4920742c0f42a500c0b5407003004090b0b000021088200000300c40c060034540c00c1400d21500d0103a0711b03004241280c045511800d1186004010300c10124070070702800800402d91002460030400e2807141d9003039038040c22030803031103260b40d400e42118414480e00503241c1c100c1504103482e103960356800c1070403011108541862042104100042c2c00450b21a0b00c2c41d1114024401802d41d076a0b17468a840042518080598086032040c145a1b1450380402c80211b81c500900030200343e0324900042e950030b40c0c01d04e070424424410b0203103c80300e62040c1c11440348992a0400030100c2c01c22045c10040e107611480c0684c1c400e20f4a080c3c0e007003c0300780c08003500543c01540d0580d003030441a644c07144200d00303c2e006448082c0d416049040071501c1c5280942007041039076030000e0b20507001c0c00203c00290880e0031060300d80440070380200d28013405100300d400c65500c0001504040c1c01d410b00800b55152107003200307203120840c0140c140d11030003804013550503100a5a44050030900c5d034286e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147181052 1250 147179802 147179819
    0x4230c0a1106150f011b110a180c02060108070302010210050c040e070c0213060612090203010b03100501050f011e0f05091305060a060e0f06030405010f05010e16020a08031501030b0a 80
    0x10303201e46a015121045242c00d05510031201d404918040d8848010084029950400e807a40241c009a9008c809003074049510100003000300c0c40f04400c0c600000350b041c40581c0203420000168002409070700b00400810150341c011400da08412141c600c000350355541e18070000c00600503900544102a111800c204071603802421560b1480e00880703400c4900142014a501959030038000c550002d41911040f000b011000c0c0c010750800c0b0f00c020000b0614400c1e07900844c0c580021b00032030000c1030b0781b204010081e9007481d04640307010010030710307080c40910341042c00780b00880424003500d01004030b030b00040d040c11803089080c0c2c2d200c1600100005e505841c800e1450000d05030a85586200b128910030009000b405884200c07070040018242c600d0b40c00d040d00800c88180c00040041e5a95500c0b84d0039100c0c1078020344203650103440303030050700030b101e0800012a030544242c41c1040c4041d0350000d03151401041c10203003920b600c802541700003041d0881d1000100d0241c00c9010790507401c150000e801103110744 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147182302 1250 147181052 147181081
    0x60702060304050a05071d0c1e0a111006030c14010c08030405070515030a0b0a0f05010c0c090e1606080f01090b060d060f090f110f130b160204230c0a1106 68
    0xb481000d24803ca504d44104404181c4108401101c1007040d610072503d2790350003d4003405000c0c10b9400c000d29850300c590240b178145660803800500c1183d03030f21400d00800c00d140440d00081c0581e01080c41c2e124550900180410194240181c200203010000804114041003c0c1001d004050210b5030342103004030710216a0f4100b41c4a082a50f0b00b8801607101601f82a00c45004a901c0c0b403110010f0036107030400640310000800c0c410784042c00305507004a07181d07030580150a0007007040c1e401003110310721014095500d410f0035003142007000100824003c4038103200200324192441c407200050440c2d400800141e0510880e004807182500f00301e00019044221350800c0e04554050354184610391380104090101c42d440c5004c650343c1c00b02408403219941c81003000e440e0011141c0b200d804491340720401c01c3d18581101c60004400d0050403464001c500b064018000810103400076040c010308500c803003811070000200015410880825192032161141403001980c2c600756061b94140e040c407030201d20100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147183552 1250 147182302 147182339
    0x15060303030209100c0f0206030c040b0310030212030f0405041802040507020a140712060506030102040b0d0f060f12060c0e1003061a040608130201200c040e010b060702060304050a0507 81
    0x113020301d101400041703008104e607413080390b070000042c040d240e00d41c0d00300603060300007904e00c0b0844d142c00e0101103032886407900154029003007052071200c2545148101320000c040154030f1407240d0000d201021094805105440a0b62000c45011600f08000c1c03482c454450790129019500c41c1c02c010038040075030340105000301d0980c040d60110003c800d80003041d90f0b50340c4d110300c00c04c007150302104003003004540554002508040c000300054641a038038020740980d0b4220780c00d01d02002c0e036101040f0107129643d12500e802842403030b10200c0c100c1d10703203200c03028441076040010f00942c0e00d41810700b05682c4030b030446401c1440000d241902d01c0d01406c200400a02c620300402180307400d02c0480060024001c426281100c00d01d80d100c464941d80c20041c0385a2416030a0100c0c1844003011303a44ea081c103140d070441c81101440c80014581c045082003040140d5812104441c00c0d40d241140c010300c0303a254542111600c0e901620403658a4942d450554a040180383c40079010707009504020071b1280d4104400e9081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147184802 1250 147183552 147183559
    0x9240a0909020f031f0b030705090c0a0305071407020405061503090a03030b0303310312110c0f0306010501030c0504150503190606020d0c0201020109061505030d02010603080405010c15060303030209 87
    0x5583d40d6400341665641058400c0c0c6070b40b520b22401c0d0288044640011000c198080c003a2003041e44c0e0780002c0783c04020103a0380070710f0303809011901400540c0d2510800346e2000461406840100d1001721030130841c07245100190040e61900005011910b071501d400078200500008980e481ca0b041d582d05440c3d18100ea0110f000a00f002480501c900d80003080d100107000c51018148584c0c9519456007865540c03034520849000d150f08008040303021a546281c4200f03154070368103038110107048060708052121002c20b11503c48895004180d8a00080b450706490003805e0000d8288283c560a60f42c2d40110381c8090a00c0d144209012026680000030b94010300c903012004010710311300d2044009032461400b8550040c3e01c004030b0900028032030040d5000c40782c018000040c88020176165041030720442e5003418249a01e44404102c242410408954511039510080208600b16551324445200360321900c0e0400030a800102c041c00021814601d540d46005001c02c8a035590b0301d8048c020390800d00c0490320 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147186052 1250 147184802 147184819
    0x5010305090c30070513051b0a05040509061207030809121902010305062b030e0d0b180a030905060c0106050904060f06050a03030807120209120a05011a09240a090902 73
    0x4000b0000380130080e20401020074421020215141d001800d004014445441c040c00300400c030460010001c1c0024025551415659801c1005200310b110014241a020700340c0300740300c40c1c2a0080898500c0590364407540c0d460b0303203003694000074043c04e0310402d4000103400b0711085c45010540c00c2194003031040c800c0e2024462552010108642454032221003040c070155110180124841ca100c80303000c80e446410311904074112500458a404030081003102c1c44a4450103000100100d0800c0c3e50500b03074210010940380c815030b980104064128841c150140d000841d41002c511020f40080d8081d0201078400d480340e140605180c0094200051519241403600602003054101200b0030001d41ea01511810030785d440b04507044071038004d925507009081d0b90a00030112650f590131041c0c402c10034070b04000c082010450810508403210058110342c00355031143c12440d00d4490072091540110140b010b00002c1c00345294001d0501c0c2e08030440e40d0302150112000c204240c1135400001d84500036140d400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147187302 1250 147186052 147186139
    0x1d150a02030919020103113007020316021f020714060a0806091b1305011707080414030c15190c0e120102040503070608070206160905010305090c 64
    0x6080748030564802d1415000541920307000c01030164902c403034610614000400c87c01000801e1101c0c1c21000c522400740164030001d888034510b03102001100f070306104040d402c3d800c01c981d010b9564810302d5400100e01d551030b0454001d6503240080343c41d000c004100d00b0102a040024000e491350710078002c2c1a0951401e5100e10702c1801c002050751100c074203d4403880629107400c0104035030710f600101a10038071040700c000e8a031386101410113400324a482d071060903545400e2100144c01e140e81000380c403844c50a0344d800c012010f64020241a04641c000050058032541c94003102e0030740c800c2048800c030a10800203039102d029020001c1700e00c250224011110141d0202404030291580c04101c0030004800d0500b1101074038189405a410305c42c1c100005141c541e842c0d001c0782c1001c206a02c18004100010100014243c040c0b24095000c18003a910042ca44c0102d000501242c2080c01424105170361200014010081080030640c0520002d16062501c0401e46003120030301001e2000c501407140c60400003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147188552 1250 147187302 147187321
    0x6040e03120c071a1006120b0d080415140d05070c050f07050f0301050405060609090a020a080304210f030503101d061f08011202030a17040302040513050a110102011d15 74
    0x1502440075220b401c0409840e01100311000080c1140c0c4208041e0b40b01c9000b012039555027001801580300f1b105e060740b29840d000010106421a9505d50280300f030041ca01108404407008881c07031005001070008590311031400840d041c160f8427070018014800c0072038941100e0000201e000454008030398041e1640030144c1070609851050f18014a10780c0242c0c00b0510300c1c502034050b154800400320484140540c2034000401042d0305510009094000103810300c0012282c42103e05508001e100710003c6103210f5542d03120300c0344070480c040c040000c00300116003144440d82d4440000d010907407400440d03210390005015440c806444c0503100d00141e8030f00401403014a85c00010407505074480a0407a0701e4948062030540344a20120780c0350180c0b511900c00a00d007200d2450407074001069141d03c541c110700c140403c0fa2400752a8a0b50420b185030403400103080003030440d884c583e000b4030030403289841d800140d002d0501802800207002580f500049001030004500040c998001c154100546403000032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147189802 1250 147188552 147188603
    0x80106030b011220030309060703090f080a0c061b0804150215060d080c0106081e0c01020109120507050c10050c0c0405100303050f0903100903020d1706040e03120c07 73
    0x40c1108400d21342c0c00c000a800318683c0755100c00c06019285481a802c0001d815540505400c50100305010001c2c0029042d2100c400050b0068200604211280341c803200fa2884091190b84100022001d0400003000100d07040d03d849644440310f01d450355100c2a198809a004240910042c451702884051207124501d420340107240203003078264103030301d5520713541c586901c14100303181e10f1364880c0400240300074100900400c45214042035000448064129820310759000160390441e0705146889002c02d00a60318001e410081d4204556a81103915040d0308015164400c2940440c40060a168454210000300030f021070300001d032640000600200002c541080e1034241c032805030b006c1b0910000e800b40004140344094404030a003454440400071f807914003040d100b400046e480e041a001019010881c1c00c60344940b9040144400071852040050024010003480c0b04984a41c5d105001000501c1100c40381c2c2d0201c5400c0c8070a1800c440b2510355640b0440046803044109414403418020f0001c4d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147191052 1250 147189802 147189839
    0x423070804080316110f07050a080304150f1101050403180905040c050d02010507060507020a0c3303060306060f080609030307020d2312150f060714030f04080106030b01 74
    0x161981982c4804490001030001201303288280b24501d26014840d000400034251594516002442258140700c28400140e500b0f90103951150700c2071000340705214141426114502030f84c170b0040c0300d41800c4030301244c20241800088005518050900040c1a03101008158890490310340c3c0b0305403517503815034004a84e000c450141c1582480d1034144902d00d01030401c66881801494614189245912002c0c11200c0940c1c419000d6402205138900700f0800d4880c40d0010300f074030f42c10002a940391220044140512840301c4400d40080a00103035414000e60210024580080081000648991034460341407018000c0000c944a100e0004036840e400000b164454500703503010f0045803d8414080e00c048101020000c40184400410640c000d01000a010110400d0700326100508180a01e580c91500c120031759070040c48048030302640c0da250041100c118a40c031001c4803001c07141140b041802d6003c0e24581e0010204000b500246240c4150401401d4038010f20007501966624800f440440705180d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147192302 1250 147191052 147191063
    0x10020d0807020d170a0e0709020319050423120a03020414030703050a060b0310090b06040c0201060b121e0c04030507050f1e0409080d06031e0b01030803090307020423070804 76
    0x105000e01c4401340e290321600840d01d8900800d40c05403c000090514134681c100d411500c0d0f01204002c0c0750304d03095900c01503000d1221000c00c01c50820307844140d500c212200301c00011003500c0314049026901048410389556101860301e4588210010040c0654081e206a01416140c4c1d06070380910700d400301d10f040807268050003c0042ca801c42d501d2102a20301e85501a500d03001b1042070031120720540c0190034055201c1c0302c00501c50301e0176904200445480711f82c0c413411a072602c0814071915921504503034240c1045c0241c6a01030b40d504111618045611804d60010f034440303401d1103581d12442000e4010341e88500c0a031204c0517181c0c800d0010386684505403a03400a858191281485924507407d84e03e4a000360021840403081e8651390038590003900c0c91080039544640030020300001400020745900452049100b4085d192a1401d2020f018000038062010000102b41d9010040049900e215400780060100b08140d008800f144000d48031180c0301d1050306000201050300c500c0b18107114a9105 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147193552 1250 147192302 147192317
    0xb0109050628050705010612060f0b100c1e0c050931020105070f1b050109050d080313050609010501030311010203190b04020904020d090201030b09160e0f10020d0807020d 75
    0x40c61468008035940c001c0b00340301e820030400000c58028040d039805009009442d1588000a1070541d0031101089880c041d0b42e442e00c2c00e041610b81c0c82070035545034200a494054981c60903410324506400c4082d000c44503c0c40e034a00c6000130403200300c50701d00880750200d03014400c0b07503948044545070a00346c0040388003001804042550040302c0c0382031a040140107250150620049a4460528410b1118280c03403e58008042c0d43e4081c182580280141c0801e103040e014840c41c2c10701054000804070030043c1880030100000b10b01e0703180408425401d43c1c024085504030700304850041c0c0200400c0c04241d00041103c0940a9035110500880740520031240d20004024003102c21040101003664610394000c1d020041d00b5510b548074009801e44003c0c0c18800a000c3c2c9c614030014040303a6110701c80c2c50040c1d01302c10400030380f5049400e50f252031000b10306092040345003180001e0640e1203460007003944a0b0851848181055000450ba21b510300c19488500c1c041e100e00c10b00707a0392444403524a1000a620 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147194802 1250 147193552 147193597
    0x318030d0c0e03070f030f061b020105040615050906060d090f080a180b090915061c060609030f06050402061c02070c0e0108070b180303160308010518070e0f04050a0b01090506 77
    0x782d226040d1501072340c8001015070b50462520798060003040000b0042c2e44407030503c02400150320600c60810b0941012542d1a46003c02040c0e400301c00501132403041e000410904003080e8680c121014850307104154030300c1d41180d85401c5585802200102000480521700358a164110045803070940e40300032001410301100b1020000c0481d4001c0c48070780c20342c2540920f5030b07154403a50090000c290302019584490002ea0310907204a0300386034050740421003850400c1000c0f07501d05500d111015008074002c04c65035500e001041d524801c13003a441c50303d01c83c0100300d100340030b6040d4007070640d980c824179040103400d640d0085040507440070700582c09240c1040000f003005181040c001c0411000440d99000e42038182400241187c0040140e5140c001c0c8140c100030815074030554090152804903440c001d0130840b400010070b002c100410703100900c10f55440c00c04a550340d1410380b0100d200b0061082c8060300c3e00c4242e040150034125181c41c04120100303404901072034807506a42d441c0202249452003000e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147196052 1250 147194802 147194813
    0x130302040504050f0d200d0e1c0210050705101a1201090f050609060a0903050d02030c1303060c02120f03070c170c0303070905031b04020318030d0c0e03070f03 70
    0x101402c1140d0601c12503400c010101c605101c501d810200a88a50039002074513207405c0c0130701c80c40c22502c1c03046802c6442c1c00007020f80c21081c44a1280d4050703581080301803051185407584104010040e501500307911005007800d60050083c55100c1c403650035588002c0700c420005d800d90b4030030340c00010341b00007035800304540e41800c4c81c0d0000c500c08004e00228600d0896103030a001c1508020382610640c009004018080c24100300d0309400c50b2444204001e00910b685004050b030040001e6817006580001c00f00344006441c07030079191500c2003060000103043e500d01d032010040105252020242c0240b072816100c1742d45007000e80d40140322008141e032460761000d04c1114951607129044075801d05030080806c0c1c1154443c080c040b5580400011175990910010141c14201c20351b028030700ca41d20180c0c00b00c0304c00c1840c501c00000450107440160301c0f03844490007a00a14030208088140344008a04040211101d4200b4245408151255602a1132000605403a01c15501403180c05050070181000042c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147197302 1250 147196052 147196061
    0x100e070c021201020d050a051f061202281e020102040b1804020403120201020304030801050d05031806160309092a0e010315030b070801080d02100e070302030307030507031413030204 80
    0x1502c080005141c03070744040d4810308443c800d542c0142e0b5195140100a0741c0c5000c0c10f602a00d00c0e80701c2e50001060352074200c0c02014100e910a4450813241c0100310b4900780351403031072046030341410103103401d007203281460b0020a204110404500e0881c100000c3c004007034018421141600d0303140e06401e140080d17040003120003880103141c3d00d4015508100010103e44d4a559040e000700c4c65500160307490500d420b008000c1601a00403510502000361b1500c00100004125540c1e0303003148607403050401840f00050340c80d016400c4404c040c1300311400c0b00d50415501040610540b03170034600c1001803015003103154003019505090b05401611a0f0500107110b4083c501440c0c0040051401246949103d41e03090302ca0889640203e0b01c00c0c40010038010750603004102c07a030143c0b400a004001858500c0b000960300e044400c2071440c056901c503070801001000f441008059500070302140d507901082c1c64020301a80c4003d00a41c0020040400404a00c514604880401707a04040640c20f40d03085808200062 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147198552 1250 147197302 147197329
    0x5130e030d020a0903050c1c06090302010b15040f0b0408150c0d110c010f05040825021f081003050709021b0604060209030111070b01060507080c0f0303100e070c02 72
    0x2444103000e0386090010307500040c840070034190ba80195031407a510b80300b4500700d01412440c0c8a039245654440641030229080050150448008100545e80d402c1c10b034010004041c5c6541c0200c5100216110309054000402c11161003038200700020b03507214080c0700540603e00412206410124034003100e000c80001981e04403514000ca44d140900050a4030700f180c000f0a260505100013041c0d501102c0c8080c81000480c0c0c0007420244a81d161541e0b80c654a8410080c0c121a42841134103180c41a44640104011540d80606040a88195824459104580c1000c3c0074001081400040c101208080031001140c3e405401050007070304168555019410035400003080030090a085103011a04000c10790248cc01000c0c0181d995040760185802c1d00c444182e030304550001080a1400102c2e50040e031411940301e440d0050300d668003440c0c4403025200708060300480703218419500c00361410120045004030310ba54890588030350b4401c02041c1b2460101c4940c004a11103520042c09421301c041445580d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147199802 1250 147198552 147198581
    0x6012c0409080d020403030c02102d1103031003021f0212030606091c0501050a0b090109020a0309050d02070609051203090415051305011d0603030a05090d0605070f030f060513 77
    0x43c07002d01e06101d012600b09500550004104006100960403c01054203000b82d56282c0902c420382c0142d40c00b21a00301c3c0400c0061030802c0d002c1c1034001184a08005c1c07042800d1350381540d6680c101461085200c500790300090384100002c0104d144014040c1300c4098001803da0003030a0440000b034902201508000c0c01141c0003141000306d003182c0e40d24901c2d5102d03803034111204010005c030542041030840e44003c10404d501031402d40d11071065a258070409044400045000d40c0d1032001c1d810407000b2703001184c0c00134004e1250075014424290042a503d09440f0790341d4541d812150348800f0011141111000040c00740c008025440d03650a03c0d4110383d04d2000f01216009081e5558030125040c030540c0b15090a83c82d0743e50f801404501d00200c84680c914020708014201c0742802400030f0b0b1284204048007003800000a0741d244207880c1e0440d519881a00301804003e46e20b494280500744203044a0b080d00007915006030360b884121248101c4064030009066601d651344000440c034024991501e204e2076 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147201052 1250 147199802 147199807
    0x6060309230a0b04200405010b12040804090204030c1a030601121d060702030d0b03070b04060f030b03060f07082a07080c0d090317090d0b0604020c0d030506012c040908 74
    0x100b0300c5070800a0250740300f6030005c00314501011a0b8102c0c0d040c1c0c51500c0344030324100b00042041413042c500f44c7d40b031408220808041a101c903d02030301d0340e21603a03000100322400840c0c000140140c00086000311a0308204860b008540c15003030b01c155100445015020a440030440d08914555a0004d4881500b0a0001c0b007011916595a071a01104079090001a4400140408821114014030b0800d440c01d6004150203030510a803020680640d01806080286a200c0005420b00c680c200958000001e415600941030020b100e0f002c41c50110768441c04104001c01082c1c1d00302c1c1425105052419210008400c1b280382e000e030030183e0340710000039140c100081c0100a54640c00b8405850451050717216814098510301d003d00c084413810f00380702c461440a22243c0100d4031002d01c4810000d600c102c10008503640d480000b4024000c603842103569209203000c1512080e007652180f406517100b6280c0030752154075904200004001c07141c20802c919000c80060015081540000c01810300c5a81e4250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147202302 1250 147201052 147201073
    0x7050412060209040e0c0f01050702030d030c0c2001091e0312020a0c0801090b011d07030903031103070306051c050703080a030b030604050c0910080307020f0604090f0902040606030923 81
    0x400761642d810b4580903e806c400c1221010f85089040441c14007400e0034444d060910070340010340c0300c840c035580d8003017032544516100010074400c00c4410f91456101c403800e6065000d00d4203152407042244e4150740410ba180002140da258a061000213501da0103502c55021400c6544544d00c52614411480039842150350000010f0143c2d1654000307411088000940c1d000c6504020040c1c20381a4094180c500c00d603041e12400302001c0318411b03404915401c0102c0d0301d0b02c003403070218000d20030901c00382ca0b2050080306108036194035810020458408840c121101c20b000c41110302c445680ca04004c220740d03c00f4034204000790030704010b17280113449410005114040c03040070a040000845003250180c1012000984078500590f03442e4002803310b0003002c0342d07420841055a0380c80340c000080c0c8561884040454a80c1d108011074000d09241e40041c030090003400c04401c05481001412032146003010303808190380c0d00c280308171120b0715041146980704400201c0080e403142d000406120442c0152607008 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147203552 1250 147202302 147202309
    0x806370b0a0320011110051905010603050708100b12040822091112010509180f0a0203070816030803181515090705040b0a1e090e0f07050412060209 65
    0x10020b5000b08144022400702141c60b900b107107104900d11381400340b80c400741c2502450001e2008959000b0a000090b26242c4558011142e0900100340c03400900f00000401d030b89900d608464064a00354480b88819110b54000c0d855000303040c003420f014004140305051002e80042c0b806034206002d030101c24941130703908900508054402000c0360011004c06c0303080107170381180e2254041d51001c100c0040d051000b54078100541013011b00c02c0e98031419041303001c40c2c00c803200c990380c0c1948003054001701c4040c0701c95440f14035100c11103941c0a92181c029603000144400c400f213102c1d001050b02090400180381155074003103043d0405800700c40d1521f9840ca6207142c2000405c11450700210b18148203050b072501c030413040c0c000d40f40e5055080c0203030320131000c1c011000c2e0007800351400c0d41c03c40c1a03030a442e200040d6040720907101d148803414051000100c2e80d0020f81c1c0060000064801008407000c455070cc0c851010450305080e10342e20000356080000b04a036281e844056000140f2903c40580703000c1d01c52001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147204802 1250 147203552 147203569
    0x2130902130909050d030504051911030706080103120804140307080403020405150a03020103110919080d080f130311031b07120506060f010315030303060806370b 71
    0x22090a640010004441c1e0301c0345060307000400c07081400b485504255500c141c0c0302e03401155481c0603da1100c001c54108002400501c0d089a054048010001051708005401200841010f40070340030f0440c02050700c80c85401e5050680390003a00125201c1103c50301160200c1c0700174020b80d141d8100014101f0450341c107000070417086019040150b1201e00b1070040000300c40c0d0103040030342141c1e01c1685a0806440d0b00c055103003200c0d02400d0028203002c812107440114440c004005900160451807000d10113a03600d03065040c0e0304d8030000c903800d40070b0804c1d0070b40d000b40b410740d02a46c0250600d000a0000b250116aa25026110785400c1c0c4c041003101c2c500328515044100c4410541c3c40103101d0603649501007006400074075805980100c040d08030345526440c0e49014020030700441b030070a10710f4003590194000100000d50310310b0042a85a49040050080a60f0b02440361540204004240b078100700007002401d4040c0d40204205a08040c50106c600216101e061103d10f525080030404a0343c03507448 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147206052 1250 147204802 147204809
    0x6071506050102120702010807030b0a0f0305060a0f020c120d060905070c0515060a03030c02060909090307050d090302011b05010605210601120305030c0c07030f03030902040506030604150b01030213 87
    0x2000c1245424103002a0074440c0c42c80c00700da2030490910100000d41c1e44034203560b40151850600081501080d0040b5200900c21f4011807418010840c0000411100042c880d201d961a58010008007018005c0e003c140d200d503005680e1940c0c4030040040d4102d004800504078580000c000040c1607683e0221b58054502c1107075a1008201c07000c540302c052020034041010307240e0f149072001f8142d10703101000600d0200d803400080d04000b40e0360299411500e42c00111202007000505800d031600d80010450b54079440040300f02c07540d0042d50500303904240656600340503280d0507160618511080b13154503145040070b0301c0c16102036480702030000701501c1d03103106c1c00c21001d0001c000420461028814600c0c1540c10f0b0300461403541d03205242c40c003099211080d25008206110282e590b00540424070f85009a107400183c004500c0e41606000c06806902240b030741403094409000c0340c3d0313600b0100740e1242d908a402410f29402d0301054002840d1591150402a005040040c1440c06001000620070780680 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147207302 1250 147206052 147206093
    0xf0309010212040f0209060a0609090207020d02030a06060f0b09030c09091009080903011505030c01030c02120d050a14070c03030f0e070305070611060c0409020f0f070b0a051602060f060607 83
    0x61402c0b0560070032000d007c0c6d20500030f8036044030052812600900852017440346098044e03000c6035480c119031341e41da810030000b03400400300ea03900000c0b070424000401180c230902c41074134070400000906130100d0007604c5021000402410007002610284a44407070b005018580707900581c400d28070030081910808071140d014070509134807500d0440905003100d150629252908240c840c0420081da400a14454000402e00e00810003d5018030140e145c901c0e5484d5880c01e04c03201050146051b2034a5110f00d01c101940001800318807400258072180320403c0d107841001402c1041e03c00d000c6801380e0080941000f18440c0003888040c072070440c0c0c0c24040b0b580c104603000c1e040b07000304109040e40056030404107000900a414a0700303008160303090b54441c5204124000d9004a0100c00810741d039003d6a40075201400c0721a90754a041c030705000700900c02c441c00700720305160402040911850300002088052a0307002041aa01c030007a884024240040c5820b6020b2405c001050014000569003419400f440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147208552 1250 147207302 147207323
    0x703030c1101150315020f121009020c0c0108092e1a0907081504050108161a0706110d020f190f0915020705060f2208030f030901021204 60
    0xc03000101860440c4009070641c0e81010041d2440c420201d51080c1220380c4048100291500d9605e013034041c0c050409450b01301040420421220080012118440c0403c0001c00038816202c10384001203020301e500307140480c0c0c17001c003a0b140307254043c1505036007104403030086842d80b01d071041001d044a510400105d0b46207880c04004603640030280079078a0300304081c41240964107140d81c0840c5c203044c00249a4400c0210741400300700c0e68601c05208a41c010400340c810b00207986c4415015641b110842444004004a8180003d500d00d0788a40540034441e4010500c0c680344c0182c5505003d412142c0c88084802010040f40024213103610081598201c600503d5407120702d149a21400502d255500706c1c240a80c501240082035400800e036401d0713803120754000300300074840c40049107404a0764004642100002402c40e40e101c881601911410b480d24202c0b54100400561510140c9d40c184a081002e40c400d0241c1c1e9645015000038642c044c656031700050500700e40003a001a610801d41d01914603040e103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147209802 1250 147208552 147208571
    0x60801090614040807020607260301030b0a0e0303061e04061d01061b12030e0708031324050903150a05220c0e0712231003030c08070215070303 63
    0x5a0042810403014a03030b10040c030380780c95140c0013a1440741c008020311400b400524a000c000e008800c40004650084820140308100c614540c0f1943c420301013652070650b1341d8000f540240c2d0074051502c920f907141010b141942c45080501008419261203010040320485a22006485501c40c041c0107054214020710708101d00e4041140010060700308104010010303144400c0c000340e005810344940e9000000c0d1010310341002c0c01718010711070b0032600411030088907000602e200700000900f02501000c041c02105a6590b1203040315402d52418550850342d0001500c5049030080000c2c000c0c0300c60103000c1e152600b44810b1030001414044030302c108040e5580c0c0038008074401502c40040c4105404144c8515035a8030785521141d0485407083e90300c0e68280c200003d20040c42181c0318407001031041024001c48bd90300f8001c0d130020050250070f80380000882e0000c0e4250401515440889400d9100c0d241d0303482c459100e1047e190300c40c1006031b03040460a0403400c0900c640300001d2001d40c3c02681c001800080 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147211052 1250 147209802 147209813
    0x50114010504030b0601050702040204171b0301060e01180e030a031b03020f03150102280501050f0c0d02030a02041508090706090503070506090d0807030801060e03030304081204050c0406080109 85
    0x121260224108081488240000341350503502e650816000d0900303946440c403e00c005006807045800501c4007800d14805480c0814001800410840e03080d4181c2507000560b40605080707a220780300c2c81149040350350040201d84c4060b03506407003502120074041610b40c40701401c94a0750340101c841c400081d90300c0403036820b40006d255009400400a180640c94030f40c10f40da42c1c1a1034000a05242e8841100c1030503914a41c0c003c0022185003190411010324040a0030040c1001004004081c0c0d1107500b04030008400400c4030701c074944101c51050616060009c81206140290001403c01c08016070800c40071880340d0600c21110b55640c0d041e5144042c40c58541039442c00d0800c590700640620080e039038240a00d54002c2500000d0b44c6d01590115110f6000320001965200c150f1006400c3d00d400088840178140d1190203241170b610341c4e071a00b05c00e00a10405150762032100b1100030b811044180840c2122041103205150010301031022034800044501c001422a082544260021f81d07449200740c04005 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147212302 1250 147211052 147211079
    0x50604051c03050105090c0d0603051902030c0301020301032d0c0e160807050913090c030516230d0203250f050103020705030f1e0406030518010c020a02090603010f0f0501 75
    0x81c1407400744a25450000420300580d0090050740120038003080341542c5100640c03190000710f40000403202c0450907030b20401d020540d80f14045e0700a01805848020324241402124100c984c0069074900402c0c606122001320b919464601d20b46000d198605008622603544a10150500c0b500194441c2004903007100c203200183c2d03020b0140514202080141e54101c6d042d1194014140e5101d20340c04d8040045030300504100c4401840e01d03118003c0402400000110240094102568900001d4449400301c045e5000141003607c00c40a0100700b10b11424030401c9000d100e4030203000c44030f16001c1400c0d0710141202541080c032040c1b442e52820482e49a650080c08000c0000b03003001c500c0c007100d1b5141c140d2248140d14550360000350000c5d0300c07030088503040d290b000402d50500000780c40c0c54551000801404051351446445212050103041c02001031103861004542a0020254240203609100212100920341945035594542071800400c43e400352144000307200a0000b01507051541c050440c9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147213552 1250 147212302 147212353
    0x103080a03051e01031b1205010c0f08040b130f06051504110403020109210c0303020105071404180b03030c03130e0a0606020d1d1c02041b0c170705060405 68
    0x20484190000750740070143d4801c0e8150b0b500001006595103c1c4008061400801e43c00003a08149a074040c0090080660159104414556400c8400d0440700c10844200780181e4001c0c241e1510700003c500c2004494503c803020502c180502c1140c089151121070840e4070448041e4801e800d40e510600341803420344210607a0000c44a0058105411a00024441900b070b00074031941001c0543d00715036107000d0811400382c1a43c0042c9011500c1d80300e143c000e000c1c000a94111010401030380180000451000c00e450a9039040f1041080b059018610a80030304412002240c0501003040010541107090009011039a00100803450300c038035000a1002d006d40040c40c240c025071038034005000c40761740441d00710142000c80c504440908040c5920107440c10b0000d04032940030300945500304200030700c02c0b0840b1b80580204c0d002c210041a240440d00950700015050340003d00f50043c1e2400039415410035043c1110060702c03035040200726903545260103420358013035801d984411245c4030400700c40110305116 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147214802 1250 147213552 147213571
    0xa090e010e100e01081b1804051011040513181704060905040b031c020319110c010201090203070b070f080703111006050312031806010f050102070803030f131401050103080a0305 78
    0x150725140340f240e1642c0c101600d01c420340b9041001c5110310741d104000d04281580200c07072807d450509240c031580c0c90000d550310031059410180c040c4a81d40c4c0c500241d80c00ca51005d040e5000d240c4d0f90242d07040003806d00310b2002414100740002040410300c2c60b201051084500c2c1c010598450130460040c104861030340c0040d00c20307401e2a40c084179a80b00801c03580541348060f040300301080380b822001d90941c060401011a0443d5030f00a00011a51180101040750b2000060328408042320004a0907204180030280d09503200a004100ba4540280102980740c001c0c0340e5640500d50035a12126503078000071090700020422103400c0d900c244103100b007140c03603004440204805450500441d4403224145807802c0d0040020000400c110a0002524080c204400950300c3c15030b120702d4035070000800d60041500602c00d203500404d01000000840740980b80d550032711100c960703c0508800c00c14015180c2203031501f580300320b4034003030120034040c00c0e021318800c015090715070240c540300070211b590081c21a0f29 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147216052 1250 147214802 147214829
    0x1b030b040609060b09120a1401050708070e010c11010207050409050a1a1521030d09110406030503091e0d05100b0603060d0201120213030b010e07020f06010b0a090e010e10 75
    0x80340c1d134400b0458404160a13240d60071462132800507076043c0003a459014280c40421640030052403010340c0118031903d00c41e15100490780382c2c0542195906041c00540d4007090500c041d81000c96140200b6041852051049a03042515900442c060340c0303000104940c160300c80c03200741d0304020701000c032091200c040d4029000a071520030f020940015041c1d4056015801064007001c007900300c1d01c511940700c445401101d03994008404030b00004c02c1004000e84a0410b007030b910a82a1415010321000c07290000000c50405ca001010080c2099200d400706481a220b1110b0089a8441010070035189004001a08003142e455580e0310035151011f510303074400d000401c100606960b900d881c1c01b0704150207180060400600c0d045020080c0b02e8440c2401d0b0510762108008200003440403064161500586d014a0b5900c84000c243e075200d8036140381e624503810600041c080c04046601900101085240440c43c65541e001176a002035400c1c4c00100c042e40f0235400300020300d41c1e410500001404120170307814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147217302 1250 147216052 147216059
    0x309060c070213020a020a0b04080702030601091e050603160b0c010b04060e04030804031106090102180301090309030312090b011202030f0a0201091a0c010e0309091501050f0a031b030b04060906 85
    0x440c4401902c6405101c5640402c110038011b10802c2030541079540b00c900703407600e030403e400d14003403e070001c403000c0f40f191003031100200780c60706140605405071000d107080740a180085004403000d89001040d1036014452850740d02c2d4035107c8640302c10b000f004902280760303640300c4424003982550501000c09014605196003004035000d9040400d40c000d0709450803440a07100c83c0f8040719034500c4030308003040c54810700e0140300404a040d8018500c09140e00c2d0350080b081e00b40c0007890700780d8045450207000305030850300410100e806840c000580c0482c00c0000103a081030b43d615041c903410203030441c50702440041c0541d01181803c01c60440100074200c02440000030a50000381000124040d070344113030f150051900340a82094050b1060844d0100081c45084180110182e61b41c100111301481500d4800216006d502c3e494028503255006035140da140a5071900c0e1a441c03540a111407030b04240d0744011a07211501c0780c40921042103150f6401040301c00151042100352049a00300039080d9142c52801c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147218552 1250 147217302 147217309
    0x509060702510a030f090c060810140604030f02030f0307051509150c09010c0b041a0c03070c0609020f0d0302070302011101020c0a02040905010209060301060908011a0d0f06150303050309060c0702 86
    0x5a110212031320700400d0080d106075a4a010385115800108088001d0f0b5004c20515003108107284145030b0b004c0108401d070f40e203403805074000f00c001403041e0b0403200c200024808592202f072a00440ca001078100c89408103060a070901d90362010300705a5440c0c02921005910983d9041c3c0c080d00800b42c2002440c07500310750740010350000c1d00a005100104000034001903641d000b011021030307954001c03a4081e031610f490f051098850303003c01c0000e04004480b00009944000702010742c2d0145a8039a40d1121000850361003200400741e881c41a64001c005220b035100b2030ba1480010400140b196010b0407810b0310b144000b4102103003510170340032140d00500481a181c003000903441d6080360119004a05160607051550092081c9100580c01050000001c6900f60304001c0c03900c1141c000d0002040301841a03403148060746000050141d000d18108442030101e01c5d86590310305030901914001900580390141002500243e40c81100480c1010040207211481840305c01d1f84803120004840c6000401e9000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147219802 1250 147218552 147218557
    0x20303060f011202041404150b030403050706020403020901060e10030b010c030806120312090f060402010504091d060a0e1b0609010804030504090603080d1b050906070251 75
    0x20303010765800e0046144982c46500f69282c50407829500715030341c5484a40306001561260020703400b42d420014400e1303804d0b0030381034260200e4038100034060850300d60740e8040300c035540440001c1d10400e80a100100c05a510315a12600900054803040304021541c000d01c548c1d40d80c0f07a080390b0141460055060100d9810403990900190305203071172450750341c441c0000342074001405840d400034070000c02c1d12054880001141e6003d61184411510b44050540e5050340c0d17904d084138024000f0b2018001000780a4a0340c018401c1c0003a5191800000038008124500c1c04408681d03c4400303648521400b1000807090007440c1400914030015110b0550960203c0c54038442c0c00c00050400640da070010f820315100b04141c401a220401c018400c40e5070b80d00304190280c0100010809483c649100d00c3c10418400d8002c40341041e0b66101c00f82042805000c000081c2c122210598111003800200b0318080c800c00441d0440d0f41104840c045c4210401d540c0d02e044200140117441200c045940b82030038a99000103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147221052 1250 147219802 147219811
    0x80705010e01050c010e0a020108090304151b0204090804050111070b090d0213090302031308010e0c010311090409060f05070c050a02090406140f01060206060f0d080a17090d120903020303 82
    0x285501c044180800480d035a00c10056001e00b154038240f0f082e8003101000c112035503101d00076aa09004c80d1121101d043c0c076846035104000740707446c074007500070302d114022915255101e0791000d04005901d150f030045016a01540011a040388001509116030341e0829280400303c180003000740451818100244440e10603c004a48510358043d0604110366490740c0e1344200e030b4422102404894024900a540da400c407801200c01e1031502640800e06440520132511140859030080c0805045076005500030140e80d2203000400c0002c200c42060754865024080c000c40c0300e4000010072003c101c00100481d04040c20000820a9444442003c6140001c01c03035001501281c010740c064a81d03141c150000e105006451005054120400c03c0c6160a052918102c80703440d002d4854640c0c0c1c003010000400c040260300d9600c1004451f01c040460300001c080c1204601e1b50401001d0300d488201c400c40140001c80710003009500c441c51742400039610564084125500403420300c007090603640e01a4aa000050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147222302 1250 147221052 147221057
    0x7081510081006090c0c02031c03060807060c140c0901030b25020307060e1606031104052e020607090909060b0909010605090112030c08030a09020307090902010201051008070501 78
    0x4903445044800d4554000d025440460300c05006000048016181922a0301d628529003038400079910b00841c180c0251b01c0c0d0080140400c070518040c5280e01c0303642d03640b1260415a841c2c2c800f0920342420090030000e0100c84e00ca0148804003072a126800440303040041c00c0b20b4001c030300c1c038603556180c2d1006981034a0307103c150009103a40c0c0c02c0154152a0710040040c0c5070040c48d120b480185034020005003040d81c040e02003030000c0c01410005968071014490010942501a80100100d030b100e81c0c0941014100e058400b49019a1400069145c0141680d02520039105840b10302e01d68003a5600140d00c4100c80c000b412151400e00740140078125544240f590700d0351900f10b2030040000f640d0003030f843c80e1801401d10b41c050406005a074000d2100d400746074007039401d42c0008603880001e0645480d443d68196100c070031030001690f480c11250405015040c007181c03a00d034200016902800f0410290040308400101d861850000a00351000a1708002e0388614103801482503100102d4000103807002030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147223552 1250 147222302 147222343
    0xc120f070501060b030f161e1205090c030d0801120f0303020706140907080304030209062107030303090c0608060a0e061c11040606080907060311160c05010305090708 73
    0x120018454030031150001e00551904902180b941c000341c3c081d500681c4294035003002c80c0c2d20031001c102d003c0c4102c2002004619075100014010748110200803030880f0a25001d255000f00c14008400d4071401d54002c8156040b0304101400e9060070030243d041410140307020031484d49003101d41420003040103c003502c0300c0384500115088c036000360110f461055021504000469400305103043c5d0840a40d00c0e80c0c1caa0245d101c00283c144400015601580d400034048020341d10b94104002810300e40c0151400040c0005a040352001c1c01848050000c5009440c0802c0010403880c1c403020a1100d600401c0c05c0c4641c000c2400720325100c1d01d107101c0070303500c0100865507a07840e1540010722008290074880100c0041d001c050f402c100c181c4d007403000c10382d07020b41c0c0a00c1140c0e00c1d01000e5800500031500611a46d0110a003003001900c1780d00704000c0981950403491800e01134000000341c41d11540c4040d9031228003414104060350b4036108080e488818000600180750a0208041e250700ca00e855211065800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147224802 1250 147223552 147223567
    0x60708130305130e070c050708010c09050f220b10170601110c03030a020c040605030109080d11190201020a0e060c070b130f0e04110a050f0d05010902060a09030b0105060c12 76
    0x403400b01c1c80c084d0810944403101d520300303030b20000d041c0e04500308110741500580200242148050103030b00d81c103600ba92116251581000188032440007649034184d400345104c01e00a05140400103045140c3c0520003020900030121400e20144130074482e078210412604100c110440000c4861454101c6d8091030700c07130300b10500050790614203240138001590502000550100d66500000c03004c4429105a40c2406807564910416080f1443c900307001e08101400c00a41810b602c0980c071140e00305080f090041e05080c000c41006d5282070740c08120301c0140c1c1d8002079490740260400c0d15104c2c544012140c0a00e030100403d08a61503a503144114500b0340c102080301c003000300101d81500003410420140440d815943e540d0212142c0d030640f0282d800c0e0f546160002c1550800c0c0341c1c00b0b01900c6000d8004045c0b5200c100511104402500040e03405540c4c421000006a480758000c01101c1c40e0799540c02922821800c21600b00c01c010380c1f1507803081d142048103290400b000b15140c07010310701c804019511030b042d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147226052 1250 147224802 147224827
    0x609121a071710051906050f0c0f0601030f0b0a06060f110c03030307050a140906090d030c02040f020406030f1404110a0812120c120109020310030209010e0405060708130305 76
    0x401480b80c00b108603074070400545020b034401c0c14080707a2045540d00b164441da0006100e182589014400020350100281e00e80c80384483c008080400108086550181280b01c0d07080c00d210f020f80040b120b84c000b0554110034041800d000070780100c0340000c100003941c40c1007805400c4070000e0040d030060001c442910705402c1018009840010320150550b640c03440c20395801006503000202c43c1010079078a1030b841d030025100c4801d0b40d00303404d0050410341c40c01c6000307800c00804c01c042410071020003050781da007a001a15903006200700c18941c07090140c3c40760709160001c0c0c01c1c0d80103001c68480051074468594244d510320f00e4001d0f0030a4102115540c90300c0c0900c0410580d0600340c000e584c0340d10035505009603080240e0001c22800301c00c41100f1004d85c48010070351100e4800c0c04c40e00c0340d94440c500d0045c8203040c02d075801035801510224040c0f4055641e40c0c08075283c1e900903441034000d40c007003000b00400d000d000e200030740d03100b00c0601d08410b503031400030125801c01c031012102404000000c00c40014815 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147227302 1250 147226052 147226067
    0x17010209030723040e0105062103030106080a0e160e060d0807080d0b030307080310060e0306370e120306100c030c0c0312140c070e040f0602040803040609121a07 71
    0xd000c0e01c00c0c841c03003e103811046d0113404103a0390603000e0f02116140c5130024104d041a003001041080c05503103035918084040301d02e841c001d0521202c1aaa4003c2c0d4245070303508000d40e042d044107240144008c50320780310440318000002000c00e8019252845003800190903442110b5801c0da202c4880307609c030070450341414001e0525108040d014440003421005100540c80a10b11171003c5102c034910f0a5110358003110000c0104980356010340c482404155403181c451079842221940180790f548401c00c1c280360080a1040421400b00e2603a2480400c48040c1c0c24025600c00070314894155103103080c035001280d21001035202134001c001c981c3d4030103410584900000003046810070b0b00f429601d500ea090103407001c10361141c9080801c1500441c080b00152260640e1042030716000038120f100d1511558441c2d0f040c00420031a2403082d180450000603407248007606c043c00f100303000ad588031801c0c02c102420004458002020166000c08450300064011001d5500380d40c0d01d00c5021070035100c02c2c2c42580c449 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147228552 1250 147227302 147227369
    0x60207050304080a03171b031611030d0c12020403021f140d050901050601020604050c0d11060c0730030509010509220b0607050705060a020f060a06170102090307 71
    0x80c01031161104c20715038000c2030803054100d01c0d2940201526900710301000141d0b032500801020500303000040326500c10b0150f0401411290400c00488030113844140d042d680603c0e10000b50b1a83d45c03100801240d4080140024144440802c51405040d038001480d81000c41740414a18000550042061441503200007640c00c2c1d02c2462a484101d02d040b01c4000e080211440ca40c82d42c40d1000113642d035880001d4850095401a0180401c0c41c8620140402c02100490568464060f40321482c11b644905000300f0440c5440c1003e05989406c01190200402c80b0342d100121828404c0f500c1603242038280001d40b80e159241c01c0c0641e9410107a00141d689003d50080c032a0311240c46a02c042d081540025002c2e0000941c07030b420440d034500001089083c1c02090005441980985800d1009081c094010a6000035900448802040f4542c00b14542a000c440c8814159250303242044203005072807040304401d030010000c8d0706081f82d07000826511040d901c103146600b8000112000480c40000c15900003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147229802 1250 147228552 147228569
    0x11010b012a082715032503020f0304050706080601050304030f1b02040911040c09080316050c091003050c04020a0509090a02040801090b0402090109050c0304080a120516121503060207050304 83
    0x12000c14484004400f072020341014041d0001d862001c0341050701c03c00301c0f841822030351112802c000031201c28062084448034101d00303045c1d0030043c0f11020301032480034500c03940c403030001000720500304940100210006012107040c40b03000d10900c40060341040140e05c070803204e450a058007210300744000303400c2a10008042d400514122890003880758440d91800348040c00d0b03c00303020003080024100c81385000c0348030b848402c1e002400001c040c0c0712081d44050405000d101101c04420f006400100d640201f500d81800790032007071404104010090204002c940c1049400f14100340382114050302034450440708902c01c0d0120b500041c040c042650603a8064080c3c0d2000300100314040c6000400c104040e20103070302c1141603400010b07401c2424011a449035040c42d45480c115100c41d9039840454000a45200600845482e1800c00d650940301300c51145044605007036030701d2603989000e071107a0032880320045800c3c1409580008110790500c418120f990040b401070343d50303020341001d5066010301e410400f030f0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147231052 1250 147229802 147229837
    0x8150a03020904050d110610060302070206040e01080a0c0503150703050603120a050a091403030f0d060e0c0d050a05010f1701020f0a050a09170606010c051c11010b012a08 75
    0x103104000032117140c194844c0e124245007034184200ca683c0d411044400e41101100c084060040030711075000350000301e102501c90307070815450340200e0600103801d0704003104c3d80d40501da15409000840b030310b0100421081d40540010302090b56000c00c0c40301c0c010902c01c145500c52000c02c0301c46d01c04100c110001071581d51056264030040c18000c0495110038107000c0000c8a03203401140c440c3d4420324921788250f000f4000d40c901100c020320946582c000e01c805c406199900c0e0300c00070344a400342d0003a0b4442c2d440c01011540d0340f01c0c0802200202cad94064054000b4600e0032005200300800f60300031400b0f80b20301070a03068041e00c20210b0180a8400c5000d0f00002d07040100762010007c0d0031501404500150b40c8981c005142c40390051524102c1c5088559a140d2018002c01d200d075001d0803900001034092801c2d41c1180c402c41001d41541694082c00d0b400042002c107262504c104213220303001d031100c804d184c9103030141c0d5450f03202010b58600c0c03281125080c947c2203c1ca010404840125031410b20852144d28 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147232302 1250 147231052 147231061
    0x90f04020d12050a0e0f130c0c080705010b0a060507020d170705010216051e0d0f120e070303080c0a1d030a120504050306010b03010501121e02121602060708150a030209 74
    0x20304039040381540c0c0010175504c5419668500c1c240748044441c0c0c01c0504041d0501003403a9030003001e000981c45440c203000d04410181c003c500428002d1031494014800071484c0d1041c0700500550040c0c40d40003504001e41448000016940c1201000103284c10400c40304c1d1180850b14500c12510501800800661001850642d0700310004c0b07003620711b80e0040c42980e60360841e41c00d42d1320018a25005e01441d540041c0002c0078001d00454291b05284210300e030400c3c000b032080c003241e000c41e090f07180c40b21000e0b8000c2c02d0400c01c060b4003036035841e44014881700701c0f801c000c0d038140e0140a0301c00300391008120707541609000c01c0a4904204001000b03421518805013801c90b00009012a8000e00926010303010b00310010420b4101401142c1c12580d061351110b040c000f90440c130707800922481d58004203241c00104a010102c40300e002410022244070f0405186041403542c6850704080c006c000011740d0001d40405c413103140c00552850340810403600e5080084162400140d0200c000c0d04029440b01b00c860502 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147233552 1250 147232302 147232307
    0x15100902360621070809060a05190c05091f020c091f030c0602010e0106051f120515040f0b0607080f040e13030e040510180e0a060905060a0b090f04020d12 68
    0x721000c1c1000d140401542d01c1d44e0004484405c800c581240381070380408013140341e01003568800c95000405001c444080e607111084d10b0266041c2e138131040d00184000c62003007450b1500303e90f043c00700200404602800768403428069101d030600e46440c0e10442c0c9050000f500c1c401011140e102084141e0200c0a40a440780787c441c0c41e0148034016100190b28100e90601c1c401c82c14030851054410040c10f43d2800010200060907440426001208004404401d880752003c1406a5030180041d0802500020740380414402221800300d42e500c11642404509459034586008443c95150881040ca13600c3c0c00000514505211700ea10aa0032001928200641800e5185400450324400d60310b08144810312000c02c8203940d401d88000441c1444902c08000e01460a4090940450500c80205018102c11803441c281046c05200342c490342c2d1106800c0d420442c00b031040c194032440c0c0d00700c01c0000200304004541e056074010040d4094190502c003040555481c6c0c142c103105030768021340e411108002080300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147234802 1250 147233552 147233587
    0x516030c17070902120939031f050105010f05070803130c12080702011d0102150604090f08041d01151b0501020307030e01050601030e030304120c05151009023606 71
    0x91001c1c2e000320421f1502d6404005121442c543e048615104040700b01c240c2000031440140d082c41c1e042c4200707500841504100c3c80101c21343c42500500288561620300050b14004401484d0010008100031480001e1860781c1529001100d1022400114415103003100303024a40d50040d903115000748059104100520008140c841d01c02c0e600d11020b180344032580d0042c1c00703c0e60f400707601581010b03010308a0549420b11305e0b54841c00003000484d000b441c1e83c44007403818200b0078041c2d44400700050244070f4080103e1601c1800c1100d0308074444958034140b044c0340f000100c803035207800b088007014800b00c01952821200c2c04241d0048002c42d90f9041151001d0018031001d200038006500304000226198040e11450100f11100d201451540c0d031150f032210203074030155480c3d1003484540302c3c0d48400b080707042200d140701e8182d1080284c102d041085080354001c64a501c00c10b1220f00400c03100b50818103883c04401605c46c00220407180003011480e0525550480e0701d03068000402142c9401c01c446c90105 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147236052 1250 147234802 147234811
    0x15040f0f021f0e06070b06010804020a15020709050f061c030c080a020115060f091a07060903080901050a090201120e010b120706030b030a0201200c03011401030516030c1707090212 79
    0x1142c101c3c1d28580d005014150107090005081040050001100c0c0d5010300e0b54240d1240c4014000c40d2000d0310342001d4140301c462030940c40d0060380980700620890701c8910885030801151182d04a0502e01540010456a9680202030010f5407481d0703c001010b00915601c003206a20400c0c49480d003e007500000d001b441c150740c4140c5000150580054440c0c05071382420f28048880e6125101607081440740070002e1402403482228180410021010034031610540102d0340c031035502d1074054140041e02c0e500350f402c0901074501c103520704491400181c4c0c0110310046003040118010445602c171144030740c0101081c1c5021608803440070600c3c0c0313182a021a00b041644e4590f10200105818081403595843d01004003c0c0482d0258912000d000c4001c24070a20603003941003140c04020b41140032a081d144484003002030002480014420054240140c1c0c00804c00da5103110001c030b00e180c403130249001c0c1031b1003002d05040140c043d90f080c1c8030050110030f005c5d0081010566451149920501c12845d0488 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147237302 1250 147236052 147236057
    0x50a0c080708090d050918090a03140901022a0306010305030307091a1e36010c0f1b05090c07060506030a150f091410050915040f0f021f 60
    0x20000c1c400c2401882d220f8012864100100103550480c07005440680c0036540041d4052420f03d202d403139100c1c0c0382916903c20841d6401500c2035805501d00074100000450220038920400d01100706079036400203ca0b100b400307001d03406104000c0340c001c1000b0341a529403036581d05070107400000702c18004008010b5000301c82d19660f841c49150380f4000340414403070151624642c840c00704440342040f842c000d44000840e0307125000d03a2074070118103188010042d000341d0b0345c511105446c07800b103610880030b03a62100f000f00c00e0900907130020451390380c2800d00c50103250040010318005203108910700f011540401901000c5e016807511f040c521a0f00c0c03295040307420708030340b41420080041d1803070901050b01030005600043c0540c0c01c07001c484a000260840e6480720801c990b03154441c4010a000401c90a40303104548080c004524107a0040b40c10794000418100c5d0715403120107404164049030b044280c1c0940c00041d18404505c0624200100112059010354000707882d28640719000030300341800c4080926038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147238552 1250 147237302 147237317
    0x306080c0d0b0606030601050f040e0105150c150c090a0b09041b140711040501090903020606010203041805060a03061d0c090f0a020901300b0402070f02150c01050a0c 73
    0x200c00c024040c08070400003021000940080b0328941084e40166400c4038050502a00740b800020b01494190403613440608507648890040285041c0490741c06820f52100581601d0042c201c400c082d9034441c00c6000f0448190751600154261601a0941d921031800501408500307a82c0c0104c001950810403599100b00c1c0f5121008a28040b0204103a10400858861ba0b80c1d03c10842c0b9152465005148181e800c1080d114201401e543c652082034040c2c10100c01c00140c00c1c0e56070500174a09031008186d6410355004002c103002c50003080c1401c52841c9000310300402c0580d40c02e0302190322000c0a600c0100304e5030070500491844000341d081d9500741400303c0115164840c080c0e040060009044d5a42c1440e10000c50100d4801c0305260010110300704181000c1000c0420300040e5100c80da007511041070700001080360341500340018000c0400380c4030115070960400c062a1180070040a551400074482c0034080450303200d2212010075241c100740c00c1c0000704103500d44501217001524210307003440d0014920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147239802 1250 147238552 147238573
    0x9060305150d030f020c19091d031e0c0105070e03100b0d0b0a090c0906062304060f0207030c0b030f0f04030e1e1e040605030d0c0303050421030608 65
    0x100390340030780a410010100c810028454506482c200791021340402140134000c1002050380702e02c0750340304e66055041c07402015103103003402e19130845410071200e0745c0b542c42510744104540e00001c2511281c01142900c0d80e0103440c00c1c1744400c0b40e8415016001d00c0b65007408c04101580340c003d0820150b642080d42680c45250a912030401102d0201c4d96a0f030740848200801004500c22100d6650b000c0d20126002868007582c0d100d248514031507038000380002e80c5881c1c0c24080b0582c000c1d00f102141c2d6034581110400001840220320a0043c0d00030704c42001025196121214401c00590004640082484001548800100d082580105d036200c4030300004c2000b01d5000d500c0441100c2c8999095a90400e686e00001e0410210355101318028110600304044040ca41d81c4031507090200001b180b03941446070483e031080c403041e294180c0c001c41c800d8120030f030720007822900011940c010030350500c2c0c00211a500c82c50036880a01610006081c4041c480780005801a0103600c43c409955070007003101c821140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147241052 1250 147239802 147239821
    0xc0a060507080d050a02070204092103090b04320a02030610030b040b06060903030a0203040f1706071b140c090c03060609120a080c160902040e01210b010609060305 72
    0x1892401052120304010f2503c800020303900c829000204294058502200c0d500005d06507000c1003400d0302d40030402680c42812500840c3d0078081c2c0c041d43e06003403064a04544401d031003074100a0014080703041c0d4030107006102c04180303200b070003181040c8055040d460310000f4032582d44840c8803080340603118000100304008052111801260742c4100c158070036039555952544500400340204c1c5d00484103000709500e9640602c0649004005a1300840d25113282075051003c07215164002c00780c03440c000709082c45000010070b80541c8100142000c84180c1d29120341c2186003403c8510241c102030065041030307096180462410405c1404945071165038031003035817a042a20058a900e54070640c00c11081c121414040240f10740000884151550700300161644115503015240036090350f00203501d482c00644060541d84040e00c3c009404500745401d0003859050008103024201c01085c0103101e066150062281c80c807003c03039000756665040d507034030301000c3c11400c1c0304e00801002ca4200b000180c02c908 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147242302 1250 147241052 147241057
    0x10c06020c0f1c18051003091203021206090402090609101203170a062405070606030503120a020703020d030b03031903050105030709020c100c11010204030f140f060f0601020a0606080c0a0605 84
    0x8002203050310300789410204422100e11420880c1410384980c0c407280401c0d01c1c020175207003050702e40e10090390302d4940cc46840c1c003040d00103269074440e0100101303110250f1034450059130710010948041d5015200c10b040b01c28006405d40c8001074600d0383c01c01038800c059001031368064010340e6548002c180e444150131001a81d030180034120955940580c003540d111940c058104c030310141420300300d00d4144291a2101601c5154000361055440051000744030100c3e2013800360300401c80002182041c0743c680d4000d407a12050401079081581b5200000d4160341c00340102c1d04404008102d1640c001089103019008e00402d108851217170061000024400806008071440840010302600070340ca100e000030030080803100e03010010080b0b411040003404609100500107140580c142900c041c480c0d00e440e2180540d20301c00000c1d103030490f95886150302000140540c01c41041c00c0c400200e540c401004034503140003142c02a01340350a00100044d03a8002245121942e10203a0382d02078000c4d00c07024166040d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147243552 1250 147242302 147242327
    0xb040e060c0a0908240105030d120b12010207030306090c0c05120a030204030206040f081e0a060c030e0307060504150c0215060d0b16081005060405010c06020c0f1c 72
    0x5411200000c1c0104000078020440c180c030030f0820861650700d82803031514114041c01011460700c1c0c41d100c1d500048405040c001d005200c210700500030420b0043c0f0040c16200310f00603016210303031100e00d0b40c1c1c2e45a03180c009150007000039200864903a0003509008001d011103215007040c0c1450f021800090174416100e04620503000070082105101140c44035a03e5800b03140124200b60b03003800048016a02c9000800c010301140000c80345450800100d14146012180301d09a442054039013107400040202e54038840741d41107640017502c4090020142e001e40780b190011031342800001a241c0c00c005199011a000e1030141c4011001c1c5141184404101d846040c50340c030150b442074503e03081400c4990102c507031102d03003e007070548030a400c1d6403191407800b0161400145940c0c0c6420488449501160745540302c003a050f000da265a01d001d0206003036210f07500690381000b0b82e803241c003003d00141b901140d4030f000744c3c501122036a03c3c1c1a03074a0340c0c0300e451303818401030b2100c85c541980307800500c01c07050340303030350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147244802 1250 147243552 147243581
    0x609050a0510143303070207030b15010e0f04060e090304061b110d030c020303030103060b010e0301060302090604200309010b010219050c06071a0702071401020109150506061309020703030b04 84
    0x140704604418000740d450000c1102aa10300e1340c149122010100b0025601a0f5241e40007880c500d404e43c5450054640028a00740d4a09400014501540c8e400700c0309c201003840c00d6501c00c00103400c035404140076210726001000f4180c0401d0602c005d081001005000711841c544e00d040e9141c0c1e250f01c0c00d268854281c02d0140041030006d502c10003500d065018004158442c0c10f02006040041d0701080c250b4100364030590b0995a2484408083d58001929640a0380101c00800c5050304560004400520150098ac000c95a4071110001145848909554586c0b00c138509030700c17850089201c034043c107000c0b5441c07401406030002d20402c210a0786158001c0a41c000054000c9452000a002c180d40014009440400c5d1440c406805440401060f60040c6000d40c0a0050982004090101044000720301070458bc90804c5200105026402c4d4058824a02c40b01180340e4441800192180c010307402c4150100d00502400501112550300500382e0a1194400340021034800c02080225944410401c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147246052 1250 147244802 147244819
    0x80c15010f0515040810020306011b0201080103080a050d020409061a030c03010b07061b090303020c060f180105040302100c0618050a2409150f0606021002090102010609050a051014 79
    0x28501c0c040c003d800c0103980070600c0e60704166070b4140e0546400071440783d540c0c509500106008603942c3c0421011120b0f812402000d41003915030340020040702051101410045000ca000c2c840107109404554444000d10b60035501c6948031419a0002c0c0720511904489070340c5c00034070b982e040003850150f902c60303d580da06481c02c60303103010003940360341d0b0201c00e046902a517a10f4040a040210210321141113030543d9450581a00b540f0300a86024000031003244111130500030401e5010f603000880780e190303441038444a5480c8400340140c80794000e40c0c100a50044e15040b0f205000d96028184461141c02160180160702c60006020220700b0b103854081c4c515001074082001080030050300f102074800b800898448a1400c5103014200e5120340b4040700d030303510307604004101c02d4024022213801c403480c0c610410813180303009400f030740c1d80000100703003892a50042181002c3e07a0003036221900803d03283c0018800d0b0310b840c2c111039008040c1100c00c04120f00340020081200078511058201000028100e0385 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147247302 1250 147246052 147246059
    0x15030a0c090503151003150c0e01030506100e0d051e06011a070b19050903090301110405090f070c05031605010c0305100909022b21050702040e0f010603080c15010f 72
    0x10f03603001008020345c0c0542c150b6a40000010f1225800d0490001344000000303900c003040340001c0100c0790f00e1410741c0c105814101401029a0380130340020f48400b141c10070b0103d4240c10004030380c4540140802030483c0c000c20034640300b158001c045183e401c80c0b24006407071090703827501d807164600c14009a03c0c040c0c90f0340c28440440001c2c3c4a445590704250051100c84141210b5030b00a0140c620483c0c1c4000c01ea040403500c105281024020510401d840c40031a0307041c5410700c40428500c1c603000342551000810741d40403c040c540078129109032103400a05580c2e881c111050320380c0e4180c1d40a402202e0541c030b0031114248003803183c0702c4e250159001580410b5858038108072000035250301182a44c0c03005001640039102e04a1808804002c1144103030307604000d415042030b4a40418840c1c45081c880703a4502c1c10303c0c40707a40c0b140458034000c0e4103d80000784044401456451b1401c08003a0252940c40c040d0040107011031380c8040e05452080b80112000d550304200305159400e42841620740448004c0b6061 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147248552 1250 147247302 147247333
    0x21608071d0a0e01060f0f1413090f05010204030b04151401050108090c090f100b03010b12100302042a0219060b0f150c07060309110d03090515030a0c090503 69
    0x1150001c010280200e2100c443d14440f5085030001d41c000810704d0300c407100c1004403410340808100280984d0b148040c03442000c0c00131900d50844808c00e94106940c801c00e1008000003d0112613031341c1c4d0007000854032103032070745001780c04410251010344140400b100840000720403400f0710302c410070002c40762142c680d107000015100c02602400d500958007078503440b90020f41f0340c92004c41c452001c02c000c2c5c0f4a6800c0080b0303180504101900140d0000100b080140480407082040392102c0c01500a1801d2075a180c012103500d01e03100e600001d50050511180d041d103c6911b0f29048100114440c00561102c019142607903140940c41c1140400040c00d410308010038841d510000e0b802d5405800e61a800443c0e030005000c071a200b28000e0020030001c100000c00300001c004480181125081c10000790807641c6841c528840541c1c4180d1050807601c0004081520030701c5c604005010181010390280311440070301d07805030012103481044900e0b264007100321f244030b110808200c6502401410842d00042d40341c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147249802 1250 147248552 147248609
    0x40504021003150b071b090209010207031b12050a020102120a0207030b040213050f04061103010b0405060d09050111070213090308060d0c1503090308160509061c0c02160807 76
    0x44001240d809500103603100e80c050050016906c030301240b00c00300c0f600c0b5145002c410000c1c7c21042d086403051000080d103036000078007481a40d0b00b080341c43c4110754004074000a0f5102942180380c0280e0040803e208000c000a1a181c1d424404d8003500c60401c840310340742505000d050702d52001a400300004102007502200f049400038005041c40003452803840320350080c1c1e98140c54031054661900b0800087c01b056104803402600c3e14a54186154500f01011000e80154090f00b031042d4030010728039140c540f00703510a07104264071000901c80407190300c4150304c03076400150050380149070500c01a501d0440ea40700360850f071541501c1c1c08034507484000501641c060302070001c44610801410204d4201e031800325107082113081d942c0104100c4220300d0020f18240000d400721768036512001a000240d40c00005071844207500f03860141d242d01860b02c0c046551490588004d20b1946802c102c1c00c407590f80410780342c0c52080800c101414150340c0700003555494905208a4401603c2400030b10f03003001c0517445 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147251052 1250 147249802 147249821
    0x10620120703020c040c0206010314030711041a0301151a090a060c050a060e060412080f0105132003010509010602060903030a051003151506030209031e0102040b0d0911040504021003 80
    0x11514043c560401240454900c0203d0b640988c0c00a0010003c20403460b032111248140740c0003460403c1003690325041401c0c140d20381c092240d0b440f0b070210010b9600391a01503003070a000400920012400d1100908440d0340344c0030b4aa580c01c20520550700d07030f4140c00c0032142d60306405800600c0c400d250072403c80e24502819001c5032540916000c50003c500e09000d0162054600e40140c0300c5803c1c14506540400c0c0e0b40b4a91f1001d004240041005517400c410146044840544080e000c9142050509004001101061080700342d490b821404c0007011001945c1aa0000e071400512641c80c0c14041c1d9540c041210b41001c168410000030303613445050f40020b904060b880a022805075101d81d5044001c07203104d1100200a5900e170300c0207440c3c1c42c3d9103940d440109018181185820046408252208070141e8503100114465401d940d0b00c490943c11640244030170840941c80343e0f040300c086405040000416294407920101d01126490140708041c003030303980103141603410b040408083e4040e201c01d80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147252302 1250 147251052 147251057
    0x50d02060f0307030506211f060b040b090f190303030902180106030218041b0804110d120315060e100e040c021e0f070b0f040b0d05010620120703 64
    0x220041e00ca42003002c0c1d40a1506a02c0104036490421705202c0355110740d881e03403104007060304100d4400b14804540080394901c00c00c42c45499068140c0c000e8007a2245e6401107007190303000a0001032400d21480509000403088a103082481902400c2100e40703aa078104040d100c001c150000c000003400b0343d10015080344050f1400030524603440d04844506070903400140400e40000d4003104000401400548031031046400f003008890403010303103214a56000f441400d000f00392001c03a080c8104a82d900311403036070061102c00040614900021009500d205a002007420001c02034400c5912142c0441901c12566486541100201c1040701c1d010304e0344406c0050084061a4007082e0b10f171800784c00e00d60405500280f610125006280004407940b80841c001900f18421030a043c0c880814010112020082c460b030f155503240b0f8000c0403511407544041460100040c40740900202908064103e80043c0c843c42c44440b0080c5440d8218180c2c12500b0030585c20002c0010101d408203000741443c00c5c002d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147253552 1250 147252302 147252307
    0x6020d0c110d0c0501030e1b0409020d020a060504050112051501050d02130b0c0712020907080612100504060b0306100614071a010302100c0803220b04031205060a0f050d0206 76
    0x1a404a610b03070100c51800e90303034022001424881940c250280c0e1902507043c40041040c82202c03280d0910380c108500301a031007541c82d0b24450065507550000740e108950014408041e00d40d45a1010b040c541c4203220701c3e40841e000c5400c20b2280d28991007002d1140401c1c1b0a03041d42c1e94050b030b00444e8158400d000c2a04a244d00b80502c0c0000d004440500f006003819071601d682c1ca03521a01d02d030345060f01a40c4904511111407000c00016110f1111044d080700e40c1c1e041200158903201d0020b891020941001006032151a0700000c1d07224ed41c3c3c02c1035016078003418042145c0c81c0078205144d02d40c141240c00340480b400b507038000c1100f9031041ea61a066140050074660130200340781d0710203c8909100c91220700680024005005500d04403520041c54074442c14044440c5855a81c0d6200502004151040140880c1000f061740340810002d07844050340010742d4000ca1500385005403c80e02004030001c4c280340303020002502400e0402480c01a06c0d808007402024a1a003402c0004080101000701d0300204103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147254802 1250 147253552 147253583
    0x7050307020601140d140105040c05040c0917010902030616090e04030203030601141e0d0c0305011a0c071a12060604060c0b0a11070807061a0a09020c0a200f0a06020d0c 74
    0x1c0c0141b0031000c1780c8203000407400d818242456a02e50207690424ae10483c079220041036000d402070300c0201101c440321281c2c0d03003115403400c4140c0100501000650540110410001d16001009111000f070983c1e40b280c46e01c50780c860f200002c543c6411140200542c7c02040402c0300303503000380725900b8880240c0300400c1c5032240690f40082d1070410042c81502190b0003040391119060700340a42a40c84d04d40346800c100f25031401e0240302c002d0f120002007042204001811218120040c0510006444422050b50301c880d02447c0c0107903a98024007907840c241d070f21200483c2c124a031a0702110100c86180d9225005551142c841c0300d00607002900881e50b1603238844031000c81045c000c0280070701d107006c1d0710010b4032900310b0b0500c0c005441c0404044001c280082c1c04400c0c55036240f00421007617803c3c1010050301d40e0360b0031a40902c1c0206003100544402c0501940380140000034802c0404c0c50b00503030300729024040703000c10f21890171054020172000d6080050303220b0300305100e5000d0024041c042c0e101c18601d42c40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147256052 1250 147254802 147254813
    0x5030106110a0c0f050102010f0e0c15041505040e1303082d010e0115021204060f0210050406050108120708040303140d05040c05100c021f111009030807050307020601140d 75
    0x107142d4400f0750b130041c407a94208450360f0280b0604c01c0b100c40300790040c0184100d0b400059121180321902074400c248418101d04c0d41c0800109031000b81400c056401c0038800100005000351f0030078480c19072020603210004210030010489218000e42c1919001c1190700c42503205c4030308a0304103100040070005120095042710541a12038020101d54411002c15414015245203031910138000405660001c800913064131001001c0310100c944624200c02c80c40042c3e03204a052802010a1000c01402e15041c042800001c0c0c2c003840c1200c690340111821444468034168403405003036800707000138009120400100340200110b40c2040c1021650925105010401c6c50407110140c400b6165481201c1c03042c01141401c000c0c05a65200505001d01344060590000352090035594154041e145859401c0c40d42c1800380306000004000f00c401e1b9600041e0003280d401c0246040402540000d9124010900c141d004030304881c010b03003459028143c0c40e800c1a0032000c00d10700e10b0300006e41150790000354002003076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147257302 1250 147256052 147256073
    0x120b0402040b09040c090b0a0302070602040803190e2403090312040f0c0605040b0a1101150303020303040b01050604030b07051c020406020a03090801020a17092e060b070305030106110a 81
    0x100300100c0d10f84480b900030901c8100d9084072845002d22865010a00c9954040800d031002d040c49450050b030345051500e80b00010780101da21110386480f022800022620440e204448540415a00c0083d6403491100f0040488960045c4040e1345000441d407007201c10f000402141d101000c0801c4078505141c4003144000340c2c0c0c1c126010303541052080020400c006d003090000009041c14a819130800d42050f0005800c0d101e1081500c0a20512000201c0b4110080d04800000e01c074800d0b00e01790301070b5079040c007a4880c1d2080720300307c42e2580000004606072801c102070f1010b40740c100c0724600c00e0b5601c615043e2000c4c1c1c80048510f4200041050400880f0001c0c002000130344000e901a0580320028038001e0501501c6400011050340127004d0f841d0841e9000d0b5401c544514440100982901c40712092800e000240070307015110300385205209069001c10302c0340c0d070310090034030f46c10000d80399102c10703c1000d80034200004000034010401000303564451120045804036040681d94090030300c0ea41e98400c2d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147258552 1250 147257302 147257309
    0x50106051c0b03060c180105030105090604200f0d06080a08040e0702070b0f0c0d030905100c110105010306021c02040609030f110901090e12030105091b1b0a0c1d07120b040204 77
    0x440026100c041c10000301002200c480e0070300300306084ad4140000183c10039401001c0d18015556000784907501d865002c2e14062510a0418903943d0710610a11070b0a1580249912500c0d01e0804200144141000a280c8180c0e0b07080020b00c4d0515040c00392250b2070740400b405400451059000102d95035030300c10300030012000c1d00303c285e6984144091003a800c0c04074260040040c14505105d1901091021442c00c0359502d19400010704841024001d403030003444014418003944c83c020021041150b10380c018061404104810400101ca0300c2401045e44203030300900000603040841000066103140c400990907128000e034a0380c542a001c085142c0300426440081e005440b0385965000d5036082c441041504201c0e03210714515030500000c14034803400540382c071114000320000066a9120901600e00c41d189140d241c0101a03c02c03840c8581c1c130064160250349844004400003040d000c0000f110003c02004040c900081d84c41d903005981c0c1320707851001702c14802e89580074201d20350382c0d910061018 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147259802 1250 147258552 147258571
    0x100c020304090c0c030e0402030c1209030c06061f08100b120f01061d06030c21010510031b0c020303040f031a06100203040902030a2d0f050106051c0b0306 68
    0xc89103828601025078202e9410343d810300002280305404280e10600811040c1c10986002d80c2e40d0b1245903a5428600c1a0a42d10201c04520014440c040001000415052541c00d084892586815007000b03510408000074541012029617581d190601410104d43d010400c00c068044260ba50810811150711500c0c2d641d61520786c1004000d11882c559a4550140c002c51901140509004040c5c49204c001d800c81c1038458980400001c0068282000302c400d81b1440101c42a252420304900d000710203c00e0141a01c205159200145124840e00c91403d40c40400c8c3c0321410014141d4805480100c50741405a0b05400100f1011413031410148039540118416043c01038004e5489983c6900c45d1000b4100b0703403003070520540070030030300d503000043d0340545020300001656900d480b030b1902c0040450100d08451003086c2c0d02c01e400ca09a4961086a02015412042c40b03c2114684180c0840d08240207000200e1014844000d0890007040c07010001c8829040001e0004501000240740020807141c40f800e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147261052 1250 147259802 147259807
    0x171207030c021f0504050a060e0307050f16150207030203070f0807170d120e070f08011a1e0301020c1203010f0b070201020a0803040602090d12090f05090612100c0203 73
    0x509645482075081a0030305101500c1c004000700e03044030505010b415044029901d50001c282031010a002141c2c419601001c10808454010440e9440b030300150810f41c0c4038083c40041424015011840b4850300040300540c0b103200e424419142c2c69000703844070413402c610458102100613102000100003a1001310b202940c0d0034944580149040d0082c0c101c00081d80c021003505609140002d40e0303400503049030034002e110300340742c841c41c2d001805046400e441508c6503410004208016135486000c2d18007100c000d001d403d01d0b2a045c5006c000449030005d40113013051034200b0003010b0030b40d0940078081006001614140e2140717a005c2c64201c801542c00d00c142e20000040106603002d640c4140103000d15900740381800f40980001c3d40750085010003600005001002404120b559030485410520081c400c101c0c01d10305080c000c034148900752500010031072810300400c0049410401c8401c542c4010041200395a501d001d10800b802580350007038040c0300f16421410030781803030f000c1c4043e403d13040d600554 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147262302 1250 147261052 147261061
    0x108010e0403050d1d0f0a0807240c0e090f04020a03020f01050d140603190c12080c15040209090c06030411030106170a03120507020a060903120c030510301712 70
    0x182001b58501030204540e0119441c1400034040780c06480600d40c02020904090003000c0810b95070b030b100362a20700d114601d007500c181001a000296607c40c600250341c0040217654105044010a000348d1700694000448042003005103803a415495142d401890702c203080481303030413040041d9000c0c656444004d1000004011140c10200f05040c220070018094031f5075000991210780b00107600e4095801010351128031030042c010403004490044050b9011030b00d4454500684440b9808241d40491007041070b100070400c01400044d00a000e103000612041c40c503211581c1c2d850406a40c1420690103540703600e400281300355036010540034541c03014050103040c80b0701c0c0f6008091040788800e0180003868941480001e40d40042d444000541c8020001003465090030140e0710142039140c0d004501e410620030852207540354201c50f0080307849008001d652510303034085030010020003150340071f01c06080524469910300456011a914050303940760007407030845000b400540d4800c6010701c03a800620421b22 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147263552 1250 147262302 147262361
    0xd09050604060e0102211f091a041104050f1807080403020115031a060a0e01090e010b03031207050d1104091e0e06010510020705100c1707020108010e0403050d 70
    0x41d0316200522000b149400e00800301440300005e10501400e0300d81310940003e1144006440001940381a802000d10155640c00d00c8000b42130b1601500041278607202d0789440d54282800b40c0100803000161241c01c2c14280424071031101d9440081d60fa005000c04440d1051035048004c490184502c2c0d03480c4100b503c2c3c1170601a0075074810b40240b083d101d203085400c10106074100d000000c0c56440b802c00310441d0311604009a42600340e40c1090002e042d0766000060100541d034442d40104901000030b002000c840c0d000c0580f20b015108010884205030000280e01d503100300014409114289000240b0764080b04c20390170300d40c2164211443c2103954034046114504401e8a90b894000d20110a00c01080c03011486916020103110345406078001e01039081e006402880401d001c5e20f406481042903501048000744001c92006c400d0700c440d10f0306044000a84c480d8400c98001a4060f110700e00e080c0d18180c0580130403034006005904001003400202c0ca01007285c001c000d050000000009603510f5010b148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147264802 1250 147263552 147263561
    0xc040e060702060f010b0306040b030109060c020105151509040b1504180e0f0a060f0b09100620030f0a0c02060310050319020f0405180f0604060b0904020d1101050d0905060406 77
    0x160341303050480200400405c1011011079070b00036001c1d07034080b60000014000c680904080304005100c64209404c0e10009541507103e00c1c4145100e482c4007201070000c1e003d200700382190004090124a00304500c03845030400f500319024811019240e2140b20b42201003540c80e0343c00580169901c401c03030b6a0814102c0c080e0303020384011000704a0107801040c816102050b9100c262000c002d00803030301c41c0010042c8100e00c2e401202c0180001e003a50010780f4102030343c0809503003640101d00c040360804440d40148492000c24082c0e500300c501c005d520704415031071b005038650880c3c1e06580412911810640058072030801540c090614000c1401849042008140c01d0591000f2000c42c200921796401c2d0240c4d5034110802c40c0b05800303540c00142c41c1c480b00141010310411400101540c45030000d0398190075000110710f8440c0d07000e06001c00180b1090320030449031000581e80a07500440160131040810189915070070701c044141041890f0001c0f0100d880103031550804140e8264104108010600115004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147266052 1250 147264802 147264811
    0x30c010605040b090a050a0b130609050f0402030a140a060608030c0f06090c0423040302030a020d03090b07080a061a040303080c04051c05031e0a1e05030a020c0c040e06070206 77
    0x1410f100349007540c404102c8550b401803048040c00c1d200c030302107201081164001000f40c8005400100460140c803c0074006d807400740315801480d86410000b901d10940c15181d18055070f0b0040c003034201c4140030b850700c01035417074161514861400792002c0d02001464a00c20000101090405184c60306422080d950900040c44118000340d0404000c01141900106140313607207a0045a001900c02140044d101d500d644009004800565060511091540000c040e2500100d641d088590076112003e0460a5903082ca9004080280c050b001c9401c06014100d803590008108a001a0f00740e5a0120303800d81e10200c98900f108842e0000d0f040c800e040e40000c2065000054180c0d40e80b805180001040e282d2141295800c0c80222840300340081010a00407201040c491f036207800c031001110072110450380d01205040011039030200e801c1c2014944017040308140011902c403603003160f903036800503c00f03988603c101c0d0f4400c1c0200e1510546a075035511551003000b00540040c03e01d4605448042c2c9030090290 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147267302 1250 147266052 147266059
    0x90d0206070210020a0e0a080105190615050c160f0614030c0a0e0307031b050f0103050601020a06020d090f1425060521040b090606010c03051e04050a0305030c010605 73
    0x82090242d000100c1400c030340040e640041e900d041d18001181c00118192500c0d501105a070030018010005401680c09041c80c0c900c1880c010b01814400c0003154030713601c14075568181101501810ba4013960150010701c06c01740c15552001c030091000410046141c005401c055800c0e6070034081d02c2d900a410811000c0c40c009c41600d58102001040303414012540b40760204850641d42524035100bd2286100a41d484108100b0312003c0c805044460322032130041300d0040c242c2c41070b458860340c801d0154600515042c0c0281030051a40d44808010f50300c0342c92038828190b2a03444d0100010740424450310902c2c0904440e40b003441c4042c91180c2041a022605400c860700301e0305201c03d442154400f034003240c000d400c1a076a40e5003c00044400042e098503440e14800700351041205200c44c046c0c01c1407055101101b41e4049540340401500d110301ca40c140170300081c1e030038000c400c03201c0301010300d0b4078144180304c1d03146052541e910b0009800d004550402c68072038101007060803107810240940400350600301d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147268552 1250 147267302 147267313
    0x4030c08071b1701060f1e0e07120b01050f0904201606050a0e0304061d0907051207180e09151303170601050706020d0b061303021306030c0501050309030d020a0305090d02 75
    0x500d40684106c0c2500901c1c00c0f01d10584600c524101c070031400f00f401800a0f01900070320b49000c81010f0800b40703e02558480441c24100344401940c494401c840c0b084c0c2d92000301b5400e0010a100703001c0106007282c00480e0209c050702006d1548036000c005000d000c100b12501c00340304003152500206645000d011a09150700303142500e8680c00010003a5000c3e5040c0d4038000075444519000c008181c03516139902c0390007a901c0b4040c00216039105000300503803040f1009010b0980c640c1182256000d40301c100a000800c0d00110600166180d41c0ba640c0e082522a004c44801c41c0000d0696480c1d42800d40b00c46440200c1d420b070f500c0c10140c10420031191211201030700605072030402c00180403840703199802050141d0004921401d841c3c0350b0301541d61848094002c648030117410540c00d00070401030000740d20404d08414929142840c9009020a40e83d008030419502403070080103452075080a028201e090005004000c0351001a2018108442540c3c3c0d003c034450604110f001e081c000d09900c20011900138 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147269802 1250 147268552 147268559
    0x62103120509070303050f192c03070626010b03010f15170402040912020d0207080f0a1b0306020c0d0e0105070b06120709050103080d050105061204030c08071b170106 73
    0x803c0050440390141485690350005c0306a07945584100d02c4444407600b100300c2400046588682d00803140d00503804c1403000381d152119550344550041030707035951585c013005003807040d24031030141d60400140c0c0541d04e4840c4000b00c102d100071200241c0044800035004001048243c00c8040520700401941000035130180940e54000c0160316001c0344664210390b02c50100d004c41d22541c1c0030240315508207202c903041d0280400000d44480c04261404014401d07500040b440c0b99011030619031059100005017110344041d6280b540c01c61981000c420050f900300c030000081449030000b800c4122242700035044501001201800a8142040d403c0c1005001d2004c4000141c041a125420680458401c1c880c000c10450003072070710040b034200c189814100000002005141800792550400e42c0005100b203130388640512103030340155464000704e940180c0204010900803408071031401c0c0201c0704985000b0340c40d100c004600d89420b606003480140104200007424220100d005003504200091208a18 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147271052 1250 147269802 147269821
    0x30315011803030e300a0501050105010912060c020f07080102040302040614130506040f1404020306070c05030a0e010210180506070302030c04091e091b06050a1e030621031205 77
    0x1005841c0c94080e0094040c9200317100303201c03101c12440d82c60614007070034580074404003e5110501460101d606608040000c903040d07020300140c8040d50f00b400000040700d503503a1503907400b82c20a94856020340c01481310203400b42d60140300c40c1020300089000565103926520521080302c2841c1e010700340905058812906c942d5503000032005c6900c07003100100c1c01d5128840014010805525480e4490b85821803d400c00346420315031038401c80c0210203030742d50f5079580881a0b42c0965030300c03030082c400d030800c00031122000d00403009900002810b204590004000314512401ca40141c034100c00140500c11241d800c100c8204551030b4000300c0c80c0380540c11410281814100b500a0b806410070241d203407264107045034031184203c5060300b01c1c60024400074210b800d01070180ca0300b900303e03103d0500708044049940b500800c2103424590003540d80b1544070899a4850210000d400f140c4002c040d2035640c00180c0040e1040304280102071003041000615079481d024104805004c0301500141c245410400c0707031407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147272302 1250 147271052 147271067
    0x7060c1115160c060e0601120c05040e0c1212030c031503120d0f0906020f07140a020303030708060105091201020417120708090d0807113f0f03031501180303 69
    0x809030705040b00d41c843c1c585001070140c000104504002e100361400005e8100c0c1106070011518002c02c0584c01c4607444106200c02c3d1707484101040b015502034041074505007040020460182c01100c140c0f0341420000b040501c583d0700941d100000484080140405081d280f0484400b0100c01c034014103440e1481041c012050040c0b10840740041da030303440204003428040c2c0111a603642e1280c0119920b00f0f8182411406401c001e00944584114005451440d00009014601c0b41d4004004500716614803008841801005288504020042c4251141c03503c2d070006002a20400000144e202c0e800c0102c40442c01003503152140042e80040003050000c0804012142c01ca43c000803920750710807448010074610500c461000300172041c002180f00c14801010302c5100d400c241100c064040c09003070b1141041d6140b540843d100c2050248900a41c070224460303003100c2d4030035110144c50b1500390340700303144d81142c100701c4140c1c01c07e140b0090095015079212501c0c0c0020f008020355000124190307240107100c01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147273552 1250 147272302 147272341
    0x40e010e0a0201050a0210020d06081c0503010504050c0403021c021005130b030603010908040f09050c040b12072109140d05030a090609140a030e0603060f060f07060c1115 75
    0x1013400a0400712162007070101c02c08502410b00103540d10a41c006c0792800400b00d0f442103802501030300c0c6240115007162103041098a82c540c1e50340f0308690078035040000412010705400001807080100000603124152a40031081070f0801d514042035490040c01081010000d000d0300300101004000b514600101da80000e65150070042d40d1203903034410101e801400f6440300038007000d801040c001900c00d070416041c4242d90708040c2c10300241d122951420350345d01075401041c000c0e10b0b06200780090310907034051050b03100440b40390082e0079408141c2000310004800018090480e224010082440061000c085003141080c0080440303080c0e0140091a6000143c00c1c0e4990540350340009050002541140c0320954001c001c0071018100c036440c1d20f680b02000c41040300800ca220b208a5021305e400010740740704090140031017450754400d03000c000540d88150141c40c10300206201490110300d45114425180c521a2102d140c54540300844510f0300e01002c1c071400d81c0111b250308118003c1000780c0742c0c2c800c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147274802 1250 147273552 147273557
    0x8090a0609050c030601030b070f2102090307051c03030513030207150507060c05030a1b09140a080304030b09100204030c0e18010c030501051201050c030c0310030f03020606040e010e0a0201 83
    0x502140c0c50814100140f41c10394581c035210f60300010050090481c60b4501485c3c96444040c045030014100f600d080d9265110b00c140c01c2c0011506c01c0d201c01594001304010080103042d698001d840f000000d6240141a00d25242d072202c00c003803401003603054071541d0380000901c40381c00012a4a41c0c0c000b561221140110004041d080c0117540480b401103098070b8036280d118000b03200c110145c00c0c00400942044a104411504240e40f86441e580d000011030384010f042d40d24110343c50f051040442035510520701e5030790401d031940c00000750b03080c041c800f43c40554801c5043d1001402e0001e4418504005903601140340c6104010400c0040c1001d54400b04640c403a200203045643e403031a00c1d0819840804510025508280309031200035030540c4107034141c890445810b04140c00fa15841ca00304d5404a454405840041020442100d9400042d40e84803030b03400700a0310605c0d2030303031740707044182421000440140c0c0c480d509000030342c5440c0c0100c40210381003030001c000fa4108103208035a145c120b090060b05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147276052 1250 147274802 147274811
    0x30c071406040b1611060703050c09130213051c030c030309060e21040b1e040b0703020c2b2307060c0203060a05070206160c1208040b0708090a06 64
    0x421010500300e000000d909010340369185000d05080c0c00b1031070202c4410b40440388000f985041103000d400160920448100103050070b6440c6c43c1c050b0010880035005940300700041c88644015a40c12500074046020f1500158540304c01030b0309088001c200d50480352140750b5048641d107000035103059040ba55601440e1402141c40c0900742a8000c02e20602c01a00c86810480c9404d0505030004070313003480c0ca51034030304aa00c1e452800d400101d280940c0c0a04100c00400700302e1140c00a62020010607029203070000e080c80d19a88403515202680014411009038225050f601c0312031420070f141400010700c0110003d03415000418003d002e41d00200020000200d5007024003650b8401500c440d410203004085443c11134403003401404110303d80e2401c178030a200390302c005a40080d030790060350300610b01600108501e40700d02a22403841904002110b007004114407007003000c580134580440140040d03448000050810307007894032164000a020205110751807003882100d14000500740403a64007c0320028 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147277302 1250 147276052 147276067
    0x10020f070308190204030f05121305010e060d060f060e01090e010603051e01060201021806190c14011104080f0a1101050c1c05090111070f03020d1a010602071505030606030c 76
    0x20140880916060a050320114006c002c000c0845107980815000350201d802c200c042c10f604c0004ca00c01e01840000d1031094000800c5554003c100d2080300c11b000400642c10324a010a0000c1280d0890b070107000d508090384030821070307035030850541e6400820a00e0701451550501410100120041c4160740401d030341c95000485614100218080d0500350381026015035947c1d0078024040d4002d82000300200e80303249000c080030720305070044411044454180c061030f43c10740c00094441600d4084140c501240040c0b11030301410b02842200181c1500d00d201540f0b55082074031507403420030855006201075100b618400b0204044400303681c0701120900e4107560345d686000e49641884495079200c00356054844041403059080000b8118950082e6261074610076100da1160342d803a454401c000038100c0fa00400d00140c2810b159608480d4090b0042c1c40400c91a10700445074514241d0040340180c0045c02d040c030404800007111640500c42d4a021829810110001695480042d1074480804000240346 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147278552 1250 147277302 147277321
    0x1c11070602150a0b0d0b1009050912070212010204061d01050a09090f2901110a0b0c07290612010c0516030c050a06021e0a0804020d030905030a080c10020f070308 71
    0xc4c0c20000980711804210760303407901c00c08a00013640c41548188120703102296180c034030f108981c40707160150000c00b02200b04c01c601e026554070403401607801c045503031505070400c402400104000c5c5003030b56802c01c0303500394954038400200a1001c82d034100242000100003981c0c1c0250b0941c241c4035181d0b0009411440380070448002d209440310300040140300d0848140549124800c1c0c51014403c3c1ca421248900e065185074482c207042c00018828100c8201040300015840043d002041c0325030b034090450b030715a107200640da007083d4100d00c010740d40a204200e02c0303040030f4001958039a1810001d000608400001422602400412000c00c1d00314819800525200e5088003020036000401d031400c0303101074180310001c1e40c02610b010300480c0c4442c07040554036680604590110b0107540c1e440069880303035800c101c03402480100507020040fa1070004242c0356400c1c0103070340d02184030721100c5a540000c1501c0a09092072006520510f904c10b00140c5148600d140031104d00c280d240ca0080141c0d5140f070881c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147279802 1250 147278552 147278561
    0x903070b1510110d020a15021c0204030506090f1b060903070f0e16021b01031802041803080906090304060807020709090c0e060d020a0909060e1c11070602150a 70
    0x18940e02050b00d00c885034419400c007200c0e0003070a0090090b507482c4e00d01c00d003042e43d8460740c020004040300045800f4080c1c04100d030b805800291210b05031945207a000700d180c882660002c0c0c0090701d4980044092003c65039017005039018100850f07014020440f002100d0b180700c1c00c803041119002d1440052540c0303580d0340c01e120744005820b5100160300015100e8043c0700600400b1103150400c045203a000b040d102d400046c5507100212024012032800000000440141840042c951180e044070409130005a0311801024496024000700242010007401d00500180019154240a820480c01e02401c1003011044074160341d501c0c1070008403921801012850300078103510012105160011980400500704213040480b040f10b01d558080e621440200004000103a60081d80400b40040c00c20032125150840d00c0c040307001d1107000601c040c0e0701d8045803c00c3c2d071701480880c1150011000d00c80d165000345213956840c45c2d180c018445a070404001a5844a9900f10900030710b04050015242d00402d411 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 147281052 1250 147279802 147279841
    0x11406090117101701060f180213060f0e0a050901051017010303080f0108010b09010515070c0f03050105180c091b0d0c1b08040e1b070b15090903070b 66
    0x180307240703107440104000c0b05200f42c01804503528022030350401c1080140280e030b0070f944005a60f4400d042c80c0004015642c0104524003850326000d0209000c858000c140b03540050541d40c0354405201c0d102c0d60010303c000c0007200103a1040e8004001070203507403640000c86055070000e031001001c94440d200142c440401d440928640560568004030805500808071401090301c10503640c9140d8981d20300b182a5001140a80d822401d520b00421152030304a405000c80d640c20b0450500d004040d8841c91030055543d0006100004281e00c10030802000348541d50707000c00a00c52020301e05000c1003059480d2592400b906102e40200340c0070030307a9400c1788180e5955004000c0003071540c42a101030000041c010240909011480030341240c40c08558105c3c01c10211540500c02a1409060584450403030001412000010b4034840d000c03684007141200401c5124000c001000300380c64094a0394103801c400280c0203004404400c140011550000705564031903a02c01c003400c030156504800103543c14803504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 147282302 1250 147281052 147281087
    0x2105070f030509010807080601020a0b10081501080c0f030d030915140a05090c13090c090501170106080a0b0112020f03030a030e0106150c0b150307030303140f0114060901 75
    0x40103404258010008011110080e200d00c1c025954181e011b8548040c00c9802902507048540b113440000c168000c00c6c0e610000384c0490751403041e1100915803408406030f03007030b01c000e09441005100c01c030b40400266810b260219401e0204d403440300042070320740c104070b0020428035854480000c1001081030306158030341c505020400c02891440b001000440c2c054402458407882c21000c108403a40100d00d0321a04503001d882c0001804d100c001000083c61200c209607000244601c01142c0426140901030007000c038180b5030741a84401701d40300360840b24941c0c46a05070742d015800c980001501500600d045405d40480c40700307019042d00116540c038808680b601d5040c0000201d102c0c18a4259004080042c80c150080100c0d0b038855030342816604003c00d0043c04241005084000030702a140069403025402c0c9844000620074000b19240504e035400031000309491380c012008409200380c509900610503842c0280741c1d4034001e119010201c0c50301080d4051040040c140400b42d000b40c0b400322200300301c01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 147283552 1250 147282302 147282323
    0xf060e01260f1f0b160303060504060e010302031c02071505090d140f070b0304020603040c0f0e01060f08070f050f040b1201080106050613051e0603090106090c050403210507 76
    0x36084480c0c0b42c008980300ea00f03045003003080d1004042c0d1282c1100580d0340075004d8a1420002e528030103004040b00340210300301921800003049540321400303640c00400e0030b060214059415441094208004500e60030000c00f842000d07009250385c001210800c8800003061000c00c0c10100300115642d201d0907141680050f00820068104032050988050f007410384401d4a4180382c180c29a5526500b4520518403a607009201140151030480d0040d0740040c460040400c440340c1d0b81c3d4008100c1345180d0305c84c0e0006080c3e5001000f0b4250002880007926060349003400042c03070700b040d000e000102d8045408042000104509041443e0001210050180c0e9417007161035003d4110620030110090007200003030350800000180c03500304541a00d21178079507055042034040c00c001c11b21855011803031803130100e000150424115610341000441c043c00c410304c00820300d0750070000c014050b180da01d0030b00c00400000300b2003000404c641c01400c00740c0803007904041c0114801c90700b01312064080e06034081c0c201d1595 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 147284802 1250 147283552 147283561
    0x108330a03061b02010615170c0403020d050a021c0f1709040204030609050712020604170307080c0307120806030d03020d060512070e01060e18040303090605070314010f060e0126 78
    0x80400301c010307100e413640248500364035001c40b0a44044006161004210442809001400c000d05030a5000c04440840c5061a590f40c00052102c0f103042d5098545820041d036800c1907041c60816107903420351520300340d0746120442d0f0354002080ca09410150039401c182002202481c0c0d242c00303c500303d22000304255120703502c03130501030300a00b0144400c454902c5171520004180c404180c0c0a0700180d0020500ca080c81e20b00103103604c500c10880d00340c41d114002040700360009040300010b014030005c07110045488104a00e407100d04132262118007001d0101400820002e603400050000080f000ca140c056114051998400c01030407042c0c21055000c0c01c0c9000d42e409032500010280202c0b0302c1146654110b90382c4013400c0d00c24080c0103250a8020388100b185050011800c0074a90300b0070320902d40011402403980340c2c1d02c11038005480050029840760024480c0d00703c1030f10101d014104003098000003518264020380302da00c4c0c1117002d505110612400000360790300080003001071002d44080085ca40b61 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 147286052 1250 147284802 147284831
    0x30b01211218170606010f02010905010507170a06051c02030a0209071812080906071113020315090c07020f120a0302011b0507020a05060d02070807060b0108330a0306 73
    0x34442d212000d42d0019080c00640001d411410501d5902e20002418a03502e41400440760420600c03048010366485d07203d20b4000030801d1190a12030051583c070121003180d00700e0380c40b14107030000d41500f40d5a41442814032103070351100f4513440310058003841510502818404242025403c00c40a540000c0420410410940052401ca103003c107c525091466031600c00c0c00c510301d001c490001c1c001c0502480031a81904080005184550049400c1180c4d6a10040002c003140c403a9568422041c0d000320502c028031142d00310000c011101182ea82c800e928000ea00c2800764064610041d108006011001b0016150038405411090212058951813407084c00c0103030180805400042c4032070055021421107030311540030351b542c60383c0c01403102c651140703000c1c104074041d0041d00459405541c00c1142e14001180c42c4000d0400c0e40c407500020400520200014184100c0205480440900411a520080600b2801414150136010300c20340040c5000c2c0824402002e40d0002040c482c50f200d00001c405c0da = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 147287302 1250 147286052 147286067
    0x2107080c0c010e010e011b09080d0807031413060b0a05060702090709080307120e0901080d210c020c13061d04030212071a01090e0c060702120d050409050a0501030b012112 75
    0x40d07c1200d805504600b0078000c0350394006920030300169401442d0040c40300740c0705402c0640c1292941c5004120181c400802110404003900c150700000c0c81d8189a07001c001700d0340511b0500413030032a620030b070842c83c0c4000f0070110310401c400248501284c40005100500640191001c1d0140e0412603840d06c210345046014081d00ad18100d0114203000b290031014540040d00078140c03550768010700f00f810718100054540c80d00300080410030882c03200c2d800074601c0c00c40c0f01d801c48941c030644c011701246c0c2240d01408102c00035007103038000b220f0400300c041c40409040032200c41c03684404d801c03823072103035644d800c00700c0c00c0c01400c0c1581c007401200001e00006000035201c1c003203030041000c0100c07001c81e43e803007281404407840b440881c03100d070b000114110850728110f00545829030014010000e906d40c2403900c20b0405030031030b12200108001182c02e02603c540c512072140d101041d008100219419622810000c3c10148600300248204000d01b003542c2d4104000302d90900c0d880110b403620403650280207085803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 147288552 1250 147287302 147287321
    0x13060c0204090c1d0a02030106050703030e0a05100f050c0301080c010804030c0c0f14010e09070c0c030b0406020a020609030c0a0809060c06010e010501110109171e030a022107080c0c010e010e01 85
    0x5030144c0f01280c5040010700c01c807030403540c0b1616018581140b0f0f54081d005072a00c2d100400c0c1130301540d0324a1011410034002488003100c00c1a0020b80c4060f000c2450003291009800d10450320010b000600c14004001110001a07a007420300c0d0b6036545d603c1c41c04440c0700051100c0141590364082c00000c00b0183e1002030000d94001322804503c1c02145001110320700400d101c2daa07401181e031008a0745030350050740103960050088042e81090398480d100c081d00305800395400c8450941c00030302082285e40c140301c0503030000c01d04d0300914a45040c0718140d60761000da6003405000c1c0c1000003640000e540d00c560490317412150b40001d5616030760351040d81d840911000d10540340802c100c00c600780742c054418460788007601d40c0500702044100200000c0c003070903085021644c1b40030110500502c0342403100c802039071040b45040d07030140e5618446a0401003030740030a1070010740c8280b0b0030b0601c101c943c0c00064407640002012441500d440d10b0400751405044000300b481940c0d441c0c44641c2032254010340011508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 147289802 1250 147288552 147288599
    0x30311102405040c120b030c060f040501030509150103150f09060c03051803030c0304060e07030b010518070e0f150d050114060a0f0305041a0108031e13060c0204090c 73
    0x1d50b40d55070184000c0c1c40900070350200080310004000c24403012a4011040414050202c5e0b420075012400315040790f0000318124141e07000440d04000e1982e16014542c0c0c4101150058aa4a00b400350640e410481c10b0200500402d102826038a07210803552060f41c2c0c00c0b0507900140021421800c00381c004010495200c0d00081c1007400141001030305041e03498814030340380c004610359950094a680b0313541015104461140c0c035410712121100080005030041c50003641c0c480b0055250000b005025003e48032003000e5603160f001000780300e9400085010400c00305566000d042c0003004000382140b030105284040030540070880391800c1415a11140c141c0d00b080f43c1ca00c00620201d03042107524041e01c1d00080002d00c903204001201e81c401d030411070b0010300c03d0070741d4000101c04074050251402c00360001041e5610100788940306000d200b040f003000702d40c5002d481e031408180750401c1e0075501d92402284244812100a901151910342c0026999a04105201e1480b9151942200301c0208a05032014 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 147291052 1250 147289802 147289871
    0x81b010c0b0a0905010b0f01050d020f21090607020a110d020a1a0c0c060c0309060703090302060703050c0c040c0e01210204060207050112110d052a090a0906030c03031110 75
    0x51405c221f402080314035016181c1e1407c015505600002079400000c80e4034820400b4000d00390420b01c039a024801120106000e51401d180090210780780c444005e246c08119031201010034040351609060205842c0103503202c0303450122500101d9844549640121a036010192018540c014600701402c030101d2400140c586141c0403004004181c0034494100031640c0041116222510b4150001c294040c481d040c10900b20790340e0f400080480e0805002903010910000da161900752085c0030440825408560801c81241415002440c40c170b001101035050240765a4a801c03e42e03c40a500449030b0b01014003507503540c0d11a103000f91181c0d0305200b00c0c0d001c2032910444981c3c52034280030300503042041c2090715042945002000000e09009000458111082c502c01d5400e52890a040c402c030782807030070781c0e1940d0701032980030700c242c01d0b00c2e80d4803110400340780c032809000003246203401000b16901031030105001d200700c1010320300740310b510140001d41603e42100441c40c003003800c0510b648892032404016 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 147292302 1250 147291052 147291071
    0x207080c0d050c120403020315130615090501052e03090c0909030e010903150b010c021306030b1006020604020603041a0906060a09020408032a03040e090d020106081b010c0b0a090501 80
    0x130711030145000081d8150012020b80d8601c900340b606451740800000668000c140d103944801e82111001d514800c0c4401c810201804644054015203004007419a90303c140464032100c66611000315440422724110589010900144a60000b040d038075000600002d56581e61448074008145801c001c40209140c0e2200c1c2c810303503000301e114208a0303070043d683c0d140604011303840c507000700803022041c2c1c1800300030035a0707c000d40c54520118407104000b20002480341d0543c01c0034404407500410402e001d1400e01d50602100f5400700311190060f42c1528040e40301d80340c602d842829110561041542e00d80340400300000c070703034001540d10b01503038054a041c5201c588880550084c0d01c643d004400855100b0042c01580d401c40c100c48ca00702180e021243c0445c64020104103045034015401942400114000c0c046500028044140a00c01a000800086142c5806140c8a0600104480d25204084c18088507640030b1400c1e65003c3d6400604c5004510700024558020400b00100799550762801e65600d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 147293552 1250 147292302 147292333
    0x302040e01020f031f0b04061d040b010c0308040609080a120f0207021513170f0c030c09130c03050a0b0a0e010903210e0604110907030204030201120207080c0d050c 72
    0x20b6542501c2030341624955500e803001152402e46015000c1e181ca0f40320603001540c0d42d1000b000d000904950750b11141e10b05003642c503104010380c3e401c84039841144bd10a050103907030380018421700041e501d414139131483d0356a400d000e801081c1e181c0c1d01820401001800121031a84401051202c08424400700715505410b03505200f02d01500c00025001901203c010820080b6100505400808001e51050f031984a00702c2242d10b07265250300c8c03203d44d8050b1842c440341180500c60f0045021054004004403000100003890b1208040c001100c4c002001e002402440201c41029001d540c206040302e48100c29441c044129982c00c84032050490301d80030000d4202c900600481544079059a2511200002c502d8802c1d0812903c108034007000d030380c0314130303d200989051202e14452800381000700c0080d101f050610004560080080b810148100f00a1005070f800041030b80661010550060700c0f9035007480c2944140c07003400440e04043c400c500e05540b4031381d8000c0041009141d8002034424514410000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 147294802 1250 147293552 147293557
    0x60f060c050c041805070f050a05060f0a030902011101020c1006090516050309011409060601082802090109270e01060501080c0a0201090209010b0a0f0807021510090e06010302040e0102 81
    0x40071600242100c050514042d000780b0a01c070181c0407100400c0003541d8605140c600d166020380d104d086a00c104110615040700244007e00082e180ca0b850154181d1140300148902c2c40d4080070b06988074080419a4031405180002c031303440400031541c2c0d04920031007940c0c500411780c0c6d055440d0304210021481c86002d024040c05030140e2110002c070031203811001c4d42e094100074088403183d90b981c035119051210000240d030092565201a04c6076040c44800100b4032030004100810b8038000c13a04204480c0202c2c6c8207820524070358040180c0707882c16240103c0e1450700503403100c0144034900911488514003413504448501c803020040103e0ac0940405c1802c1e50400d100e01404102e00d00c0002d91081014001003a96070700074400010780000070760020b0340c2130300286c0107210b07400ea0100d03030b800310b40d03401c00c13440c040d05c801d2070070000258070740300200030f545c0d92101806450600904002c500200c41040e06c03240540342d802c4082c09001c080200311a55500248000d901c241c0c240348050b45d0302d0744103108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 147296052 1250 147294802 147294827
    0xa05060d05180a111206010e010b09040f050c1c0501060516050c0a0b0d06081207020118081009110405060a03080c10051305010509070b0d0e030715060f06 68
    0x1140c0c10a800c03594054000e0800034500006100c01c00c040d0640074800384200140144100758201c03c2d401c0c0700b018050107080c808104a05944000c0040c00540c80c040346141c1114410000c040c0d41c1c03510301001c14090700d03400007d1118103060406010907001580007038103501a441c0c11203840c407901044503006444003071140b000400c40c200020002c0f26a043c0031104100c2c001c6084664481e10072000c40c01d036140640c0140058000403031004008841806007a0041025070002d04007000c140a01017018840d180d002410b024401c440c1103820b415680c401002452100e0a40340600100344c4804064200181c0407640d10b120a10304040e50714040c40f440e400b910000c1c110500e12070031542c0d4003081da8010104080184a00c0340100c2003d0800e0182c1031041d078011000f10103006207403400c903082d41c8000d4241d000302c1e040f4071024815080b100055854001d5160000b040000d18482c8403811407203082005070484524180715040c445c07080d0032920850b600da0050b0010b5030364502c011114400600d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 147297302 1250 147296052 147296059
    0xf070f12020a0b0c0d020705060903030106090e04050d03020c0c1f020106061e11150705090a0905150105130b07061b11030708090f06070c0603050603030a0507020d05030c06070306050f0a05 83
    0x101090820131500c024002c0d4444000e001441d020143c0ca946103400d0046410b104a80d00000051100316401459a4010700c10000320078082c0c00d1650f502038480c9030b0344044408040d80030681c10b19840042210100b0440c02401c4080808100c220500f081160395003807401641c2054030001d00603100348542803130303040342d00d10320704000d03000581c00c0359481c041034902d0700180300704203000c01000440f81500780269126100c0a580e036218405210054443e40d101600052400f4100039500400c0ca80661640f030713091809603940c000d444d206159030300a64100203040f1401250a01c100300f0954800224170041300801080e00116102c229540c404034082d5242e10381007070141e000002c0800303019004080000317000304040398108020074101d402c20001607858540b041d030100030080d05440f5041c2c20030420340246240100501c809842840355200080c01006882d04070810300006005640692315a0425507440382029900100581003074041d40c0e21403800d05015404074940040b00004490014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 147298552 1250 147297302 147297323
    0x3030e1501410a0f06120509010e0d05030406050a06060903170405060c01020a0f1b081308150f090703020d0813051002031c05010b03011205030f070f12020a 69
    0x240e1040c0c014140b5900780524108802e905450328040b42a034a01c506055032040088110100100600501c103540503452403455a08107028480e44811070319503c0540480200d22605c03615001e0f8010721080361141120300403602c1790182242e12500850060380030710002d100f140c0b200c00002084440c14440e1a002c100c04007010400960341c1000f0b15035074000c5000c940c0c100b96031100416801e85c0a0342d2000e4640c1d50000b2080c0510b0f41003e88112141100e1800b100e940000010b0161016440000074092100105607a11104002c007a0354002c0c0c00490140c902003040c049043c5540306055601d494120710290000e842054009a6001100c0c0c0003800c151200d80f06032a20a40341c0c0c0511058800c40c0f05404010680341c58568004001a504d603000710f41c2e41201198094014880c40e4210851a051030010011100d880040d1f80c1581d28140e10903031082810324150b0b1443c070606003641010400464050300344100034010034841400b0724001410500c03e004d040740c4030628a0001400219030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 147299802 1250 147298552 147298559
    0xf0e0a02120105100507051204081e030f0c03040b070c031703070f0518100503090f0714040507022e0b0616030e030a0203010504061b0f020601050108040c0e07020a03030e1501 77
    0x5080d0b115100308217061052400c2d210b0340303515003400143d02c04400003103c000703410004100b0402c00c10034074071400040d1402e1004001840e03038580c41003558640e42c1c1c0720b0101c0c0706003100e141801180d004042448007696102c4144c0342a1041c486144425103a1240c0040111a507200c1441124401c500b25a41c0c40c480c6200080c05580360b40000041c203400c1100c003141d241550b281c808040342c1c00c0c03c054850b161070b854003006041c540701c0c10441d007001c2a007202808001806010300034207101e28040310b0104895545030000c0b403602c3c040e0050b0040c0c40326040d121211101450f01d01034541b4030000024014205000217115130b0b442014101c482d100f0941480c900407034030a501c0e00b1803010b00182504d00c0000c684d0002400e403142550b0503104c0503920340303443c622244d102a2000d442070302410018464900c04c08044d4480c0014418203050000b14000601080407000100e00070b0219007049160609000400130f66600b04964101d01080c6094081030010100240c940c2030080e181008038856801c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 147301052 1250 147299802 147299809
    0x70302060703050c090915030f011a0405070302091e09060d0803180f010e0312010f030302060103060f1b020a030806090108030703120209030304120c29180a0f0e0a02120105 76
    0x8044c240091810322840e8603a80e14022040c0c0101c52041e45151a06111020142000c0e40700e9a8010160324040ca08100803149021424610108450000b615580c0c0704082d40a0310498901a51000312402c2100e40301200180d0042600c10903502d0007040d54902c024480d542e2845200600500b1050000805404101c0d905010419104081e00c00e403ca50345200b41c29610314010749109500003240b6448010442d0038094010a120103504400c41d01e9900d01039103c800c10300004e8074031611018290720700e054a82152401420f003810502c42e0110303400000752104120303142100026110341c0440d90901d09a00728506944141001c2d5113801d90070380e410307030301c40a0120810407226024041c007030440d80c081c00600010500d000846520b0011403401301c006c206690066681082a103401d4240c107885540056030300e40000c1e0300f0a42c0d45441703000c0390055080e03500e5202e40c000c2c035403d00815030801d1003d404048900540d080d00d0b164480754051400c0e030062416110005802c1c00042100f0314 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 147302158 1106 147301052 147301061
    0x3070342090c0c060510050904300f0f0903020a05060a021009061506030c0203040603270804050a0801020c0303041101180801090b0603060f040221070e07090b070302060703 76
    0xa00341800207200c1c200280c005040084100c001c040c04019031000ac03640018815000c0c5040f2010322002000c0f8004030602740300107840107000d9130303946020780030072010303280e006100105450800c8144080c0d40c001282038800c602c100c8044d184450140d01c40c880381d00c0d000e1000420706141c549003084005d04184d00100c2010302d44858880802c0d0f010003a181520082d01c0c000c82e03020b07041c03030301c034400030b401003c2142c0e410003d48424800c00451b10014800ca4209841d010741269841c640b0034200d00680d0304104590300100300007400508120031810107600e05040000020309e5242281d00d446201c1c0c2c0250029a40d02c1481c1011b020012050382d43c020f40843c0204014500700403464081d003000b400081c01800146401c04030642121040c2d98028200000c0780e080c640d03580008200000152045000b1400081c00407481d42c1c0c0a0302191011a0190014421f40d1500702c400c60017403 = true := by decide +kernel

theorem cover : BRFrame.Cov 147122302 147302158 := by
  have h0 := BRFrame.cov_init 147122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 147122302 ≤ n) (h2 : n < 147302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
