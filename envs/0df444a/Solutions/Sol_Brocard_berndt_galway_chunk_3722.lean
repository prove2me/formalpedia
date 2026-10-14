-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3722
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:29:37.012602+00:00
-- url     : https://prove2.me/submissions/38305345-cb4a-40ea-bbd6-3ea2d26b984b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669244604 ≤ n < 669424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669245854 1250 669244604 669244637
    0x1e07050a0c1a03070e0405100302041a091b03130c0e0a050f090304060e060c011d060a18030c06050402012303041a09060112080904020d0e010608010608100203060406050a06 76
    0xe206942d070048141d400d1080040e019002824440705150032a40082e055a5640090005403071075003019400c140351580000052500c815086201201282d1011300b0341d561080300076500501c62124400120140041000707030f04a6014040520f114070f950b04e082540b81c0381c186000c040226070000032262940c00380700d5070441e00c1180c070b508084002d020b9403402e42440006170110900d035070301a000c1c0c14000b59400d0503007401e5108111078a40304d89030000f0305204203800c0350f07175034016a4071120451410603440d1030741100c0c4a090460340d500d600c400000301c0d40341e00c5090003020300030000e81c103202c01c404c080c0b4501c031600d03009400b84400d1003988645a052505282027540f084102e030b078040d20380d50000c0c4024014000b542d00c2c11540d80040110074103c080c0b4040c081c0e80150403105070403500108250003001d1a03078200c4aa0407500c4402080000d95404116082e9100d51141042c1508204c8a00c1081c41c2c458004540c4000068800b0038180d5a9502041c07000c903e0b64420000200b00842c01e49820 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669247104 1250 669245854 669245879
    0x90c092421011e0219050f0f031e060d02010f031d072606310602070c150f08010902090103110c0d0210050903090f03100c0f140f1e07050a0c 62
    0x43e40c1c44034214100520001071600d050404d1000005104001c80d1642c4c54004900884e42c0c0c00f0a110b205644178249200c1c64461102014044030407000e070440017400c40d0400e4084001400c0d016136030841d0604403e1010750041c40301c2920110100f11a01a0304620001040644001c0c405412030200071124508500c104070740c004188400b5030001401c3c0040101821442080140a140b440d1061540d1020050f640d07010200010019400400d868042c440c4401e01c11046518440200e188840d25039000c645c00d810b1081c440c1e001c1240540140114915a8058200a04181400280c2c0c0022120100c51074009013030120702c81d44048216581650305124013418000700240c280014100380240584034001c0081c440d0003041000c0c0c00c07040941e41003001b074145440302e04003003195260308030000b04014040b11954011440701e070040d644d500040800c0700d000e840c05442c142d00301515071409004804144d80c4600c480c81091111001062051080003902441a2000803c49141c03043e030402c403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669248354 1250 669247104 669247151
    0x1002031b010b060f0f04080a0f02090f07082403030403080a090609120f170d0603060b010e130902010c12020c030118020609010309031b030305090c09242101 69
    0x1503410b256002803940c6460701038440307101461285946540703200d251040d80e40201d5001510030b220340144001404010815041028000d071030a522941c1c400304200700c4804142d07610300000c0d86030000500100429000c030594080f2001d01203c0c0c40f00344000183c55500f007170b0030a41d5907030000540440e11642201c1190014030490400000b40d5140201d5212410b4000101900c9404d044440c4002c000700c50381c02c80c000224028000ba00c0d180c54000f10700007000240407c6802916010303500210390b000e2813488500040082c051200940c81400c484042c200021089040c040840707105e80009485004900d000182e41d4010001c081035141090f0030344841d0011500c3c191003405008002d03885800c200c980803a428200455914640e1500b10b450702d0300080301910306080011410101545030708130b1400740c0161402c91b6041c030414810000500c1c0113031910703241d04101e50b40b030710402d174440b0407400d08041004015202450480b00394075030000824001135541d035540d01040401c006201844641d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669249604 1250 669248354 669248407
    0x1506061101050a0c080c0f1207050d060f050609040905030c0105071d060f030412120e010903030f05091e03120a0c020d03060311010c051906140f0606180609100203 72
    0x21310503c038001421a440c040e0085661450000703882c000300d0a0781c800c0b00d01c1499080340d00c80b881e1034500e0000340290028010b4542c41401d000700012400070381022602520300003402c841c9000050000c100003400c0c1e81350102c805000034410380d00c0c013110030701c90140302d10f5003030715405d041d00309024440300340301d6200b04214071480c0300b48900e40080003141c064a521035480080b41e4100c00c9a18000c0e5078080d280d03a0554002400e00042c070101107419001089014404e44040c081d9445210001007907031800c9a0100c0c8541c4071180801260790044941040f00359040c00340c038034005851038400502c000c11111004140d41324042c0c441d030903a0400c03402c1400d50307451030b042048034150340d41c40301d003400200501c50420110041850500070180280201a0040d055880d40c0c0035580c82d2040c0030b010b12600310340e9200c410340300007203100d0190915280316180043c6520302d40096030362810b1691400301e50507078002c10f00307200c80c8100342c9500d81500d21b0641107800a54a50f5490100300d0759046034007500b1030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669250854 1250 669249604 669249611
    0x110a110d08010b0a08060d02090412030b0d120302030402210303010f06050c06070e27071b08030109020304142b0c0b0f041b09020901090b03011508041506061101050a 73
    0x44603081e41c0341610f840d03151a145c01c0310152103143c0000d000b00e08658004e5804140030040c08100544c950340082d00f0002c58805116000b002c80800002481452002d044c03c0044000748445601c42c1e0300459116200505441c121251104400710a000c09485040746a0002005124a020700c803c458018011450900d1901c5110a4595210302015000d68240701003032141008694403141e00050420050004500e01001e00c02c85420805058402c04007140c55140c1c0c1e4041003074443d580c44000e60300610028a181d1820007540000d51005109480500200000d428032010901c071301d401150201c1000c0f98910220200100d076801800280030074448500103c90006803410b0b0700c1c81d4840d260a43c03400303d540d6181861032a400c01200d81129000f0704200114428001da130141007172050a0703842440003611000031412900c401e0144030707005020740c1c03000d0700081c0c4901c4103254498402c449582203401c09540b09015510b46c0c1e01315a010030b90020320850020024401d003a80171400d2801403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669252104 1250 669250854 669250859
    0x60b07081c02040b190509030a050102040911030105150a0315090c0306050105090307060c1106191803031d03160b04051f0801030f11031b041a130e01110a110d0801 72
    0x19030b41071140d82c00d4444001700d0442e401000034028420f444410001409941e00c175001840d100d03000703600c64003032610014500180a038000c01004166030589a015181c1020001a6403181070300340c0107828010704040d00c440c0c04103050213043e00400d00038150003d0209800c1d40d500400380070354542d03401c4641080010301c5114050755002507610212900f500740200c04604030304002d0034482c1400a010341080e030000b40144125402c103000c0124210301e5031007040c4403401070101d0358121050f1002031700041d041c105c91091800c4e904145508140010300303c8a402041c1383d80f400b001911a804103d02c010081001c2045080c0701c40c518030700200561001c1c0d5642e00000e00548800d60600000c0c001c1004054a0702c200840b070500c4031518a001022a0b07000c0c44005144070940d00052629802581449804078500140d80092100e10000400c480b660001d602c0180004000c0e4080f0307003000d036484406102102d400200209924105640c0e044000413400306aa4a000c0d0300400280c108031548004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669253354 1250 669252104 669252119
    0xa030f030f0b0102070501111e030307080901021c0b120d2705060a1404030605010e040303110702031e010906050109020702040615090308090607020301181b27060b07081c0204 77
    0xd07242541d5003400e09043c220b0890104034609401840403002d802d0380889c41c0007a400000003d140b0590260361500700320364852181c0b03401e0380982d6548a02c121181001007100c000107422502c0102c502030b0a200f48681c07401b1080b407900b540c4d44411300100c0d003d03c090610392280001c2d05920b190a1034210081c0301d10f4240411030782e1081003924810030018007070407441c03010408101d400858205d8000d0080b561903542c00e0b0351580081d5001c030301282c5000d88120400e0501c03000e4815040c4c006018051171214640400d84100490603002003039541c5001004c0000d0551054601804080600689800042c8140000c507411900484c1c0ca05a030340310317400080c1e9031290400068903071003041c40f5200e003a00c4020610901270208000d40c194285103940f403007041d040381e40c1d030010f50042130b03002e084429804180544070315900030101a00c40d0720155130841e000d0a13144504542e508080005c21070380e55012066550003071201115400c41c0020728120f5400300d00300320140615540e008610702032070000c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669254604 1250 669253354 669253363
    0xf051908030c03130203100c090f260f0d1d01080103050601060c0804030f030c0b1b0702040b06131d0a0501050a06030e010e010c0327030f1805030a030f030f0b0102 72
    0x580901c0c0b45002000a50b98455880c0d2905541d60250407600d1400703082ca200700140c20f4000d480b800107180403070001450924a90058100c4140b0001840400380d205200c80d9002c650440070b02c42807040d0461100100b038200500612502603640d0000940c010b0b41c4900e00c100c0c0d03506541030403c18004014008504085140f07811500c1d40d080c070b1881c05500d0710300312025006990000c1e114204001100042c950400d88081d0350b03510400b44004640c0e260704901070702840351413400724100e00c00c1c000d01e0b005007000ea01815480400030401400c0105100101d00c1103805a08140c500a41071504000c00769100c140f88d40e000031035074400340055070600010517101c0009108510406480704441d081c190001e500908000181038028400c184603040c002d80a0250740d030170340c030100000803445051640f0000110040603810394425840c807861b040c04881100f00345244c80c50084503071000080907a020802d0311101c41c0319844441c0c0d155070040000c0c0458880b0b443c0b02d4001814120040301607a07000c00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669255854 1250 669254604 669254611
    0x24090f020c15130203120a2706030f060e070512090708060c09010c1a060a060503040506070c14030319050601020c21010b0603091b010203071a070e06070f05190803 72
    0xc441010b01e940b2400011034242108802942501941442100c0c00c1704400c01090030a1850301d941d400700201c0941542c2d41007211807400300c20781141c0c20500c000b6100360800c01e0806107001c80840c0068072200740c80880002a00d481001c551700180100000089210b240d80c05000a4043c0181a140c00c0780c0d580c031944000c080e00080038000940700c0c05680203001c002091504010130031408030380700c0801c581030340040d194a4460380140c0400505207110744120307403060764004080d11150b114a10252814002043e08841b070440050100491003002c00245108500c3d0b194129804030280d01000e04546002d4050350443d0040d0041e0340346501c4018182d58280c0020008604400c4940c000314014103c040c1c80781c1e0b02180010a009a0510004070191104c43c03d90141c5001ca0600d00160307924400c19100601402600c0310003800148000e40490740102a4107080303240c2c50f070340ea000070441e5100d010200c80132003400c40d1400c117108040001c0360300d5244071092090400c0d2aa01c3c1c1030308600004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669257104 1250 669255854 669255883
    0x110105120f07120c0305100801020703051801110a0506040201231804060801060b0c100213060c0c0306020406170c04050d0803180609030a0f0c0f11030124090f020c 72
    0x40b0b08514030410303200d000e407844604100301c0150034a4009020b03244c103607a00184000210004074450b82d041c030807220581d9054558a02d000c0f864010001111b2900c0c1107141440a00550485d840500340030460303c0504c1580903100380e03d014800541003455013103c01a05030f0104800c0d8081c1e481c0e440c1200c1c1c100c00101c1c900c0100310312440005001d03240ba9007040c00d5039420240c000860f1101c0e1030161020303a0414040d15281c075000b1118030300b00d028114601c42404440c41c01000303024024100180c2d010300911485c15156225200e107800e0340d000c3c0d40035030300003106648100604451114580c1e001000705000503d060b24207000590382a80ca01d8000d8000b40000010074512945800408400070700d9905541440c5400c1d60300c0fa4403034015042e00310201da030698090008030b1084400860007503200e40e4400141403561904440b010301c0502d210380640d6607840c1c100c409540039070325085203440045000c540505119241e420b03904075280c0a246070380140448040401c0101d20744821035580c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669258354 1250 669257104 669257131
    0xe15030a09020613080606040c14030c040308040e090f0d020c060c0a02030724020d09030308090c04050103060605010207060905060d0203060112090c3003030e07080102041211010512 80
    0x2419190002000940d4000f0340c00040024605113070301045072400112400b00003910100c0d91175000b48020b4451440c603420000d401440340040c244210000f4580052000c20303403508007512aa5480b895038441c2e08081e4141c0c40c20020000340c003030308200802c011003e43d07024250802081b1006550340d58805500d500c81d0308041840c101000c410804100155002030441e90030542e074160054003048055011031405c101038201803040342c00001c0c024880c029542d1580400b07031171038a04a45641340a4a052443d0094040700d000e140e8490080718043c601070f000000d036241c42c204c00a407904015a20050600100c0300040015684803000e5840a00d102c0b08007503175030f9946800490b40d104180c068a0581c80c6042000000c8c0001900e4080581d10078200b6030804140d03e003a07580724030001c1141ca40114400e0100100042c0c420342015010928080480c5c4149031034600b01800d98101d0780101c0840114030040b00c1c14802c20b00f443c2c6010f44000c5c200b25280407901522440e01c20b5008000c141034999 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669259604 1250 669258354 669258361
    0x40506191b030e010f060902030709050306010305030909070e1801062a11060c03070f06050c030105220e030a030504060b0d02010212070201020304050d14060702030a0903020f0f0303071b060e1503 86
    0xc00e4100b800710028082c4108417481c7c981502c44025001940d000380080c0c00b10300d002c079441c02c00241850503260040b0085090542c403408000110000074151804c215000c01c3c8a030b81900c41d00081720f00065200427950884d0306121004001d0704e41e01d0016040c0552001000c2c1190b240c0501070b003075941c0c101d04103101251030440415424407500d118501c45110000303250051100c100341080d21548520814461074480c056120f540c0e00080c01180c2e48000c99582c0d6554002d1460180300c40006d00c1d038404a031204030174000c2e500310b400c0a000341010a03103c501301300400880b8450090080e6046070351450655294000030f55640c08840e402001210000354142568002c00541d001008000c0c080c80b122619403601640d411714543d6059914030804020809450002c42558420000355580c01c002900d140c08201e0300100d00c4000641100940c22084002d48080c001041c0d00c6020b0b59141000001040300740800401c82e03401042000400c10bc1c200080c0e441035003515011b1178a111041e141d88 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669260854 1250 669259604 669259631
    0x1051c0503040b0c030d0b0103020a081909150e07120b010e040312180212010908090d15090809031c050d0c11070303020d0905151b0312040506191b03 66
    0x41030350003904042d800412000c5402c4000401048502042c1b0014001c03140d0890040d810303405490140c0010982144c00202c4c1c61420000110030029089408a10141e580c0c07210604405140704a154490702e55803812000c100c20050500203003c8044582e0b04011191140800e080040c01a00ba038062900080342c02e03d485071008410303a141d102c9040200e9244210001600c001c905000c80c000d002c0000f10300d004030410700c201c9035607603042910103103080811400c02640c000b841034102c034408035195202e101440184184100988120b0046940c1c0146404041c50205007503080c1c201c1a090100c00b4001c190300c48280d80030307030124040c003240e48104072a00755042880300074640700502c1100400030500d5400102801e00b81001d07160345101039201c1e8180080c600d0f0396042d500c040d84003004000d41e030900744c4400500452544003980d00f0f100102c000364085101c04c0d142580d85500c20000e005401d1000240e50301064143c0074100007007a0800e039007050515803440b8079001c0c55640c0d0792003040315 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669262104 1250 669260854 669260857
    0xa0f14010b070303051e07020c120309030604080f070c141c030c0609020109080d09061b0302030712020304170307050c1210090503041205150105013f020304060504120801051c0503 79
    0x240811b9042c0d00038602104000d560399000f1400074410044406c03c1d03241071001004488070303504090060070b00d45e0355a40702d00d0542d13400320840030303954441000b1000c0411404071060020300a4171b20f800c124044010200510001e40f00c1481c03c1d1840c0d040710800001760410039072003219900c84000701d00c1c1c01103800141c079500f255a0200606c0c1c040c018003240c41c83c0e8040201400e88104d82c0740c01c0440348010344542402d6180880040160307004206040104440b40c91a40d841000c610407640742503119850010b00c81d0700e40c0c060f89659800400d1860170454280a408101c1e4420745000000d42810094541c0d80c1ca01c1070345005205d07a4030110407003880f009008803005040110021403800400345481c55451424001030a01440008000b240e00d43c890b40389140710551440c4e0b0900f0300380e00b4010f0303c4103000c452012140c00344d400c04200380c1c0303c60315030019501c264090b00380040c1526044c1401000e04c40c04001d20010401940018003d50740d4a6143c280000740600c0e400120580d146070141c40c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669263354 1250 669262104 669262141
    0x6060b040b0316080c0a0c140d09090b01020613151b1106100b1b07030203100609150b0406031d19020114030f07030b180a0f14010b07030305 62
    0x200400240071602580c01d2000350702800c184121880d9000c1d01c002c080721145001d41d1070b00c500300801c00c03003c0101c03403240d152610600d01906c003903d03004400000040c60205005001c1000c40c200c1c1e441006000b489220b80a80d443c0207002610203454649592141c8141e03002005002100f290040c04031441e142d40414071000c90200e240282d2100b4503c00b504c01c0c900e11020300514440e10001440b92000c410070074040b81c50200c0f03401d0034038031054400100384200c00000701c160b11421100002583d0b080044035203030341c681c50001070054241480c04007910504241d55400c00000300c1c0400519803a10102d80c12104145000629032544096414082d01d000f41c88003c43c1c854449580135180009840c408080d20036200d41160207210440340e40e16000c21948804610514000211a00d000e500301c03414240006011000c00300d68952a000c8030b2000340c03103151009a607103811070f40c042c2a40c459880c0f803003040b50b8810402d41c0750503c2802c441c841c0b0f40c030003000c054941000c19403200c099070f2402030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669264604 1250 669263354 669263369
    0xd1b0b040b060a090618050714030717010504150e060303040e160f17061011250501020f06010306150b070b06010f3f060803030a0c0206070215040606 66
    0x1a0400d41030401201c1d005a80701849180c1d04200003900760390900ca01011100560540094440c02c0803246e00244001440207050001603a10443d908541d00010340c455880c07a00e88801c8001c0c11449803006c40e6058100501132881d01110703550f01540b0707801300421691500010182552420007090441c000da521154401c1c2c0c4080500000c02c0010b00203079017100c0c50b551542d9800410941c00c4032a207002d41c0c0300821110601021902710305040b128401481c14a050a50401507080050751415100c03550321410303e8203000c2903a6943d00f0508001c40288001d100502c400c103022200191141410f100007841d10356500080c0c09100101000a40100510b082c01520f4050601b080038500c18210b079003500203259040d0002041d809010769051110f40b0003441c0903034a1348010046908001c0d011000111500c03480d0034031081119004000180c03102002960b2203040000000703065443c03050261301950058030802110950005a1416410703060744404c11949850a201c802801d00e900040d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669265854 1250 669264604 669264623
    0x20a0212010e010614041b12050403030b090c030a0605090601090e0912070b1f0f03060b030c10090503061605160309050406031a0a0902090105012105090f1e0d1b 71
    0x30f01c807616411000e800c144140da05201030890b00d002003459403180087da8001c0b03a241e0704004615101030340f24582c000e1007400d00254100ca08000109044021a107101c3c0038180013007084444000c034000e03840240710541e42074041e42080c000282030605503006908000140d1130028503c00c104100652090b805609115503c070410709080716030352030450780c4030700b40d0174003903080300c0780100d0754100c030b82100c80e00c7e1840107415007582c0d00d1070040c144020505074148038200150b407103542c4416052500346a00e0b101c0d4100c0c030b0303e004249810640010194003a44100c00003401215402c10101c54840000d024842107940c0309150a50720460300360010781d042032400501004018000349034080142041258140f1b03650741c80800b4080e1038451038029044138903680104200d5016100d00020088600229000780d00c00100a2049810840e01d034203050703000340c00042c1c1a80c070504c031a00710082e0040341d0b56a02e0000c2041c0c076903550881d514035810029064006141d024800c1e82a800f1990302c00000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669267104 1250 669265854 669265859
    0x12050a1704140706020307021807032d0c030b0609040c02120c1513200103020f0c0a110316030f0c0b03150a0504150b071707151407020a0212010e0106 66
    0x703500c40d0301202042c0005103c3c620f80030030128000815694801d500800c4c091400c201013102c8540b40314054024000e060712200300c910303204d0401040b07414202020304c284090051960100e0103603041c9058100515107042c0c0081c6554613034501b1124180010788004c224100007041c102e2805460b4040c102e030400000c2056110b064010a141d022107010f000c00c0303001d40e01d908190031075504100c0c2c00102034481c1040700c941d4402d008003540407a220141001410024030049107240e0390700c80d0004000580059010300104605600c115449c803000380e004041441584400c2041502507000103800d41d10085013030340c1044061042100600094058a9241d08020036011500c043c000c5040d44a4407950070041441d0406120b05d00705981e20750001340246180032102e100c1e50b44414016070b1101031241c184404001c40700c0c0100316607071203444403940b00255407980e84212841910210041041001400015940060314403441c40d0115055280d0100d0b43c000320303004121100c00d0194550911000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669268354 1250 669267104 669267113
    0xf0303020a020c0f0303030a0e0726061003020d031d040212041a280605030607080703050112110108060d060c0e01091d04200a140f0306010312050a1704 67
    0xa02003074a819002c03108601604420080b050f514888a113400d640144001240304640da001441511100c000341c420040e01c0e501d4100c01180b0b2a03c080400c1138582034440c0c40f4980c20811140e000041505032002142180d001400d44166840040d0402603000c40803420b401104409201068000b00215615480202d08120f06501150f003130f5200300c0e642891100c40007110707600c948224003a5141c80002c2110180a4a4407407110f180c410480c0d50b10380001c00c89890402c0018007451158490304000d150803800202a1a41600720000b5020443d40702400660003107000307220b110003401c00c400d02c2c0e0381c2ea20114019654410000c4d056504100202070125000400812040401e03620f0f0a1843d855080c1c101d410ba003040c1400d1501288200060f0100300645842e60020070914603401040545200040400d00c441d0094102d0141c400902e12151030034086401d500c080030b8010740980d6141d0b07142c22110303407850241071003805800100700c20124071a15010181d00c1c0300204440d00d50600307040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669269604 1250 669268354 669268357
    0x6060506120a0c020d021e1006060509090901020703050403080a050c0706080105040b0d050601060507170c010b0a0e062407020d050109050c15040603020f2b050a0603080706090503070f030302 84
    0x340300c10400d24040f02050507130300c041a09101c082d039070b07001407210b1441c0e816000410b0405880780141c0d0300640410707c0000f241030140300000c00b626030f01d070f030b0701d412100040111000024010100983c8100301150000380c106007a24216a004a0115140e01003d001a1070901c64005600c0c0180602200440d2440d04410000d041c1c9074162420040f04055109100000300030100c0039080e980000c004111441c4681d008041d10f910808101c108000358080500054001c1000510581d440721090000383c2490005400104104d1001994900b01800030a68242040140c50039884042003000f07801000c0e8800c90b03000a6016007100000e04490800c54001c1c200000226145e000d02c100780001440d06401c00d00d4400540160340785054130f030040940081d0b1140348424a005805c1c0820b1038142140c20101c1003039540028203080000782032076450116600100740d0007a1615086081c8040b4201c0e0f010b0b074071669400400010080300710704240307285000f4034000074000a807403442281095030540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669270854 1250 669269604 669269611
    0xc090209210105090d050408100f02221e0621020c070308040f0503060903040b0a0c0204110307090b0301080c0f0a0812220b07020915131406101b0606050612 69
    0x50175104001030f0140f04891078400e511800020380c0c0201041000400254004041d000400b44014940444070483c010b031060881003069860807010002c02444000c1750507120f0130410700d178001c0482410540c0245c41100401140f0740d484551108851480e407550b070440c6c5e040a604e50440390a103540c3d28203200a54410302429030308001303c2c0800209030400013100341c000d219540245040c03d05200402c012071300b09035070400800c00844000301c05a01e40d403003168410650f107446540e032840c01400103800c6c41c0c07455000300c0501c7e808200411042030302244001c5107141c119610000b0707020000005800d0020f68202400741d000b050750070100e036141107008003000030307003051f125882c40501c1c0d07441c1d0350461240c841c0a610701006c000d050010719081440359445494036051144001034030010600000ca1803044200c5682d07240f103040384130300c0103143c069400041240c003541c4c5071014981c020071000452807844415404480306104205290708100041c1001425060b01e80200d410f007080205000c2c1d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669272104 1250 669270854 669270871
    0x3071802090f0f0603060919060e01060f1d1003110a0503012d03020d1406010e0a0b12030f0309120c010c08010e040b1602010b0d0f02120a0c090209210105 68
    0x10240740c419420030f0b8000580104008101500356520207051142040008020100700303002c0e9101501003802510680c03024040701c00111407598104000075006000300001c240c1800051151909501c800000720082c0d030200f510000c0107900d4048d41600640a081c01e01542607001040b4031a00940c4500614100d0b5010000c0071001420843c940c00782c001080418040840d0010090025060105080a1340c5110b0344010041310305010a05081100030b800201c492002d14090005e08041030250100e04102110359100340c080711507115560f4410b0305402c1c02100404000241038081c1807042c001e60042c80d0b45443c0c2d54041c440340b200e000b80a1410014080381c2468000706030028108070085c41203502206081a51b2030f40c201c20b400414846007582d00310b64a0344104221380c0c6a0500c0c0402e0a442002c40d00d904007417510402a1841707400c2a124460f5010440380c4002c02c02d4a210350741161000c1e030340107a0b04c4080c41301040c2401d400413120400d00400c800c558400c0181580141d1050301c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669273354 1250 669272104 669272119
    0x30f051207030216060f0c4112070306260a020405070507050d120c050c0a02040b04020c031809090a1208090c1c060e030412060e03040918030909140a05060307180209 73
    0x69030340504190182d04001d800004210600c0a04854544004482311140564103007c801c0c1e02002e0100002c555610009071507400c00c102c140c3c14019103100407111a10701103c3c06000c10440703a603400e00040060f2140c0c0c0c440700400d004034051001c8030a5a9045410b84807008503403800175010101c042444500280b5103d80300030400d03c624203554840c50a4005400401c0071a0200006030444415495010754204041440c09070208003d020345601400840c1c0110380100400c150340c48002c10390700d0550050700c04200094500b04800c8082c014a08255580d0b803150543d8624101810603010b4204100c0040c6200d020b00702c0d01c1d0440101e2241c501804001c2011640743d40b40c0c0514403031810b2030b040341e84070000021030603008810f1b00111202201d040c141d803600910309503040181200c4000c04041801028543e0000300c10026051000b0b00b808002440b09031850a03400c0209100343e41a40c03140855681c0d40c1c06d111030310040118000c07092810812000200082d8050f0610364444c140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669274604 1250 669273354 669273377
    0x2040e0a030e03190f14010f09031211030f0910050c22030b0c0f0c03031509010906050108040f020d0512040f0608040c0e09100f0207030f051207030216060f0c 70
    0x3c001030328031000e4110404040120046035984c603800700d4611412200142c04001d075080190091260351405140043c01003451010ba04014280d13801c50480c01c4c40050912900103020015901100e4003d0340b140542c921555410300114140640c04001902840c00c00090050001c04180a0802005402c42000c0c0d02078601400100ca80341a120041c04c0480c80c400155071100d80c0c002078a0340c014400c0c0440c1c600f0084c0390220b03041d6032084403031a0ba111111003403801e241c1070522084d405824080d03000c1060500f8040007030407040d4018802081140c1c40300380407045458086103219656031200c100c0c4c1c526100e824060303200d0f030014001d2500c0a003a24500240151194044034092a00000b509a040d410300c540e032001d540000300355000500c01c525240c03550078078922541407882420400161580380929008100701d480c4800b410805c5014000c8502c41d02d4540c1c1407607000001802c0050307488001d0240c04002446044d4003811003031034400a0704c074442054100f4001c500c81a0b075034056401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669275854 1250 669274604 669274609
    0xc090801150603051e1e0f090604021306091a041b0c0b1012051c0f05160312020f0414060313060513060504050c10030c050703080a0902040e0a030e 65
    0x10700780029852540401c1e0020480c0c14000d13807042d41c1212100c40d01000c0d041804503003a00c505019100138400c5006d414120324201d0540c00340036006400d621b1b0f800c88506000d03111035a54600680042d12820348504104070b8002c1c0d9501c160010b0010450500c40c851a901040310041d03543c00d00e50b8002c2e4244a0f628460500c601b02c42e80000005494a031105500307620f07080414040140084580d02c440d0402285281c00c950042c050188904024540b218504200e01c81150140d035650341400a00300c8025000ba4008054035809110304440307101c452118242103850282c000d0030710304010700c0060a20004095031009205507442c101d11100c440107440240306491000311480d1001c00440c98503140010401c0e0005074101410301d45d84072074902140c490b0b07011590b082d9070448981d1300c070a000c8034290400c551001e080400c1818204400744440c0c0d0084c0c000d2060900080c100580500050b00c1840c181e03104803034464014100b005405020780c0034950b20416204203130046000c18030b0020035032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669277104 1250 669275854 669275861
    0xf030c030712060b041107060c0305220501060b13080c06090609090703020408101a0d0206040b0a02010f02040905100f1208030c0c0d2003070c0e061906030c090801 72
    0x1224003030010403016240880010036501c00c403404440082c0c8440100020b90b4441c003c084c0803480c1e849040c0da8407017161810300102d9105003500400d040c100000c1120030001054280c080c0d5860a0501c43c40110314948030780100032a0b00003440038031010448250400410026009491001040b9071150b2460b908100042c001e10001650024040000d00620700b00601440c0d00080c05040141c28944c40b40005c5017040341c0c441b100450190380780503204110000210440148100f91200740c18940c080d004180c00b0703c07440c0540d000340040040d0f82d8074024801d5002c0261303a20440320840d1500d84850490025040a0b101920005c0c4d0b07501020030f400e84454940d074201c9824110201200005544005450f00020f0002051040503c03a41030b04960030300604201c001a40d440d0a0301c114054107102c801e90b080d00c00000c1d03560040c0481c80015000c008003009507040102c54043c203585903800110703012030300c841c0b070056110a040d0000b0b036107415400920100c088e548031482c0b02e64460b03196600301c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669278354 1250 669277104 669277123
    0x70614010801062909120a08030a0c030506030c190b0301080d031401061b030c0609111e0906122b0f03020a020613020a05120303010806100302030d0e0120010b0f03 72
    0x2070300d0030480c44001884c60384000384040d10000d0010540c01009501050500c1044442900d4010b800820406890098403658841d20010308041286040000c0800d90ba10540c0013080d000e80c1207403811800313a500e0008880000e0110313503425030b82c07981c480106945a0640c0505540440c5c18842000140c1d200c0c00754482c1a1402e40d903d280c1240320031f0000e03115030f0f45c1c03500090301071050001304000401c9843c010b2044c205d004240d4041b90030a041d061014968588111005641240b1002d2000f9550796a0302c0d6001141200d000111100c2c4900b40b03414400703c44d000c0f05c1c00e0b04010400003100980280c08901484607500c1d00342c1350284070301094050b40714010302000142c1000c00001c030034504511117107460b50300291203043e0310751315003010a40b480340841b82d0b50400d91000c0010040700c0810000c070f684c044150300801041c14030b0355011a03074a52000340d45030140104103542e1030700c40c0d02c84e02c1d0a01c4160700000304802d90120104000b8020401881030b03600424100035030100505000500c000e6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669279604 1250 669278354 669278399
    0xa14061219020412121d0d02130c11060606041203360906051903080307030f020307030c020609010903080c1608030109150e01050105040e07020307061401080106 71
    0xe0501000d9006009520003040c2981166540c810908901c03400e20142c0050851054595400b844a040103030b200c05a042c2000100031002114400300c1c204215a105803510541c2c0701c81d0300701c1c00e034800100d143d4050041c000c00340e89403901a203e4030394484070241c00c0142800649800fa20b440091180e46d1003240510f4080a14801c01d0100081c850780e907211a0341e5090440c40c0487d402c41d01c3d256030700b4210b0fa801c0320244126034418400c00c0054407030340e40141011100d412011920700d00080c044802840041c11140d00031000034034060294010410040348008115035078506000050000d1080b007039008018464540052481c160501c00c43c0a2207406450307030196070f620300a050029038401000d06144094040070800050f100c03030080c43c06081600404140e00103a82c2840c2c1003000144e02001c00e031000000100920303600310084034140c40558044260690315204140d146207c0c0e5100140800d240c0501d128100031a203507410706a4010400a000300b6030b892204035400c442e100c080f4807 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 669280854 1250 669279604 669279607
    0x50c0304121d0108090c180a0b030f07060e03191a0114210c120601060206070c0c030807060209030d03090201030e0307200118080607140c0c090406290a1406 69
    0x210a42c003411065500041d002d0403100b0b606c50010105601c0d205841142e20310207840340c10300c119440c082c090741560300015401400c100400c00141540c2d1101842224103010b0401b4003000c880d01c003400845070211004200c8020040103181480c41601c00344020903400904100229040390001c2e025074410000405a5162840c8420800503111090318080b41d148150118222986c4031002d0b0040700240101c0540316030b626015003c2d00701b6000914080400482c0040000001d000c000d2000039a500511400c2d1140d90524005001b407003540001c6605102b00103110141d5940347e000130500314400e0b0781c240a41014802c140d070ba60f0107082402446125000541e9840b84110714150580900500d0301a107803001a640166009940703800c00c10310740e00301804100341035811070784402c450898482c85502c5d0907101c240e000d1700c0e424001c030441d20400100002c2000d001c49074208c1c0300e9900035585205100303103071400301c80c150828008a05004002600c400205011509100c0502c3e003806131209 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 669282104 1250 669280854 669280907
    0x30606010819050c0c0a1b060503060904080a0903151b090513020306060904090f14060106050d05041b14011101021207180f0b03040317100b0f0c01050c030412 70
    0x80c00f500c2d0040000004200c05c0c004000c19810412200380014001c0b4414642d4400366800084801c031180c21a805100302003083c4060b80d150044090b60094008a019071610003688084814a83e5980090042c40510203075034090078040e0b104c000c240303a035180c004800c664298020b0b2240031461081c02d5102840c00e0007108140d00d10780081d035010b43c00500c068a000074110005040700c401c005d0076501d02c00841c0c840c504124100440c007081d40e1289009011544c58424000c00034031a001c080008261240b012804100c0230000d10041d1a0405810024240e12604189039201c94502c1081c00503444442c0002441c0c0103100b12aa10003009080440316602c852040e03542c101400d07004068400b004100191000d00900828050324050b2401c5640342081e01700100014450320521240720315002c180000d0903440031801c02111820003070b0540301c00484080c80070340c0c02010046a455400c00c001c0140040da0b40008510840c0324030701c004104100941c088469504041c4800c0544540b14000b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 669283354 1250 669282104 669282151
    0x90c02010b0307140402160206040f06080903030c09120f0a15060f030f0b061201061401030c030b0a0509090304030615060906020d05070b250f0e1012090c050603150306060108 77
    0x5c00c2c00c1c501d03280b5000d005410030b03070200d00c060b03100d40d0084d80f140b42fa4020a2000d035902100064000500e08011403c60038030480c800c12909c0303819035582c8540f40c2c181842c1c260100605c440c45d0007600082c25907144561900b441e0f038041c5580003d404240e4900240440c00c105074902c1d51040d40d4000d610f081e0400026540c50400340c070003400c1254040c02c0c1c1c1340c0c480c042d62400d01800002c2d25072174240c8410303010001c0000d010745075444043c42c00d06041111061503500d5060a0b0007c8407000c4071b0448482c1c844440f4142144559000505081d0400484403031029241260500b21140c40c1e440080d001e40d5091b049886111100c40c420020b04100301c8000801c0010030070680095407003c000c8201d0b80301c24400d0400d10642c0d2125000700c0c20b0076a584100036000f4a44008001c4142c0c0e801300307a036440c1c420040949010042e45100e0581d0b4080b0f21051104014600c009880302030209a40e90504501c0030304540031180ca140e1291080100183c110352150a044e030141661011022008003d02e0300b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 669284604 1250 669283354 669283357
    0xc0f0c090507230a210e0105010f36090b0609010603020f0d050603010209060d0c03051012030804060e06090a200f0d17040b04090509031809040606080601090c02010b0307140402 78
    0x7031034100700c000310101c03a00086044191245d1407403800005800c40440b105e15007500e02c1640020030090702c007a81008101c01c0e40d11034100030220000304030794030543c0c100011000790781450203100003403420919404100304e1100e4940521001c49100d02140e9172000114264803a0214142c41700b117090140c3c1d803070700d4510781105401c07203401400541000b12003030100f005500240d80d82407141da1600c070040c2c004d641504c20310341c0140707554406080d00782c101440f030008000b28180040c101700301c810004060113155400120700210b1030041d07448908144800350b5541e441020305507240207885940001d9010461030b26440b03c03001404c06201218082c08102501051000039256a80820303001c00c40b40341964001c1c405020b030070240907102c81c00c2011050481e00014003c006a0303004204070b20180e11402e10210045100b2646066103907144c0c54810064070455100e45050b1050b41c001080c083d0f041d41080c0101c1110342d002b004241141c40030995a20854412041c0c01e5082b0111440113007030540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 669285854 1250 669284604 669284617
    0x40c0e120c031219230a17100e0a0501080706110a06110a020f0309030c19170105040345050307140306100e13030c0f0c09050723 57
    0x6040e00c1030100320002003800c1a101c0e5000c000340f044009030085840340600b1108106030564500043ca6000344960f01c245c0003401c150700c0840036000300e26180c20310f114018004a0038040c020b11141c40c2441c4040c00c803c0b440318050099044c480d80c0006070048101d104550403950b01c403004000c2140780003402c1e42e007140c0000f40c05800740500103005000c00c1c224001da00043ca001003035140d58050743d00c0c0090406510125402c66038204200103001e030740d000140c000b442c2c030088414880b688070301010308a160b100d9921100300341d1800c0108805111041d07205620aa00035210281640d80d40d100d1104c042c51800c408454a46000710041004c4207000341485e0301992030006011001d4540e0006450400740713a2206a0350f0a80161100d10390405000e0250010f1070545507040a6082c90000b1441040091014203602c4400e03c03800d0601d40b1540d0203000580e00071100c009a4449810542c004c0042401a0708000d402c00c808070b028180f003812540000004d41005038140c1075031005c15840ca62110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 669287104 1250 669285854 669285889
    0xa150305010b0c0a02150f070c05030c060c120313020901060c060f05040b040321180512030702030f090a030f030507050c090118090f1a041b0b2b0608030a0905040c0e 73
    0x140080c0e6011a100360040401c240128940b04241d850281014540143307420714501a1009004c03c920040c00007523031464481341c52183c00c0e269030b205641c0c03003140800414040c0d0b01160440c00003e1154220035695601d601881040c07010342c103e45022400d4401c1030310010b103681d507644006000320f48200c9640207200d00f01440c0800c01140910301c3e4058525041001314004204950761041090801c003100c03006c10780000b62811f5191800c1c001c1c2d181d0040940b28105c00c02c0000e80f00e03042e0350714110007001442c1e00c5929501c88804508009003a90083c8a08840510a440c00044280b40c480f40a904035281c8016000450f002c4031030303401c00703030400640494180070b0b0902c84500060306407500c5007045111400300b2b00c82d843d0074204000b94406a56030001400c0039094203003d0303401a80c04440000359094a8044460484102441da12400c202c54070049490800007045414020006112001e401c1e594074080645072004c00007200c80c106a64400700306c00c0003212200b800c1858400030300a008 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 669288354 1250 669287104 669287107
    0xf0703090801020d0222050901030f210302071109010e011202030312130b0f09030412031806021b0f0904110a03080d06030605011d0a05060a050a150305010b0c0a0215 73
    0x103541a203803c2ea00710f40c000411490b000b10f050b014a00c03142c60081d03403142000800507107143c038000200780c3d100e10601000e0000e0120300c0c2d000b01440b44521131154020f21007031404580c80108000203000b90810030041301d90746039071841c0c00c1c420f00d840c00c005410b889124031408185c0c0d1810039202c180c0018104204d0701800144500300400815482c1184100015041380c1080c241d6460025503240300181807180444110040c0714444400206a400740d03184210b58443c0000c05045c1690242c0402c060a0b02d014003100740405c80c5580844e0300030403407004d0891540c028080d4000c01c0240782d2031039100c64003c2041c1d400180841c100d50550066624042c0607802c000c0d88a80350307012940e02c0401954072131a01c0d000e0070400c1100a20495004103d400703509011446800390041d2034940180c0000301040d1500082080c960303400c040d03000105002014101000c0d41c0303090904110300018824004130345070400004420030248211480500701c18080e14010545a0070050b000440c1044522020300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 669289604 1250 669288354 669288359
    0x2030619151b051b1c0516090b01050315010329180609070f0323160302090d0f0f060501092a02071a1e0c0d030c050f070309 55
    0x1511034089001d0199101c28001c844144080a07000d585410b80d51038140302c0b001c28180204402007460500035442c5038840300100ca045001660a500030b400e8507100500300c11003c400c05c1000120901700c0c11800c1c50b00404103a4a019440840c7e51030642d960214404200007544c00f5010489501003610505002494100090071801e4a281c25599108101103075100b040c05850f03d007002549070102c0329040801850542c01184205c1c501501740000e000811403412600c0d0300030b0f000303204001800110241c85884031280031141c03120581e80c000000e082a00c55121840c880e0007194280380300580513a14917405075503000f84000340100280c8600803c180398000080c803038000d080c02004100e1002c00c60000018444c110340d089200002c0000d001d000c6010100d0380c001c10307290125040d40000800b02c9040703c1c2100340901c504950130720708140800b00c8640312020080900702900740742e170031070305880c2d1141400d40891f4010b407021400314401380b05a05409564ac0014580c151091420004e80342c2d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 669290854 1250 669289604 669289639
    0xf070501050f090c060304080403080702150a05070c080f0c09190903050c0c0a06080c13210b0f0c12090a061d010f050c03010905093c0d0206060103020306 68
    0x400070340742070b01c540c6850001e100c0300da80100503e01c1c4403203007143e0043c95420640d4030034040303106503c4000c5c18100701150960a55550350421030031b01c000540303510383da818070900c002d101c2d0f8080d0400b2282c0ca2404000840e44500000355010f042030074000410340c0408600030030061940061501c1000303400141300b0040e40b0918019000460300c291600c40c0c071160030348495400e01080002042c0186003030001008000e9200e8041d641200421540302c3c1d40728104186803800c1c40e4030340c000943c000300300f9034a541040c0c2c0254443c60168060714801e0b10725100d0308031200c2c0301c100541d694110210b05010100e401c0c802440c0032500094107504030703281c440e0642c0d610360035907035101501c0b81603070b0222042d2100e1900c20b0140980a0022a90421061820791080c020300d0106014080866503100f001801d01c240410443d9031104000c069026056101c600300024007501d0024840c104440394070720540c1000004d83c03060b580302c8a0b00500301c10390754600110001d4100401c842c2e40003600000c0001c2a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 669292104 1250 669290854 669290861
    0x30c0f0b0c280f030203090109090b010e01030f09061505120a050303191b030c0e01020c030304031b0b19020706030e06040209040305040506040306140702070e1603110a020c0f030c0102120f070501 86
    0x207104e07801039521844008005001c0000c940d0217078100c6820035030402c14a85e880b51010000744002d00b000180c2902e0310640d68004d08415000402e81d51a0100f01c580c0040703041c0c512000c59000700c03400034092400c00d5007076131142540c10000345107070b0040c00450060b420070f0b01c07661344400005900043c004e4540b40006201e0b0303003042007480825502c042c200d690030303405600c4044050f000e0008002c0c2003010b8000c42d0356803060348005042403521b91440c0714a00012070244000b03040c1e8042590311241c12030783c00007800c58022a030300c002d84240d80e0b0008600f4040d001e8280014000d80161003955515002c0c007074030050081c001c0742040030401c0081906e46d1000c020f000910b0007040c0008205008050881d000d080141c03c801c15580600410454496200c003d143e205000c0206807a45400c081c80540c01b500354034070220074440300403c40081495001500000001003115011105c42850701415260960781c515540107800c0451a8690600c0c0c0c03400800407940000c20300c916241d06501d0741401c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 669293354 1250 669292104 669292133
    0x80a11160b0d0b0f010c140f030a1d1504050f010c140f1501080703152c01150b0405010e011806020c03060a11090405060d0c030c0f0b0c28 61
    0x19003601040198032101e03180300b406840390041c4e8603207000d0007940c00068500200c0c0c4500410220349501d88008000c010b01c1408820010308049039100c071442d00e00505409007402d181600c41540e2000b464091515150301200110b9040c1c1807490581854288200640f40074034050600501003801c000241400002020b0003511201030900c40701351035075003811f11207004074800342c001196005210809000c5440c0d4103e036840a8000b8020341442d100401404041c08024181d618640021001c0c60342c2080580b8520101d030002c000c045c03458460003c2e00100390003900c4803407400740018030095000c5c00e080c004410050414420307101c1c40c00f21905030352440390010030060700040c02c0c40c185424204640f40c0c101401240a20848046030414100c1d40142d07802c031841580c503400414000c4d00e481c0c00d0100c074190004c20b00440c1e50340703d003054050b10a0512410070200314641000900c010380c1000e48002804420103416120f03248400798002c50300003104a544040d08c1c0c00158000b603c00e0a55444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 669294604 1250 669293354 669293369
    0x601030c03050d1419021618060e04150c090b04030f0c0504020a0c1401140907050f100e100c1a011802070c051302040b1209010506090f0414160b0301030203010b010c080a1116 77
    0x35258032340504201540c186601040580710b180c0c0a0000069004010381d81a0030031220000d02c070200a14100e641103015400b01c5000007000a0110a00200c08903050009009142d410f564681c0c1e0003d01c0308a1068100c900c0c001494098500d001031315151102035013205e03210000c5040203965001a51410050b41c04081951003010100200c1c104422813400c1074804547c448402001c14078060301096481c4020f0744a0411141d08442c010300801c0000c54441e0031602c95080c40781c0ca007a50340300c519400c0c041c1c03100701c11002d10719101c050b00c14000c0395019035000b6070740c40b42d80d4900000c0c4414803070714000d03246186800707200214140e0703103800290681280d010518134650422100407800c458019094038003512703080040100410301001c0705034000b42e1044064100b5000d89503142c2c00d0011708c1c0700b0000c003c040340710001101c101c0d10b0080d6042c4c0f4000c800800c611004240151440980352500401d071601c2802140308180c05240c00c004480d08980684982003a0407800030207191150f0061038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 669295854 1250 669294604 669294629
    0x11215050408090a090f15060912080f030c121b0d0e010209040e030a0305010905040f03050919090c02160303020d23030c030123031f0e0601030c03050d14190216 71
    0x146420501074000100e070020501d00072181070150089c19420396009640202203c14051403c010400342100c4542d03c242001503100d00703088141c0e11680c1d1001100f030068000351004030301e96050740d01204001c2d03c1441d44140c07a0103d0044a02d010708240420604c40355424803110728142c070756000744c2c0b001c10400c2000c4c56880315210740140072a001a001006840d180008000c00150b041c1c60801c1026010308240c0d03110303442d0400103020100c007003002502035000c2001c00110b100d80398005060866017502a0303403070110305551804214800340700240040c0c1c452800706c80b000c0d0003200c400c00306200c044500d851340c5440c20520410b030f92094901030081200080100000d0042414030100f042460301140408101d10000903520070041214001a03080102e180798407001952180c1c2468618805403206513030f4a091050345501030344002d1f01e41d4041c03099610300d1039119030306042c9141c410100403401c00d0300b600c001c011100c0b007082c040d00951050304058416480c2c1d0042c6400100201d84030403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 669297104 1250 669295854 669295871
    0xa060806070e1f030207140a030c02091f0b04080d0e2b0501060b0405010f32070b04050a05010c090f0303050304020111010f0e0d050a0c020607050a140a050105011215050408090a09 79
    0x201108601011f80c1659400507c06d0800280e0b0040b00100c00a070100e8248400340c0b110003100c001c04001708084440720f040050f0018541410002410445003500140d9a00c0d4601440680c0c80c4200e007450b00d5030024080c40401a1082510001030401c4a00001035039000c2c10f5944007800c4510981040000302c5c0041820000d0351390141c0c2c03a924480340c510b8002e50401320401c0001e5080034032207111201000400128000c01c0e06c0301c0941d8041504182c2c42180d40c1014180b0544440d086442039a65500b00800c005840740150070300c0040781c4074820040302940c51034808451700c3d000a001241000249035014201c5c031402d000e06034600c0000c0100040300c0d400c280c13000c1e251140c1c2e05401c42c148281440b007030066903000422942140d4042ea1141d40e500080e10303026040c03140c00d40c0001c0076041407407072407040c0100000300000018820002000b10342d172900c907a83c50111940354018001d4000c40c3c061604880d85400040d00b051140041d14148003882c0006481d8120540111a00035a9140740 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 669298354 1250 669297104 669297113
    0x40c0c0f0f330e120a0801140d020904060c030212070e0307090c05040e1801020a12050f01320a140306010e13081318020304020301050a060806070e1f030207 69
    0x91060078402d00412145100c400007034400c0311110500a20303910755580d001ca41d2915400d0041d6000490701c505101d139946020107010f400043c0c04e001c2c004081c0c0000f02c41440074104581420000c580041800c0401e42e2031f6030352040a424144124810107400f40115400816040c2c4040d014120766110302040b07140d06000d0500c1d12a10b5071001d04013508010b6120300300c41c2c104040342d040d81c08056000c50700c3d43d10141c03061014045002d80d0b803055803002a070000115484181d200c80140803603401c0c411a110104043c108000a000d01c03482c40211503407507056800301202c545082d1420030511070000481d00d00003081d0f80a154002c2a890074101c4c0862030034981446000c4c05809803501e02c42d030301c0c209840b1201206000f59030007000c8000c00103140b408051940c502400401c0200c403101c40c00b00182c112440603401c2624200d00a40c200030120700c1c8040076005040980b084000189800c0d0780d030306403c41c0e81c5100108010703040701c403241d1541c9510745001c01071a500c00094030056a1a85c25280 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 669299604 1250 669298354 669298373
    0x1b05061912050c2505100507020d0e0913060f05010308031605070f0308100305010519141614070203030409091e0c050d030509030f0a0507060c0c0302040c0c0f0f 71
    0xd041d1032610b0b1038200034404144500b501d03240103982c401401c15400761003000d10500c2c4140005001d902c02c040407141000b1058001e2403240d4456800c0d00e0b0602c040c15070985004880050301a030011059001607143c825030508811510300600001c14645111110350044840a0b0401c2e41c08003000020441c0315003d6404125411a0f03030700d0018035203101da40311110010301002004081050150100759180612802117000d150008002c202500301092801200b030a100e0031900c1c040d007000342074010959030017851072280c1007000502c10284aa01400c9480c0030131403c1141e442c031014400c100150300d081000e44050108030400060408041c00d141600f402031214034061017088100000021354409141c1d0111003050b2802007003a0150b01c0c0c02c0e41e0a002d08a0240e801d0701c180c03e0011049680001d02242c100e014100303442080d03480c1d82e011214a41f44010152012404c41c03010001418140d00c425001c603110701d0302003010303205c5586900c14071030900001e4a5044141100d1414003c40300b5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 669300854 1250 669299604 669299627
    0x130212070e0c13050913140d02120c031b101113080109020105041701020d0911090108072607050a12050709020301060e01080702010e031909080102161b050619 70
    0x6981c03c0442e03881c0c06440c8581280250307401a2071041c003068400d86036882d074000c103541c4074103030032001d448844500303603500c403400b070818010300c0781000d02c41c0c001c00c0d00b07421102e00031141009189001c105540c004a101c20250a0750040e03c0740c00c0c3c101441c40c1c418030030314440401150f49a0340e641d1003540c035002502c10750f42005811740d05d02460600103070380000842d070484001c90745000c42e030802410400c0c02409110a00e4003883c4c2403210440420007190700840d41110308450341d098690b01d4000603035076101180140328508404044003402e02020079070201402020740c048913640c649501c0802e24050b0564401c0031014091402041001010b00902c0068456140708500350361411800400024036031750f1183c10700201d02c010a076014404c1d0003e508500d0001d08881d40c4042c590715002c07218030601406000640c07442004540c4290600844050700c0c14441148403155046d1600c007000c50341c0a0304104003289803000003544c4d4403058040d001d00e4086031001802e41c04600409060002400e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 669302104 1250 669300854 669300871
    0x510020a031e230703020708071a07030b21030f18120105040b0601030b0402070c030803070215090a03050a050c07181b0903080a0e090c030604060b030c030f130212070e 74
    0x41115981e25581c0c03169004500d07030f00d2940031101d03280d200c400d0b4002e01c02d01d02d01601c02100014003109200e201c540e034208404400f00d2080165403401c104034102c40301310524070b1b4400d66078640701014240c29000740c0b800341c41403400d0301c1c5405a14424003a041c2e1001c130150740340c0b0030340544241061920b14005550701d02c00c900244034034505503403006d014101c01803045040c0750f0b59151030032640c1c4460341500e0b03c80d54066010386030329072242405a89504200c580748010b102d0500f03004060032000d44a2401142d2036402400800f0480e0340a5a1640009910b8070400c20305100e8160b200303500b0070414008080c010055411108071413141e6090311502010b0205084807003813540c8002d0750002860017280d801031485600c90410f01400c98132005014101c80e4001e10b00c806100d85000c481000f1401042d089808100d0745550384015605808101c5201c0c401c080144002503903101080403803940908205c5511024200c00d07400145a007003440c1c010707002c0c0c0d030240006003d0101d44162058204034017 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 669303354 1250 669302104 669302111
    0x2a0105100611060c0706060509070e040b060406140904150e04060c0509030c120309100806040c020a0302030d1815140603031303080705030f040e0a0f02030712090510020a031e 77
    0x15078102d40e031041c1c040c0c110740c44260000b0301403040c042c46505c008003030709009100d46144d080c0200028070032401d001c0c950744070b245400c0940043e890040d08440c21102203441c2d000001064502058458000b08440c40e04a80c4a10329510600303400a100005841600389580712401d041c00c00c0c1003151403000140d000d20800308414600ca41d1700249006078941c0499034551000b14990300541140108035425030840c0001c1507d1310301d16089107880740f190314107460411500e003007400202c0c2d452030001070103800360f007080007090070202031500032035504505d40b040c00b0290b2049a03681e5502c40b10304e01610b84015500d6282d080151199102d40d90443c4d0304074005d41c1400d82001801e40b0f080d02a110003440440001083c0080003024025503000740488030030241c0303413550f801a1070110403084510303c130744d04e240254102c0702ca40c0c14401d90340103400b00c2e9101d0080e48440d0020400502c40d551003907a5a2040d040705c17003030801c12400109a08c1005035808038103202e0b03000b1b040f400c00d40310141401e0410305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 669304604 1250 669303354 669303377
    0x150d060f021308061f1a0a0c1e03030b09010b0412050a021509090601090609120507180b0a0902070f14030c010f150602150c16080403030503040b010605090306040303022a01051006 79
    0x4101405800e0303511042e540348031f030500a5500340c40850004100c900c4036130303100c0b0042d2048101209054041d85081c04500a001d0070081111024000e54139103203000d00042c408486840a280512032185040700d4a40403550005106508400844000014001580102400d00007000c0780c205600b0b007044c407030040c28503402900000c4140140203d07039226166440a00c03070200982d900804d03000788500c05c5140714400d200051f00345900c040340100b0304c0300b10004404849208862010340c000d00c040f903514500340e480601c00030719421128030030311092011600500c028820032444038801c0e03400098510441c040403402450320351003c400d64001400d4148089922000241d0007a09004026036403804280d45040a122101003d40f248002040200c10140c01c034005600850080c40c22001036a0f13120001c07a258450b80891640542161303003c1000a4002d80180004101c15465196207580003090304419400040c24043c1c00da456405000c04401d0020f140701c060122803a050072100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 669305854 1250 669304604 669304619
    0x10207030b060604120803010509010f080d120e031314010215040b0402011404060804150920040b0616020f030309030d0f14040801020909150d060f021308061f 70
    0x9a1101401419500001600325078a440c215000740120420540440d03606041c400c0040c6c100b40101405600003c0002c103071041c03082c418000b125103400043c1820441c041c012640080641c0c000d1402d0764031707050300000d580741c188090f085242c2001c80d2104403902d04032403007030388149041c500f5040d50051a54070700940e40d4907441603400350b01300755071a845884078030040302c0c40a4030050892a4070381c0410b02240c070a07846121980158001d0303c80c1080460f00e240190119510410024075003c200595000040100012881c2200c001000000c054101c8404254513500031491100400c840030400c00451410324088003001f01c2c241c00a50404622101007a6145c8000c00500c05000080084c194030b1480b0340c80c5890080320358941a51515500c07180180030f900980c2c0c00310700c141c1707030040000c668030001240745843d0440107040b07416050440d141c074402003050003ca01d511540030081c104594025201d103000400040004140b6450075848a41400507072803040ca2051182100400104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 669307104 1250 669305854 669305863
    0xb01050f090607020d08030f0907060306060e1207090608010b0111010c0503270d0504060f0c08040620010204081f020301050f100c050a060b1c050304260f070f140102 73
    0x31090b140c807582c03040a40005081e404070204024140c5e9000020000c04200c24903800b0b0080610604944e40341ea1a400c4c02d80035160303503004140000d00d035044102d2040c0341402c1c481884103802401d41d045592551500c41c280d4400e6002116140c1d1680200c42072540e00c07014031001d45107010000c00010245040080c02840040d04032011044455401c554104a81f00381d0840c4901d110304484880e42401005007283d08284101c0d004101d42443c4108501d000750040d40d49a0f0340041802d240a0074600140c0303524a803402c0e00c0c00140700004150180300700034401800030340110002001d01c0e008140700c3c00000f02811aa1010103801400100b0554452040350080c0d20b00854404c0b180c03000b406001c40d00d9207000c041c044c18500c564015501802907a612900e040c003c00d460070804024840d441d03c80388204032500404a41c8200010440c52200c086c0440681050041949a40d4145d5009501c0c00c01c2c601a41861030b044180c007001410380d080c0e460130080180d202405088a10100080d484 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 669308354 1250 669307104 669307117
    0x3031006030e100f0902180415051b070825030f030b180f0f0a110d091b03060c0806040b06030402040b040f060815070c1707060603061e0b01050f 64
    0x1070585500140c940030320140140c4520144a400400c0322800c400320744c00181100f108140e006a0100b02d1008051078402c0c01244a20740251010890a82481503100108401000d16403146101011000300508650007010114080ca164135183e40d00001d00841c50000454031840d0b11f0060742c5180f0019410000100340000c2d00c1c00d001401c0800358003c90440615035243c2445001c0001c20030100345050491980119202401c10403181d41e415405400ca4031a29408021440c0070f01140800e0000c64001440b00c03803041c1800d4001c0c8025440440300d51a481c0c00442d50151554240a0030662080101d40d20290454041c41170624201c040f40c06844040d1000e806a42c641e41380e600c1c0303501c1d203412481d00250b80c41030420240359140500c9464152031002c1200040510001c200118440c0c8140d291240d084400d030710b11240518108009079000170022580c036078a0f00c0c00000480c265100310700d031070f078214210010210350302001e4004603101a00102e051143c144061500e04030a081034a95 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 669309604 1250 669308354 669308357
    0x6021f0c12230705030105130e030405090408070b0c040f03120918020d230f13080403060506030d02150109020c0f0102030a0903120605032a041d0f03031006 69
    0x3010103020104840c0e80304241d84110195040941100d2a01c025074060200c40300780c103811034110b8079004401c0b10f0310f102c2071080741c3c0d0082c02100904101c0c0e10907031010100f081d45904807440c166440c40428803401003110183c900031000b16002061011138000c8582c081d2480d80301c14541800c10400d203508200c14040546442680c10385003940900848109028100711210700c1580d00d500d4900902075030001c1d038007455050900b10410401582c0c1c02d40101c1188010410302000d075988907886001001c0205407c0600003102d4108010440c8c01c0c0c0148050350090b1004905403802c1000e151511060522980865010124580b0344030089202241950040c0c1800b40c0e80d05185400e0b5480c000d031031405182d1551000044c0400b04005910041482e031198465079446031511641c401217608601c81c498158000d20070000a4000411809109004155410800b51010350100d0200c1e0196883c0c1030305007207a0003000036030b903404000600d8000340b001d0003075145240c56804c821140c1150b10a060 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 669310854 1250 669309604 669309611
    0x9010f051807020f070f091401051311041a0a09080a02012a051b041506020304090203071b030207140a03020a05130e0d020a020f0109030201051b01021606050f0106021f 74
    0x80782c9500c01d1000000c030121072001c9428041d1079050100c2402c0c000c3c8a01c072100c07884c0810801002044d20521412918001c040900004010b065a0003600b0000a140500102000003203103280d850803907a10900710018000d61100c0003198058100e24182d000944d6a40c80404140c0050b03074414070b007440c1500116014002d580d44840d61950000c0401c0008095010b0801422800b1140c0b03d01802c00d42001ca4003480030340c0084140c541050103a0280b1001600200824405082c281e0000d580203e010710341241020002482c602c081101c5210841c0107030040c28041110f800c0b4401440000300e03044911907107c901e150f0004002d8001441268060060308040000c102440c1c1e2201c08071010141c10345a003101c160350001e4850444640c03c0384140744080e456205035100c1e40302c407000e0343d0713060711100e18240c007545044280440b807400d010344940d020414000c8409e01e034007503449400c1c410380c804200c0c2e00308828801a08107058201c00f00b1580010300340c103000200c1005a4001c11b07030828000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 669312104 1250 669310854 669310861
    0xa060f060527060405101107060c03020706080705090406060f080109051003140a020a03030c0311060c0301050418023604112e051c0e071401020f010c030b09010f0518 73
    0x43c001d802140c1c0031550100c5c1c134404034040b0940055005103041c0d140030550781c0850712084162215011400080c005030f0120342d05124290040d1903450304882c80d41003050818210400240a44805400c40c400045184007480141600078503854058a0010424420b0349400d43c59402c4a407007a20000d80810880301c4a6980702105000307948101d034002d0009102c03513850b0700f4054210a40f607103044000a6006c0a8a8191240070400b18016903408075160700d141d10303000030080504a0002c110040010700c880a00c016500d203001001c84404564240304001c4030080c500300505d6200d1004480845d08804010010f0404c204403420f8660899100050881c1581640003049502502c0090f00c941d00d4108202d00360824098034440000b000c8054204e0f001041072010303600440742c980590743c00404188442d1456a00809c41000180b0441c1c0d400c01c0010301c03203130035503070b0348103112012070785c1c8000080c0c080c00c048183c00d001d4440815005102c80c90034011803032050342031003602144001d21011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 669313354 1250 669312104 669312109
    0x100b0a05040203010803130e0c040303030b06130e160507050706140f070302030d0f0207050c0f040e19121110110c0a1b090c050405041508060a060f060527 68
    0x608000e010080e00842d1a50b0310790801d103540e540f1105000316203000d05540001d44880c4180c02e684034001039070140d41018519a41940030f0080311080a40c011400d02c8400d600c486000810402802420103d00c1903040c00c0c41f440300031020964618003081010850b910108800143d4482181c0042c600b03101d52100401da21032190050721001d140d09900060164181580000070301038045588004001644807405038204031b01c10000010000c0c1c000e0025100c041c5404403103c040e0200281004c1401d13011850340d03904240d104130707000035080c146846920501481440917010b8004500f4035880000f65048003d546110911141307071f489846003020710301046d0301e1083d03d0201c0c0e5944210340c6864203502c3c01c80185070000d4542843c078410501c0010342d80200c0d000e5100b000c840c03900c940740b51a0500040c04064244041003000350094a100010400070810449102c0c0d4420b0701c002800760b090802006a0311000c1e0300600030081c051000c807a9219504514a0741c9548039215500048e0f450f201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 669314604 1250 669313354 669313369
    0x2070e010323030408010501060215010312030c140c010e24010b0c0a02060703030b1504050105070803061903030206040308090606010504260102040603020c070b1e0d0605060f04090506090108100b 86
    0x81908070f0101140016143d0415001039040c1c0d403044d000e031840c4082041e05041046401d20001d800e040344a68101d42003030003076110328140441458010140082c0d4004203a0540c80240340e02c036035a44d03030301060691003001d002034003043e505400840c459000c14050703444108818003614440d01d100154080071a407080298a00d2641c0c00350801e0f4585200e03080150042020601c0a030180c4816600c4000302c0130284100d070142c5505840d00c504020003034913013203181c0c1c0000700340c80e420101e44459172075521040c40710040158401c0c0c0c003c003268507151500030168040645811043e612505c00d000a980c0c0141c00d031400c0c2e522905070310114800090507800451840940002d039544005004200298540c006150b8840c103401150746207603407081081c0a0b4031500c00341403030380f4002c801d040c0402c1050700001d003004600000c0c085200c0e512800002c1c940d5000703154020880e40c0000d4204100491401031607808581200d050b0540d61414201585a8401d44502030380d0f65504e1500082542d941c08 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 669315854 1250 669314604 669314663
    0x303041a0909010b0d1503081c0216050f1501080d05070503070c061d03070b090906060403062c0d02060f0910090f14030304030509040506130905071502070e0103 71
    0x1414020b0320350b5288540c02c01a408100e100720f0140c02e203088140045134161014085952100da901d19240c440c1000c02080110b0781e03d0000c4158082040703148104100e90110485801075005d80140d00c002440c0e5450710b011407809581030740582e80100a0802c1c040342040d13903039159082043c0c0d24910b078548035042d44214000180500c3d064400880c01d55880328110310b4400507c3c0c04584001502001c255951a483c4108a8985010842440b00b4104100c4050308004c015281a0400b503ca40d11003054606c0c0064410000f81407a0328440750b40904d5002018000800002c0d050307010300c100c0008d407a990000c00707100e502071800d00072401c00c0c0010840608050b40c1d915081184820a00d007400401501c880242d40c0011500704840304500040200c1c0c1c007a80d4103845461400c0480c10501019000c01046c0591005040e000203000c51401c1c05080d03000c62081d8043c2007810f0402c9045610300220000c4142194003101d001e20210307400016440c1520b0300040c140f80d180b1241070100c3c107181c4504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 669317104 1250 669315854 669315859
    0x270d0e0910090c0512160f03270602040509010e0709091116110a0b22060f03110d09140622031b0f03020715050a141e1617090303041a09 60
    0x110806c0b1814030f0422101070ba03221a40d0316040015441c0c101141652035802d1140300400d4917011038203121f440a0315108107584076403000340c00d066035030000030b10594003607001014442c020000c1203a507a0340203c0150150040c1c6d101007010390075501480000340640005440a6101170041e4000c4c03119500040c505094010f100f0000c450312241581340d507420880ea1000351460301c00c54400c0d0072071030602a50a6408994400d500c41c0200d60049002c1d20155004d00c950f90003c10002c410040c040c080c403424207008220300c0c0340d0054500e502e140703402001000c0e1080740507401800c540c03c00011002080c1180c1510b080e0700d00718034561010200c0440144010a441b50480130ba1041503004500c400454040042000206a180d1016941c510641c8041e074000703241d000da046031031703e00c1d030010302500310f88001c0e0a11841e5848001c44495403100468410454800c04c2075000c000404850908003038400349424142000100400e5503405180140b225a140011200795003207118404d03544081d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 669318354 1250 669317104 669317137
    0x1505070308060112060302040e030904270201050d0e030a050918090c190f03030c0b0a05040201080f1f080129090f0601022a0f0d1703270d0e0910090c05 67
    0x307486500e980ca2f804400c49a0082c5d0a12108030344441c3c0344018142c80d040d0190307048205d0241c0d503004489070f9110055103103140e81e85a960a862240070000b8004040082c0c64459882c2e816604204020360034081012581310294204480e400d4085191900540b0076240e00000c40c5103c00228018a01a0840450300e4103019000051640c03140c401412140a40114492900d540b9030040035a04100c030301a010402000114120f1084411880d174072400e00e122030a144c0070052401c00e242c002540c0829503503074680300c1e55111a490035000c560144550804024010390b28400725030342c802c00034007603a00c07a14000005005a402030010142d410752504c00b860000c00e104006040000c9030400490040200c0d101c01c418a04103240c00f06400ca420113000c3d1600c00a20508134a240d0000388030442c06290070580032a5200b011858000c030754002d5000e851080707003c8000a2200044080540c0310b00e07407000500c29080c68540d46401528000740011813260b980c84c074240c03018411002140000d020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 669319604 1250 669318354 669318371
    0xd020d1101061e140d0b040803040c09052e120204090302070b1308240f1803040303090305100204150813080705011a0111070509100306050f01150507030806011206030204 75
    0x103961104030305543c2114a81003940407004c00780814604810380c01000170030000c011a01040c1e00301d000e55401446018500b06094032001c6400946409550414840e041400c074000a01d00580a80e21410411030980c0c0100745003c0c0503d0070101780714000381c05166203011003002e15100380210310141020030009542c907035005d803103580c010415100c0e00406d030117801c82400d00300d000d1300140055001010402040c5407640107070400010006403201c03c20591140507407000b21018406400154020345030407000b5455400c0990134074480d68800b602c454810001070208100c0c0303145052000410380380c1070003642e0b20101c00d12140000302c02c010f003040e034002c03440c0d50801c10150041407216001442c0125005103c100550b4001402e12490f940c1d0740100c14140a00d081c92a85240d000000e0004bc80442c0c0c2e40352030f0b00e82100d81c00d680517050310840b000113016003103441c5240b000c852440d1404619180032a1401400e000d0081d0541c0e0401450800c440300c1c2c1141c0d41c00a0003e190000c108100c0c0c0304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 669320854 1250 669319604 669319649
    0x12030b1c0c0801021902070603201c06080309120d020d1202120a0221150d020411120708090601050109090b0619021b09010806060f061207020c01110d020d110106 71
    0x810208400041c46405400b05076513101e4014100300303401c552b0225100b01c00003028216150011441c0310011580b1303034035600c001000360003400010010180550742e164007038400d01c51044488080d40c031080c1d0086000200181d800618142401c103589081c450026042d640e06001e0701c14800d03010050301d121420f004036030b00240e00404183d50304680050400c0c4d00c0040c6200c15010458081d4489001c0078565005d0f4102402c0d0842d0862008100050641c5980b01c40e813003940103000340c14400b455400404c04583d80000202d03810010107402402e146d8901400202095601d0040c9441031303407104510341c10742d1034110035134441d5501000c0340d001310181504000d544152186142c00c3c025081c2404101b90b0420b40c0040d03040c3c507262000740083e503640200707100052006008068010404109122800a0400380140900e90550242c0340440724017000401c00e40540c2d41d01041d80d0010100792016a800041e040d0b0681c0f03041c18a030354812044454240100b483c0d40c030002c00041d20025402184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 669322104 1250 669320854 669320887
    0xb0304062a0801150e010c081606020304200312030a020a14120f060406080a0605090a0b0129090d0605061c030201020c070906031e0c2112030b1c0c080102 68
    0x3144c5800d80c055028200c018101d920f2400d941031680403450300961040072402401c0100407550300f8040c80241d007042a0781d5082240c7c81120152844414101c0d48001050010103551030070804a005007415010f0340030462031840040c154500c06a800a1241c80c4280115200180c1c40004281d56032140711010703822060740c1044a20042c80c94048000403c02d241500c81c002c10b40b04080010301c8031041e145e40c0c0b4070080c00c019003070075071300e02c54601d1610016170380c407080502804150560303031907030045040308500c54803d01e10302c00902d1205206071452500c508a140b03601036000000424113403581008248200d80703113031131f64291480c80c159600c2403540540082c0b082507000404c072600d070741e69a07005804546650100404c0c480c1c4842143e001290781d1804032030719a001d560128801e81c2d942c810303014941c0e054840104201441d400c0b40091100d62006514030120509080c07040c000c0a10001e840341c030245690520030900c80c41c211051040600f804005406c0074002156078150703003081105e41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 669323354 1250 669322104 669322109
    0x50c120a12030615050d1103010f0f050603040308060d02010306030b07030b19030210051305031902040b3003070602071a100312030506030c10180e010b0304062a0801 73
    0x100180708007034900c0324801e206400490319007020071140182032913800c942e103900031901404102e444410303001510003144010f5000f021007150b4a200d080c90300484026000a56220b0f5200c0e03d02130082002081c0c000d0b080b40c0d41b01b10100d03288000c06881e0303c010380c0144043d40025080c070b1014020081c419806502600c0c02c0070702101c50041c103102c94011030700c0b406c009001c02900545200110302002d4000c07406480300303803100080303c030030961264082464420071091501140e81265107403015424a40302d00d041c551b01c1500c1c4030104411449001c841c0c06207007020441c2c0d00d1105c0d185404c108170140152032056902c82800d40d40d41811b420442001040b00150140102841020a00d585000364081c001c0343d50000c3d48071080214114150b0050400900554150040d01c07400d403442e42e510b24085c08001c2c12a2035111142c1400c418108620a840d00309448008200006005106006060700d078001da208001081288400c24080c206a858a01c0a60301c40c0448608242940c0c012200c10305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 669324604 1250 669323354 669323363
    0x726010e06041b08071d060a03050f010f0c0c020a05060307050904150e0708130201082e060305090c012c0312030f0f390f0315030106031e050c120a 65
    0x30070fa6100c42e016919582503115202d01c0381c0e41c2644032502e51014982041d440340008102600c4280c0d20740300d190808a000c20017840c240d40d0b649481d485260b69110300b10007a5aa0300e0600d4078000305078040756407007140340555481040003000013012284144101d507840e400185c028030108001c80e04415115040e4001c0190600115001503d058898045a442600c1c1000942070804a0740c005407104e40d000b82111092032600302034003000398044503104402c0d004000594482510b0080014200c4001804048040d0006d280d401d80f40d070b074042604115580724080c10f000005030a00c800308111013040130b0541601880801c1c61018000360080c44c440d0300c690f14012080d640b000345102d0682c008841640006200414200118130b101c2c030300d81c0c1c0ca0711409407400400c07265034628290350703040703400b0b000c0200e03130300100308100032408460320814643c065009101aa003995078680604844003101c10400880b07140d5081480000c024001c2c0c61000500300d4403442802e2180a91661160101500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 669325854 1250 669324604 669324653
    0x111090a0506070803040f030e041a010201051807030b0c160803070e06130323030409091b06020705130209040c09030b16020d030902061e0a020f0726010e0604 70
    0x952800e2003011600360f00da010480c00e10f107a4a1f50b451144001209005608020643c080c4801d42d4039140308552517007031040c10807044100c2c1d2100090958100400398030340201d1945440c100c0c0c200004800041e41ea008002c10f00c1d039900c6003101d05180c0540401c0d00d4547d0341030b619900902074004000c501461050340c4888003203480c1800d00c001d03445461142c1d031141c7c0f120030080010a10311102040079140c4001d080310f44040072218a45036401582084080c2c81d6544035800130081044100142c0c420840080c1103207629011000c0d455424512895004030107100d140314450426034111039144800400170802e9500c0c0300c10003400941140800c482d031101c0b500c04601c1109090700c809003240c0442c0e00919210102c034008802600c4c2c03519003280c1040062211400b5a500a041c64440842200c0039a84465030004c0c0249010402020142c4a0b00300c42e07001d001041040030842111345a6440191416601220803401032203003526140042c0520782c14042001107044003583e62010a82e03005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 669327104 1250 669325854 669325859
    0x9070c140a0c0506090310090c1d310804030501060504051302030d120603020d080d2a052a060403091e050d05010e0d02010c02162105010204080111090a 67
    0x31039403140a518040c18449556000308900e2404d540104030500c00a42610400e02030694010b0644070f08550403114644003000511003082d00b20741c18000b20f080590001218144041910541101b4900902c0104400302c04d801c0300d01d1800c645010fa09610107134030340e43d46540b0300303101d0f0081c103103401071600c5682860b020400041c00a4065108181c006000c2c042e44400c41006640e0050424190000700b40c4488002025a035a0520101401e0103066000c0c0c3d40d0300030b45023081c100e45401401031003d038080340c11000600f40308001910a02c0080c28100c0c1e0f24854000e4202c462440074424507000c40d6501d0240c0552900810018019842a00e601c406240c58144903510114a480c0c0c481c43c01701c0b11441000a40741c03400b0303011402c5001d04000101d144450682c0c5051400e03031008a00540c0d140d07000e8900ba0782e810005000f40300c040402c1c941029080a9101018400c0c034014445c1400c0c01403510340a0100c2075046a00401115008001180310072604007a0f42e004000c00030b1081c0c4516100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 669328354 1250 669327104 669327143
    0x607020f070b04270b040e0609061003050307300f12051e13050105041b091103060405040501060f15110c03030702060f0c0d0909380d0209070c 63
    0x80c0c4055842020001c014024030a1401003068a00f0380d50480c143d40b90400382007541ca5910a03a420110302c40003230711252410440403403070b00b230025002206020700c0b150708201040d404000c3c0c94a0036404403131b40c440005503054244100c030614030014000742c004d81d80104070305d400c003d0380d000c42d14541e20380305a11200d00d18001c046460880c0c03a00a001880c00e048424403c112100940c4601c48010f9402c4c4050b194940740e003100d1080760203e038408810403071010070034000345c035400041c449840b0900105010400c540d00500000e01051701582d1600042000c1180a40201024128018191040b10394540b8032009880c00c80c5201008250040d032004c1c01e80101041d010103111024000350310340401c660074084607510000c040305405e507043c0b011001d20041401445110400c0e40c0d201c860948c1400c4031401190a031f100e410880340640b842d1149510441c0301d0700300c0c41f4045100c0038806110001c0125010482c02000290710411100820084507007248c9500030240c0583c04e9107140070300c0300a5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 669329604 1250 669328354 669328357
    0x906040902090f09040b010510020f070e01060809010e100c120903050a11011415030319020327030a020103150306061203080f09030304060c050c0604050c09100e010e0c07050607020f070b 82
    0x14086c0c0369048020050041d0308240c042028481064030444029000e07284015040c001c8a0b04909411100400101320b1030350710111064003c00340d000208a242d0842d554203540e06131128484003001d4440100310250f90203058010407800100034144004000c51a0007080c0d03900080b9810081551308003c071428034014401c3c01051614001105015100d840c41c04000303405581490f5410f02c410002003140c50344400c00500300000e00d400035a241c06508101c40382c620b98400903107501c0040030b04410030580d0002481090140c0a0070000741c2107082c0c5200c01103842c0e140d0000390100d82440000900c042222500c1c1a1940c02550b605a0ba40c8441e030b22080001c500361000e94495000740003150106d1f41e00d078400d000f1040035003003183c5800220b150503418001d00f144c055500e50000d1141000f10b040c6448100e9100d02e0b000110031545090507031064045c46c047c01040c00d0941d540f80000c401803074030400c4032a0b80d0b0308a411584d191800c3c050013503480741d1202c07100d8940e0103950b030006000c02c0c50741c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 669330854 1250 669329604 669329611
    0x60430111e07030212030702030a1214030408160809040204290a0c11011815021005100b07020f031203011d06010f03020a0216170c0d0c0b070302030906040902090f09 73
    0x10042c2c07003098910340030045c5210b54070582c84000c0c0000c03c000c1c00140d50403c20314080710320428042c08078024800c40a040302c1e85038808004145810810000060b150104581c407454411910220174020b40c1440c29160090018980d0028070000307001c91000031094203c0c04d240d0035407001c800c0b0300202c0341e0164440e0040a0340c00001c60b404480000020740426a8a8440e0006240c8540c0c00740d01503610410118442d801014188192400e40800c1d650500c00c3d80ca5103503241505008900300b0f9803007010704641601c03a0241411000c0340080840d901c402002c0d882c0c0034001d04446508640b0701c81d203a481c0d4828402d854000c40d8200010300d18101c10101244142c07016158901c0505521000342d0107544003110540450041800c0d032140c044050303460358054600d41030b0041d2580004102d0919200c2a40d01c428898121445501c000038071600d40c0070240c40040c1ea0280d1504000d1031f00764035601903035802c0b03944004085400310700c404155003c2c0000e0035003201c00d11001d03100c500500400f81c41c241c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 669332104 1250 669330854 669330913
    0x2131d070309030917070e010f2c131506090c170f011217040603021902150402040504060b120309031005220812071e0e0d060203070c021c0b070801060206043011 71
    0x1c000042d032032461012441c015900ce107008207450740c0401034120481d50b0581000c200299a0001c000d4510b42c009008142c404154000b03180f6400c2c505d020008104051048841d105202d841310b004000c3c0300c2c2c4010108044486802d030721140c03540e4014019400c994298154a5808451082d605100140031422511120504511070300c030761f000d2002030300300284180d402c42c0c2c450300194030b0f03030f01ca41c2700d400764440c8100003468650301c501c2d04042c00d069006408003021410081849504bc604200505501204285100390405186050b500c02e0141004c0c40140316441d00800c005a5008080030700140c020500004401e078007104c0964682c4002d00209400000d11f007009000a0652f50003507030809128140142c00d000c1a40c00504510800384222080f076030035050350403c018613101ca0a8002441d410403200d1507040c1a402507581c00c00400c050000d8240350307031020480c88031600b015030000c5a20140c070500d0010300d6015010307546050003407200f446011194114589036006122503030510 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 669333354 1250 669332104 669332189
    0xd0f050411030624013006050301020901140d1b09030303051602030702010c021f1101110304051f090b09060f070f020c01080a02131d070309030917070e010f 69
    0x250301210052800100045c14400500507004100340c552861244c4843d80054524211071210018019140384d540176600a038014045c0303d10320380e08815801107020000b91103546990500310b2200181c01c10303004a1900b5400791054840b13881e80038400005990203074905001c0d60325a000340d4122002c0d1060110700580041c030028005611031000040c4090004100d00a498041d8010300343c400c200159202c040340c11510025440380d001e0042c880c40d4141d022034607007145415101c4607111816841c684e020750300354200211003182980e10060083d6040b0803400f41500d02081c08960b113500544a06401040d941c0011340301070310412150a614040f540600f640075090401900d0820015000560301602801140815180828150010004105209603040f20b07101c0f402024a4040d05580415080c2880c07640071a801c40008421240c40702001d042091107000b207036050008503041400800d01d03010000880344807180441c1c0984000161820b114902080b0b0003010203004c1851800c00c4c0344 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 669334604 1250 669333354 669333391
    0x503060414191503120c0606080f10060806010302010e19030506190b0906150a0e040207051609050609040b070201090b0405060601110c090c0912030d0c03050a021812030d0f0504110306 81
    0x20406c0d01240042c440d00d008a0144e880f642c0c240e040c03d4490000e0015039100d02c580e00c070b0b01d0a860140324002c2c020340f4080d001c65411500001c02e20340c600000760303020708c0b401e90010741c1910011a03008000c68001044c2c80560400109001d240225007d01107410340c2001a03580503403420082d0365018040007441100c2450450101c6110b80c1c002c6d002d05024007061035800c0e1500d880303500007015118030603400340c41304110402500065001982042840c3c41c41e020420003541c42e9407502507001500800040d54603a603d84080b0b01410300f2840040030100194240010010300090160007007509880d813240ca291742041c0c140d5030f07445000b40c242c0e000018401283d4400214030003040a441c001d070010388000750115602786150701203000e000c412a581c1c111038680390b51501c40c2c0768209560440641c0342250185500d00d003044680c0705180b1600c54032141d40380388075041003154801c060306a000c0c006014143d002c8001488225001d50302c5500304030820200c0c0c54041151441540d074031962007800c03038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 669335854 1250 669334604 669334607
    0x50f0f01090501080c0d1103060406150e0d080415080f1317221509051e0405100918050c0301050405210708030c131a0a050306041419150312 62
    0x113034094070b450300050b02001102034042a030301600b00034800c0c40c0d10b80c035600d00f0f00b5005d001c101d50080d80107120500035180b01d800816030003040340c5031054089480c0416070f059400c01e509580300daa40001140450024880f690a070042944c51258507100981203117951170942041044501a000401181018101422221420001d000c5203491807060a0844500c550a00d41000c203d8219400c0c40d000c00260490403a4404401c0000d40002d4400c0c1811074041e260040ea00310080d088144603588030400210350284c802c040d00c0042412110034004030111007510001e506000205942c42e01402c0842c004509050280c540955030000080841071900140002e181250961006100c0000c1080340081150940603602900c80c08030707101e948802400503080c00104a900441803042c20701c42100d03504107c0c0382a10b9007441c141c100195070365148400900102403500b00da04001c442d0409001c0000800d001804a43c40c00c00010032000607035418078000750426103c01015161940c05066005e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 669337104 1250 669335854 669335867
    0x1513141504050c0703030906180b16021920040f0e100605060301050d050106090f020901020607021507030e0f013315050706090f1b09090b0106050903160f050f0f01090501 75
    0x2c0e000d02c4000944090ba120010300c1c1889c3d00405880100c00342081c01010802c070004920b20702c1c0c650005240348183c601d0034103210124103102405450440030400204450000c407003c122600031300c10000c40c0156858000201040134109010b40b0600c44aa228800c0c0d51141d6420741d40700424460640e0302e04801c100180064441c2201d45540764074001603922414080e1b02a140c89901002d621042d01c1c500081c17520000800410466010b06072001c8800c008284594209640d0301c0d010035988580c01d0382601e0005000f1050505620300380b0480d2601b541181c5c49500c4600d00c892401c4142c07894050304d040100715014124280c041c0f600a081d1650045006006880c8240c1d00810081d405890381c0788503044c101c8003500d000b01c2c280c9001c1100d80d030101055000d00740d41c003402c1141b100035454808014105001c6e01e000e0150000d0348070790b03503601080940081412044040c105945401003400f84d5081445a64081c02c141d594054651504800085401d40c0694130380b00414580303001120356 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 669338354 1250 669337104 669337121
    0x140705191d060c0703081206040f020345060108060c0c0d0315030b1006020d1107140111030403050c040c0306120308150d06060e0a090b1513141504050c070303 70
    0x8501c81d6080000c00206a8401f42001c003595140089040c87c04c03805000075590000c003168070641c0b0400030030542003040511402c0d000590302c0500c950010f0340c1e005038034160300d041002004880c4015217a440c110002107040c142d0304504140e0f003258541c198600683d000d40c80342100190004080300d00c4a9200e544101c1c240d400c40011440000e9070303034440c0c02d80110140c0c0e80402d6840301c1502405110b404003ca07a21508a900c0c1407800e800018404c141c48521030300504412607100310303421000360310030041c0c030103083c40040540340e81d10307071301d2030045d40d10002200f203d0b0140b41450030005540c1d0103072040c1800c4030642c0602c1e89903030300c40b42e400306c3d01504006d11420800c20b130075140c0c5c491510384200243c8030314400d040000d44241417060311a9016401401c1412840c03e10000ca00094254400c66410805070f045440c944048400010340e44c0e40d0f054101511a89003485050130f0300c0c11004c51a0241020844924107500c9500502c0305680d400c41e84103038045010403420000920a9000960 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 669339604 1250 669338354 669338377
    0x70f02071203030b010e15070f170a0903060b18040b1b0a050c07170d080403020a0602070317091218120d030c1b150203040303140705191d06 62
    0x4505444602103000ca0340c0c1e42400368002a030700c01c80800c0c10f50f0000311324180c40104945c90b40c07140c00034030004a154071034104000d00c4440c0d0a01e0a0080003206002680c03402e44103a84c00b03450b4400c4000081a5004ca03100a90303825080c083c8030170b51810601040455004203074142481541c0f90340f545c2500c5a0083c0000302c01160b8041c4c01d41c8103c841c100540440c42c41565001c1d50b410000f84400c0c644072598000541503840300c04d003486d09400c0060320008982c5c0c1d074146020030303a603141000c1e0b00b020b90464000d0300c00c9000145000070160710402038000f82d15500c41a80d900d4990358a215074620b811500d000880208009550010f0703960300a0048003440286214070b42d0403c41c040f5070812004c8042000032a4580210302c6009030014a50118410480d954003080c812503103802c040c00d4442c2e00d42d0481164000040b0f41030502c26080004040020980c2c842c107400c20040c020171550020812030308900d01d014007054081d03c07442511815808200681c40c02c81281820003400e6482101040e1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 669340854 1250 669339604 669339613
    0x4021e0d0209010906170c0f041517010605040617210d0608010509120f0301030b13120c02030f0f070e1f08030405010f09050d060e011104030807110a0e070f02 70
    0x80c0165101d0031400c0c06440804804a0454075015505402017500720302c590881c2c21481c4240a1a00c403541c8180e07045500329000f0485041424075550680b409800c8085850492544180c1203541500901d00302d440c00c2d51308100350fa544503143c1c9090b03248900c41c100c0075009142840007140021074284a40480c4e007648910713060038001907034101c0781254001e05050351100208516120180090b100b540980403078a482c02d031069400701c90b188014003006141c0722183d004248040d1591480c2c00d082035000f24110f80e000030a42001e01076684442c2c00b244a403094800030420110045505000f1780402030042c84800c1c24140c040828601c020103010b140c242d18403000c0d902410a040f00c100a044000140d560ba90501000616202424400d282842300340181041152505440804030381d8004d4000640c0036090050f6a000d440c1ca400d8002c2c02c40350200b40070040c08220f100600440d8481d903800b0307911181d02803e01c0010012445001045400c15000810340c0b4011107150b07010240c40d10648 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 669342104 1250 669340854 669340879
    0x9040507030b030a140106051512070504030c0b341e051c02070b04060e040e010b060f0a080901060b0307050f070506070f02061e0a0207021c0b09060c0304021e 70
    0x1d00d002043c132400d03140d82035102d081c9050414203104001c0601800d0f10320340c1310740c4d012145001040c0314034030000000205400004290398400c900760340241d0750281080c11401d60724003c04103039030022450f40c910a001d180309019803002d030402440448890740c000303c42e45050380d01d420b809070010b003c060340004101c80f00c039000240d0910005906e09111410060442c0411170001e10b050b03001e810541401c8001c003c14425990070240c1b9a680803030407640441e00c0240082080c0c0902100780c0c0c0e060f00401c001c5030044102c80e41c10003401004050341d40b21841c0e507441c4a511170980d0011700c1a40f124280810116040d54840c000804511405809045c6060703a10759840346002c0e0101e078044000394101e614841c24640c18042190001303c0c220700d00108120b041b000f61000d1402902d1a55650346c0044ca8200719122766400d5032124483c1e0048400d0000181040705011604030b0345607649000b524001184410520162402940c000c2c02840000d0820004064503004407564254044004500c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 669343354 1250 669342104 669342109
    0x30b22090c090e100c02060a1116030905030c0d0b0609070c05030d0605090f040c050f0406030510060611031908060a0b030a0903090501260a020903070609032609040507030b 76
    0x303020080808040014001d011000c3d21410803074006414080c06060200318040340383c2c00070342d032508035152110000b9a42034940000c2d0031440340802e034035102c608003400d0348107054014030120708642082d420b94400003107006c100070f0980700d003003c0140203401c041c0114425050408915902007801e05040404d000d4071f0f00d802e85036401200c0000842a00c03401c0034090340c103003190306a0b0400401080e65045040c140d98034085810031f401124041e240b04041a54a566550840c8006540200645a06816110106001d01458021a4041009820114802c2800104444644400f0740e01c0c9215410b24203821220701c280640480d41c00441c12001058010490300218003807140d43e100016005110700e0050100c00150f805941440791030380b114210441c0d200210010729070b0b66000194160340d0300e1801e900034006d50b00d42540500c152400883e1041e000441803080e6802803101c80c0b0411440f9001e0002000002d035101c50441007800f1224580c101500801c1d00511103080c0802d950185201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 669344604 1250 669343354 669343373
    0xd110702180703110c03030a0f0b13240609060f020c04020307020a11120d0539012421120c0b010506030417031e0f0f0601030b2209 58
    0x14800002224105002e4080d4142c400d00c04203c51150340320b4284041c844403d40c0741c0c00000e11805d0701548030707900740e00ea5808650002c18000402800c0003480100e15807030200509440503150808180501c2805500e5891074148003100c00320355810352100e040071800c071040c8140300c00d41c0301584038000701c10b00f039039070703a40043d40c0709a505900904440c0190b0801c118142c80c03e2805600860312040c025403500c4000c2148010382d20f15017042d0742d49080282d9207050022117650540a4a0b6516100e012002220071824403480c0c10040203100240c1c0d94499104030002c861180004500740d15020051092000b44803e03c2c002004030115040b146074441340801108440c0a0300014280e1162004010b910941c1030301600b01503030014214641039a039800c03c2800070002149412001c070002e0544403000b2880c05000440c01c4400c200c0b8280200340004128080c1c81042066446c000080c1255100344140390390341c0d10050124801f69443d40c040000c212040d035911380b41580365010400400c48912 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 669345854 1250 669344604 669344629
    0x5090435120601031b05030a0915111908060f0108130b0a0605120601050904110d080a020a030e0306070c03260c04050319080d0f0f1805210d110702 65
    0x400780092a05100040c12100038050190300080e905045000300c0b0390110540c0d60100002100062440722403c2c801016a140c9401c0101142401841010135214030003404417801c500c401e404403031884940540300d4000480d1a82d4016603a940c4181c21503104088181d00001010407013450400c03640c841c50000441100c103030031011740720507003080103040102155441c0610300c005001594103190000d90700c10b030054006811000c00a18014403540d8035600c03040c4080c0e10490050382c41e0300c5005d010b500c5011440c02a404101c103240002000c2c207010404c0da01c10301150b80e8001c404015617501740e0342d621882c41c01c2c10031404046050210180c880b41d4050003000002690346d00d032445c1408151a10a049401d00e001d0442c0507000b00c006101102507030581c05100d10089040b001d028030010003041c100320300762052070078000752250f510507a04000389894050025207145115010510500b2030007003050b02d160903800c0206002100150f480986201006e00c403061074103065400041e4408100b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 669347104 1250 669345854 669345877
    0x52b05100803030a02091f08061f17090309090103032c0321220513110412030507020a170601050a060509060d150602100c0305060607140703170703030605090435 71
    0x2071000c6031401650b0300ac4401140440803204000d03903200244201070300600d60340d0080014000c100803000501c00d0f00c00c0d200028006103429039503410000c249400121044074082c02803001600309003a003a07401462458050010034038807907030b48000e07001c0c40103070300d040c140300e98081c0b001c50070002e60040030445060000280c2c0c0f407400d04000400c5603010b218030f000d102d403500d00301c0c10b511000482001d032002c60303040d0311070071281c012103007402d40b464454a180254892000c0c100450541c6940340030300051ba500208584581e078030f84043c000d1610a034080c001c00b1520a01801c1041e00e0150010f006908440e0340200d0322183d141302c1c4142c281d98030307008a000b68010108d940070340744c1c3d40d00c112032000c0402c0c0307402e010710300305540070075080d01c224000a06140b4076031a44c1c1091700d50802c010002542c1c8070b80b0b1443c1e04a0080c440d01e65a400c20807086000a007071410024441c68201c0000c0d0241d600016060b114060514104c0c0c840d02e1121245103d0300c0f000400c1c800014104405440c180380d22 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 669348354 1250 669347104 669347117
    0x20f040f0209010201050906160c06230106020d11100e03040503010609020c0609060424200d0c08100b031b0705070f0e041a07052b05100803030a02091f 67
    0x2c02d000a400e40c1e00083c44020180d000340d08002000c1440c100510a0410354106501d41801c0382c00c042014010320f9030340e180300700001481624096562080c040c100c6505038240c4040c6550030204682d400d85001c00d101c00e503400142188072404c40e07a0300c4a6410785101c0304a070b04d013075580e10200f030039109507500056440780d0100b43c5440d466428420b4603070001640340588514070b400d40d5844028076a4051042041d00c0a0307810802424070341d4000c2100041c00385121141100d030840c05012503101d400784140c1c4a040040140129000d148594001d044400b142c4940034180841c2071001c2d08010701e40c01c502d4111900d00904940c82500808000f40a01d001d404450b0074207082c002c00204507480030005030015001c200c08120b042c00f800840e0141d40039001025152324070211a140640c1c49009402400c552501d002c0e98410140da04a00e034451409100e036030350381d00d080e0001107030070f1080c03c00941082002409030f1546900800b1401001007186900c060720b21104001210380f1905e90000c41e01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 669349604 1250 669348354 669348367
    0x10020a050106081506190e100305011a040f0e280210050903120301060c150b031002030117011803030906021e0c100e070905100e0903130504060e0c07020f040f02 71
    0x111071380150721100548050002105102c541181d81c00c0900c5050b12544950002c28144800300017480300a5400c98000e00c184000d100c540c0d2062f5058015039445a0f19005030000c400c1e26a0260400107800c0101034134000009804c00390100b1000f90410703c00d4403000010400590310055a4102c03010a40d451503100ca51041c1454688010b0822655481e641840100003280c2d00c40c44580b507140e03201c581351202c0c12544000c60094000c051215500d0f000d581c0710703505c490000f680514100d4091000080128080480050885901c440045c600707800107910b0f280031134040d4201130300d0070748201001807902161718150b02d0500b0250110040d0700300c000500010040c02040b5410090800e100104040c800320400d8980e0b4100c2849400c00e0719484d130000441004641c41d100000f0042550748031103600d0a90032982c0c5950002400c00383e4040e0280010503e420305c0c0c13180c0c100751007a02092804d035858060010a0782d0b085410226800480c03e100c61420742c6540c003582c0900c540c14000941c0b500b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 669350854 1250 669349604 669349633
    0x702250315020d060b133f020306012c04030c080f04090203040303060806071715030304090f020a091e060e0d0f050601050307050607110f01021c080105100305041110020a05010608 79
    0x802d980c44407003402005146140000c01081c840121200c800c030b2411054030003200d40380c03401f4001e900701030341c136006d201d0000072032558030f0030700941c11075101030030080c100f03150016401d0a0f0420740b0017400103040900744c100040c000c60700034004c079000c0c045940d080960b0b4000356000e03680111411800643c070346208110148080104a4000d40642080c10140381030000c1e8a1304040c2c0189505421a032441050034251828800c43c0d000e804a44020b0000380c40114400c0c01070347c01602580b000890f4004001800300d000001100e400380d5001c06c580c682d9140c510112144a000344809a0240b0500c00703840028004410102c00144100040d001940c03500c000c0508010045d80700f40e02605080000c0e9000661b0010358201c440d4080300d03134680c98410040103c2c40e05040d003101070a0109080c01025a040d0800d00312070407502d048564102c441c140c030400301c1c00d9803003d84d40200034158505903450340d407500e44003144401d5400e104a40403092182c0750706080d6162640440b076603410003000a017030380e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 669352104 1250 669350854 669350887
    0x22061503031202190516020406140a0b1c0f1b0f0e0f0307050904030c0209040803010306050109020c03070b040201140d15080d080a0f20030702250315020d060b 70
    0x9101101c04604202103181d03d040c0c13010700d9002c0c3c2401c10000148245840c41940c00c240341c1c0039000307003041203125240c40d00300841103040341c00c6512030002c2c42c1001801e003214004075540510f00001110100c3d05040c5404068101c00c2130038020355440d120260780c009610304103a90001c05d00e5480c0c601c2068a00805000c14810301101406554003510710102503d0010348a41100c100340c484400b5a541d40c1001c440602d8a0a80254009904428881400442d001846c140ca0261104200a982c0c5840c0300089218540c08450f07183c0060083d4408110300c884107540c054010b041250032a0000340c03810840d6801503207100c141907510360030564120b0b4a400300c4400340214000428124120320005031610f1401440803111a4456420300c0300f01900d60010640c07085c0c503034124094001c4035440454260411030704034006105602c442194950250320001360b20404000500303180e4203544590740b456026941240f0b4564081008142c022644d00c0351038001d0283c54261a1201d5140600ea20503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 669353354 1250 669352104 669352127
    0x23010305010e0106020d05180a1d0f0103030813324e0703121415010e03030909101a04060206010b1804060602011a0402030f2206150303 60
    0x142c0b45005001c0c82d900060100440049803e0803500c9444d541e1002401050f81c0c00c603243c021880c1034000030302c8222454408141ca0000350340d0500c42e80d0b80112007514200910000e00040d4801300030400a016400d1392074440790280c0c0d062200755400d07081c8413810f2098901080040214882d603d058440309004601d501c3c1403405c00785101e40c81c003058000c1002c0d49446028044480518003520104003d5003401c2c80c802c1e466440d80d2101001d00380905000e4194045003040781c2041e54444801000007001d61142c902c01455100c0481041d00440d4480503c040c62a0503100821500c07244e41c2d22000b180340b055143c00b8150344458280310f2110603802441054000c3c4031030500060142c1500400d203241520010040c2640354100c080e004044490050640c42d042481c2020100310a41d0641148003a03d0301040d0041d200203000c020b11007244011600420520289000704101030541071800141d0195407200c060160048d0312078904482907802200106400351404100301034120440420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 669354604 1250 669353354 669353369
    0x70f17030f03040303020a0207151701060807020a06020903070512010606030c0206071b0c05042f070b06060a052106030d09030f110102010e030c0123071d0301062301030501 76
    0x300a07444556060324003000e0402414907801140c5038400601c01c2100400500001121a14140550b000604001e402c0080400300c0e0408000200381c8074010035200d4001c03c899401015000603607192a402508469000b43c1d15000d034401c000b83c0366940d205808a45c0c0340d03100c00000e03414a4884041c0484d41000c00302000d5400c04810070040640148404525040602c8440300c114024540310440d00415003001c0e5000f841c0148034035075070f07500c0c044114041c00450511004403000c0d100703030480c60085101c000c042c0403003840000c559080c000082c101d1081039080060501030f12518001030a81104440d425808208081054a2504006022000da40e038100600198103540f41c20f68080c2d881000985082c3c001d42e4030100c1381e4401d44c4800c200100c14003d9030788a030146241140a006560701400880e83e00701c1c42000c00c08000e03600301d0b0046040f9158107040c40800104600c0344900e41d0f01c0c082c1d16540c2e481340050803010180440d01d010080118102d1441da80340f0000d000c50340180c000c00c1c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 669355854 1250 669354604 669354607
    0x41d0105180414011e0510060203090a0603020c010b03030a050a0311040b0a0e030c030d03090b06040516080408040308070308070809060c04050f06220503150610031d070f1703 77
    0x11038849000c150341d500a500008000009006070078020b024151014540c3d11460588400c5203d0350303401c0d8840c40c010f0400341c848410855880100326501d00400300c809038020a9080c04010081c080ea0003080c2e20b2a031755001040f907861200002f801c0d600f0403903480003c20700010b0400c1d055031345480f555407a042480e04441c103040c1002243d1030700e401888400001d11540c544041031a607410030003d81c400900504460624044900050141441401c12281e100a03100440c5c100d1a1070700540b0b10a007101d4151320441e81d40d22108807001200507105652030001004003001240c9024002c0ca10749000351100e020314200448020030054006000810030742085050025030864101194120381040b20908000421100040c44038466050070468100b030300b04900c03481c813000d5512842100c4046040c1d036140c01c10300345071200442044503050b6009080d02042c0d11160301a0340301200700f0040c0302c04580603a1401411a1810585801070740c40c03060381d0a4204009080403c0b20700450b48030300e0107103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 669357104 1250 669355854 669355879
    0x1c0305041e03090306020c031612020f06150913140102030708090318090a180f02100c05151003051e010b03030a08130f0f06021201060806010c150e03041d0105 70
    0x100340080078040100341075000a00710048107020002d8504501768110030050720502070ad015003141001000c1e51b4054040c00d950f00d1855200402e00b244942001918181600008000c1120f00302004040d075007074a0b8914000380c0030030071001c9030040c0f20034810001650303410f2544002d00500340c02030810807241e104102a000c0d09a158202480040054420980035100c82c04178070060045003c460a09901030301e010014860003101c07030f201140c02502c00300d01c2c9a00d1480c08991304200e4820180665001a551480030842c4500c40c951112640d86081c0405840380c0e80d1078103140484400010951541c42c2e0040f00d04000e204050300288220021494203085010107016464005c01c110a1140400c2d01502480507580c48603200a5221003880601c0e051441c2120094025800e00300401601000219400b4001c1e20020b0061034143c580002d41041a5200c50300050800d8042c9100d41c1c4032100c40019180420142000c5c204002007a42e01d810003a01b507400460050780080d10490521585 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 669358354 1250 669357104 669357107
    0x2180f130f1e020405130209090c03190c031b111009140703030c1e022d04060b09040e0d0905100201090f0308040b181209031c0305041e03 61
    0x48626a200c204008100d19111012001c01003188038915007040307801440042d1074021543c02801500d20442d522000c04c1c450032560300403030156090560300b25042c2008901221950700141d079004002c03150707401221603a03101c007009540b41011804042a1514480d0300703202251080099110858038000008075551800d07107a03208001500500c045039107020303040c04c0c00280ca2104050400ca003048880b032550f649401020103045800c1a00c84941400504a0341c4e075a90240c1248150002c000212000801000100151075103034080c41c0e080200c43c2c01c021a484034042d0100803c500a403003515525180144070641d200240500d0403500014103040034580c102c81941d00b44c2e4410345200703104201d460010780c010480c4030f2014282510a41c50314040641c0a06160700c00c610404101c902c03078441483d28900804029111003494001811103075003100b414000d03051012006045400883e007250302e0850b0110040e85010029880f0001c002c1445841410030420701d030124500c256402035601c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 669359604 1250 669358354 669358369
    0x1170411010c030915020f0d0518130906140603010b090f1605220501030e16061805091f061e03150b180306160504030224030a02180f 59
    0x41441c1403101254010b01414821104c0e0310203030440a640c10101c070a1281c02940c0c900034409602650300c92820895207080c401c000340c0d50060540c0c8000c0b02400440c10801c4003602118000c0326500342e03205124404101c3c5070003140c0000b82100d40e0545103007001001e040c02c0d00d550115050080110409004541e01c0d00309015500503a0001d030416040c0c100202120248924801c60700265085600c011045610101110880b5001d0301c1c2000003c0740c01c01d03140c0c1c40300b0703e88522890384001d0300c0301000071034021400780100c2600003015411071500c440000d14110700540d4080d040032409980200c050800d151010040e25841c1000b010030b1144011000501954140d02c6c07081544030405030304080303081034000014003218900383d1385500484010001d0040400f035194481e210311408100400d0746246502c3c41d00c190380d96541c0c641400d41e001d00441e0f00340188003403034407075400c00030186188004020790701886918201617940c070383c1d114440600c0c1020130030f42d13445104a40200e81d09580c4044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669360854 1250 669359604 669359633
    0x27060c0801140f240a0201050108070f06050a120e0a05070f1a0f09010e0405090606041b05071704120f050c0108070503241005070c0803031e09032502011704 69
    0xb5540c0c610341c241000e4142c513800084100c041c00e140007194608a0a030190072a506841603003045a403000d90790184c8051f6400f0703034030030900401d00822003581210310910101c0300300901c0d03c0000c90200344002c0c0307640c5171a44014066800340c21480061261020f0309045100401c0032a4020500d00b031100729880741d074800e00320b40c2c82000700c0000d0340f02505c0e4090010b01701c1824009200704100d160038045951540011280284901e15000c00c50702d560f940250f83c1c00a030b4000b60307512070502c20607a03950102c808901801e800c2c080004e100024082c00940d034040946c5100d040b055091000c83d14040f89005104442d041c1440919000c01ca030031070344003007a80d85c0301d260040070304c0c0e851400d0383c6002d00c0640031403842604581ea034040303034200700e41000050070100d102d031104807416039503400b0407602ca00040d580c1e91080c40c0700c0e2042406031442d00007000d401469030002d4a103021030300017070301c40041e80103c000400ea54001300030303030107640c2c00c10b0000e068020444030751031162031f0668515082c0007414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669362104 1250 669360854 669360859
    0x306140a05011d0d031106100f0611010905030316090e0714030c0c2506020f1002031905040f0b070206270304030605240d030f0327060c0801140f 64
    0x207420689082003c8148808030360301505040a05200c3c0c2401001d03030780300b0010b0360340920400d40801d0131001000c4c03000c0c044500c02101a035405040100440301c00741e000c48062200d40d01c2d034a1007004200140000e502070b0030007005101e901450580003800d624035603032082d28a00055001c2209482e0816800c0320083c00c2e01c12265642d030b83d004941d0003036000e861240340340c0d4032400b2a02c0000c80441003e10400402c4040d0340c101e0143e841800301c0c1d032450010b460300741540042c10340c584c05c19543d4024513004150168030013088002d0070010030848200f11021b41e11120381741d0070a0b061048541541c0c0c1c022409101403e01480d10300c3c2c8018088a008070280202012101408507200c42401030740c0c0550f5000805001034240180b800d0704d802d1102242c0f601c1d0fa0441101d440b0f5900d0040c1180070265407680394a084588225000c1e170040000f4a04d6506500500c0071500d0081070021140070214840d4500098520101600805540058000ca6a01c04400001001603030300c00c9140f10410404 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669363354 1250 669362104 669362117
    0xb0301080c0f0d05010e0714120a080a02010b10180609060c020f01091d060f040902030a0b060409020a090c11010203070909051e040c0602060c070206090d020307030b070f0306140a0501 81
    0x203030b8000c182141e1180701c01070130700d52804001c010145004900e10781100d0303284e0310103000106000108010a80d00042050740c0313511105507240003581c0310016100501841c0000102200d014020407a072030f8540c1160320002e40d00b0031001c03080c03821072604080600b00501c0c0030028141440c101504240341c0d0b49001e0720440c03036054807168503031095001d44068040340301d540841c84c003603500c400140350013600c0c1c0c10f11070142c04103130340042d05081c403c049001c0d4000300280051115616034032141800a00b0300f44d045a03d4030302180250f100c44282d50000c0014100000d41455502001000da1244100b40c1c4100e03401002808002980103103403900380c82e80742c82c3c00922601e8006064501c000c142e200c40c5c042e03500c00420071003408a00c0b0310400440e00d41d60207444160b0b0307409810300b20398840d98100070750282c0180201c41c04c0c1e0601e4100750700c0347c901c00707801c03076203115180c0e150748000340c0c011101d080014088110a801840d03150095000070a000d00c00e29140f602c40b9000150a030440380039540c100b050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669364604 1250 669363354 669363379
    0x3200903070b1602010e0d05060c0304140109140c0a0302010806042a1701080102040320131b090608010308071e08041202011715101404080a0308010b0301080c 70
    0x80500c40e600040c00e007840e48950f92082000c03200701c00703c40800140d000c43d103146810401c0b41040040c2884659004000c0c201c070707075205000260a6040500305843c0101028150014100d0074440c045050b4020131030fa11024442d03510942c075022046000324000d028030042040141d07080165180c00c00700488011480345041282200003000d4082c40b11840c1001c1d401500310b464009072181440b101072032072426941c1c0c840d84002d090303104a00c07009001800381200280110300c0c04910b624400e4008041140361449a032005003601c8a01d00c0c51340105002c201907400640d0030034000d0000b001541840d00f41503245441d0f1041502440d8409000c0e4400394618602030b49100c059400e440340c0c810030041d11191500e4004900583d0100128081440c1c2d00b050071184141708180c0b44100300000c0000300c0407941406200e4043c1c0c1f0201550180070080151440840c1d1100c0504007405601000b04018010360600911405041e848801b071300d101040184114600412100b140040640340e1115003803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669365854 1250 669364604 669364609
    0xa09090f03051b011508060705030709230d0b010e060109050108060d060e060705031009110a140f040b0d0518071202010905041b020c03160603110f0304050703060507032009 76
    0xf02c80c1074810310b15442c28101d0070140c4544030000c8103072868407003116500e90b60054261202d1000b9504100810f8009400308031082c5080c0884200e4450b080388181c501071800d02041d440d113100401100c41c0324409005220070036501444551000007407a140a0300d519020000e880c40700042c0c605070040e0b40c103207040c000b0300009070483d4100c10b07800011210303180b23440c03400202150010b445854201860000010303251003203000c3e00d041643c2c80344909240c029261b4042c0c4500c54001541c1040d0042441031041504002024000400d10315030311603640d01401c0800303021900300811080d00403484491529401000242080030b130780441e10000c0e00d80003d0f0005903684d0840d544103a82c07050404c0b541030030800200305419507200c000d40032120709a60a10030162240c4180c1c0d0010407981141c2c4013000700300c2c132980000d02c18403528003000f880c0c030859034880c85007644202c4040c0ea0540c81800b0800402c0640d110700340d881080740c076040002d1152040c994940307604a401c0603a0046000c200c0b5a10b0340e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669367104 1250 669365854 669365887
    0x130626030403080304080c01050703090b27010f14060904080f0a0908010c0f02010b0901051e1f0305042306010504021b100e0705030f06070804240b0a09090f0305 71
    0x3180c02c0800f0903124607051410094a510803041b1814135400c10300841c0145002e03029500f021640130110f44c003981e9403101c41d80259003441c6018a0340c0c0d03a45802d00c202d507250030310462496604803080400d4122510079541d40003200501160302400441d0304110209000c4400da840300411000c0c3c99994a0f08078004407600c00481d08183d1803546410f544800464006554071100e42e402c0d002848460400c20401081e41c50900c5119000765800303580010034801078281c82d041e00e5008101070540c52240600740a2140769404040200c0d50752401e0009221581525801c586541a031100c3d4007020040805d495007010310500740560380100c0c800700707190751340c0400d0002094910102c07030385c59614a010780d001d000c01202e0032200c1d01a8070808200341c00d000c214420494800001408141c0701c00e842202c180500a2040d950741c4040101c403000c100c505181201e08407100d540200d0310010a00c200a00b41c803032039105826207850040e2120002e4400903151940c69054108141c0711800540000b042c1d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669368354 1250 669367104 669367109
    0x40803091b211c0c020a061d01032004080f060105090910020304020418060f050601320c16060318120f090b04121401090203070e190203010b091306260304 68
    0x1418a8980d420f080c0e40c1d022046000e201e000700c43c0c5096050713855005503048040820000c000002d214904403980d4040d804c148a201e080440e0b49038500703001c2d41d0b00b80042d007180d0018411504902c00ba24281d81e02044010702401d401c035102001400c2001c05103036155504084c0c1400c043d00400001d055580707aa1003c070b001080e4035a41c018a2038a031604000800ca6025203445040c9002c01040d800d51082903540300701b0b0404640a02050444010745e001c0200050011780c460504201c079040c005400c4c80b152010248485548460740e00700000a01914281d00c003005404003180c50308404140c00c2c1c03c50510803112070806040384c500c4040e049403081c2c1990019443c00c00001000075180c0076090030705051078010f44041d03202c10002c3d09240e003600c0c0795100c042d525034444003040c00114070440000f40c01000b440078104510645240880c140c2c0c0099200c07000c00b900104110300f17642050400b0b000c510103602410015641000d41074040d049480d0b007103504a00d0000e0b45181c0c04d000400c102c502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669369604 1250 669368354 669368383
    0x207171f0b040e0d0c060b060403080a0503011505090d060c0e040c0905041404050c130b0d0c030233090a051315090501061707050909040803091b21 65
    0x3052503111504030142503034040550140785451044440000007065121a0000729035a900d4080015100e00b8050000b040f003059214104000010000c1c2050008080c0d081098a49649961401d1295a03601c0d80222080061010401007030440d0703034030040d024a031550f0180c000602e01a14000031150042c8020300b45e5001843c22424003407064010184c43d0859008a80034000c580803005a0200510203540003084c0340c0c0b0103c601403040c0380c41228003442100c101c1d000079030844110009070403000380340f6042d00c5450130b2580a205509000c80e0003d40320b40c0d6406c0030398041800078280044c3c000401c0c915907000d103012848140d590303107010071000203203401003004140754541c0d42d11130000e181c03400c525040340180390000901c445250041c141207071035640354187c41075200e00480b901004024544020044100140341c0340365075004010740a0350040380155143e103841c1e050702d0304e4050315007030b581740044590b12085001c2d030303034101c1813104244500301400307607084c07070004c0302d440d00c44001203075031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669370854 1250 669369604 669369643
    0x7030320040e2d0108071401030b0a06050a05070c030f03030506010203070f0b07050912071403120403020409030c06020d050a0b0402040e16030e060a05090d030506060d050c040909030512060f01020717 88
    0x1175150400244001921002c9422075500c460060055084524180549801070542407040003e0341c000c3c03001d060303176101c50300301146008565500c100061001d5007003110a6000c42d05404140340d410312606900c0302081c0006d61600c015502e4100c00c1b038060041c002d00c1d410502c40061700f064890f9065815616020f03085051030f485101500d52503c6440c00390320200c12420070042311320303e40011808020b038602c12003236280c1411a000d12014280d040f1041c2e040c810544424000200c8502c02000d1a00200400082074109480f08009480b800f400c00c0e44501e0051009225074800e210f0640d030460086800c11032000514481039010304174000b42000380380a1601042015170320794000c24440d8030303500156640c00c60002780980c1251419a00c0b2074002001344803010391012036600c0075030441d0042d241f0a041c40c0c3d03214048025a804510105c0c001500880d400c03000c141c840e030045401c00070455200d842d819603140001e556000500c117202c034a070084561460b80150600ca0b5a04152103201c1e1103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669372104 1250 669370854 669370859
    0x4021917070509060102030403080711060f040902070605060111030405042a0f0807080c0a0c03090e10050901050906060a05070f02090c0c0f01050c03180c0607030320040e2d01 77
    0x12074403000e852040601404510001546071740c0702000f1241500d6101d900f460900c0140e8468580d07900300c50002a801c020300704294000760603c1c00141c40102651500075988040f2841d02a0a07501d000d019a8180400c0c401c2100c0700d19000700c00e0b034081c2c2d4000d03280004e4500141030b410101c0b40a950b24001c00740d4002c20300340a0564881d9131030b00c002d4056140c0c0c7d502d0392128442100c11810488806a0814040c4900b17085035104209001035503019140400c44103841e2000349039905070030b1340c1c0060f0807a10300408000360700b09103080364010841207880c4902071804c1404900148a030703c00300f07010014001684020420250040e001864014100f8002c1d403501d006040501d40c00810702d00c05600c20405d043c011400140151842003040504050460312160464403d4110742c0070000f9080c054101a00328a454401c0a0046180241c4d00030540c01e1075107488000c0b101d041c00c51032505176402c21045c0004480e01101c176402c584000005501035400c0300440c4054071b54440400003260290000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669373354 1250 669372104 669372149
    0x120c0c1214060f060604170a0c080c04060b0f0304080901120203040602070b0640020c03130f060c20090a050603240613060f090f0f0c08040219 63
    0x78000742502200301c0360b280c3c0714160964200c010450300719500c4041004284042610500c03200685004c0b8402c4540c1405250754450200342a42c004e402151b05c0700d900c0c42503031f1600307004040040c10360402903844d184c08041131004500c402000079284800000300365896074802c1e07456034950200300078219143d060514007040654407000080e101500041c0c0418000e01e003200c00586076100d41c404c00085040942142140c04546252019109019900010210110740000c1a001c09454051951106048101e00c0e5034102c6401c44004007080300010b002e03068010031818446a0031508030010121600485000c0b181144041030300241c41400384000d4044981040b0b0044108806880070921902c0d040d840304554034020481c20071040010422508218911500318480d04401060503502d03214610192401540704103034041d91100481c0d004c6085106a184405801000313000c0d81c07520f000020000040540b0203403080c001c51210b0529001c220908200900d50120110010001e9420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669374604 1250 669373354 669373373
    0x90c071a07110f010f0c080f040f02010521091606080f04052a010e1002030702040906091a0a060e0f0601050a09080d051b010b1809120d0204090b0d120c0c12 69
    0x1c2c41a80d184c10b00c040b046c0068080c80640b88140d107010000c840130b0359152580003580c101c1e50303010303414060108003851541041c80200750308080c111000c030500f800c0c41c400c0707107161008841e05540010410b1a051010b0307507010030843c4e00310039643c41041698845040807030074040300515111150400410318032650444020684658030243c81e801420794a54052081148010100d00c00503082040700400528040d81b1607444507001e45000146014507582c0e040c14440400600d4200899003c204030380120380c0d0207844050b060031103080102c1e06114062801415001d420030741407200114003d110a4401d8441c0707001020501c048524113540c1d400c000d401d55110200416100da8804269481d18005005560420341c014002c0042444249070301c20709980050b10304003070740c01403490a44540389080060420b02d0242a00140e0b120b14041c9124122258214844d01421056841c1c0020400025000d000c0c0d529a0524190020481c03500c6118855140c20001d006880f0f90041402d021600c103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669375854 1250 669374604 669374621
    0xb090705060a2a0c150c0c0f1e0608010509040602070b01090501140102030c30030c2104031205150a030516050a0b04120f02040c0e090c071a07110f01 66
    0x6507440003c041111050391803400c0c03a001510351803420740200b11720184d045105200d035699151900c1003a640340c0d02d80c140304080e584080b07403025206d4002c2c003441c402c02c107c1c140c099003100f0034a01c0103843c00f5400350104005104841c45842000002404d1000680403985800e43c04a490b01c110340e11181c0300c6005003c28000c550180890f074114542d154000030485001d039041030001c2c4580000303100d46512a00205003c0120031300d42102040d00c108800015600a42035018026154180c8414485882c041c039036205800e44081d0042c4400320307808c4400d0030121050070300c012900c0e50b650315441032580100561142c110844003800414080003040d40e07684414240ea0360074485c3e84c1c40040212410041c0155149600200070400c6083d80300032401c000b952107031a80700382c1c01500e82c0009d0201d82d680041c403004241000412034843c0b510f80012948250400009410300d070302600d400310403080e007140c0c0e0744000c210f03203022031450340c0240007000301c02c14007804a41c4021142400c4502a00164 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669377104 1250 669375854 669375887
    0xc1a0114040e190204061512050f060612150d051e01051b18090109140109020c1b180112030914010c0b07030f18110607020a030b090705060a 62
    0x10114a1003601d0700c1d0007102e550008150040c030300c0301c1e0300000a01581202003812a8007607500d500002e071803004110007050403101e80e00c801074002500d030714202c00d40c3c0000f428400603881700d03405c00c40b103540c3e01416142e5805440c000c480e05076540b900b008201507444e04403642e00c224800901002c0000c00210203d9542d90046000001d0303e80403440350a84509035480e078030317402d044008610403000c0340c40503010b52850342c0c201b040c0041108001c50200e403403c0e001090b00d5074440c110802c01030303000d440860040c04003140c21032600b0b00c166101a100c0c41d00c8aaa40c51451408402124a654030700700d11032603c9900200d40c20950b905c189082181c01034020843c00310300014000603001c082c0c070255003150315040c4c549c10b481c842c40751344a04036103400410140038550307111407065030503205100d102d00e01140302100c04010070f841d040070582c00303400f000e415204840c200201801a00c03040050002c9079800b6810074a02d4680d08503a0307003840c5240d08050340106020a0414280303500c0307600010001c588 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669378354 1250 669377104 669377129
    0x60302090118080f12071e0512041715060105090d0609021c02010f0e010f0c1509050c0a0e1b0307120213060306050d0c06121e021905030f070f0c1a01 66
    0x17078019075118011a0005840340c1c4900c4110071700324030104070b018080c91246056400500e0000322601185d005074002800684202d50041a01081008000035002c5800442d40040c0340c9100000c040b0311641d00640c6c0240e05030705017081045640e4001d2420103034001d02401410f045c041c2e40d010307929910706099000036504c6040c3c1000d0390042030001107680c0b0694801020180180040c0c81c944010582200e2080070000c000110b43c46071321030b610780e691080e805001d9251040042007805086600400324152044060100400d615400e01110480c4034003401d4036981d03414001d4505019600d000708500703000103940b000034035070104000241c86454a0401903141c0391002d00c004c80d084218010141c00001d8014820750b4019444c1d039100f40c4800c0d8000c03c034224500e179070702c5240303100c0302650300000d4003c16110304141b58900c03d10b402e4a1580307005421031900d081c56034003620025007072105101c2c544680303183d590300c166000e0701202c2d04580400311481d41c02c501250700110910594072490007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669379604 1250 669378354 669378373
    0xc0507021206102c0705190c2a05100905031608010513030c02011116030302010e060a020a170603010603060218100e012f01050f01081c09060302090118080f 69
    0x40c50b141194150b40e0005850071100f03181500704c0f0100c4000350100060110502c2007080d154281c0c1101b00883d1984e681e000342a00e80c82c50101d02e010400d80070240b20b0720003001088001106850002e04991048805411010054406540852aa80100b80c00d130040c0c5030700300c021051700c1d411201140e44480003000580e881030900d130310b0b41a00d2840100050000565078026600c12031a910301401d0210595000403141400381c0e002a6803a130088025035150800014a580280440380e48075031160780a514207105004001e210100005e030351411001711601180c0c00f903c0075031010018640c07140741196101811450b98203106943d042e0380384586203003102221814400d0071a0004a10181c4440c04401e105405011000f82c1d42011105128013100307010086950900030790b40284611f075070090b0b8550410424504007070700c44481c00a92901c40070719224090b407207542038007260324610b401070301c80c4141e0004030380021052041c40d05903e02928049141080030840d08407204500b0100c1d1340804 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669380854 1250 669379604 669379619
    0x3c030c03041101020604080306210d0c020a1a031b13090f05060f240c151006080c03011404020c0703030801140f13110c0a050106060e030f0c01030c050702120610 71
    0x1c00702d1b0000c000c1d02091004c2142d9091440c010b22810300802c0102a03000f06008684d0f24201020501d000050a0303030700760300203509214200c0c4c00500111041d000418000b14030825a51002074041d11724080b0a0f041d404ea4050404151a1603800e0b21241002440d501c4042c24040c10740b029401501c14a4040404e005203011030f038002c42914054407008106d00307030b81c031070140c441e04c201c3d50b211a42e103040004411424060101301d1190071032400c0580743c0e08041c3c100c0e8194013880c2e046103084c400c02109011025200005582c111540c02c4014130400ba684408500a030041c802c0d4110075100d025404803c00d40c206140b00d050395a483d100300490755001080180c19440c4d0422640c201c011800049420748403a0041c05807610140030640c90304800103a030f5403500d1440d010a44643e59660b6050001d590f0040c402c075084a4100c000301945422044401d0300da090598006060680c0c0711034280009020301c007910303181070f0001c2c01d4040c0300060751500d945445003166142d400f410001030205006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669382104 1250 669380854 669380863
    0xc0301090c050928030222060605042409080d080405102702040204030c0b09100e03100e12072103060b0f0a05091201020d0b0301023c030c0304110102 66
    0x24010210304d01c0311564420008030b200c2016010510038044100400540c0700d5540e203200c85000c40c0e281c50003038624481c0f240211074064000d042001000c02007044a65000d400c040d90814040ca41d500c0c0c131240c003070030588680900e50f01500440c01604400381d41580c00c07c144600c9580580203882c0d0394071110f503021045503c0c00c000703003031101c1702920314010500d185103000c2d10031440507100500d0580c03692500c2000b084180e0280404020004035a00d8908164942b04030602081c102910014840340c006a00d81c445010100085c5030341c1c44990000e40130802c00208480350400c03616035110818144100d204400e22a5096034480146060821611074030841003101c06258800342415081c0d20821210303030125200d0310030401c1c20f10644219a5508100e0312100038100c000599560b4072540b65400c2c2e4001c81c407441c1c8640d206000c50f40030f4421000a100c5000c40210006440390051a40c0e074101150b41d0010000d107885c040200003c2c0e00041c00194007640c041e09855400503240801266078 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669383354 1250 669382104 669382117
    0x1b020601050a090f200c010f0b010c201903020a0f030b0412210f0b0415051315060e120f0c040b0d0512180d02240706050c0301090c05 59
    0x94001080114507590b50004102d00d036003180c0441c0554045d9420314040d0748644c1800c07a011800214240420381c07d119030180300748090300c00c0c0103070600d110002e440600a640080c0211181c3c80d1b079070325000e550180d5950000e200a04801d895100c29958030b01814860100f02d0150364511804182c12185c07100b081c0c21a075004a95030b80c42c0d0368594440000340301c1c1f94641010302080c1c200d0499100e40c1e540a4400c048640c00001401c40c940340208402e0794482821180034614001d01b05488100440b1408150381d000c2e6a004035000890641c500108040d138501030500c2c5040380041451688088401c10707421040702c4501440300512070107a240d0194250064203540f0109560060b81096004680707a45002440c101c12510741d51039090500050290740645903000203011f6140c2c4982400100b600d900135241c100c0503000d540c0c080b40310380e14a0403502145984100020020b03200d40412150003940c8001e06004909000308030201c0360700280180041d50317041c02c4a02c02842d12410590b2074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669384604 1250 669383354 669383359
    0x1c020303091009170a060501151d01020c220501061404151e03060f080c010c060f090507060c0611090f01140f2a011e0e0c12011b02060105 61
    0x141c0308407201003240c0294103961000c10301080d004009000c040512458864010081c090000c4c0741d0140340581c00c441d0140c1100c00311403100c00b011029584d00100c5003200140081c2224000158030740181d282901d1030601a0348600d2414004121403104891000303201c040c0c81040c4416620f0301403e0764050006140701010341e8050000304028072051146a0f80403110707040c0350320500381620681c05805500160320012980700c841c10030000d0b1003481000e0052544074003608040d032019000131f202c50300c408000b40100d6250411451101c03030b140c0c8690002c41e03000040340d52460b502c01024200322030f03070a410348020340380400945c082301c400e90072204400720040001d070144a000c401035a4440303810f449800a804103025560101822000900c10b141c090907010405212660072240c54180d4808070520590402c03441800344000f07040420f030300c41c480740c0c0081442c8601c3d071002803408405d09a941c1d031095160300c81a0510300c041d0b0041d4041c01c0a0710b800d041c50041000103036503903103082c840c00d43c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669385854 1250 669384604 669384607
    0x11107020f0a180c14070503030f100f1a0409150e010905010e01030b07111e101116140a08090112060501080c0a020304080d050a0210050f0c0702180c0301051c020303 73
    0x400c605070940c08100b18507018100448400d000c0301c22600150086e8004440c1680000188103064110300360710b40d0f1099001034280c403100d04204010400500c244038070400c03030102980540c101000c0c2c4040c2c07005000501b03010051092600c0104205804500c80c015101240b80c0c0086580c500324020203040ea5501d18607400c19901c0d594420b40b021703600404010401c10700011003c1003000601410034080340009038a01c3d05908080440d052030b060101c20801c00d032800c0b10710386a46c1c5e070410076980700002c40380382c0140307001c01400c0040015690401440d414050303d03091504026104000d880100420307601c61921800c2da003002400c82e1001e0155502080c1c1400004100c0301c1a40d0040110224a1040e039003400d41d11062907151603010080c00c00803440105031300081b00d5040100e946001e041100600c040d0500c0500300301004000303041603c80e4840014030303100f075480d082e4001d1418184140d003481036250111080e0004d401c2800b03414450b0000400e40d2441070b442c5003059501580007006103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669387104 1250 669385854 669385889
    0xc03020a1b15020f0d120f0501080102030603010b030303040c0608370e1609021312050105090115060806011404030b070206040519170702040b091303030f060b03040201080a0608011107020f0a 84
    0x151486d01c0d08072440d00e2104e450741301c0c1e061a000a0300a8900038850340c0000350b120708110080500b0344042c0b0300ca440c020791080c410071020591030690b100444080d4200b42046440762000e0502401038041070807480016038150802c3c6145801d014203401841810404c41080c881854a840b072240b08400a0704110b10903061243c461070398001e114180c10901e440380c1403075464901000c072001c4031409449d82d9650350304110120b031080c0600703611803002c60008800c05060140103014904040c05d0181044801c520001d034209078030040341d0155400041d502c61074540044029070786c80c0200c0c1d00711224056000c070041032244401d410f1901075070102c00302e0644010400c420006400c0b1032000c4e64440e0301c920a5042c1ea8440c0072800d4040c66443c17280c0300d901c0c4410304014050f01d10b039181ca106018a1300000304a18a100c40580350019824a0954402d440340b9800170060029504685015460182072402c042030f04c00c003d25403248266100144601d20301c2c100710309000c441c89488440310304010403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669388354 1250 669387104 669387107
    0x3060e092a130b030313030b04020f0a030213110f030f16030204080c1314330f010f02100c210501050d03050d0908043011010c03020a1b15020f0d 64
    0x642c050a201804803400c0106d08608004400380e2a441a5007000545041c0025030400144100c180c000680c2e120020364910f5011030a0024224040c1514659484503103171014211030440312150001d41c07501b0703241d041540f4000d40c06032080c3c40c41d2460441c0300c0030556589000b802502c046400110141510350954000d004d034441d002d00801e48460f03641d003111009403280d1401b21b40183c2d15000406d030840700c03418404c9040f2101044606000d0041c0300c0c410300070b03902c240005032900320a10f00218900c200d220268900302c10b035400c101f00a411f150f903008920b5409030f810440305041a11000f02407002c8001c030f804440c0e0a01516400c83c000854040205e8000e8000780b080744e0b005071000501031420b449101c00da1304a600014500303000350b820001401402e070340380d007d090041e010002501c40c0c650368a0907001000e07a14141840400d4040e0350a05000f03010490303142d0703041a0301a0507400f030415082c4900085005e0302541010a40022100c10310000d5a070007000c02d03180081680f002a07080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669389604 1250 669388354 669388361
    0xe0702010b030a020a1406070606030308061002190f1e03030f0c0822020a0b030f0a0e0309310f0c02010e06090606090408040b0705010f11070309120303060e092a13 72
    0xc0c547c202004104880008006115060040d40030340da5100c05802d100c01000310200c21045103004650207004c5042450001d614007162255000b0028a407030401450309545013090110aa03002101011000c0b080c180c05400c450040d60f00c034403041181001100050b210550b0a030380c0450300f10411704400e024511000440d40046000520850916030b65200b0703014240d000719440c1000003c40d03401d00001c00180d000e030344884942d14000d58200020200840c0114a0458001051102d10b080403070401d5004c01c1120b00c1e070b11203164180501510219000043c0c00c01d00303c6c4000540c40c2002d00c410702d02021a185016440a02c09448141c0780c290400a4203c4046c00598038414100000501c081340b0b03000510400e4440c80011a000c0c3c15030045900b1192561020008aa001c0001e100000e83c40540c0c3ca040e100b00e03190b0992079040030b0504800500280d04403880e80c4441e001400283e050005903a01c0c0c0007040d400320f01181e0b040c00104a0307401902e103292500030f030003600051038402d407582 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669390854 1250 669389604 669389639
    0x402010c020a120507060c080a0f0e270c1c0915052d010510230714010c1e0c051f0c030f0203010602030406051e03010e0702010b030a020a 61
    0x2500030355514603078002449600069011200e1140c8012040741040740603c0101c0040c03005050404200b606600d074481d80d417003981003000411266845082c00180911018034921501414a0403100030007284003104202c0104900803800340c0354000340c1c0242001c0120360703e41042d849203460070141c00030341e42d001e0103d02c00c0c00c940c01003001a18854130181740c42460301c1428001c141844050307280300c0340c0e488600602d5800d02401d0040005001d65215460008802100c43c0b0f88134000da02403507500750507030350441d800c4400c070a0000740000500039808000c2c0211403105000700201e00c040441502c04d80c02031480142c4001c520003c0d12100341c01995404200741c0140d00b500c5c0203142c00524003003d0250440b0170b40e8840e541311102403100f80e141c400c8032606010000c04625550401c2c101a503640503512842040090014024040080d410306114903400c03251552610784d61101102090054100c46000040d0300c0d290103d1568500010606100c0f90040d20058409041c400c510b5401c40141c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669392104 1250 669390854 669390857
    0x105090108150402070308070816020c0d05150903091002072303010209030129010c0f060522150c1803060b03010e0f010606020c09010803030708060121050106020c040e0312040201 79
    0x114041561114001400791750b200c0d17600c0030024034284c80c01500042d40508a08000756600201c00704240d000620039003000e0b000c032110450000035142082ca4601110342c042214521101400b014400c004081c0c01211000c0300d03c4541c02c0318440f0b040303a40305c0540c42404200c42c030a035a10401800324000a404a800141c000b40c5095503803000f184c20740c1d01c0818407a03002513100d4603802c14903900c3d040c0794900041c2444c00410950b92601c3d24411507135800b0001d8201c50791900410190082031600c8461220340d01e0048540c200303103040c00c5204c0702c140032400070305a041014030086a44500b0302c0241040340a500311070114216210440140442402d2035010b43d650355101070b940d1010080524241c40140010424a08025000b800d143c0c80e03034440750007441000f00500c00404088142d945c0500f803483d16403a59540c101c0101c17044c09400300700c443e031008000004000003a594000c58185c4403d90211881c0703003010803e010444681c0f18020256810500103422128200c20b5400c0c1c015005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669393354 1250 669392104 669392131
    0x705070f020603100302090115090b0c03160317010f062c040212101703030a02130b0703030507090b090f0609130212090607030b0a090504141c020f0a020105090108 72
    0x4a40c04a402d95100755801442c0c03a0344080204218504042c42c1405003030441500e80340c0d00701002d0041c1115641d4018070311a00000b00d0380d00f13220300c000c0050310b1a1688110900c40c549070349080160a0071100034500a00e0041000042102200d0940301011039400e80c1e10210071000a948d280d0501c0007212903500400360156402403655694000f900840403030301040061070800f101e00c810304001c01e50102d5000ca100c0c1d440c00301b0a20011096a6000e084540d000d0f80d00e0305100751071560700341c00c0d400010a40e440860f07003005043e8141c0c001486101d080e2101c960141d1a01080515400348400341c070b03408510700302448114100500034110144003c2e003066000d03124064402c05070b82041c445250003907001030422501203001c22a81d170b0040506c2c2005c016045240001c111a800340b4001e0300d0101d615440480c040044003400e400c0185c0c0d00d8400c0e503003907000c4544040c4010034002e80600052160402c40250280007017170407540643c0c141c5402e85048400d00040d10340c4600103104103040d44a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669394604 1250 669393354 669393383
    0x709030b15130b03030f16060f2c10020c03040f0603151e090203190f020d0b0f0d0b070c14070303030f0510050418050f0c010e090708070507 62
    0x40085486004081c406aa4070840115006001140204000b81d008540c20304a50300f43c1e907200403044407148460843d1070399440c81a00c0d05194124030014006185615003038001139400002e50003c042104080c0c4045000d52045484200e099003644440d03c1c60340015100080d07850569005040100742d10041c1c83c10b041d5160307200320a8007203940c09400402c1e21048015940f40d11003083c1000741164036180b80b00612155050811501603026082c089580000405c00096213554030a800030200c1380c040c400040102c880c8806908500803030304905060021643c41c80c90000e54038042c815001e820042c02e003040b62500b00050901500c00c07010720640b2601d410102c1e4406102008031414000207012052441c9401012100c0e20341440c03170082e160005022003942c08080900450f5002c460118a003c50880e54190900b08544010b0052140300303503040c04140c0100ea001c109040c00d88071788040d142c120003441620b231411100350740090844070010700f0160107000900600c0c0d0040032020b20421 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669395854 1250 669394604 669394613
    0x61c02030a050a0212030f04060c031106040c091107020f0d031407052107020d021005131d010503060c03070c05070308070501050613020c1f0e07170f2103070903 71
    0x340c2000e06a600303801040f545401d42c02e201c08842c2c4800c6800b00214541010008403c800d0b0281c1c0c0203920420100134018001d05116082d101c01400c1c460054610904040c80c0107180c010440c411800503504085403291015140b400359101c07160050f1110303c00d0b0740c85400300590503020810881c14000041111000d011644e806020554810350007800141151a45207031056154020092010810050140141c640544208903a42d05803103c40e007050502400f99450b000d100b4407181864040200046c40e6080c0700b02840c140c0c29a03440300e0b45940d0301c3d101459103400d812128116400c100300041011244200d00100f200c6015100b0340d01081d45954802e112070784011026195603450f4800d010451034001541d213680c2407100c104600d415a90140680c9502860400c00291050f200381c5840e690001d802903c1c0880a00c026205002e032502f4444542c003500c442103545900c10b04100300851500000c3d40446800b40500342e0000c0035119240e5066503000800100c10005083e00000004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669397104 1250 669395854 669395863
    0xf0c060216170c0609070506091909020307030f05010816030803180d0509091003030207060e010306051309120309021509040b131b05210624090a0b070308061c0203 72
    0x41100d02450b03a900d2003203444035403400c00c000d4109580c07038005d10800c00c2039680e030604a80c07549500303481d003204104468540e1152101c1c180c1c801c800082c000010050420340c95030148060b0303041c40000304102d0762036043e01c550340c0d41c85030f03401d0100510051042c400f088081c400303158040c0500900c02103000e841c10702d5508207500b10f418070011940100303540c905860110070443d40a0000440c1455a5180d610000e60b1100d2501c81e10060107070051604000307900c242c1041018240180503000710342810346002c2d008107241842aa6284056181d24201078440d01804004c180c0040000b03c9858106541007819400f1039429a885642c07126a500c01d6122650381d6420140c02403000100b02429582840d007a030360541080040000030050f004040090503201a503c2c0c181c480059296540d40c0007085a0003c18941c09462404184145125003498002080c614006854500f00d8a40d9110704042ea801054401001300f20f8800001b21030703042508004040d08200050382d14054150740100f03051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669398354 1250 669397104 669397133
    0x1030b0a0906060c0c06020c1e01020a0827031903180905041401110f0d0b0a0816061d1f051c02041d01030b040b250e01030605010f0c060216 62
    0x10035800c03035100085c41262640100103007018009445041d000d90001640e481d08404121540032440e4854043e50340308001c0b0384615a44102010758038000881c17028042002c1a165202504440c0303803011703882c2804070f4181c11090b003d545120740340f240d603601500c1c80341c800d201c40725040740480d03000110f0420341d02803d401075015081240904507480c0380542580c03c510058541d8070030801071014442c0144007124020340407540b00083c40c4164200007205a03940d903020350030703e05c140466042c5100000f50110704641c1541c035405100c000c10526802103903a041001a84039651003d4015544a1141c100885078841d182442c1781918a200d04403070311984d4280451103580c04141401122034454036030a034180754039070582c034039031642c5d0f5000440500180b008000c900c018011800c032411614521003030030306851068080d00b4501c0c2c03000b0222020038218900203402c020000070594041c0b02d440c4506102582d0f400090301580e241c800296200a0b400400750040d503105102095580650414 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669399604 1250 669398354 669398357
    0x603040303020d05070206060a121112060a151805090c04110d0609090b19090602030f0f0601030e03030105011107030b090a0b0c160201030f0216260306030a0201030b0a090606 77
    0x1c660f480494100300700d440041c490b5095520100901103680e441990041c00c5480f40d00702c1c0e00a1140519201a403100c80820b050307001000e240450b030000c64041146403080040d440c08000e07100d04540c503100c0440f494480d044031040c1e070031401c1c1340007505500031a5104184000300c4000f5031030003006c0b0b0101c0d20503042c40015010080b42c00d0828096600801e0024280d0300018000c0d216951901400d45001401e09041b4100080c0c4d1181e004941744c0000812507003140c4215224500080c090180d80d00446104103040003000000b0415806441080e21250794400210f0640e828140199107e84600340400002e02c1409800000900716070f4809104203044030140c00c010005140003030b0940303c050501107000000344000088100d24120383d0f124280c091170085803602d00d20502000038401d80d0f07184204031407206580014004211500c00f54074250304181d281404c40e480740c1d140035000a480c2c440e49038001410520140d8403075000620304040040075100b0456444c002c007021201c0d203a00900 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669400854 1250 669399604 669399607
    0x80406030c0c12081f03080703030f0e0a06240f08070b07110402030606040e15011d1c020a0b0a080402030c040b0d031815020f16050627060304030302 66
    0x1249a40c03600a82401034001e00b03240c0d140740529501c0b0711141d070640b4040780401598070002014a030500000d041c0324078a000e402c104050712400c03ca4440c0c0d101c102d05801190500d0101d603c20400340c400d4400d0a210b0501900c6415860703034414000d4090010284401300e420746071049660780015800c2d00070400d050341c84107041d190440d00c0313007040525440703041c1205080c042c0700b001c16100300a419584004803001642ca9492000060309030040d90032501540c05001d0070082a1034904048100310202600c5840344012403643c038407110808840910f4011205000425201c800314407807224507480207001204407501c54031200900e8109404580c0011072240c00d100560505010100240100365000d001c00b98080010074005048100c0017010440d120f100081c00540c41c40383c1c10b01a005590880d0354001e2b980000a5445601c52418070103402140311003007a03200c0c002c541004407a07024240c1400c0610500e4000003c2c003549100c1500b401200b44010400c1d641e900080d4800d520a46006 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669402104 1250 669400854 669400859
    0x106050a05030303061003020d09152003010b120406230114010215060603090f1209040b3102220312110615010210021b2b11190804 58
    0x200303900003103a01c4140250420402d004840e2030300501d1841d40c6540b4100581e80d5200c0480c41c0005000d0380c1c8001c0d00031080b01c1040b00b046042034000060380e04420151220100d19450030b01440d10082c070031842c4002d405c02c600c001c043c060449056100b400340100056a805c0f480030fa50b0699541200f002c0031a02203001440070240300a00000598020300c000e00702c0c10134a114200c2d480714081e1149100e0341007c0300080201000300081c090000713450303003034950340690380001440d940c020741030040c400d0742040307106491421308039000030898071404030250b8020080c104107441c114400141e00f05080d000c1040c031007091440741010400c07000e10f5901c036031010314600301354041c001a403090400300091841c0b000c3c8807100000707015811a8040b4800c0e001e120904005030310b0907117407848030780c00c05001007440d40700080c031200040740020003203094803e250049410083c1c05415010280c0d680d803100380602c01d8061041140e210007840e041c003198541208050b503030b03803169204d810458040384006000e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669403354 1250 669402104 669402109
    0x602030a111e030c12190c0224090301060501031a0d020a030803012c09070e070c050f03031f03030f0509040e1f0c02010b010806040c0203130b04140105070b1807080f010605 76
    0x185c00b540050005101d0078603401e510381c00000b200c884402e204110210740002c055640d1036440c003010346026903004240214448440b03400f500300c003d80ca40709502c1c1005c0061154005c2c02000390080d059020308001d401d182c400c001842130001c1d03003aa00421109000310010305890004c40c080c1402201d040c890305130b03070301d40b0f1300c240300552100c040744041c402c051000b107035000a0b204099503c0b168010b4100d031f40e010340465180c0301e181d202410f140716558221004a00100003180150403032000d4004100140c16074104884042c44001c000490058405d020180308001601751007a00030301c00b180000315820032a1800780c00202c40d40300e804c4074041020b5041c11a00c101140100c081c002030150f00c0c1c1c9000040d2403d5802840b440c0542e8485110b2a2074034070034030071100c84d0f558404002e00c1d82501d50158000d44d0f0464028286ca103142e8480c0d010300c1d0f40c0284155181c0c1c591088a10010b0380e101441066851501070240c090b07840f80c00c40100d00100701b070001200b9403160400004901d40b40008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669404604 1250 669403354 669403363
    0x1e03010e0a0b0609040c05090301060e09100204060203040b03150d030314152d100f14270310020406030b0f0d2f0d0606031b0602030a111e030c 63
    0x4010606140c5400006592100f20076920300c0b0904a0f000200c4020003a0b05032214854007440544c55441c003c80420f000e070088090500a803034210032604078407800c90b660402c0340714034041c000160388203120800458102c4d1000396480b0380a4a0690a01c0f8052008140c26003c81001140803a460b81000a401031100c0802a03120428031141440c40e2010f50114010f1051030091204030f0341030300e031444804540041c4040030b14001511809003c0340303d40000f001901181c6010b40000c1101d00380f5200b401000d41601c01c5d215903503460742d012641102e1001d00003022052480d4040c051130320440035880031803020700020151510003183e002c840314100504034400144691040710f0ba9400540866103144c01c0c08100303c000802c140c0f0640c442518021004d40b821100b030350180303012044404101d403035000402240d1180c107444209900032801405c1100080c05800016403045c080341c6406e501c40d65140c2c00c00c030440c01c103554015101d03813440002e482a02c040040309034000528074002ca41d0800c07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669405854 1250 669404604 669404611
    0x1050c0c06060103091e0606031a190b030616110d020102040f060809060a090804081c031d0d140409020706090209060d1e110d0c060f02151b1e03010e 66
    0xe010417128140d544c880007071801081070700281d8120400d401e010002c01c0d501c00c10103140c21030459003660b465507038102078107036040340c541044840f820701180d50341889020344080040001d015150383d0b56000782d4807400c042c20b13502c20410001039840003c01c860042c0010700c41d020003540056a01c43c00c1c00e0681090840c90785c450320411400c1802c01841480c046040303a005030400c48040740042640c05c0250003800396802007402ea0140c0301110310715075401d1884074074903141a1820300002000301110300d404607101a800c01250055016044054811000e2002d20445519804d061549503030390a401c07030f00021401c031680c40d5146028425842c0141c0d80d030344e00c41c4040303440c0c40c061600b039622040881c3e401d030704031205110403002c0c11041109000e696285418060000040201c842c140a10b640000d846520041f64031040606034913032010444002a0107000803003c05516025411000e031070f0488602416200e00b130001001010092842c0000e082624510513141c4d4108500042110f0014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669407104 1250 669405854 669405857
    0x601050f1902151812071a16090b040b1b1009050a1401020405061c0207120e130c0212180910090b061c0b04090b0c34120e0301050c0c060601 62
    0x412000c46144000500152803540c0710381000e85481046c1703058004048102d131040300300032804082003510030011000340e0380201d40740e849034002e1340e40e12168003044c80f82d80901080cd4200b001829220b28000281900c003002c5082107410383c092403650381086840c842c1d4110340c03d41114440809110340b080c03086d4555002a8000c52415190400180c403505c110908420300c011185030300c48084100c0d9056418068004911076502000c06d503004006001401c240e520581d1600e0220758a49545d00c51031180c031009400034101c1c0c59400b460040c854101d4111002003800c0361070102d030381b40c0b5689a110b029010b14441c01542d6801c0009207020366221880301800f0301c4042c04524080000509a2404134203864000580c1100400114000c0c00c8000809004100e03070030300b4842c15400f01030040001c89058070240c28110104507028103404d07004018899501032981c0e1110100d1010050200340c0c11150501e1496040e24201290a403102183c565070310010114020002d500d0601142d68044400d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669408354 1250 669407104 669407131
    0xf0f150608061216090e010e01060506030a1503050307050c0a1e06030504081b0318010201051302091e0f0a06050d0201090b130b04090c020d170601050f190215 70
    0x61400003845504010003443c8114040c00d0344881092050003014000480880c0192040c3d4a0300c05e40c5018042c40c4602100a40c42c2c00c2d503020a0084c1842400180e8000501c146d26541ba140807a1010302a4040440c0c4002c1c0700e080c0c00400a40100001c00d540b501c00d20191010a81040c05c1003c0c40310381c0d40c014201c20032030340314003074003203101500c030100707840036802c00141540303460a14180354000d018100f0104e0032800400048201c0000203050040700c89140ca041c005042c000490a848064540c0c40804202601d42c030010b00c3c1030b0002990011001a0680f140210a0b88060f64001c040e0340181c200e001c101e090060342400c40c060803002c0c0200fa500101c10b0613541d40003c04651462140b00f011407004181c6103641c81c02180369070000e211040891740c80d50f486d1101c0c1c00081c09620f00c1d0b0005407090001d09010a401a40d258908130808400c0442c0c640d114401900c4544c414881041d515130208903420304601206100900b0721015030060040444041c40c0171200c030000317007904821505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669409604 1250 669408354 669408359
    0x4121701030b24041d0d030605010903021203090d08120c03011203300e0601150914010215040605040209010b030c0702150c031c1506090303031e0f0f15 67
    0x81441c40ca0b410941d010300409090f64514800c5540e03280c032651440e8450704118451069500c8440c0080840e2004401d0725a245c3d89030005508540d8184601c3d800b1901558041001d4a00081d2045c6108062000d030380c0fa1440c08130000e01030b290700100c100e9903520040b03802c6103100480d003215079110b0031648a80e440e55040c030403100503400e1101001410021101084c01c041044601620340500941792540d0007100c0d6900c400000e0300c007040030f0b00c0d854402c07500006400d00801e80c240401da01252a081c02c2581040d24000c04220030001083c154820782210b54510440c3c4480c451107070b070290100117581c0c107051041048510040e8020140310005205004803501d41004030341583e60b04031900240900f00403d401c035203001c0c159280040b0300000c107066911080e42c8101004203410b080c801c02c15071201c0d03c6001e034030400502459000860490043c00000d00a40c450500d13682d41f0500140482858400c00059584820078403005688480b513000180b2801e0046111019090740f84030512130 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669410854 1250 669409604 669409613
    0x6070801031e0b090c0405060d02061c060e0711010e0a0201090b0901020114091c260c0d060605131a090d031e0e0a2c060114030412170103 61
    0x4106010240c44980301c442d0030100540d05880821400707070300a6003000c031464030b114500c2e02c410070300c0c004600450902000604c40d01e0502c400c559401ea00900782410001d410381075041220326107450400c0541c0d2490082541907100501c68070034001c90791106900061000424203581144540448907802501c42c3e0340180c0c4c129140c201035a5501c95016100c00300000100d014150b080441026030040e042032052030240444c0c03144009000c140011000082004101d881202c5100c0401da03d80c0e12030a540c81d404400c00310a604005404035160400003050b00da542155a00e40c09000440c400103007113141006041c0c0b0300401090481e2601c021090080d401241d5407045042d00c4d4070410750701c01c41404042c0036030001010f17400400745600d42403104000181c40d804010700e019105090707071800000c8951310914080501400182a20310390031205a551083c804003a10712814081c00c01002e072103004610f800303107101d203004144a11217020020000380c007002e0302110347c4c03001d102c0300001131010a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669412104 1250 669410854 669410867
    0x501240b19050d020405040203010b031626130b100602070906051c020409080403050706121b0305042301050604050c0705070b1804020a02030904050702011a300d110607 74
    0x1141c509105548065901107800244100c0e00040d60051007c0008034903001e055010710f00c10890b030406800c0050028600361100d142d494140d0f190310b0785006804800700c00a0b10f069411a248030821242e04100395546501d80004840c901c00a40501d24200102c690400030b89000700014141044520b0902007ca010380403100b8800b01200c11a003c03c804546480d8000307800c443d041a905030b02c23142c1301e150642d2507a0480c8a50400603607180c00e04072201d48a8450011542011107005c2441180d0071030076000742800810a40b8030340205074a260084880055000034036105800014040c03900c2c6003007000702c0e60003800b41c506840062101000040c0300045c0d64068031924070070240c403071003800d403603100d03005500c000150400c0c004940c54070142c1c0c000014282c2c0e910f00725410f009568484800300d00b207600c40c1c0401c107150710003070b2003011240c104400d460794907801c0030041c034110700080e810740b0640494030000d55245500c961000d8200560010030782c0c0101440c2ea01411032400d101c0c6004021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669413354 1250 669412104 669412147
    0x501090510080405071a040905090705060d0917030a02130e07050703120f020f07021c150c0c0501020c0a14030325020c090f070e2403060a030501240b 66
    0x14014000c001c10240704041100000810f440e03480390720204100b403006c240c280c200340f1400130170b01d080801050301c41c217020428209440000d00b01741d04116848100348042c00500c2c40c241c602050207220000c0020503103004500ca03070180f000c0035a5810400019900c0c001c0107600006110b00000c0500000c158404100d0700031541501d010f01c103150040c4100e500600359003940e0b66030640b0000d801080b4400c0e004c0549075040c02198008421003510302e0350700d070141e40003400500c608802035002064004541c090400c030340c0d45103400c640414095550074220791151101c1c042039402080b09030200840c60561060446040c0c0107181141010712420940e805981034509030060a250700003000380c400c0141c10360022000301002d0316801c0c001451a0100429103040d40001c26941800c42c00c1d060480544640744500550340c0c243c6503901c05449025000034195941c070180d41500080420424011041101e54200842c1c00022542d5014404000b045e801416001d405010b04001c210350603048000307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669414604 1250 669413354 669413357
    0x6151403211e03040c210317070302090a0906030b060d0302060a0c0e0306042301020c06040f02151c1404051902040f02120103110901082e021206010201060501090510 73
    0x80b164662038010301a030b8000c04200c111840d0200c1000107214948051717004444181101071384d0f892541c0b00750030328080324250140126500164030040d0a8a406c00c69602030301504e80141003201c1680014001199680503648450716800d00b0310900a07101021070700301c4403c60780903202e28030540d4081e4540030024440d010403542c548511035000c0c0682c11130032840f140107060790007d2500340391229103c1c00802040818a280566900000c80144202d5008489190080041e03a9440d82c034070086d2105d00004030303080204030103292042407030107016104503d40c1c8446400d2041d080036800d81207420800c02c20b441d03001c0100510000c100301003030046c50a002000d24070b0984281e03001007001f91080d1046500c5c1716100181c044c0040030041c0003541602c1c0300c2c48030300300714005000410904c00800c1c080c07401982c00454140c2c85481d0303080e00900340340781c040000319903180e0000c0042e0100d0f0460980c1540800903e020070130a9a030a1003013201615090078903482a0b0300b0035000c0b4114100e181c04180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669415854 1250 669414604 669414607
    0x109090e030708030a090507080304060507110402090a0b12070e0f090a0b0a060201091401140601050c0c04020d050601112b0c020a081c030203090c06070f0615140321 73
    0x441015062044410b01600092071a80d00d007000c100c1c900c002c0504050540e0b090054840100e4544400310495084900541e039a40c14103c003601c50106080d03d8569440d07019900300b18101c016185c00007881d00800740c80098070b885078000c0c1a803102000000b401e010800a8000d20000290751354000f0410a030001c0c1d40ca414155101c8001000816811060590000741c1c03110001c1e046034150001810740344150f4038420b900030403804241c241c03242010000f1204440f01e0002e00c90b94480d5015040295000041b540c2840d410710210f401c9a0040303503440401078680d803c11025581021482d4013409946004092218424100075041070400380f40000740e480139a4501a0b6a02c151484880381c0e40091660010b243c2d100d401c140e580ca8000e68800580884081034880113010784240d070722601da03040c0071b4000e502c0f501e01084100d80c0008000c81301050400203138000714289101d0301d00d8015080c2c0111103e5800c1182d09201c6079110000c69100764440411386d003408041c0c4510360f1240120b0b440c0c07117 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669417104 1250 669415854 669415871
    0x20907050319111b1603050609010f14060d052e0506061c1d06011205010c0512060108270109050f070308180a03050a030e010e041103040b070201060b0703230306010909 74
    0x10342404090000c5c507409402c28400801408030116038103001c2c60a0b0340081140b0400d40382c2210075198094941070b40c80c440f0300002013580c02c08610200049101c2c1c4240d0701307142c00402003004140c01841c1d258080900d1148a0881c0d04140d00c00e0075080041110701c0307030410700030421511608900e130b00c020182c5622990b049d01010b010004002042a05900380c4200f5a11003194440281280106a5040d070904101000186c003810841e1902c0c2400540c000980d44c42c0300041d60b680801808001012103200c43c0a541c8070f400c4106070340842064000490382c02003e040c01480e0241c181181e01007070300562420400541111308070340c0004012154003601442400000e0000101c903480a4110300a016546040592090218441c0d8009032610b40c01c01c520a0f041c4400c490103e0b110880d158010808035010400c2182034660050b020f00c004161103403034084559a41e04003540c218049810140d40e0350015100034a09511145070350f60090030f500c0c0040c0000c20b0b1111510610114545d90f0402 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669418354 1250 669417104 669417157
    0x1a0c100e1e0f060114030727020d09051606200c03010c091e0e060f03011b020309010314090c060c010b060711030d020a0b0c1602090705031911 63
    0x141054200c0300400c6820104115a62a48140b07194151940a98800800c0c3c030300e01804038581c10031003e0300425504c1d09000c3d503d88045060a0144035040181081c02d480074407500083c1006041c843c0d010507545414507080340b420340114a4101031100248060011990001c0c036030480214041001000b000c800f51500e0522a070524465055401c120383c255030583c004008201700c07041040030514400400385800c2140205000e5601030030040ca004c90002c0ca407104c640303160013000500011345440c51001e9581340705058181080907070404102c60080c3d680621401c84900304900100e8803501c3d00c140a40d8841020080c20340c41107101107041c00022009610400044e0300113420540d4441e594200701d01e020003491001446403080140d01c180c4c0602c04a41031292039402912001c498503580c2001403a0740040d604200101140f00c2c0319000350b80d40600340f5000e4112174480c20b0742e03401c0c00d4685490900c1000400e02c07860f030401201844485070201220000c1c0c082c061500811101c1c17550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669419604 1250 669418354 669418363
    0x1030506010203270d12120209180a0b0907090501110123101a04090c020d0806120a06060308030f0603070e07080a110d0605030106150c020603151003061a0c100e 71
    0x20000e40040820f117580080160303400480d240e9411640b108500784244210f11030a07403160440d07080d0000000b00104000c01c01c0303010501d4101003001c4c0089041c5100038040380002e0002c9502d500040c05001e003c100340d5800014442d9500003090082c0800500103400314000c00c0b034240e1443d01403684000040318401844203210103009411211081541a410002200c1d080b501032403196600d4140702e100b20702d000103826612128281c07140e113180c0c0e075814200001401a422010024016105c109001a09a2140308007440c4030390811764503420242c880c05000c50004010314000e601c40d2506225174049200000d82c416101d02e00105186d8072090190f0181c400160301410449010603000f0400c0780c03542241094400a500030414250344441c00c43d1142440fa0480022940b144112009030a00c540210740c044040401d1100d4942a44003150010801c4140000081d45c1c541b02408001c2c3e1441c28000c004001480c2241040103011441d40c4400e825200552195a228603240d1140030500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669420854 1250 669419604 669419677
    0xb1204080d0e030a02070f0509040b070825050715020702031902030312010b09150414062d030f0603011112040c0b1902070812090d06020702090406021801030506010203 74
    0x81c0c07600d0b0b4130314040103903551502d801194944c104016000c5114201544224480e41d0800d1554042e07446a81042d180e02c10040c4c100302e00341200c801d100b041c00640b140282d86402d6070b5516139946040d2170419905d4415503031051100c00d8010070040c400341c0d800042100303810462070444050b8420a10000340b0f58070584103065040c02048000150643c2e18101814400c01c066910915031004041500c1c05407007240601308040e88180360360310243c2448400b4120f64150781400c0c4030006000d111401803016641c01012640703038000b04000c0415401081c09800403000e0700240a80694080500d02c14015140c2e00c192204900002405204526041c44014040042d40c1990b81143c12650000340c5945070442d8094402c8010001e088040042c428000300101002541000203a20401405208070442910159000d0100d100582d4944010074040e611030072005a0310500b01c4510b40c0800325454140c0d05161034041000702e1640c020049039078242c02c8020102c0a00c00c107000c80701c128038590 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669422104 1250 669420854 669420881
    0x1e0909010608160e011d0a09050f010510170601080c0d0501061107051203040b13080106060914060a0e040c0201060306050a05010e09030304080a05180d110a0b1204080d 74
    0x40002140754100b011103010700d40d5901051000740804000b942c0d4046600d11050004040000407007805000340e48402102100504610f90240d07a81c0310602980d40031380e203000c4e0fa01480c02c0100440c3c0b405c1c160b11015414a810f01d0100c00551480d602e924403002018641071110100005000e043c0f040c003122050b0015003000c001d1561145001440036035100a8205248560000441d0341e10b0540345030b4070b91210300ca006514241c140304005215400803510120450302d0240081042c14088c061000038103001c0d540c10104030b14141401140701c094401c5c1d1406030404100c8003000640c03080f003d401c1c5034030607500480c90600302d0b07104034010181984060421864081071162005068224604880041d10f10b040d40782c40c0c0c4000c980d1644010303200102078080800070a05000e000c1d4004d000d00c4800015658403000c000808501082a008002c031003460482d081100c40d442c0c2843e4010142001e03680781414480701d070304544604a400340020704120740108805c0c2c0c840085412040040445 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669423354 1250 669422104 669422119
    0x3050a0608030a0c0b01091509020d140115030f05091b03030d092006030c0711041b11010507021c0e0301090f230a0210031e15060806151e09 62
    0x5103800030311503110404d0880b6500e01c54400010400200d0181c00910102103044201c00c03454111880020340c810145852000e4603a014010507c8124102034000c101001c404400d0503c1440c00070103c40440b0280d10800340f90101703003c140350700043c0042c02890701051001082c90480b0000e071840c06085411070206041ca15110200010000c010b001884500340340351072120140200081800221802c00a000041c0050f002052001c203280700c05610161000400e100c2c2c00d42c0f100c09000d805000da5020900107890785040400074070903107038800c030144054100d6a885040d8011101e8003094404208201e408a1a11541e02076014451a50b802500607440700000c1c645141c0040340303c4003114208402c15808848500041010700e805030380182041d403a43c52994042d001003030611390561481c0002c9002e586000d6041c818200c000ca551000c419080f8545036004100600040880e805808624038407800788045030103a410003580000114010345440d4821202e500034004041d90143c40b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669424460 1106 669423354 669423367
    0x903150912070c0e0a0e0c0a06020d030207061404110316030206190314150f1f1407050d050403030e010302070c051c140616090e010603050a060803 65
    0x80b0309403108009031280c65400c0e181c101105c521540320b9481041c0b9000180c100944006428201c902021403401c0c403000946a1080340c10381810b25801180d40e408120198201498a00300d41c100d085c0c0510300350402072000030051102c170f4040e01805d071101c1d5040c2d0b0500c2680068035005015a450440d462580420b08810310513907901701030380e0306588000741000c8035030280a104111220801c2604080800c24103206181300184600d00c1d1981700707100c00007241c00701c0200300e5141c207050742ca010598412075414412480300404c103004043d500304039950040007400c2500c2c000d64986450604100c0158100c6c818414003410042084074100118523000343d40140488400ca03145680003203035514600000818420540c26400c0001007001c200d506010250280c20b49151035020340c1d00d040065103482d0300c12700441082546034400240c0709007160700180000d01c1c104048954814 = true := by decide +kernel

theorem cover : BRFrame.Cov 669244604 669424460 := by
  have h0 := BRFrame.cov_init 669244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669244604 ≤ n) (h2 : n < 669424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
