-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:02:06.078006+00:00
-- url     : https://prove2.me/submissions/3ada3f6c-3449-42bb-a6a8-5bbfc4bfc25e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 226079136 ≤ n < 226258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 226080386 1250 226079136 226079143
    0xc0f0d06050a0624030e030a0909150e07170c0a0f1d04090f1208040c050402070f0203011803140c070e060d021503011e0b091002030412110a06020114010b090d0203 72
    0x2584c01c210441c0030007400c0301005054400c450000e1b02d02e43c2042001042c001e4102d143c9004442c803891020908100c2144c0342840145142e11440004e1542030400c12001d90100081c101c0810414030f0f0302c016240c03103043c8010703801074455400c0490081c0b82c92024042c000d41d42c40602d00c40d40d01c1c00148491040000c1025107500c0c2030b08882c541030083c0000704200d600803501120564a20704159145841c4c3c840c0e50070700d0b003940f052a02031076002500c6014400245490207015401400900c103445034000411040b058281068002400d88a1045120003140d01155141c0c2400e00040a0f451308100b601d02c5c840c040030b4a12030f442210360f01c8c0c210060b03c0301030040e00003000c00703e0441e4403036241050340e41c030032001c6555594600c54141d900b0312000001e041511036004099903e400314252054040e8507606c030b00e402c01440752800d01c4480041000f000c41e100b0501c442a58010601070752804281d01380c1d40803030610703210b040c0e030807005004907a050307406007041002c014498031542d0481d4022130305 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 226081636 1250 226080386 226080419
    0x703050706080c07020d020909070b040f03060501080a110103110408060403020f0d11100f09080f190305060904021212040803090a0e010605030c0702030109060e030c0c0f0d06050a06 80
    0x866811044080152641003850180d00c000141c81c140d1802042c2ea0000d18011466503000b4441d0320780401045c0c024100304180780142c0b00354001d8075031b9541c4980e02c8094110003440109d411905101c0041550741000c038068030110760004100300000c2e80c40005402500510b080000062024040060b003044100b21150007079000340c0142c10f40c1c140015100d030074510f20030380500620880310100c10710ba59000500200c0d20b1182d4400042134001c54031460081c003e5058051b1204001188008007050598010005440c050022001102544000f50b060319011250315510008190004016050a2150801c2281514191850514000303000030003900b203038001e04525800414103040d0307070500202100103440d1303030209800380d03601d411402030031440300400b90940b051000c588001151025000305001c90362100c0244a005100c000700c50b41c0b5008100c0b81e140c0d40c8100c0c09040907c4c242884a070000d000c01400040c0b96484a48070720b030141201070024002c0c21303070b0307160002101c8124002a95 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 226082886 1250 226081636 226081643
    0x7080403113601080303060102030d0f0b030d081e0c07060c0e030304120201020c032b0909110304210e1210090f0b01090204060c12050c0d0306080d030203010828050703 74
    0xa102c22521808419405030030604941c1e004009101080c0e8002040d107034800815100400c0d4810100c0521001d00030626a00313401d032140036888150140c00112051040c04035515030b0000000102824004400550360803002450401c080c0c004540d81d84c00405e110003440c20411200110000071924543c0958000c000c41120030f0039800031582d051289802c14542200140700300403608001c061085400c54015241c0c900c5010f61708030380d80c003034100c000c000e003020141004107001e25000c04086070700c212021144401e510700c42051050036103400801101150b035a169601d602c80b000d000c803c05141c3c3c5a040740b8803d031040c01501000500030b18171028440e40c6141223612152400310a800010b800040100f1b005000c240a01c43e441240584400d41003500d403000c40c41c034508240c8040c4201030040000340110100030943c240c02d5040130044402400898084501c5071000b10200e000c04c3c0500314864000030449400701e02d5500c0315803201455143c031101c983d4145d030348107132070000c4030b52040303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 226084136 1250 226082886 226082959
    0x50a0c022706040f15150912030509120a150f09061b080907080613030504031401060510020a030210020c1606020d080703090b07080403090504021b0706050708040311 73
    0x400941802e01a903980c4241078036090000e41103101700303070f104001076000340405030105550843c1441c2c8940c03061401850301100c420881459400c000b49241c1c1314845590085c20b5022000c10410000222011602d42005038400406802c102120203002e400c0700606519441e88012804075486200707248a002d40c140d14601e8018403004040c00c01c03400107000307071096041002c0800903110302081031540710407050301c0d44524031000e1404dd249e5004682000d031a210145600b4030501d0815809003068840884000c92105840101240e80e01d00d8001d0080c010380003c0318035441010b0580241c0980841801034504880140742d4615020105d0342c401e10060f4002103071000800d811080d2590042443e25081c03040140545a250310090043d202c581004030f000001400d15208900003005407200420656a42c4654400600b08034503c1d078100105011380c0b040003a955004404079500d195001078138074109455622001d5050351118001c030b411022800d41c0a01c1e103805600304030b00c10180802c05 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 226085386 1250 226084136 226084141
    0x61b012d05070228060b0a0b07060c05071a06030f010606170406090b07090306051f05090702161d010f1215020c070b040815010e220b0f01061e050a0c0227 68
    0x2411b541c2c0d0300031030741c0c0a2040941c050003039214400031220101c1d008000840c0c40301c40c5140465141c802c00d0001f500700c07001c0340c03103003407c80403107503802400703030300b08030200d5001940c080e00a500301d40b214410500401d005ea45109040c084240c4100d90183c0510000903400004e501da05101160032907507035000909245062041000e944034003600000124018407a80d00c0000b0a1030403c0040e020b028801c850300c000040119100f044109841d194140a44003030035640c024600348518211320400c616010344002007210364401d59018103d41d916100d800c68075400340c4407640045150008808110340800840f55054004c008030780060944800c45659545001c40312400e10514510b1200400c0070f41004100500d025144240c000300c0c1c00d50302c83c1102c07021030005440e0b400c46200c0141150190030421009c05800a842c50480350075482c1e0440e40e08503070445800071500f0301e100d40045070342800000101842018400341491021384202034021250f26a61403030320882034a01a080d080004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 226086636 1250 226085386 226085393
    0x3010e07090b090402030a021902010614040e0d0804080408030309070918111e1309020406060c0515070e04020d1a010c030c080a02010209061b012d05070228 69
    0x10055000500d8501080c14038140310184155104100c9801d00c120f40201c080740b0070b8245941110f00e025042c85405401d2004401e01a01170314491040c103070448080305c0c1c065124145801001c8103904510701800110101c40d206584070b542c068000d40b045407040c0408039004404000540c0030b904011300400300a4030b8121900161245d0781210b1521098441401c00050400019030340c591a0850342c41c40c41f0380c40c9442c0d045c81540800c0b1060740c005036130401c0f030002c8101507014143c86402520240021500d2f10401ea90b006001c0200900c1035100048424044402c403680c103801400510b130502c00c010300100050180e8212881d040801680c0c0e0403040030040c0342c400c980302c01140030308000009521580b0060a500c03e03100000d0410400002d10b40b004c0c034400e60484102d200001d1449498041d1140011000349001001c826190720f4500b109a081d07031500200b15076001d0501c220004148030002c040050217000e40440c081d44650f034080140c40c14100d80c0c0890003500c46000741000801800e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 226087886 1250 226086636 226086659
    0x60703111e0712051c0e03100203190212040809010c060e0d030c111009060b0405040b0a060e010b07060c14040801091106030402010e01111002030a0f05060306060924040c02030301 79
    0x1884090000306043c0840c0024001241080b00030030703030303031000e65180d030b100141a22610002400e0544c1402492510800d40700541c1c00345014005000080811b024006544412449421011101c464080000030009441c11b0f0051208010615000c0010035866032000141e5030001090b20094000c4041e10800c59418030507004040311038508100212218812551980280c5680d86425610f945c0700c00e040c411540c00001c200c1b0401b0f881040b003460181440d048021041c2c8868500342c0c20300c500011500350445171030303041e60744d01c1400074034102181e80d84e036000740320040020040c030291400d900c00c20010308020700002c1c82804000315800102c0d1a011200e80180700403584514401e00a001c0540d9100801c031301c80400c2030900d1501e4803903150a00d440c00d03d01e500007000305400001040700d80c000640060b600b50b03585103000c0c041030710342c201013580743c0034101ca031035030000f000d0400a004060480704101042407500600000312203000045401d5170f1104d499100543d1000004100001245 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 226089136 1250 226087886 226087889
    0x180f0c0504142b29090d050301060207061b0c14040c0206010b030406090c0f0932061c05061503190305030708070e0301090b0402091e0105060703111e07 67
    0x464900c0c50f41e480240c000a100c01c501d46000800c0c1e804500c200d01000301c809a58003c01110450484010031038054032405020103c88224140c001c110002c01080d0141c0103581c141d0703038507402401e03146041103030443d18001c28840e40440c550300341e00c1400100e1043c05c94a00900a00300d1081000020007092000340c8900c00703654011584100c0040100ca00c000c2c0549800c16402040491400000d04000510b031382c003070300964a001052031001600350328503804000614002c0e0700400703640701040d00d100c3c02550704403c48001504100c0c0029800e01c0c02c01882845180010640c005861564441c985044011110114481c03450300701079007030b1300d4104841803d02c20410340400e00500a03980c0107003140000b0b4842d2090254902c081040c142c000e41c40503403521000f03402001880381e14107120781004026138059004460b0380001c0750768101748a01820203201403200705940e50f4030301418013010b540200c10982c100040009000c104c0c480a020b914114902c1192a03a003503042c440000b810405107 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 226090386 1250 226089136 226089139
    0x12010c110a0f061104080d0809101803032f04030b012405090f10080f090303060109061d0a0e09010b0d031b0c050907020d02190c180f0c050414 63
    0x100560a00003801c8144108282e5840b01010072001044a0210b0340390055810090701401800420000d03564416400c6209100080464000c403d00009640c202e83c0111200300030008401a036201013406a00698040c68072480259030070004100340c3c040d0000c0140c03031192000f4000070b003042840001e030030f03881c050003030400e180d50390803040b0903405401114140c907141030001c0030a01c0142540d1701c02ca0302005c4240600a407a004600241c0103080c450112454185070f80380700b010400496000003680c3c8074400603110300703030640e08181040d1800c004803c82c01107100118040c0407240c2c0c8690041400412040704015654108914400d09603142d046580d402068803494036070200354800c41d204000c00004620314a0182e1608001c82103003020381249410584080c01d01c400d00707900049010300854070b40e00b55003001c1c4c0c80804074803682e90103203805001142d4101080c00150f0400701c0003101c01d407081200003142c0c2030050540065074001c0041c440420b502007030800060640300c44500740c4000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 226091636 1250 226090386 226090393
    0x1504140a0b03010b0403150e0102030a0509212a12071e031202090d0b150a080f030f0f070c060e041a1305060d06150303090b0307050301050411070212010c11 69
    0x104001400c085c09184009040800151424401aa100d40c030400740c40120600a5540b4034001401a000d020b05513690505489a0341d000c044030245c2080964a03c62070070316117403401200341000009032a4607100081c0c2202840c0440008420400140410b042080d03034160721000380b401e0852018418a0490b00d00c1c0700c44040102c0000e5004003040301100b04200300580300c003640c90205102800012006224040c20401e1084500012401d180e10b034504036036560800d5194403500b5160110b5143d0304105600034010002200d004001070b0142c1ca02c8075206504107440c6803900c8072003030940e510050200d90320103056406800e103801180c0c0e62030b8204021501c029040c002182d014514904d4905440e503132500031400568400c2135400030b15412030360a02180034076500303210300402140300403401301c0c20b26040021080c42100c2503a100d06101d40b03440742903030b10300010b21002c0c250103601454a210200480380050b900c11400c901d03000b40240c000140a004e041d0060030042200c8c00d003004070b03030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 226092886 1250 226091636 226091639
    0x9090a060c170106030207060905010c080f06060403030c02060d0e070303030606080f04120f0537030504021e030703060e06240a06050f161a13020a050f1504140a0b0301 74
    0x11800c0b40d84030b045504501d030044c0d40f000b003414060020580004020f005500749046000036941c00030313545000f95425041407400b80c40d80002c01c202813180e484014045107191031441c0251401c00c014240752002060301003408003c0c2450981080001e40089002c42d9403010280080342d802159181d2140f00880c1006076410142c607118801c0080111034000c00c0100c2c40c80e0b4075003a05c5070381030381c9024561004075030344103504c0c0600e80024a4a81203400e0248442c0e0010b607041803203401514080c98025041803401e0015074070b40050b9041800405030035105076180000040c96a01c9200c0101c1c000c140a8611410203072004112100d44480c803103c0042042c41d000c00750307514806120112401410000e41da1641c0b0038142c26507004400c02d028411103003652007001e004481030100140242c0c2c2c2d0303849549941d40d6141c4140302c0c9600d0006504801120000e02042c10010b42801008000400c079400840320700301c0f0030889900640102850291501ea418010b08050119102500f078900c203150071503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 226094136 1250 226092886 226092917
    0x81c0c0305070807060605040204090905010b030d0c0f080405030307060501031a061005090102010609020c0a05060c0c1c0c12090f080303040b07030b060c01020a0903140606030c04021809090a060c 86
    0xd0081020141ca0b0701c43c0043c402007040120f038800307001000084c000303540359a918815000102094507007070307c455080c0b1400d80d00c249804144010701036150f07144c00c0394101c05a203e6008510304032408881d0814108004a4190780400151030141c0c0b00d808007080d5903065141801c00e89400001c148001e10340ba00605c5030704d40d240c0030790100e100560b140c40340c2c0b14801480100c3c090402c40c0d202141c0a4800078040070510000f08007103c5035402101121460b407a2440020042d04c10050f0020349030b0071204100c805c119000340840c071582030514260b460700e1850b0302c410542602c040c0003940400c0e8020384c20080d829207505d0310300040040c030010350f040d4a025100c584800e070005000d1410542e807450308038a00e0b03079003006035081c440008008645510501c40043d0541515001c140ea4140c090840307070440e4400060803620410f80900903041d90b2020170148000794004100103103110708005215003283c0c0742c8242c03280c8107407403420082050000900744542207454001c05402000705141c03841201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 226095386 1250 226094136 226094147
    0x10806060903070e010305030c010c050304120c060605040516020609030a021506030708030f0d0f060501121d0d020304031103010225030215150315160309110a081c0c03 74
    0x11590694420356501100e500082c00c1280d15040010380450742c80c0044103101002010b8821520250b0080102e034020000c04c0e2914001250004c0c400030205070720419180c400e09146241030300c51b0380041003507510b8400150560700b0441e01c0803a0700030722034401c03880c0907410008071350010000005507140003100035009403900fa0214035441300c040301d2070100f08562010044800203002d44000d8a0b125907038142c0d407020590048820a1205080042e40e8141c824644144021904141c54081e4003030000c40e040c030050610145038104400d240b0000c1c4400043c1480182c01d80051036024503a44d90842c03410758211a0035030b00250090307106201803400d01300e0420039000c0d502c900340d00e02404080d280c41e0485c030700740d14401020668003240090010740325480c18a509050412020f0711150300702d600d4540b5040b0b13400c451050081441d10701240c4c019009601c46401280200e0036112018948000700d00c00c07070030650140000b94030464100701003001800345842103512625041c6c1091985c2d8030024032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 226096636 1250 226095386 226095391
    0x10f0c120207140109050d1103280216061205010f0f0614130f060e030f0705120f0a080403020112050c09010302030a09060e0319111b0607081204200108 67
    0x80c156000901505010700500b5101d07032241004001e100d00b4009103451500e411840c060b002c00300711a02d94070000f03d400801a5620340030344544d0900fa6480c5444244d460450600440c030541c001c00d103010794071100724001e51000d04101d031600107009405644810031500143d020300c0391003002600510580041e0100c00c01150131528114000840c8502003161501c00c10030800391811004800040c61840c1d941440c080300c402d0b440e812648018030040c951507425001070441b154020110522a510304040b075014682c06480c11544400242e007031003490a041084180c4007250045030800c110340c2e100c80c040e200b0800901090102c0d04106c041038046004010415040c5600400010079900c041da003c291201d0300b210080c8291150800da103034590740300a50f600c95031031022036042c0c440c50040f08401421802d00004000b00380300700082c1c0700100c0348001620341c00b00c020480b2002150144015120f020510b00c0005050700b080d08d800d082e400300c003241003c076010256121942d5070783c03c01440d69 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 226097886 1250 226096636 226096667
    0xe01020f0c0904023708030711011b060e0708190302030d05040206070206070b0403030507090e0f0402010315060207050102010c0311030708090c18040203100506091602150117010f0c 80
    0x82668a4078400110700b01c0d0480f079880b03d1762042c540c4448150000440c207a11200f00c41c2100c50601e511216502e0704c91103a800d000e054940400d00c103003040d5106104c501384030002604503051000c1180e46900070b0340e240d0a510200c03a841a0024081200c042c403190400044d201004240d071000c0b95006034407800303018090058140d8520014040d91100e2044660650740242080d9803042a8900010a20401c1d1000d40000b0325000c00281c4082c084c902da0015203140c424804000d030350341d0f81d4181d040c42000b44124100f40c1c884152242100c5400d042c070001d01420313005000340d0340c14a400242140e1100c0e0707404080500b0b00d08104a0b8460392011070742c0050480c80c1000710b41c1d4800c140b8915146a0003c459002a40350668805c1c0308084003410340228421411780c2c81100303200e00c40c001070b00c2d007e480095120130303c1030103c0c40c0b4500103003020304503600d21300595000e8884449070700c0420b0000d91140784034042c20b05e00c0442c02c10080c854615041c5111100b0401c95041c090300074240c07100c030390300030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 226099136 1250 226097886 226097899
    0x50a030305030a0908041d060f0607060504020301180302071a030f131a0709050a0905040819090e01170d140405150903120405030f0a0b06010f26070e01020f0c 70
    0x34960b000f46801c6a54071503042060150b840740c3e14041840c156039100d64103030380000c261000c54020302c2e212a47d0400c89c0d8005142c01d061505a0b01c070304000f004003600881c0e1640d42c598014030028000389010f00c041d4040e1300034182c102d00e1b140b801c08140d0f460b020540000c030b004204002200780e003120b1141d0000007680341010782c41a14500160700700801f082505010404404000f80240e0040c0040150f400c01d840b89400e4a598064502c02d40c4c0341039030005c000203428004200c2440d100180940520500d16058417080da0b620f1800f40080c0b000c2e0040040f4100002902c03081080c104440344500140d442c0c4041c0380e418854005800f809a40a410b120b2521480058100c203001c40c141c1e2800c0c0002016110012504441e86550394010b2203042c3c005d0040c680d00707185103a40414400842900020041403699400004540f480003088802007801002d800c2c03a204501501d40044290260380481d2030340d4100550080c01180034801c1640c11544054189400c824011035003c03486482079611 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 226100386 1250 226099136 226099141
    0x18050105070f0302120f071206032609060409020a05040b0f09010e0f011d03120c0703050c090c030a021b10090620090613050d050120071109091e01090b010609050a03030503 76
    0x441d011a5069984060b0314200340b80801880f01d42d0306901d84c400f4100c5580080c0d07a4490b101803814cc040c0084050f88110140000c120541158008000e90b0155140943c82c00740c440c0903342d02ca40110780c0000c4422008560440c403944c000c81d40611001084955165610084000a0031804070440c0003d00c40484031046403543c030200489081e41011003600c0b030300c3d441c9040c4419a00c95480c0300c291864402c00c04691003600f040011640911050704490740b550b41d58424803406540300c40024255401d007441124440c410503c6a04a800101d01c0007084048190034000107a500d40d5588840f00d00c5051203d05c01d03c0c6a210844043c1070055171039a4850102c031030b40040717508046d4015600070710040c540500b0054103600490300c80c0c15403484081d6481904500c030b10280203e18005142c48102c03c0a0201403516078005903003c56944100e9440d100d00004191034091210003501e056034440c2142010404810383c800e016004c1403419002e01e0f80342000003044010184000740034000000302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 226101636 1250 226100386 226100401
    0x8090c13020906122205120a05130810060e0106020a1127010906060e0904060e10023c070213060e041203150503100e0118050105070f0302120f 63
    0x5407400b20000800f91a1100010b9424030b4a404003114040c4804034807031003c00b6004402101e031401c00d6001001480d001081c6286074126074012800c001c02d2103c207110025030300c06044d1200f4050880e107800344c070b5031a11494401007a01c01035008041a03540400c014007129600081c1e59036507a82040402041c10b18071404901c003042d0080c2208007010690400c104d5141021b5940303812160903000820000f640c8050444051030301446181d40281d640c404a000b10f031080c0c01060304180e500003601d0f012503f16000b10220f0f40120740c40381c07044140c3e00e450540000104074001c602d4049042d9000703102c617020100c81c41ca20034036030024030035140d103101c070640428694020009440040c0c04035980f41000d0403c02d48880c8080310030400241415440700f815007002c045081282c2001c0c005002c40000c01d03610102800d82d8005e15980f40d036032580c2401448450305e50015039180990000103060500700310040030400550f569505150040005401d6254040d0047e5400b07100361041c034846844510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 226102886 1250 226101636 226101641
    0x90a0b0319240e0d09060f0806030313060f18050f010309170403030c060606030b031c02010213240903080f070204060914060108011505041a07020a080303060f0108090c13 75
    0x42006811080141109260290b50303030104104140a200711444000540070840d840b40060103040c001441d901d00d00c0050728003c44d8115080a40241a642805422420300304110071a40c003920009202020052290b50001041c4041401c441501d001c01814180820403011030130316103038101590b4410f00e40c00d001e10300f01001548080310034000d984994038207008100d22507180c1d013568480e00d000303000a01ca034028807560b0f650744c0c0060080c26480c0c03240c40d41c070904e1084020004d001d554003000103450140702d1280c41d41c040c04d00c040c0f07010043c1e00d403104420640c00308006190203000c4542424000304400c1010703910a940e18402d4160340b004c1d18804500035108035405800b41e0713070918400990050001040a214103000c0c1d03907121550703076240400800c1841000c0c2a1003c2401000107006000d00701c80301c0142080c210f480716240c040554045010034001e0b510039103140c1c0001c410700c00c0503d0003185030f214a50003464065000d003050a1050f48450309080c0c1203200700d401c2d1a00041200158 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 226104136 1250 226102886 226102913
    0x15020715090b040f050405010b0a1e0315031a09060603101505041a03010e0303060d02090615070b040b0c090a061d040609020901080c07030c03080702030702040504060b090a0b0319 79
    0x2c1c03030325445940e18005041040018020301c0e104a090400129580242c03030181c481000c0d80d503407007030b03a284100b950700801d0342585409141016102d003c1200c070080141070382c0700114801c0d01d044e450140c00b0300301c802d12a10090094030460b004101440529500050443c1030072080000c00181c0341482c0e2910984050300354459038200e0b00f040c407124100c07094a9508000c056003a0000c0c4524640582d00d281c5030303c001c89500c1d40c44803190000b100942002520743d940300c8c4015082c5a5231000701e05150b19a600b2550303040b02c110789124100f108000d00780e0383d400d0300301d2013404c8414184190480002c202616600980c01046515414603190141c4440140544103020740100140d60b01c2d4004040690303c00f1911074041100d11001c908058034080481e03080540598a440d0318807076640e811114000701a000a00314441030007d8800340c2d44034810180602d10610002800c1e0038200207000915070020718000c1000d2410700c00d48181d0300c01096200400718410042d0700f00c203440307280c5400b0b8055031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 226105386 1250 226104136 226104149
    0x105090705070c0902070302010c02120d1d0102030c1b01060b161509060b040606181401050c1204090501051002060103060f060b0f0405010206010506070c050405060d06050703090c1502071509 84
    0x1c000e000139512842d5802010340c14026402031020070302004042c0d0347c030340300865202d02030074082024101403400c0d0b03071001c100303004800203d044149005000714266041074814900071600040d0342609454010036810000d80f100c0002d00c40c080c030384016000c41d0b01500b4103080400d0004c452410401800c1c581a061101150b1000c11080140b418180300130032810407105d000302d10348200400c00070b000b250724401c0321103103886c105215401e1242000d010043e035111503050005c103004956440c1d2041c0000c05480c865050340d03e440e81d06d000c90340b006a585c1a488140181404041c00d20b45a40c04210941920340191000c1984422441070f80c005183c1031380410f289100100e0303108540c0540000401c101c07942603086810700c0c4d803207504002039440342e40001002c604066004001e82d00305a0090782d80007100600d43d03000c2020366113406059030012144840040d6955410074100112405200090b140101e032000000090f917401965501e514044c03500c20403413040c00a03038440d00c2103104078007401c0c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 226106636 1250 226105386 226105403
    0xc010c020d02040c0c030f02010605090a02070c0f0b0306100302040b0d0b030708101b09260c060f19030e070311030709091a0c0a1710080f0f0105060402040608010509070507 76
    0x522400070704107503c22101b10005451a4121a1035034414003e840586400410000d1b0750b841d800903600096200d0102200c9109450b00700081080850072100f000f000b100c201c0d182c0c0e92404d00c0801c01d041d08413200403c2814814403050004c5a680760603990300c0d83c808040050311034402c0002920b02004c5901c4041c09220f4464019104e405580043c0700c41404810740e54280c0c0900b401c00e0350002c0c03a6020b0244a44018a0f010a210030141c0ca0541158008425182c101c0e111001080c1c842c0e12425140b0740f48000014500310300007443d1010605000a854104600601e03491041e0700d603007180c40302900e0702191004071000c5507820f00003140140382001c07040014034610300e402400ca8504201542d440408640040c40c1030203a41c085501900c52a60350100340500200356898208028003003082017900300c01d0101d80d405080185000340740845c402400e8408004042a0030340748010800350082e40180801c02c502c81c1c0103215241516011200d200b280e98400c901152180101c510107031445d031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 226107886 1250 226106636 226106651
    0xc0a120b0310020702090a0c050a12020f131502151303050d23130c06050307020c040e0303090d0c0b060906030f010c03151d0a05270102040e0112050c010c020d0204 72
    0x16143d500500040d40300303454582c22503803030a00c1c0608075149074445a02203002001601c40d410701c42d143e840b403564500e0340300504042503520f5810303039504507001d06032002140013014030010b0f16064240304000d90b24070080c20f601f101400d0051036900064000030581502480c9082018050419507041d8a50040c0401140034030049076600720b07002c0104418072928000c0410034212031404800001d5401c105c400311914a403000495a039400100604110b0086103c0401d280d40c890041c5142c14a15000442d1603090021040e0308004440b8000e005011a400400000071032441c815540710314221000b865070340d40c400109003000c001403003c0c0815480e0000c4103080c10b42681c000c0c80249055603102d03800c0c41e00d42000d180480c511480c505148014140083e01d404126000f00358058042c4043c50715003103039908411183c031a0031400c40c404e0b940215090142c640302030400790061a280086480680c1c40b03071200c3d03449445c2012034604001c002c04c6c001c015901c076859446d070350a90241c001c22504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 226109136 1250 226107886 226107913
    0xc010f020712060b0a050a080a0b07031409070305011b12020a0504030f0b1b0708070204090503090402120f060f0901030609060209150d0b01030509070608060a09050f1506030c0a120b03 81
    0x2c140708004c503807040d48082d00100ea1400d1510841d82529035500c01084c088038141c45600c40048010600010580c843ca0404031030305100381600e010f07a009400078a20541107103403c509441450501d1341030001003100c803141c000c1e8000c0002d054141284d03401642c9680c5c0f11402c5900c0e120300c1d040508541920317204981000003403032185100e50030200b000030085048035a200703402c0c41900c0d405018200140250b402624241c0d0086010318483d2040783c1c64400d144021078103980001e541ca02d0101035090400c078201c0e506150716640940200c4e481208450304074005413038000107000103005d483c0d85040e00404c2044d0ba40c1122180c0c0d4001303101554880c108801484a03510680c080e02d0035500b000300c0011103501078001c42d07000e154840d002e8005542400c00407a540800200101d60064130f03444005809580d511485005100f1440c0008180ca02605061fa96a42c1c00e6160b900921080007080703000010340b01a00c02420480c40c001c1d540418203034a07100a03007003600c00981d25000d80042c00c1c0c0103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 226110386 1250 226109136 226109141
    0x60703050406090b1305060a0c0516030203160506071403090a0e041b0b03010b0d1803020f16060210021605010e06060f0a0b03010302010309050a14160b030601020c010f02071206 78
    0x202c48090341d49640c01629144401d18601503001d2919050004401c24091813824002500f04a590b40c50309804000c1ea81d00d403030385401110b07003240c4110038126006200f54101031010b400151102106c1a00440c60900440d41602c00e0100c0640740d29618582d080e8804818400c55094010051841c007840d501c03804141c4148400392400ca50070880e10042c0d1221681b0039100c80115401500725a0440c0e103810480c1e02e0381c3d13000207584504256114440c0f6002c0040d070a100200324004d078010080c014000711851b00d8401801c0203018551a142003c11920340c0c0061681040303c4e007140c1c0507840b03006600b03014428410104009125500780312006558080002e1035503c1000112176041003100030fa006d1000701001d90281c0c8034811070420040c005540617402400903a441101100c1a003049030f19410100308510192201c0782c1c020303200d60303844400c41e20420b10240440903e000e1660800200103540e07500b1450141d410300001250402c0c10900a20244000348860486d120900740700b450f00000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 226111636 1250 226110386 226110389
    0x30c01020417010504050a080a051c0f0c0203190e0d020d030f02070b0f0301030204091a0408040e0c030601020c130f0608071703030405100f0902060703050a090e070e15090607030504 80
    0x198269030800c05040b240c140601405981c02002800410300d50380c4900711540c1c031495082050010400070a1a80604e0840b562040103071817800040100350751845006407091500c071902154020300040e8841422100320b044d8503074450400d1140f5002c41404901c1c034030002d4001030b51001c3300c1441c050070316400110081510503164251240c498070b036071100c1954040e04014240c000420310041c401420f16520111aa5028250b06035030032404900b8444174050485040341c0000001c02c04000100610444507009407011403060309616002000030364900c4440420742c030801009086550103c041d500c590040c1d9000d4034203004080e1650203444e42c3e45a00c0c82601c02c4804c49400020441c0404403d40c0d00407070740140600742007651448103a010b444c6a40c095000b45a0b103514203401666140d000b040e40c180f02e1f44a40e601d960f04030002600c51440d541c031070f8042c020113008111400343d00c4206001c0000044510519000d1503104a0340c980c016030040c25013200001442006064212000c0c4c030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 226112886 1250 226111636 226111649
    0x50702010b04150609060e040615020a0308010506030c0316121d1905070b031005030106030b0105040f0c08160504030512131505030403031e050c18181512030c010204 73
    0x40c1d43c1990000742181c2c54144164030004400342401d0000c6449041c0c080d00301540140045045910b0b000004520420a1740c0800581d0100c3e070501c040680014500c2d006000c1250900d0461a0005500361180700060018400405984a2065043c06010500035200e241102040f8106c50b000c81e540a00b1f21070b03402c80103a8421030b29840d5021440309819418150f00002034903406107055490000d075040984a100005442c0401080715142489040c00450245041c1e21b03c0b545410280411074014240c021401070800262070b01705600112569007185001d0802505662400300840307840c001ca0308000c22038020440300307584100c98040a44124079021805103041a510962f0700d105038122038102d408600240b00040120b4083d81c410007c82e0200f5480d07494240d0721445100444e6800c448400c4074640c00315400686582c070b84542c2584220564000d01070150058883d180e041c80100303010280603031807400e1041502e1b000310300c402d590b5190088a481e403480c01c0c10503020790410702800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 226114136 1250 226112886 226112891
    0x5030a090c09050106170c120c16050102031006110703120507020a0e0411030601080a1104020d0c11012919080a0501090b0f0105090402151611030d03060b0d050402040f050702010b04 80
    0xd8206d5202d4109070b400f44c020103070010f01c1c5c082e0386010810700100085c8580a9600e06101000c1c40041c1c011160030240d1040d40010780d2490070300388441031002107410480030020b48050f4104580800150b0b901a0b98100c030940d441c108101c24200c401d4070401c50020340010400300005080e981303110703625010346e1044241480785024242407690302c5ca0248a00403003680720305545008030340314050314010040e010b800940b40240801404c01900c50203445a40026151082500100ad00384614115010206c240b03450008050711203040c41c06030450410700c2101940109040000d09800b8400140515800d446441091341841e50080c55452070075210031b144040080c0d00d8541114880341a280c00900d031143d80d0b03c4a8003401548617036125034071130a050030000000303401400b10751000090b12814007245020308180034141020700e141440000c2c54140402130007105591010b56100c070f04400e40008450340c2c3c03800000c0c0900401c1c54000105803500081c000c001d54190410840d10303c040e03406 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 226115386 1250 226114136 226114157
    0x210604061a0303030114013f110d1104210b060907090e0603010603051b0102010e010b0a05131103010306050402041503030e0105181206160c020d0305030a090c09050106 74
    0x901c8015030140342561542003000140100000c00200740321940040c0f601030b141e900c0802041c500701c010750b501c00c14078200129030240f00c0d54042c02940011a0208014403a003803ca13491f541d954004c10b6100c100c02038035150307407400908841c82510020303c50301c004001d41d03002c8442c5150690170390300c0c0240c0c0c1c000c0550000800e40d00b001c0c0410341c01a540b581c0c0f210b00040c41e2008808030010083d007420f030b01d5500c0381c0e800004510704110340680c013800740541c1406e9415410000e030031208203101c1e003029a4101508004696a4694140111681a40c800e4854010b02141d84020000f016100202040c08030000c1f042c000c607a485284668400d031410030000c0304444e043da501c002c052000800041d001d07150034080c1d5118401406c050040c00082c240361000755400074554291007405265250700a1040000b46881d201c440a0360303100c24144002c8213282e94020030306840d500e1002400740034000010a440003129481146441c1e00722000f00c68894886404030b001d800284103460000d4080c580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 226116636 1250 226115386 226115411
    0x5162105070206031b0912030c0d02010501121b0305010203011e05040209090c130504020f030601030b0a0b220e07020c030c010f0819020708070501020a0807050f030a0b21060406 78
    0x40700e00e02900107002d10b043d40e98071024007034054198030504143e1501400f041074152110300300d400d000034000313016507182c5042101d11072510034132040d088210389c144001040000c10880f08a60401d400002c583c03620f20010a42450003840d03640000c00d90340c40000006103000d40f40222051103e02280300174161a555800c00060b40203030359640c0c2d48080890049aa065501001084010581e0586a03001591a0000750403608100030300c190100001003007040304c0da49441402030480c0122058103030b441c00c11000c2e155a00544e0b42d031581c120028400c003101400340303030001d20081160305014190b9260043c0c00030b485802c4024468001d100d0401105403075070141c000041d4800403a03440101c60340e110082c201060700400a08036015034204004030105403954010210a8001c80001d651214103007070040203030f4402007049040100900060462a0411045a070012001040072802060b00301c0041c1c0303000040a041c00080f030b10b400302c5400e0034030045511440381d405294100402507080c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 226117886 1250 226116636 226116647
    0x1c050703081303110f1015030c0905090705040c0e041d030f090d06150e0f0103030804031d0a080a0507091503080a030609020708042c01090903051621 66
    0x140080201d400000003440860303600e0070b010726103400f9107091030382400c0030030140741400c4034201000066004018031900c040028042d001342d450350301d40084552455500d60001c900400d029554000741c40303101140d11b200081040c0d00c06090010300c06c1240d001d40840c0940f801c2030304951030380a58203101001482c4903190a04800d003d010001851400042008030b00c11a0310520540340c0c4030500440d04000b085c00781c843d00c0c20080b000c00103401c609042030568900d04c3c000a007075100d00ca000714018070010b0b904c403100c140c205501d8246207a2034116507440080c0014007081c0701c0e41140406d01c001403400000282e01812600034402d907141280c58821202c10361309210388400000d415410300700000361380d860040241003860b2400241080e204e002d80c01c16680245001d8400300720115082c060034095000328816025403901098000d91140e41500c0c00c50720501c184011541d660050500317050084080710341300c103001e0703218001036111440c0134182490320040e903608041188007000c503020b0007403 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 226119136 1250 226117886 226117897
    0x2090f040b0601050901030e100527030405040905010b040c18051c3504180b2d0603040507090e03120f0703020c152a09060a031803021c05 61
    0x302402119a8842c0c006565982c41664001d04041e034031105001515400c2c81102c0408040713000100d55410403403003d00c11928801d0a409062120301070a4501500000c2143c08031502aa0302060302c69140c01c2c0640108000c1489540050400d24018000e60f03014a40c12000018032203000c014680355818007a41c08070f500b40b801c845040c80f010800114000b0186c148000c040007201d81d0409210f050503991020a9002c41c043c010404981880000d44c03c01c0903c1200d44440020400100e410000841c40140c1010f004042ca070f2614905201c52810600315500010260240d907403400d01e460429510b40e40c03403203500b1500d468102e0002c284000441101c54501494020200940b200c8002984900380540090207040e8200900301800001380408032443e41500350500707481ca0500c50216009500a005800d5018249403e64041c0c0d2103001380c407120201500c00c01d40700c511b04041078004021390744a0b106d8008070308042d48101680050300b0040d05400c0c500007841e0b80785141d030544060151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 226120386 1250 226119136 226119143
    0x605010206041104020919151e0c1502040611060901050601050a260108010207060b030102130b0f040e01080703050709020901171906081005010803070201050a0f032702090f04 77
    0x344085008203d000c040c0d490540c0c401440149001c1e0000300240709258410364084411418200810408054407030328404812a81400107070440d5502e8609034540c2207800c3e80c024801c80603040e4061022400c1d522098940e80030085550725210310014040b40004400a8210311a810002d00d903c41c041c09258001c102c1a15818209100c00700191032401100a0041c0306c960a0030101010385603010482d8001c0c4401c9000580c2ca1500e4280035082d1544009a107020340c3c0104243c85500c54001c1c09001103403c0c506205486501a0b241140c4500c120750201035203181101c00400c045002007001001caa106070101d1340704640e5110750100f64000c9103105400b140401480c009c901e20400f00c500c0e404400052411040038104142c1007c90f40309400c51485680b10102e03031481098240716090140c07181e0f9006506001690740020aa84030710f03140e508c1001202246058020300903040700d40e41010b42802d1110900c0f0f1b040d05a034000005040980c4540e040030003060100101c14082ca00a0f0340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 226121636 1250 226120386 226120393
    0xe010f09020a0b030912030106080405061e0105013e070e0705030c0f1903050a060608011208090d120509010e0f0a030803060303070b0f0601081f261b120106050102 72
    0x40c129803d500c5800c0107120640720301400540c02444504100294082d04041e2203c103551b013050b007031903441e140d00100303d20b2200b94580c0c05071505042155009045910901c0e055690300365410541d07566011000d000203504807d00014200401d01e20340c00200c040300d40040b00c403003c2c1d403100680403000080e244171012039410002319001d1000b1000608001c068001c0720741c0f5004e810035008990500b46840d40d00029942c100f0700c0102400390040c60020401340c5048540c550600740c0d051500082c0d50380c020041400040c20850f5070f202e404400c0742c800d030042030004104108010241031a0300c3720a0090000d808021803507041d00d801480301c0e00341000948010411411a07482007516800a400d240d4580310602c0840c0c005121a02424410590a1544036450034094005481ca51015080c00c0020604028081c612148960240c2c01c60381d89510300c07450074010a0740c40b114010030040790b40c0b85015850f000d100c002000d07103010340010815074500a15100743c9e4240e81c200e03811401094010781 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 226122886 1250 226121636 226121639
    0x30108062206021303050a150c02010605031c02010e0303090a1703070203090904060204050d140105070c0218071404080c09060103060b0d15050a06080115020a110607050703080301090e010f09020a 86
    0x211660701802103c1000d100b00030034180c40e61216450901c0c41241201c510723000300d106c030005500074040e40420b1011400280419400d00c400207889140d6000034003030100609800703003d0103200750014111148a001600e5590500000541d1034001800054a15000038903240b00d0440c1d0705800c50740b20300f07816800f071410a05042c00700890800080c0084e11402d03000e120205031076039208100e0200701c0c8100f01e4068444d00c0b0703a91040c00d449009000c5028010912441300241e240d10042c8030000c49640324280d030603542c00ca01500c40c2c1e841058118018000030501061340b1900080b11074140c603088800341403076a07800b030044081da00640100446807070107114080d00141140c000c1d01c030303100c0340c0f01182d542c030f0f5180d0000c03480100c02c075840b007000100e00b0001048129100c8004d401110110720160040c1d072041c0c0c035107560681000e1191801040300040b1042070103014404c08002c0c50340124001e42c1d950f5101004800340c40030b0302c180142940303014903101e0003000c00c0c42900744003a17001d0800d010b01c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 226124136 1250 226122886 226122893
    0xa03090611070810020a09050d0206090607060f020d060302090f1b09010905030d030b01091a0f0c0a050105042a08060a0c090e0a0c110c01090e1504110301080622 71
    0x1104440c05900c0c0302c1c4040109a110080c481a0b00c2d40d400f01340c005840302d01e415402000540a82d01c01400348803a601e0b90030150b21428105d4906e038a040c0c40761a80c414080c64444020308c0004091303079005102003100f13442d8070250b0b00320070210ba000300c0d0500026100c04400030141c174415140350f80480311188840d8100d00c4000050803400d5014105910806d42d00c001290500d2010400b2400080d40ca4001d800950707004a800005001220710302c902d800b030040c425548a00c580903000e9070a480206040b150100d003040081c40d80c5500c00000c0c00203061910300300a0309011a005c040780c5100d00f40452200c10b0305510f0210490380088020b002c2030310740011748001042400344450400a4a6001103141301081d0800380c091241c011000070741c0c03521500000c00c101c1c2e50200803022a001403101b00d0b40c5a9000c03404105440e1402d81200c49501e40410207414488403200e001d030090300b8020403540807065100510704842144080c1c0c1d6540d510221407540b5132032841c1c254100110040c2090011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 226125386 1250 226124136 226124147
    0x80708060411030103080d18030509011206180b030c01020d08011401110a05030a02060c0a0e040b04020c010608060a0c08010305070e0403180b0d0b041506030908070210050307080106020a030906 85
    0x3400c0940002001c05803032101512a0384260800d49200d80c0020340c0746400041846656a5515100c0c1c15102e41d190035a0010414842e45002034100031500e210035800c503c2c0c40c0d02004c001c08441c8029076014400500e01000b034160025030600c03e000d9070071240710f19400404d41d410340d8403103a81c44044070780c2801200500260002c038654104010101100e200c10b804000d503413081c0e40510300840c6c4400c1d00a00c0245001002001c4000e0354030305000d5104901d4204aa00d41107180860340031401d8551440810024000c440340140342c0d6081c0f0f0703400180c1d4000070a03010f00585101100384942d808404080e6940d4000b84030040c201c0e40200c0c010003000e4101a10690064481d02e0310240b80c030540b02018940e0b000035040704014034070000e2403a40d88151486003404085050341c052045603441102c0d0410483c0510900013415102e400030000c1061603000c64038410713230080c00702121031810100100240c004460b05804100f45c007001140382c50000400701e1290303503d5030b9601c4d038031400d0902c100c90 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 226126636 1250 226125386 226125391
    0xe0c041406061611091e0c0a0822021c0303060b04030b1303021203010e090c0301050405031602030c090405070501180f0b0a02150903090307060503240a0803040306051e07080708 78
    0x40c01d14482d028041c1c90342d41c00b01c4203030040c8030000f000500e419030008901c08010001d00b0a0005440410200c108035070000c0110b079001c00990b42021508548801011698010900c000d5024400ba2110443c4514100c070360401137000e03540400030141c8980100000d031090307000c042d00781c20707080e40080c3d48042c0ca81c400f001014842e105070348601100c5403403103049410a07000b40e154640b21908001207080200085202584c04074001c1c45103040c59121243c03248070381180000b040d58203440310415920100600d0f101031344007500c2210140b510742002520b0398418000c0c0d40c0064808440345c1c0110044601280549448011340300c1054601100749143d0380c020b805030307015802594158902c038806400c0a903c41c1c032581e00550ba0b6080803004250908002c0c0d0840070500500348180407904490010f01540e54480302c0004038000c81800000700d95451a0b030200d80d075488001004001c01c5610341016010320000290790101b0a40c0408402d0012030460b50800052800030010310420710807010140c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 226127886 1250 226126636 226126643
    0x27050f041e060308070b0601030207020d02040b1804080307020601120302280203060f0402040b01050c120a020a05070603020903101820040c0507050607020705011205040809040e0c0414060616 84
    0x200441c01007240c1000d442190744165030200e40070130500305012500300600e5100600f46003c40c9001d00c107900041142c003140c20040d0045075100b215462030349411100541207036820520a015180030700c0d105800c0c0e0700c05c40b142001806204000a101d0700a8501c0d0522241d154010b403504501241103030100000228440400401c0d00071643c0250f202405054050111403509241030324290041c0b00566110117070090420004020000800b0004121241400035904409545101c5d0310412440e01c1060040545140141800002e00c1138042e801060300c2d400c103400395081c00b20202e0408040342c07412415000310750007510021000844841852503178560b11501807041d6010b903000b18080784e54021104000c14000a04601400b004100f0244d01510310310003450f5413030030100001c2280041c080280e01e030644920101c2c003006070880030b4824144014008000012603d0190799840b011046054000d51521841c0c2e025909010203240c4640405060140785c1100819500c0061031050b000b41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 226129136 1250 226127886 226127921
    0x80a030b06070b07031d030d0209030a02090f07090905010f0e04020325091104030201020a02100c0501140618060901060e0303090a0902031e04050a230d27050f04 71
    0x486007581c9010240c2465400341009040b80e00d0090805000c650030031854000510310441d448100000000c06c959081901490142e1141280c901207454000c074180c00030f50100d00f143c01c2000341c2104c0d083c8184600030030b54501514596854083c81110028041c040e50362600640900840d400c111a10707401600c060101c1e00c001c1c05c3d00d088580c6070120003d145001078040c88040250403294010410034815080388546018075542c0041c2d52000c0780b0348001e0090310712098076407096000e01d100e0a810341d0003c009108200a512a0445021080715200d10440108102c010140b00058280f4030a610141105a0b140d08000c000d4420400000c41d440c0e05200c1040120303026110001100020080c5107005a01da00b00b4966100c0d1280050080d2132040440310704000c00715000161006100b500705054040300c0700c400705190011003d0110b203180da0700c151101c0d10740003588110b10b640b22160801c03440000c54800002c000a850051141e954000440c0950140600c0c082c0e00001c015078868100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 226130386 1250 226129136 226129151
    0x90a02090705070c06030b0301060504110901200607020319080f0622021204060b010f1d060712110c040b030c0909030c0d0903050d091d0402010504120804091512080a03 74
    0x9030920789404d5003140c000280c540784c1110150a0901810003d00782c125014403c4034041101045d4500601c0c140c2030420029000e21501a002141d5041d00c084560069030b48034a00081d000c0e540340e000140d03904296404c01c1080409034890f02c00d0382c0c014146824901c540c1d40790117080100414a401c010301034009142d000f081d09003003910082c2103181c514441c4519515250604004a80e0312a02071414000d4201011143c07540c0204070301c201c1c4c1984440006000d030250b000c141e07180900318006221441c4841220103880c6c01061700700c0043c50301411a00400c90040a000036500d503051031a4142d0b01c48000c5501d5480e2441c079156004408000b00da0500c040c0001841c50300c00107000c0d082c0801d0081c80c0c20310602c003050041680400a50800d030110728640503041c400da01c0500d2904014030f4080d40810708680c82241150010002e00c88415503c00c0b503400d0108555104e0320a4044140c541402d0210100001c5801000c0f00c10400000c5141081600c42006680c84600c3c40030405940310382 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 226131636 1250 226130386 226130393
    0x904030e0406090603050d0309080d0e0c0904061415030d11100507050a0207060201060e011401021c0918060b0304080d090c15022a270f04031205090a0209070507 71
    0x5003400a1075040c5004c69414079509100c4c3c103224119004504041c1415600310106640804660650403018400545040e501c881e00d13082c901c2c070742003031503000020b01c085c481440b5264202e0071011000048840301611a8828641d02d8200e420711380350960040c60401d005607020f4040d10f40f001444909842c01d0064440aa500302c9004031210004218081002040207038100b05000c060007040c00201704a504041d840301210005100342001c2000b11902044107034400d0040d00d4124401030b502141c51060b20328054810b10a40c0141a4100f43c4030002c2031441542d03008001c100c400344528540755460316141c0c0b9146034082400030001503102d21103080010b12501c03400b4005d00c0414000014040788680081c00e00b04450b6800c80d00a000181321403a450706104940310140c0c0c204c9a542038048502d40540040c401402c2030100c004441c420800c81801e008a01e6100310b02c03a0342c451321071a00601648084900940c1c2554103684251140c07c01810400c43e125000642400d00c0e504129050341d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 226132886 1250 226131636 226131641
    0xa2304110c01020a17070c0f0503070c1410050313080c070b0a200d210e1204030501060501021f20030403020f0705180c09060c03040b0309071d04020904030e04 70
    0x6041d06210303035001a420450781d070f004020703034450b9002d915403c0ca10300f40404000c00f142c03d450300c0504400c41054580c010403a0400480b041603501c03c64034141103540b428403a20081c030f0003024a00440e00b4032508804140700304100e0744200300070305824181e5101501d401e242e5801011860b403492290150201d03c3d8204c907009050a00040c1c2d44070005104280d50840b07108201480103182139010455011405400010800007424880011880e203000c2004e2030001e082d100203880214011780aa480a8495010007401a240588000d010041c1e40e00012070789c171b00c03050149103035160300b440c0380d00a104482e8200c0e40c548440410140040d40c641100280d5580c42501c049016070300070180341481c103030300b441040b0082c1b00071208000c100c00400858004894002e18522762990001624051641c5c3c510075103030304000b035800316900c60751110700380790741039000340e4025100788107c03840003032551510701c2c03988500d0b100140c41c104039407155402c0c40070703024010703200b102448242c0128072000e8a903403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 226134136 1250 226132886 226132897
    0x2120112060e06011e0f0b030a0b062b0c0f02060705070503040e07170709060e0603060a0f120308090705060403080901020703150911120616020705041a010e0a230411 73
    0x1c110b0a18452000070740d03d4171800c1d81c0801c0011820040401040300fa05003075035800302840078045070720b48401c00050b009100c7d1240399500310454008840c110000021030700710003800c40d401000100498807041d24000148210384005074403000024640c0c5104a01174014203115104883c00c00340c4a4245690b02076040b60910000b880d14500304d580300c3c10005502e0f070485c4a030308161107010f003030110003003c0c0340b5070b681c080b030152600001090040e19040740100083c03049541206486840e0001c402a9240707090341a80040d44000100d0301807240411030030100c0c1d4008084501d00791641e40c0d0000c03e40c2025070002d06602400d04004007040280008411100100c000054a01060300c1c004080c5103000d04082c1c0101160752809429040c001012030700010b084121a81c00c441d03a0008a25012180c1c02075030300b113414041280c0d071941c0f50051000501c0402d0700c410482c09010340c02d1000d20000c03881142d100900c1042241c201c441803503108404001d0281020070b816800000c10800f9502c01d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 226135386 1250 226134136 226134149
    0x13121410020319060602070902090a03060f050402120c010f2708010b100212030a0e1f09030e09060915010c020a030b1501050313021309021801060906020102120112060e0601 76
    0x4100002c0800710f00c9194550b0000c80410000e441c00c101d0000d545203003074012440f00c01e90011b104415542c500c0089002541e00900070300010642c8070070703000a46010348081b40280c02207002d0503030303403034020070349900101043c0d4481c3c940070a4074008440c44950004000000c501c01e82001006103207002000c0c0280680710004110305100005001142c0c204100c0c90b02150400c514040c040d80b0344400f1250000c2041101040c02c101c0411694200030181075010100442941c14800011a90304200e944074029112680100320302070612502d03180454200f54485521000140319408000101c2c42c00081850622201e8400382e0120302d032041290426541f0b104510f0070421034504514030445028030a00c4d010341103040599820f41e80c0142031000038410010100c0c51814154681d21009049400034018481102a5a0749004110083c01458002070780c1090101e0014014001c031107034030074075001e04203c2e0b0b032030030460148681c4c481d003040340c80584410440112003000c11840d03001c2c0c0710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 226136636 1250 226135386 226135391
    0xc010c03271716030906090b0426010b0d110907030506010215071b2f01020307030828020d0516020a020f060f030903040807060e09060105070f050318040e0313121410 73
    0x806d0740c042c000407080e5204001c0e000c001c1005000c00c00200452004c40702054186410344000300f00d85501610402081c1c5411640c80402d5000780042044420424441590308861507140c482040301980d10440d102e80c0542d2003112a0800d5041514503960700035200c0c9000da440d03202085e2015002c00c0480001d8915001d0a286900d80c661400c40c00b42860200e80700c01e041c45001d0f40e0002c1c0d240d014141014051001c1140040d8004104924006842e11505202020490302006100080d0082c100c252112846c1c50700290f0000c841410ba000354013100c0c1c00170099103106a0030404c40706204049950449800e020f07002222401d5000342d4054002e2001541d03d0b9810300f00845d02d03010040c0d12150030050944000b1176540c60380ba403042c1e001882032a100f5665500e0303007004030780042d4400300104140f100140000c0201211640c10070102c2c400c403401d0003401201d00500341c3e40e015130f00e104525408041d80800259119000c0c40401d14410310341c21425001c00c480c07550501200000d080c0c207968 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 226137886 1250 226136636 226136639
    0x609020c1005011706061e0a03030c0605060a0303050904020f07080c0f16050108390c07060509030c0d020d0f0f0212010510090c11030c010c032717160309 68
    0x40050040c64050151200d00c0c1320742825000003203a64010280c211405650800c00e5844c481c04030444a0041113000b406c1b001d911556031500800000c0070b420140c44440c540008146107103082c0030394030100e94041c0d84840c101a1503008100080d800843c130b203404100c04112002c00100100007138140345080c0400303010088131855101703040143d90100241c40c14840c01081c00315a0b0401c260396003144220703c0c7c1900c00544c56920303484075100d10b034159115121400310b443c090409940100700c2003040400b500c4003a40e55400c1030312580030305462194103401000b14081c0c1400c10080c0341c0c0e2414002003440012401c251a0442c10b480703800000d0702e80c511405080e8081d401e05c01e00c02c04040a04030020083c03803070040c6442900070035034001c00304201c0e200c8410441c01c80c45030300c100c24204100d006983e501e0700d66411041c024840603030304401180c204018000c00050342e000304500202540108111211a6030300c0c0c1c00d80e03825009020088600c28812002d441c040b901140d42802c0c8a500c4100025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 226139136 1250 226137886 226137913
    0x1111011121308070605041103150907061110020711150a030b061620060a1205060409052104210302100b0d0f0204020c0114150103140f0402040609020c 67
    0xd010042c55200d6042030750030010001081c0c04119020300da008400010035448519100e100604242580d41d850b01c5214038480e44001001038282c094915181219951342d50b0b071005a070a44500290301c4c1d13880e04101d4a00c0c682104a4000f402100c0c81603a403501c044460708002044504a131220a41c034410214a12041030f80501c40c0180307101044070f5150604907903855411603100794100080550098060030328000c00001e044450940004040c0760b21b4040604c001031020320041440c880407801d2002188035420a4440c11400581010103130240142c44c0c40ba40c0003486181d80030240360a010030001072440407440e003040d0421070b25241c0f03840d00c554230304009162460ba0280d00040f1850581041e0140e540c030440862001d0340b152507125070380c50302d0000400074020030440002c1035082030300405000001e03c0d105440b8041c5c480e000c00c441a503000c0110102c1e40d81010a00304a00210046404044d182600f6944244001c1010496588562706a4103907006141d03079844c1d40d8030050f11010034 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 226140386 1250 226139136 226139167
    0x302240c0304080f0a240b030d0e15030132100f03050a060b1602010203090d050a020307090c02191e0602030106110c0607020d080408070f050a080f0c01111011 70
    0x80143c3c0c3d000303013001d8601c0d803143c00c0030340342c6c48080d06e03601c1c140d5420306250311180c0d4102003200c41c030040540b100a070301e00b14080c14040c031500382d89102e55040c0a890305502c0f244000d40341138603100c0c0221940810882c5103031541c00c0c2c1c0300200c0ca0417100c007030040700c11555900d403085030f918007a5900d07a0b10b040b95011001e400c1c1c0390003401340c0038854140703102400b10b0008001034412949010000c2d0345c2d21011400103034194401c4405580d005a4920402d0060040c00600004100d05c26011607100581d0b80c0c2d003103401c80d01403901107030040e0421018110340360503444e03480407154010380c0405036101078101081c1c101c2802c4801100c4860300030004020090b003052680303080390054000b030103840084000242c124811140d000f44900d94000302c078000d2010aa003954042c2a0101c1110b04503501c0d160950a0b5104034443e070703403149080c2107012403c1e41000c54803011600f00f0f10000c2c244c00702c03598010345503001000d01107149881009406c00c5407281038003450300e070b0034419a80503a079408801c080c2e400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 226141636 1250 226140386 226140403
    0x40302070e22150b0d050c09071e08070e030f160b0702280305060c03010503010b060903060708072601030c05040c020307060f02040308070506060907180302240c030408 74
    0xd00d07840c00102c071060750840c41c042d101c2c1d0001202000709031111909004040f82507055401c0065003101c402004000114401d183d00c04039844a166603c000c0211410070104080800c0310f82c0f082c0342000c02c940640c04003034220080d418001010080580800c1c0b422100c0051070300036620515404040b80e8603140e80001030301003800005c0c5012401d40104c4c001580e4a4011a22002000e50b0704000c1c11407c1800b1002c1c507482402d6559a060001d00740117150803e0245a1284d4600300e10107490340f070181d00716244001c2c0071b07020b0280ca580e00d603400d40e402c0c80c000b001802480f00000c1481014801c0e5012006c440410301c1c2074411070f504508001d102010305420041c0210f1400c200060065000020b0b03032034003a4032490200d408800b20342c205001c0d0086502c000e0154401045060130000c0104010740309072420b85002095590b00c4804480000c00a645104131300000001031025080054012985c458841c0d4414500c00c0580c0c0c4400d07241d400982c0e1307040c02e81c00c00f01e400e1000c1542800b2200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 226142886 1250 226141636 226141651
    0xf0504050a0c0b0a14091216030b06090f01050915040c0c03080901060605030f0907030b07120b03060103080912072c0108150a0f14070302041701060e06100c0b040302070e 75
    0x1410501c038080c0180c08242c43c107545d03030f40c002c0c13010840c2d12090f6103240800301c070556200140d500641c0d03036602000c4100e086000460700444524000740e4582072040c410381c4100c929244407141a4030b40b0b0144103400002601c003407403802c000c048244281d01c850040340c0f0803207840c0c1c1c3c902d1110b1620303050080103008080c101c1c485590401c034080240c40d43c002e0503250803600c00d44c440c030110f8a41650725031030000141c3c40241200fa24400300400349412121006101d81c8111052000010150415880d803401340001031205009016199450070500c0215039070345464402c030b6080719200c03455103003a46d174421000400300519250300322605180f42407041c014400c0000030440d508549612510348040148103402040d61140e50f14004d5065030030042d01941104210341c214200b0100003000f0703611038004d000044840d0402c413804004148100d0702210398890070403800ba21030208005032110850140c0041109508415000c20709954216010ba0310940003011000d2420809000d4801c0c01000d54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 226144136 1250 226142886 226142909
    0x10309020910050a1205100e070806070207090614030604060c050904020304080301091d060106080a140a090311030a200f1504030912021008190906090b011413050603010f0504050a0c 80
    0x2002900000e11010f2207d0904000320700c1c0d81c110318410385807068a42c00003040d4400c020501c02c0031a004108503003544d0704100305004054440306a0300e0742988030f84480b6010781c801c03400107010554940c0304140c400b01078a00310340f5084c030180000d01a608240c07410345900200200400c20581c0500c280390b9181d02e15030307918201d5008500b0860721514144501000c0c0324401c0000f40c102c0c11a0b80c803d4013900d1050540c20150700349440c0150040050150031004030b40f030701e510b0f225036620010a44100291070380e0b43c801542c00c0804409030500701d91000280b144550100804480b000b03004906000b20024101d4203280390a0500030a00703103681e440050032640b0510450050b032207107405a2410032041c10140c0035a1101c5e51a2400e1500c106102c0400720f1400c41c106041061036003003101c503140141c20340d21950342c880940420464841d15401e5000403140074008025000340c01040d03207c0304c004c0001840500c0c4001010560714101c3d01200c40d03401c007141c3c0c4010040c07401d1002014010b41203d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 226145386 1250 226144136 226144169
    0x501050303030c0a0212070303051e1504090203030903070308130e0708010302010e030a1e021e06031f0b040e0105130b062703160e0c090f0609010309020910050a 71
    0x10070344a10000c0d0003050300a00016000958900170044501c0c0365000c031620300c0d580c4100b030800034018481500c00411b07204441000302c501c00320103504035010710f02e0241408800701c0404200b000402c0c0ba00c000300c1e014001400220700c10b54050009100135400b0b030300302c00d64132135107a01400303c0400190031003003400c02c001060001e40c0d644501018107503582801c151a6003e04000000d00d050b0316408000c10040c1050311503443c00704868400d030310b101d109443d682003982082e00c111b243c0000c90320301c05030024400d00000d0021b499981001d00312503080d41c0c400d2050f540390312070800f0380d91084e00301c0c1d205103412000421490619031000364a01c082d07003504020300c0c04201c0c00103c19204980d044101d0078900410a10982403840e42212220001400c886581c0c841a0f07800110304100c4c420b0321400c15034000040c030203c080364121100444000c095010300400c40c0100074407a0002c1c0092070406075a4074a03040140c071035208440c002e00c204508840343c0b510300010004c40010030b40143c81c1a0040001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 226146636 1250 226145386 226145389
    0x60e07030213050d2103020a110a05060403050304081b0a150209100809030906190905011403130309121112010606201c0801050306060f01050d0c02070803270103050105 74
    0x10001910400c40d0800141013460802ca80c05c040c2c3c408000720003108006804c200c01da0154020a140b5400c3d07254046085540c0590380d8175102c071014045c1258101000240000f84a07500655000344a0703c1214280003194840311403a407100195a85240d00084241c3c0500c130036021080d404038556801503140202607000300748101a560401414080540045003000a00348291031007001d01402c003e444940124510701942e000c0c6000c500441e28022005c15154490f042200c00d80e030300090b0b100d01d07640f103250b078111910101c04400d0b401c00485080c080303070b03a451089048102c80d0051690340030405041c410020b000d050321800c42041d80c9401c20401a403030b082a5440030b5045454400c145074003140500d68180030f22021701a80c81c418401120414540081101d030507a0402e401b00ca4050740d42000b070081c5034005d0044540480d10034020032620103a507800c0841c8007409403041e140d500d940d034140a031030b541042030146e012035100500c1000543c1c40c88110b03050503a0910301809554074000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 226147886 1250 226146636 226146667
    0x6040b0a031a03030c0109060b030624010302040510080916150309080c0114090601080c090f04050f070801020c0f030a140a1412191401090b0307080d03060e070302 72
    0x4250400749074a80d160010301002424450400d04800307029203998105450600d4001c24480d2411103010b8500381030140c8038200061407d200d068040705000c0001c0f6058030a0440c42d02082010b03040640030000403da90303c402203103540e0403005444420700e0b420301448050034002c0c10281243d18001750711082100c52000101030200e40000c3c140007030b40c414a42061201445400d440700180e608003a030383c03040d18404e1121030384241e800e00107868075070b40c803003560381e4440c5084900251f002d20510040380d40410214025504680700b0f0342281d0888500c51800303070034104141d005460396540414040c8400d042808140d034003120020141d49007240040000e001e850300042400c3c1d042c0f40c0442c0b600c040c6401544195000200c150065440345005410480341c01d4044521400c40f141c0d0695104003003800d801105000060184005d002d6800c20201ca0b0040580d50714507a818407a0070000204040d0a121003a002c4059960100d59a403e20b000c1003080700c0060710b02020141304000400140f00c03000c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 226149136 1250 226147886 226147897
    0x90408040b28182d0b03010302130b150c01140a0b0a09050103020a0308371103070b0f0603010b220e03030106080a0506040924060609260f0319080606040b 68
    0x2012155201605450b03140d9507605440702c0c1c904c035030f0304180b4045690707503000e001b841c102c0c0e20844c0c01078091013041d5800804da52580c4c00351034016240ea10000b10f58480400540340c42541e5100001d9124010143c2101059003911078030b00b5141e44044800c201d08000c80d0250284c29032000c14003003540b5503070120740b00003140e2002400740c140204802110f400d89092180100b40c00f442c260301000300807101150305091041901e4049804d40e400b8085030030010007900c8030f07150031100b040d840327640d0905c1c41c0090790b5004000b1645035680c1d1a00c5238142d40ca01004443c80d9602c9082000d0a00941c620f503400c99030091007921306d81d4810300c0100700496010944075400070201d00080b410b622900e000c600981041e40780240709010301140c1c6c0161207000b44111a1005a03000140006940c4171b2003512804e6650040034050001801c02c0c5034078400c0134000202c040f2013442140c1c00c20303080702001410341d00b1205c07203241281d11500302054030f82d80c00b14045d0380250007110411718007860011003030000d03c00c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 226150386 1250 226149136 226149149
    0x9020a0e040c03020c070609260a02010e0301060504060605040e011712070f0b010902031e070f0509030703020d0c0f09051e090a05010629090609090408040b2818 71
    0x1a02e42ea0524184280c040e100344203441d0040fa4503560b21540094014995809200000d05510800542503c0d001c212003001400070400f1740b0030b040e030a07001141e0b05045480344030b4141d03403940000a0680c99070700c034450003884940c1c4c88940300e9091045251040506920072030010f206801c2e01c01b070100002c00c020070030b00829502d840d56210240340150b0100300740d890143c07a148002000042d800d8507900118840c0041900709424412510301e0b2004041c416640d120018200046055889011343c00500d0340350402000c880c450f560740d40c00900712101031402200c0844401b8010010807149540210141a200d07005025070f01e450411544022004050801086c2171000410107045003881000c034a25000b03030082c4915501c03650b40305019500446a4006494130f407601800d010203860a0340c60000000340943c0c60b1010001c200304a17a10b021b002580c140c582040002907040b0658000c1141d001610211580140c0c52982c1c0306007011813032010070500c01d0200006070041c1d040940401910007 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 226151636 1250 226150386 226150391
    0x10230c01181e060e031821031b030903010204081c09030809060d140906100602070e04060b06041809020f0d0203070302120c0301050405070f0503070b040e0604020c03030708060a09020a0e04 83
    0x101d030f0415501410294451550f913000000c0d036102d051810003c060780d07560083e02e6040c031902242070030544040f0745807168103640d00b0038031500b482401180d844907031014860088030b0402e1082c1001a08991180d4099900b036845408200e07501c40020159410044203418000d42042c6076440d03085403841041d404170b120b14030000d1482e1669400380d0002c02442d003100f1102503039142c04e20140e03a45100540e01c48114104101700001c51510010300318044d240c180c900c0340226200c40e0381d00000741524844169020f03d00780008602d06803550846940744c05032400118483d02c5070f0040c8051041070004c60703402244038071501405a2000100042102c0d81968011200c0020891060a22965200c01c0343e00d542171905002c00c4c800005815401d8442880342c01500d0381d51502055a01c9000b4170561031089403c0c8010001b101c83c614070154410409080035142900b00c16100303003142d10403280b03800845c048800303101e61414101c0710030005c1c01c0c0c2904210b00d45400c003000076007001500f1038842c1c811038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 226152886 1250 226151636 226151693
    0x224070206070f081201050301061703190c0f0309030b10050d1401060b0409060e0c07022803020604170607030204060c081804090308041403090a0510230c0118 70
    0x205100410012500041e0076a15030170f10355400f0070705800130b1040343e1096081c000081525110002d60f0320034210765000441c035105034a001442800d691036401400e110659041c000440d0902c03210b0b00d25a40300c1da89512403581140b40400c8106400b4244501c0c01618980038460b5440f801ca0003055a90890000e4140a221020503409010345c1d800035200b40002143c0090440c2540d0410000e0301e860031000100b664030000031040d1401903e0005c0d40c000603a50003070b04014052141d0400c49045069094011070300e80d00032a1980d44207502002c42210380140c000040c3c00148242d907008025031606515003072400c0da0041c4074400d10718018100000008001071021200b82160003243e20160080c0600e140340d0402402070102100d003a1212218001c030341520b510040219000044003c0071002128140010b0111040303000c0c08034801c1c000400c0240221403100400240f4a074070401079541c0d00e20300140054251280c4540182500500100b2000001c1021350340b040384114283c042640103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 226154136 1250 226152886 226152893
    0x80307290f310302010b1005030609090118080408061008070b091210150e0603330901050601020c04090804150c3507031d06091c022407020607 63
    0x180450b4800c1c0c2d03002408120b0009440081e0001c440146019400030030000844006100c8020400071140780041c000300001046440c0c0030580542040c0d000c000021500d081d40900381c040d1403400303c182c900e031f18089405c00c4840c104104d40f43e400052000041c1c2c10038030740310131160341e1111401020389006021440c1c681c5a00c030702040041807210b4408030340c0c588519111070b000500e1b2002c0c110403c0942c407100400c841c0c044180d45401101c025004200041c42c010840c0020811060241c080e042e407030841030310921401d0011070140b50614000581030401c0400689081c440450756030045041c0400d2a0114041b07030143c4048481c1e090324090360140116044501400840009010034003018001c1904403480c0402606041c0c0c05003149500f40550581c0900da0144042c001c0000d100600700c44d0f0340441d0450740c001a44800b0309103900b020003840008007010700c4038400070140740054101605510340a01c904000805050281501401c40020240b20b880380440c040d0240c42c0c00140346041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 226155386 1250 226154136 226154161
    0xd0213090203031209070614041e03020915040c02010c0e040c050f04030606050108070306080a0f02120f0f0606040b100f0c080c061b0306060d0f0213080307290f 71
    0x4080d801000e40e40d462881c84c0320401d455100b903944850398403d907040428188d004605110903001c1d00380b41e16040034031f00400303800484a500605040d40280b4000000180c4401114a014082c0d90410005d2180a0018401151481c51520b021603040c520a00314150700030b01d4100c0302123030585010a150080110640c0c1c94498045820071810000400100707000c034503400079068030b100b40c1c2c81d54030355110707039500310142c60441c000c0c0b40b505d401108210002400360010441802c0c07015144807801c0c542824131b181005034a41000c1402e4010603a0480100001c0c007070241c1c003006c1180c0401042010700081545001003480c05c100788140c0b02030444085000380e18000d070042c0e2150310540d48122003c80c55440e65410303030383c8074202580701501c0054030841d0401d49214003009410b1900741000c1503c0d86015103e001210a5041d50030821140b0500da14840180075050000044d541d407401e41c5080624840d00c9042c03910b031481c0c0d210444205418413900e113900588180c0071278445884d005042c851 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 226156636 1250 226155386 226155401
    0x1202120a030507110f13020c0c10030c020709090b0f1b0403030915030e1b12010501060225080d030f0b0d030206071101050c0a0c0c08030f0909150d0213 67
    0x8840c400c12258208042c0e002008000181c0329010608004200500b030106601c01000c0c3c1d5544201030100c1e404462806502814000a0080440340f20035050703400301e49104800034426001a440e0890070108a4040103840b00900041004000c04011525002e103014030141c41d00300c0e480d800c140428681d20a5010707114800720710401d00b55445a492502a01142c1d482c801c4103034496803001560580360007841101214007060b8041e00c580c860102d05404860b464092403076100c5100008040d139000240b003240c1c043c1256400074420014401d44c001190202140c107a408400c45000c00d100341140840c103940011042c0c04e0100d030001401c11604090010742035069041080400d1001c2070560000d800d0f40a1001a12a6640c5600307806820742a503030300700d42890140c0410040078207140d01c40c0c00d003816045d0090a0385502c4ca91210409801d680c8a11050500d0b0080421303c100d040c034126a01642010032070300001d00da10b1b00f03c80481c0302040d5440c0040c0c451003110852040342d1040d13420038113 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 226157886 1250 226156636 226156669
    0x2010b03060103152f09040b18010311060403150e060115020705060d020903010f0605010e0105071a0402011404060323090a060e030f0d0f0b03210d0605120a0302010c0305010f1202 79
    0x805d00718043c540c0b8000d50080400c1034844d905000b14410a414100da0b440505042c40942c210b9a85c290b440b101c0c6070f40c0907491002d070010010080040843d044120064420420f8031000c140800c03030780c0360503141035410b800c401041e181140144400c41d0300085c02c0c604640e03064074125107420400928800034011003c41607015400d10549403c14840c0381e100c80b00743d44098807040c00071500d080044a2500030700c20000d00013050090b0100e400440000760550162051601c0c080d050b100c003984d440d041d00544d11640101e515410340c000080f01084400c1301d01101c040c1280128640020020342d84c0b10320840180145603900c20304000702c103041c0304595a00002c12201c0ea50b80a43e65084c000a0200100851040746032444088030380c82c0101e4001e0052001c8070405090101031402c602803580842c5e0a5595155203400024540d2030380d00079203008030007500251800c5841400d01a00790b4034038225000400d031403c0c0061010043c46140441034840841c900d0100080c80e03c0071a030061490200d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 226159136 1250 226157886 226157951
    0x81510150201020a03061a09060f07020301020c070314030304030503011e05060412031d030d0807020109060603080306130b06030115210518011a120c1003060602010b0306010315 78
    0x2054081c1d015001004481d4039542d0400816a81d20302e200c1d5400a1441d00284006d000c1154200d28039028010b405201388128004d4038160096001900320ba0001c900c02000f900450803c00178410035500c6010b07441808000b0718654900355400903d00d20050040400c2d4a4160544203100f00d00030034107001074503000c1e020130341d150b0f12484101d440700340d40d52044000400703901000c407500ca52500e5822000c01d01070000c160007118001c00307541e590b00003840c4604542d070311444540402d0b030502950b0011070203101c0450b62400c2210602041201a4031010006404c14540d560143c03501c07400c42c1d0444034158105e6a46440740c2e00e007214080c00280ea291125258404034101280d0180d000a00070000c0301928540401c520300b00c18240e880c610400c0c00305401c421240c0b040b41c10088019010181c030402691220328080000454214841d080000000c2ea2030600348030040e02440b0307050710000221700500a540c51982e03909c007424644021a100e00b82c461080440003120491040d244400e80c0110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 226160386 1250 226159136 226159169
    0x10608030309071e05040b18010b0912010905060c0903120c0c03163501050a0c0801080109082a0607051c0b010c0b0601020c040207051e07081510 64
    0x51992500706a03a5000c07a030148120020300303c03500d00c00c48044040703e00e8070800301c1c45c07600c02080014a80703009200d400076413594600a524202070a0203000c2e12006240c0381c0c6401d01c40080c440381c4101c08501070b005a250840c48004100d00051883c0c0c050552040b4a5940c42c90402090802d8009002d8202c40300c0c001c102d448040801040038400d100d400d0301102c1004c20b01815070310284010b88900c5400541e0302120000344000c0032884d620500da020a08150300b44101034443c21076404170303038000c1c10750341c4d99040284da00e902c480240e00600c01c01000740b0020655880d41c04c070502c107115241c40c0d05e8012042c86620224080b01c0c05c0c070343c200036a00b500c2c0b0341e20b0084c3c2c01030080c6c0d020004c81c01c40c00300c0e80800d245217104c0d24403e0319900c480603551201c1047e01951444000800900914194030924040d1980340d0745a0004100341da01c5000601412041400c51003034004e9191401c00e51030304006418080c0c810300094904505803d4100948a03460700c4a0048040c542900040040300d4400c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 226161636 1250 226160386 226160399
    0x20333220e0105040b0604020423030c06030114090f060a06080406060e0f182b0201060e0a02090406051f0c0606050d0f030e0d02151c091b0b1c1109030106 68
    0x1180c4e00c254002c080403480c9940d02c0080100300d100e5402880703c000e0340ba17101801e060f01d1000036002c5080d0043c00702c2d1141441240012460b80090340005035204241210510380d003409840c0e91f07040f0210902d0754109040c1440080c4082d551401031400300002d10300000d090103980c1d00060002c05030240090354bd810840c20000365040c0448130b1092100300141d110b0340358007001030210080213400071f0210044806007404101a03500c1070400c0119902c0d0b072800b00d407800c0401801401180708580c0140e45102c4101400140d4111740c0c0600d01c90150b100d140317003502c0f00191401200d40c10b00e02e0505151709080c0350050051806070495600840d40514540030822591044824a03010782c84d02410305181c80204180c801c01e202c402500701580c84010924011740c0c2d0701900c20040c0d0900c8a41aa241960354041140c404010644001044540003c10191017018403000703006940c030000d113407000c2c0c0e00c45105e10100c01042d004605540d02c00460060612105541d07901c10018000d110903540e400c03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 226162886 1250 226161636 226161641
    0x7060504080903060c0301080606010503130b090c0112020c0c0d0f0f03020d1b1203020c12070c030b0106080c090d080d020d0603060b0a230a050a0603020333220e01 72
    0x2c0b08540a4880d4001003980030302840282c9040f101c0c440c1c014101c030780d110401181e0641010307000a00d10420b1b88004170005d10314002141c45045140c00a00c0040c83c035600050060208101e100506481004441074548000c074101d070070340c0816920340d00784113154900881c00d010130100150550b28190300f02030405501042c2c4003030100542e0f451160410f4207500d5000445004040140075100002520650600980150003000015000c1d9410320415401d400200d41c00080e007124400c8803410140100861209424058002803418040c04c1c42d03d07050f2110548194860b040c4618103003c0c61204112515049a00c1c1d102042025901e031200a10b050028120500084600c3d6040901d800c03407500704411144100c62a0b42a03904409521a95a4800401c0c40d04060f8220a1384680072885c0d449a1138443c00800156600507540e10303026100c0009001c558202d903405400003a8005880c40c01c480503c1b901c05401c8840035420b503901040302202d002c5a0740b82c0c07401507080c189004118035065 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 226164136 1250 226162886 226162897
    0x20a060507020f0a051c1b1d0c030c030c0708190806040c0f0f03092105030103060e0705010c0803102c090c010504061803150b19050112020f0706050408 67
    0x20341d04007210300d44031810011900d1341409203d8001202e40701d800b198054100d500d14100c1d018030300100e540003003008100c92020541c2c1142c00d200300040b042400003480500042d030320201d1500f1440c19803d0110005c0c8043c40080c0904400e541c002c2a0002406010300c12503044144000e90f5a9040c00205c50251201404881c2207108500c0c1104c800f62a9000d024040b194070045c4e0b4928004501340b520030783c0140310451041d1000d00c417066403054017603010b00152210113080e0b240c1c035480703600d103103003000a540030b200d011a9a0303000031008210a0340c01100d20a420740d8401911601c95440d80c800940c4000c46a101549640b829844140ca407000903240c28440e404030401c04007991b80310048ea581c0d8072182119140081c0c0204020045144140c1c1d42041400800c81c031042102d5903900d80e0110405d8244030911200e50362881d646942c134044034510010381d4001711280085140500107080c5600a0450f901c070b941e000110095140214400c989420798000c100308614105030401031003a8012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 226165386 1250 226164136 226164139
    0x703061d0606091c020409050f0d021b0402071b150e0a05090114032a01030c080906010e072303060f120a02210a03020616050c120901020a020a06050702 67
    0x2044080045141031954103445000003070002c0c0d2401030303100107000400103071100311030013040c8040d18a8016612409948101402400202208090b607104941013848650341e49040d50300103040607840c003c40030003a1804240c00c40380180c9407030042c10240003800c00c007014540c010302d0b0f220012603d50010801400b03102e0103661155010309010090018407007090040f0b5510890050040205913200030f00c5040e02d0101034207540e010280d0484e0140405c900704003250801d410301580810550f03141c4903860001496140080017420a0804603440d824180507801090000c500016005e40c00340303070f44440144424080d5460312040d554030900300d402c2511082e00c070740165a444000c6180c02501130311380039100e402030080c41d45a5802c02410b800c11001000c000003a041080c01c1041d0180070546d403160098025065920b494940711465a0500459105201041c40401005407001401c0c08801407482c003e5a0707a4050000180e10b084950000294024141000440c00c0e513440400342c12600e10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 226166636 1250 226165386 226165409
    0x30b0d02100c1b050f040b041506171003120c03140f030405010e01060302060d02030403120612021201231003060c0207080c0d03050910090803030901021b030301050a03080c01020c0303070306 84
    0xc0000e200340e8081442c4c40b40560145290b15240020701d0254410003a01000410005040890112002c0400515441500440c40d0302040d0340d815841030f06000d81c46130400c4941d141c00c13415660307018010790b00b039100241003204840b00c2800300b42c001c0d29003d000324003004003e91260148204000540d108541c100c40c15424200c0c0d441d44c080d014081d00040c1c941c010802d40c2400035018070b100c003c2d000100240c0400c00128140c9481d07500d1889a01d010380741c49104045403a001d8014001d070b0b0080c9103a000c1c0568908129241c5280d000d8500b6070802041d418440ad240d12850f2400003120f1140d040500068034041c054030440390001120021590660151095038541ca01040082445880083c0124104120b5650246080e17000b00841c0209810070200e0b407612000384c0e919582089844040aa5000034480c0c030000701d042c2c00440c0e18042c0c0005502c1d648c10080441c00c10310036480700410224020842540000c403e4040d10060900c0d0030440c0e4891030840b0b07005001c5c18651189070021130 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 226167886 1250 226166636 226166663
    0x1e0106050a030f02120c04060303052d1c02071403030106080702060c0a05030c0c01060e010612060305030d050c0d05070c020f100e010e010c05070803090918070501030b0d02100c 78
    0x10840e00e40c804894004032140502103c0341c09100b56613005441e50710960242c180c0b5140703591303642d1080d20080c1d4007a80e26183c42c1d44040d608034983c1880d00491543c800d05004070303036482c41020002c8841110590345c0301c1750010300c144c2080020780240800180801da0344d14902d00c0349032002001d14100c46641c1d440444985900c40300b80d880d003a054500e02003105081212150003402040110380041c1c0c10341c0c0840c034007001c1c0c050b040e00311055038008a51010444c0f00402c89540c0c011040c44505007401da0401465245076101a0369204160020403025101c00000381a022a07800350741540304007003000c1c0414905030500505c10d44081000320710903081c03681a20551b050033b50a41001c061584c5540d080c1100c0000190b4030004d0a520720b83c10417115681d9030000601c00c0c0445030040070750000954803042c000040200122005000001214800e44501200c10b000580764080701c0c404c1c20002404001c0c0c40100700100c9054001079000a010010280b60b181c0c0040c143c404280941c4000c012030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 226169136 1250 226167886 226167889
    0x806190c0f020c04090f050313090b01050405060d27060605010f030e19050f07080c13140408180604031101020607030b030c01050d14010f080706020106060507030503060f031e010605 80
    0x1540061403070030060303000401c9514103003000d034810320049000340000300512280c0e81c2c3ea03514681c000032642601ca01001410044500d09011f1590848024203100b4101030030000421454004c0d10320752024162074201e010200c0030140c207004081c04d92a5401c0308480c02506000001e00240d10440b40001c500d1004035030501d11030700c940244008514040d148049687c5440d52400c006c3c00c2082e909130180c45104040d090382001000f0090946074060040c0e645210100080d954401e43c0c1c54485a08003002001824412031031550700c41da000a00d65203510340e00c161f4084849030300080e180c1000c4001004814001060a02035640d44d0903403c440d020b90360540c04070103480c90358007240c0d055844032403080170a40c083d0016040080c2c00c00c45c0014a18820045118594000c0e484100103201d0b01c88180710502e01405800c02801d030b103000a01c040c9142c03c6000300307603202c1c0b00005400c001020000c03421541d101941c0c03a0019400400312039450ba02c1c06501160450201c00380c0090350300c0d042000401d07 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 226170386 1250 226169136 226169147
    0x1080313080109020d12030b030d2a050a0308131a0609130209060d0303090f030c0b07180e040602190806040f0b03070e070513080a02120105060f01030c090806190c 72
    0x700b550152400f107111145946e50766060312850080010f250b1600d1502885440c00c00089401c00740030359414100d203410b40c00035907058002c01d0120000d282c40000000102e038000034090041540351404142a6403185011200d03c45503000050601c401482e006c000c0603400d481c120300070601250301c2c80b0241c41c0c074804110314031100d0b00e00070340040b480000116140f17042400c440c510b5000342400724580005a8030100400e800e0f901c1140031503517229000f400d00400700205030340100c081c108603101c804000c000080f40742091180f42980c40070b45000400300234442e0117075400035082021100c0310f04414440130704140c400701c03503e0f4004c500e000c103943c90600d014020702200c1000900034161240c2001500500d5410017070108050010402c00442d40c23012444030f000c02800542c000d02402d00f050310421000c5581d002e1804070766130502c1c09000300e40d0b0f01c0b002c1d011181c1c1001d00340000e6a415403081030340c0c625619880f04055000d0034042020880c1c002c0e00100d094a40a6420089842507030410781e00f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 226171636 1250 226170386 226170401
    0x70908030a0c1209120503040905090a0308063006010512120409020306010315090903031103070e09040203100c030e1005010f031502090d080a02060109060b0d0f0f05010803130801 79
    0x240b000c00304002241250201c1c80006042d0b24106a0054039861902d1030801d11400c00c81c0c05a100060801100041c3d02c00c1a400c5450200030342813054030307500e0080c8120710180c00b42d4482c82000c445d01c203041c103150b001c4040324820130862401000e0514100c50b25903800b40b007021f00900042086038031880f004141444800341c90704003035040a0034000114000e4100405560506980381500c03078001d804c0d034005c0700046c04000000b0940040b00e1a0003420b0326014451100320f01c0040c02480b140e1a041501c540d40650f0946426407240d840c2c1c0002403401e10f1200d01c1000f02840d00e540b00300403d034503403c841603503030000d800c0f10009da000f50090b07005c5500074441d2802c1880f211005100289861120203080f00503c40f01504058a00c00095484504140c0407034100d0380004607200804c0c5c0510815004000340c039004c00c58907180614894451040068010046030703265040c02c4440140d03489200c0c80c06410b00100047d40e100c2c400244d4a43c01103e83e4021740c810102c2c000b9660405002c0e030340 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 226172886 1250 226171636 226171657
    0x903060c11013b0c040e10060609030b0402010e010c0803090a0506060a030b130606082a0301060302030c060a020307171c15030609083105040912180e04080307090803 73
    0x60403c8a0442c1c805503081c00c0d8503504604c0c040c1c19840001c0b03035203d0286006480ba2603000d0701007410480e09207000c0350025800401030184144080011032031000300e1951080d028201000b4207128200102e036584400ca9008021007000300601a400000040d40b2000c80d00c140c04450307a548800c0204040000d2030700c002445d214118001420000d40c1d94070200c1c0040c403d1501180258943c0c007284d060400c4401c9a0180600104800301919052818002d0054042e002001100d013581c02007a1038801010040340141c6c800109648a580300b0000c40702443c0d000340e908170b04c40030f421600c0402a8480070724924800c00384521002107800a1142d07000004203c48202c0a0901d580d481101804201400384c80c541024040800150400790381c10800420a501117002d10f81c441c5020700381c951003608028000c40c6464032060014550445694401d0f002d814020a29460310700594843c00590f0840c1d807000e64201c061004004000b00a58000c0102ea02c64940550f00c60711a50f550303018151018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 226174136 1250 226172886 226172951
    0x91b0609010f110102030906190e060f100b0d0e010506060310030b070521011e06091701091406040204050f22170a0513080604210903060c1101 63
    0xd030940c0a6003078600303914598240020501c4050503401d003240c00440b240b40391600200204040f40b281200000c0c0c4071045a4010001c10442d0440300d90741d00001485420b0784e240490205120809400412000340350081c0d0341980d8070800c00400d0041d11a901a0303050039802c280120b0348078503081054910608021004505017450f5071240f4421500142185003408030030001e20b0840030901d410b41c56820801d401d0761100d54580030b500c0b500613001400b002c2801031155030038020103a100d9802d01c1140d40a000700311183c118044d80c40e00605101070024030195060095034494100800d00700d01c114000c9a04100b1640c4071b1021a150318800c8420f80f440444a035070201c07803814129405c200301800303150109594040c02a8412841d401140220041600400e00c560003095000303604000d03202100240c81c6a061a40c2c1c0c0e6000308114800100c200242504c00ca4103040c440c044000003550040410320903d880d0100140103a80924079640c455401d1540445603015090861402c015414200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 226175386 1250 226174136 226174147
    0x60c03110a030522061b030e0c0402030402120723030309132c07050a1d0105010c081c020702040e0601030b061e090106171f05010309081b06091b06 65
    0x12001404010008500710755840b0616003194940603150313402611425000071501100d140ea1005c0e5036030300b4428000c060400c08058000d00c030104006110040030740e800358594660303100054811541e0034070060b0520400f100007802d0400d1610450003800c04c0800c100d01484c50f9404d00d40c903441038030350064100c90a000715140c078600f580d0050401e4450810118129a003040200346600000c0346180807680c040002480300349400100100140361145030102c0074810f2001100013000144a00307414811b2f4a0701100500c55400d044130350349602410100324105e0700880070002500b03d200d00ba40a9442e25030005610740001600e281a01c1d08610341e00b01959951007001803d080035110025903800082c02883c840e03c4180c00701e40a0503954450320071060034480c9a40c00c2e010024006070245850f441e01116410b1030004410560780c0031b107000303d4a15424108101c0d24820f201b4aa8821a41400c281c0071102010421038001da9442058074591900c0040f12560710300381406055010000300030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 226176636 1250 226175386 226175407
    0x902070809060f1204150c09080c090402060c120d0606050a020a14070e010b0703030c020712060914160f080c0906040b0103060e0403030204030320102004030f060c0311 74
    0x9454600c0e000c43c00301d440d003007110081a01c0c400341540c0031540c51302d840c050251020a2801042c8112080780740c40d40155140c002c481e503a4810001c141801004501c01040a54862204442848020600711880c80e4035040741d45450760b0040d6110000d60780f4288011440601c9041120b0300c074090b5900905200344962200550410801e40c891410320500c90000307403424032112124000c0508100e43c40c0c45124504000e401c1e1404440e206003190098442071080345502e070b01410080c0d801510001320501c0918010701d0698250080328614450954240902241e98852505072030441681c01c1580b551140c02590310208404003d60140110300001e100f820680e0080100400514001c0349041d500e40d500d0741c0410080d2415000a500040c0c10300915822450009a01001842c00040100d0711a08180c13565194014243e0707c0d501c400074682007070880e2800c180c666012003051a995641ea152000c85c5910400b0304542050801411058950180c416002c20250719800246450020103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 226177886 1250 226176636 226176649
    0x6060907210b13090309050f040c090e06040f14180f1b03010f0207031115071704021807090602010e0606030307030807120f0905010b0405090c190513060f0902070809 73
    0x84280e83c10500e0251400c45040b218054441228040e4403445c0f500c6080006120604d46072200890046081c03264886400d030b8000303840012a07084090299098175404e0000e07006c9c2001d00d071030000c654100400e8500352150001c0381c50040d40900790001c0c41c0544d02c054152101b02619030381c0f0700c50300280e11000c500704400d0329030820310f50010000108080319040da64102d07000b041c2d0990002d01c00d116100591141001031888581a440a520720362800800c010f184c00c0c032542c0c5401c4841c3e40300c2d01003401c40d1500300d40d0004c1c4e041d12004203000c070715100030010550801445040c00640c2030070759005403c2c03c08100035004100c040d000d5890960141c07400d50b0180d074042e0001080020f0340404840101d564407844039034006131a00030500c0350035400e0560969210002c0b09100b05d1801050040e400c10002c0c1c1c04001c290261000a4001d54a00c0003040c0540701e03a105a400121038803022074103021640c0218256030301c400b05000c61a0300e460f130a10890003030540082001d50204442e55480c039014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 226179136 1250 226177886 226177901
    0x60e01090807081c2a0203150c13050d02062d0d0209090108030a080402120c062d03070503071b35070807110f0a080606090721 56
    0x1814100c0c40c0c2035490070810b1070709500b54007102c40368000e01c1c0030004411150701d100c8030500e07452400404000d95903649a03820340c080484c80c0d07a0040d0b5802000300f152001e125281d1412030b001c0c039504113440d01201a698940c001d440c43c500a050040010865161138400c0303590094000d8081030511000d8050101c51100d520100a6050300010300300c020f00724043c0051235507500d108800758460b40c5031014410008010b0700b00350b001d82c2040c452401c1880d48544d601c0e910540468101c550039096011580c2042c242d905034641211002407850128280d1110000000402407501d29190344050060040ca00080c1c40c94000244200701284915100720032000807800900c541183c1c54445550700700c034002c00c501d008245002c0107030140c1c40142d0007201c2c0d100c104000008180c90310a0f19918079601d0710030a00d0080890000d2140b8114548031002050740d8600301420240719651240040d66a070030040316028810368030100028005841030f904074003194a0a05c03401c490f907902e0318051015001c075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 226180386 1250 226179136 226179139
    0x17130c140a080a0305220503100f020405060403030503040515011a0702180f10050405100302012312040b07050a0905010c020f0910170106030503040303080417030406290109060e 78
    0x72040102d285101801100b00041c42526a40c1e03079000004011440385003020151044004102e8041000c4c0d1404240c12880ca404800009400250640546c000303000d01c2c1c10164000c01d000c6804810160808025401203000d00102c840724024001c1e980c114400901402035042880004c0c03100701404503001d07250f10340c8000c0402c5131420f0000415020b0000c101c60094804044134140441d400741c0403455405842d05407010301c0940b90026404003e00600e1100a040000010114508000310004082005040340d07905a40e00b0704181401c00200c0260390a4840496a0000c030304080e0142d81207440c031007069120140311620b0607005640f4a44020402d9170402c14446010540d0360b40d00c1d11a5100c0c2480721000d16402e4100078140d5503881d5a02c0407482eaa030314007803081c07005c82d00000c01c0d90100c030703810b15040031a0780e264940840c100781c580d40c2c041e2a6820200a0204000e83c507000000c0046c01864507030010b1200740c0508100c040300d41e01c1c0c2400b0603078408040c000107211316000c603002e00e030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 226181636 1250 226180386 226180399
    0xf0302120f0109210216050111072315090f040e030c06090706020c0306040209010b030c04030c032001031407032d0b091003050c09042117130c14 64
    0x60744051509603203464100300d07443c020b00006402081030460700b000320688913200034299107244410b03036610204a801554107101002c1c2d0001da00d00001c10408020f401480c51205040c440700c5a44c0c1c04680d02503441d24410f4080403940408200c4400a407030800e40018610340101c00c0a00911004050f0406200c480c1d000400c0b58240c4e000040280c60301a0186000422410349050340003401c1c1081c0d0442d591003500031400303010260707aa101142d415600f5950f07a140c4d8079101c13811404800d2140d9070009000e02c00c01040001882240c504101e1100343c41c5405401c00c182040044003214440e0005070200c004503408240001d1080d0300c558480c80f9140c10104c030000840c01e205071a481c1500040941036142d0031081280e062100c0115001104244c041c8903060441e51095110707848000c0c90b0303014034403c20008041c0f105822205460b200c0d1141d017007081c50000c0c0f40043c001c107041c030100200d0040b0000400d90f04e400c16003c10715142c1c0c00602002440c1c2c01c141303401c058034a1244046600c0301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 226182886 1250 226181636 226181653
    0x2503060e04110306070203090d20030f151506120403020c04021206040f0506060d0c05210f0106110c04050604090c121a010518091e0c120105010f030212 67
    0x140c00c0001901440c05507035409550411030301014640100144040700b150801d100d100900d45403038115102181c2e001c1e01c512040003040182100700742d000819640d040c03040091111603110301080b110300303085440d030b10b900c25966107600c00c1da40084d5003002c59070804000c018803045000c400740e03115000b520a1040d101403c0d10400050142e0300860640c400e6800c1000602c80d080c9800e01c94a80110310500003400f00f071034080006580e50042c1c3c095855255224900442101d10840454101034169142100f000b81c43c0c44180e02030240442e000c89252545600114100e4052195601c5039520200180321070711020017400007070640545102d070400e80310646e540000d044440b00802922040c040d961403080c6038201241101c1c02c64602d08128409a40148140c0c0c4910114180121a00a805d002a00c842009900d482400c40b101341c1c800298001415114002054041d1405e01c2160348944034049821014222202840395409041703031820f080005041c50b00085554410200640d0821b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 226184136 1250 226182886 226182899
    0xe0904030207091109041808122e05041a091801020d020403030503070807110303041e1b062c10020a0b010f0608090d0f110102160809030f0303250306 66
    0x4615400070713030700c103076a010602c5001402e192054031303506030340344c40d1356007821030319445003034040c03184030005d00321020300c03800164100c04084042c2000c401551080c80e4401140d1180820005590141910560600c24204107102144403044080031004080d0700c0c881d207901100f40441440f0100e244000c0d5020311410342c0d912180e1001c1c100440c001e03103030300e60b032442c1540e001050300000810f00414000e003100600c1c8100c0300041602da1203075004406240f800c3c150181c0422040c14070300001c03c10100c2400c51042006c0310f0b2a0242128220384407038000990f401129070299030f130555100081503903140d0917000c40c9000842c1034a071100320f0041e41d5071110b03291100148600241c020044001200b03400b0822507900c6049240e0100400019001d000389078080180a2a1180f0742d1408000b078040721044007000a40c12a03e01060303080c28201134402925041c8941d030000050a446401a6084c24a1040d0084122845040c4c00e960182000002410210000c0c00e06c5c0310403800c140d40c4403c085800c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 226185386 1250 226184136 226184141
    0x5150603100f090f0e0a030c02060a2a0605160206151903030201020a02070b09102d020703051c0813030201110a05031b0a0c0818150d0e01050402010e090403020709 72
    0x2070590000080703803400c05131100400b9180c541030040410380c80a104880403d43c00032805100c60340c12130b441c9a42d80c0d80108125880c0b41005082000012150306c00e100b500480d4200900d0036124600c140042d90315021f008207888041e1000c0d80240e00700301c0005017003960614218482200041110352062030204070703080710100a40044015030740c000307014204a070701045110018011440440e10b00605080031030113a2011038840014000c14078002c45807000010a44061805100c50360001c55040041c000c0d40c490884c4000e80392400386504400c803203243c24544030000d1045458005660f2038400ea08118450a51410341c11075580e9a840040c9000c908001c0c00301c6211079644a48030b05005041d09044202d5030b40c041c8824a04205888402c1c2e084005a108950001003068580c01f00792043c20894158a1011f5400288039215041030383d4030f100500342c0700b080c110301040888a0076080c10708950003500e0203030104076402516400c0c2e2030210180d640c0070b80301c0d1054801640c1d840b5450030070f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 226186636 1250 226185386 226185389
    0x1409130803130b0c03041505060102010b040c0c031202040b0406050d02160b0601020c0d1101050d020f030c03010315050402010c0f061407020303160203161101050c060109020301050a0905150603100f 87
    0x402e51525129410321140b0121140c108440000251440c1087d95451403e101d900700d40004480d159070019030741d40c0c000e42c40000d41744005030007030101c1580c2900c0103002041186080340410350303440800c2940c9080d4030036141642e568010440c41c1034140030040c0c1d05500500100b8410940070025642414907c2444241c0b081c811469540c01d13041c14400039040880e40e25106005036001943c500114903400c264401c0442c0030301788969610f1030583c3d440c1c007074442d41c80000010300d000000d01c0f0a1301001d1005604a0340500700001034100c82803a03000c155803060b100030703000403406d1501c0004030720315890a103003c522030900050303500c02c203490300e00007171f502101d034100543c1011041140081013101944018030311440650b00d008410b203000390500f01c11040160600540c00160380c0f10f03900a1040342c0305040303010116030203580d4038140e6401941c000d02805000700118140000d01402c203000b4240254102d0f104840c020158006000c00c903000100000e00c5018044400100030080740100d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 226187886 1250 226186636 226186651
    0x415090e16051027090f05090d0f110c030f0303071b0302030f0f040e070201060918020108010b030a060e090309010e1e090c0d0f0506040506030c010f050c150117060a061409130803 79
    0x140c1102c3c802c21201c12140c0041030074040e500030000d0680b1403544913072b8a03001c1d03d8460400ca5252400c00701d200e89003800e0032880075050310844907514010380300000910304c6103a00f035490000c5a4072000a0400a092940004025a0083c401050761803035850242c140302e030903005002d0130281e466004c0100d0010035614040580d42d249000e000e241a60b010380f888181d6042e080b0b100311442640020031200c01441b6010300f49a000c8040b4803038401e1030300581c2c010003010403039418031b081c10031445859602940440380411210b49089249003000c03d52001803800128034400c102c844030742408020070006240304500d0b4800c002c48000440c0903c1500c120184280b000035140c034000c024001241d6015155510030707030003040314020a07a8003100054030b00140745861510b4103c8010010320344083d0040c0144c4014100300041249103d480c0081e806060490850300591601246034046134000d00842c29404000300d41c00040e03003003000365540c0001e20705404903100b440c1f075210003e542d0001c0d14400e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 226189136 1250 226187886 226187891
    0x10e071e0e0121020d060e011409041509030206090d0f0905061b010507030c03180b01030f0c030b160305151311070501140f07090501080402040b0415090e1605102709 73
    0x10280c1d441c1780d104450142402170484040c40d41428029030201d00740b4030003075100d181000009810020102d440c84107980c05074805110b890800e03d0060f485420442e0602d10310f210308522007460300d03c111022440003426072504e041c5281404207020b001ea0100955140b20801c8080340d403024a000d1185c02e00c17440e4142d038001182459408000c0a540002500c5d208454040340803501003050306001c1411070f0b03070241030b517004600d051400147c20340c0c01d94001b0702010010010480c0d00b031102c8800d0f5500c20981d039010480baa0f1358080b594440b039a200f01030780d040007070120301c0009400103a2203034400c1041294140e0814030380d40c0c1c6403400e550650007184403261083c0113105401c6541c1c55500e0708005a414120103003420140004e00c0b0400040c0003a1190307881d4001c1d01c00a03251980f00d0403403041c0c1d04003007580481c3c54030706038005071903120000c142910840d01960f051000e075680314000e84800400021201b406000b045403804000410031401c05c215140185c4410317802c22030a0010103401c1c030003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 226190386 1250 226189136 226189147
    0x1103070b0703292b0b09010207030806010302030417160c0b0403020f12150a06030218060a05030a050606090919031206050406030f0605220506010e071e0e012102 71
    0x7480314402d05207203621004402e04030048507030b03038500032110282200d004442c4248070700440c00d00c40d250010136004d0000700504050044000c010340080c56420b001b81c4030b084075a120704004401300e200486024204160341c0c00780c0700980a0b070740f0042030030716026408030780f8030786403030310b903070000600c154401d044a01c1c00240400450030100c02880c2812303070840302418500090103445481d00000020100201c0e031074800030313203c4292a0b1001c00650b40140c0428a8072140000200102d4801d13140d080c840ca40c00c48000809140014014241c1c42d0b02901500132500c4240038050040c80c00381404405010350402c6113a13821456411420950083d0340c1d4591400c08203000e001181d00d2900140d0060782002d0060001c00d49244080240301e5021900140c00d40c1c43e20100c5000c0c4e0052130151030682c4c0d8040c075800a0ac0b400040b0075048c2e03420050b036490070ba1644141947c44011810500d61100100010300d000d06000341424a00d40380d040c1400c0e0901941401d10000400006103082101a0302144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 226191636 1250 226190386 226190411
    0x8010501082103070305100906060201050a0510050307180b121c0e0901050607020f090106051e030601140a020a1703011502010501290d0510030210030504080403031103070b0703 78
    0x9600400300310b40e000700a514034010035a480c0c03000400359002e1603124800706141ca004c540b6010700a044540e802c0016585400d80240600002d480300c035440750921010800c00400d440c040f0701100c5000b001006041c2c0303400f522201e4024540d2445051547d28240d02038103841e04070255103810143c8000e0603000e541603070060300400a004002d410800e03050003903582c64941822440c1519002c0702d0080d00c6011601c000b608200c0d0102049400010020000403419040400740080340f00b07034003007441500d412981c1d9030194001200c00c81c2c001586001b0381d000c060050382c018802210340c1d2050703560b90001900d400081c114407659000007a140003004000400701c0c441085d204400d07900c02809a545010328004191042010341d088807448100c8a074860b418410490fa510940e080060004e80741441c0c0c4014180140c0c401039000720011001c05410300d20034460345100e1a403080d0564141405c646040312540381401d2540401d00c0108000d10104540c10707501072203060030b9640071408003c00ac0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 226192886 1250 226191636 226191643
    0x309140f0a050f060f040803061f110c040915020c1c0f0e040509060103061a0a0306060503010b032103060f060d06032112051b0d0c021908090d0501020f040801050108 73
    0x191080314940020003800b5540d05d18010050700030b500a150142c0b21307180c070b40025074100c4002c1c801500e071682d41e00c14404065040341e2100848400c80d8181c500b82500c8a05210076079100000c000c008600140c8a003009804a030f0180c15103150301c400311405004080101d1000003e04480500800c003101485400300d0f07844089000340040c280d074280000d062080d212507542e00b06010080c05544c0301c0d4400303030b4117888845041405050081c01444215544e080c040002d03c120b004003402542481c14020450400081c0c56041c1640000d4051241c6440c0103040407640010f4001a48641301800001081d075401d40544240c41c403060000031401d2030340c6404000c61a450300e40c240d08654605190071066004080311240c0300e910180030800e9600d014400c40314a00410003a80130060103e2030541074046a40110b04441d007070b40803540c00424904460050311854440145800300802000d8601e041c840603c01250344160001750401100c2c0744d15a042d60003c2d000104280c0d50350700108103c00040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 226194136 1250 226192886 226192903
    0x2a0102090a1a090f0303090a0b03010306050f01081e010603080a0e0307091a061602060301240201110d02161e0b180303010509040c0b040f080c0f01020d0309140f0a05 73
    0x90071035420b0885510101e103540912199640f0440c203280c0c0d59400d0707032401c3c001c440c0c6004000705000c2c031254036200004c1c03041d003080c002a1406850310000640c7e8255441c0c101c1d0603a072084000348112921640341c40c00281502061600554840c0d40c0000016800000351264402649800500b446060706051400c21329034440301a241c101505e200f840034581c100c039a43d8010035110169070315070203001c0703113043d49914000a410860000c000a0140e0703c46040308401101c8200c0514801e8010f01c0803426982441e5207502c1c04030341000b01c0740701000aa030080002000c644070715003d200b1140c56803409400c000c00c926214025501e410b804102c1ca81c0541980440300d032a61031350365604001d059542c0c0c081405414081c0389603501103001e02c113619002078010711940013020303036841e182d040b005190030320303882080078038401c0c0b90620506140c501c0704d41c070080c14181c0c01010184c5074030404402422540a0940b04c005103c45c0b8900b01032010b100800c0303103601610040141c50707413510f00340e850a051b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 226195386 1250 226194136 226194149
    0x1b1a0c0f03013011060f041206050405191e11030105010b131d0105060a1209050c01080108190602130801021803120301080d08070e09040b1506040b0f2a0102090a 71
    0xa0010070000212801131208a00c003042d10300c0c64031740c01c81446100342481180c0140908022880c00d1004001042d00140e21491003441a40d480c29552008480502d0704010020010510b5208000d9085e11080080c100140107034081c0400381c0814010900b100c0e002e0704040c4007540c0008485404130701541007280141281c100110020111803151080b0b40d206000e01ea12400700001d4507002248075070031a500403148400708114581d198505165203074070040c18580820303125000040c07030780341c0815140850014810070001c1c041150780c0701002984100c04400307807014154804120a030091024085044120030300d0302020109908240c030f40121850b48900c00202000140041540410704805110003424200e2450300e6011096504420341000c0d1500640c10204000c00d101c0e2030303540c440c01103140c610340d102d980d481141400741c1845030f80150000c00303c040110601106e8600c008000d00c218609240b15500048610100ca08076030580c0d06030703da0b4001c540b0700154a0b00c61008001050b2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 226196636 1250 226195386 226195469
    0x2d060102071a070f1419060b010c020108060405040615091406030106030c0909020a1a0304060f0509071a0409090b010806100f060309151104061b1a0c0f0301 69
    0x16120700d4000d540b00d0100f00400c01d01180c46188100700f140c00151300f0303994542040d502e8142c50741d0200801d0b0203c0000640c0c00c281409244c84a5500418800c002590103175212215682c8030700500c00238010184c0215044c6540f29140c509140c2c910100c5070103020359410218000109412a1025100c00340001e071090b498902d00300006009510900102c0d5650701002c00c3c0d10015000180c0c0c040a075520000701c1e0b80640744004000c00400b0000e5200d42d1081c6010031054400203503a604030340048820130802c0c2d010003014400e101d281e15122041d0390210b45c0300d5242a44503042c180a40b4003000c41140c00105c84c10040c0300c1c0c94020b1000540c06101580303500f1180380741c011002d0b0520420f214500c10f05a590464070140088406030000d0006400c41c1405076080314101403895074801d11400e000a05030310301c08403405450061421110ba0015110000f11420004aa588020180050000c044100079003c030309600c01002d10f0003824580c0302001c80b4000025000d6018002c21480d000502 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 226197886 1250 226196636 226196669
    0x9050301060b0a0c081e0403140106060509130e0d020f19020303190203070204090b09010f090203030d022a0d0e0105030708012105060108061b0f0906032d06010207 72
    0x92440e03007a64a000080d1810340c3c0e26250fa410022040c4c850000400e41011109008a15490f0942e000344108c0380b1a44a000350701c00c1c40c200b6107003228224050500011030402000d920b40c0b0380311609650300c0700c512200017941c02803840c88620340780c0741050381c0707016811490500113201c1e000c2c0080c5144910300c00481d03071b800c00f50758002616403185012030700465121504019542c0e20810a9403402daa010b803003084800c005041641000c4400c86408500350700304155440010b00c14058982c1d407580c05001507090480304038000c030280d040050ba61203101502000d0b010754044043c041c080d004254000b4240d851040d00008015240c0b0f240b544d418882d0400034002c9141c0d01c1005c0307d04503200100c170140062662103000c2e06007071940740040c00b284500d00000c0789600c00451064042d0071424111043d030940388090344c0701800342e11103140c10120306028908050130f04000840d48000c1d0401c03c03001d210b9200c3c40d01b1f00600c0740c540b5100101d000381d004110310b41d40c0410112000e008140041134065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 226199136 1250 226197886 226197899
    0x20901051503060144060f010c08030903070f0b0105030c010503151210020a030f0515030a031b06050a0c0e010201061a07080f030f040c050f060901030e0a080f07030905030106 77
    0x180710180449040115120030324240301c15004000d0105e18102007080131450401c0b90092490341c3c00d0103107210b10804c05010404a00d05855140d18055060b19101c10140c040d4449810a800048c0724070101d00041001c82c0c001446200c40c0d0344024030415000d50554140400d051030300c1c0c82c0c180d80e0b0741481010000d108403403141c120b4001900d8070448500880901c60b4200c0e034205012000b034444154004102c103007281d40c1507042a100d036a10081e0030045079071039046e1b841c61650240d40c01601500300040d0200401e2052174035201c43c0043c00446800d42c80e1340e03aa0310301260720454080003807555520b584404035900c0003d0703000403070007403009205050811012120100f82d0040200d58000000b54039010800f0500a444020010745602603c91170600940030350150304403000c48200c001d01c0000b05403454a00d08005000c2e030301510ba24108860310f0015001010003400c0386d4802c3c03042c00c0c4d4142c00140408002c0c40e5005015201d6a250080781ca40503041400300e8200234481d905000050090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 226200386 1250 226199136 226199179
    0xc04080307030f1103030411060a030f0c030623210313060807020c1f1d030304060f1107031e0201030e070b0d110c06040602070c0e0106080f0702031207050903070e011202090105 78
    0x1c00c0701c02c4885d0ba85e6086280b2b0180c0040c403403009114038180c07c00321513071300301a01035225104883c40540061528000e14203029100042000641e80c050743c40380303001c10313280c03100b140c2c81c0114041507084924142e00e0540c1c0c40300203242e41c1d000c44002001c0c07000708441d1070340c1444503d0f010582030380d2203090841880c034204400450841d0200801200c011b15100d02138014855280c142c0010f420340707503140c2e00e604005040c081d00d010300ca004144604144403071114001240411a80c00c240700d0509540c610b580710b2540300c490b20701a810103032607483c08007843c0d900384031360070050000d10200c55a401c02e00d10b840c02036490041003030300b180c0814400f806184a001ca416a0311503401800182d862816141458111070b01d5045011100170b0100041342141d00301c11014040c0244240d1030001c0c2e610814101e17a248a11540f040d00050b41c54041640da50185010b402610b100070203850714241c484d4a4140d002c0d109912840940b00004a40010f50030050301540c0075000c15909001000e5501054254 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 226201636 1250 226200386 226200413
    0xe070506130306051e06031902010f09180506040b01090f0506070c030503040801020c0c060403050a02090405011b05030a0b010201020c0d0804051e0c0a090605180c04080307030f11030304 82
    0x50500000c80031030780078080002402865118100300001d052503032442a410301c50300044083c4004440100e00c4c2840c00140041d6041d0801c0401444507000b40e00454042d2401448402031150551000c1100e40b600c06d40300401110396180020b40386455801c00094820b000c04180c1844030088051010340308070100e050541c4d000380c070036540d102900c0c58021461031050384040d01d41d0101050105072980190006c004980f1084222144110440100300d00c500c12888002c0c120b6100d03000c1007005061503072030a948240100c00018001c80341202c0304400c0c6c4e0148400f40c3c0090000810401d51541c41d121f403268441c0b00307100031800c0407003d4480d03c3d540c2403005210030600040400003810170204005000c0c603403404d1a020071171074010070a0319550314101074240d03200380703260340000c5940c0c810787c8240000c880004203e881265200480c240d00c48501410140412808000105500c00c0400080a5991107981c0d41040f008420358028964401902c0480484c0c20420a00c0701040c2c17960180304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 226202886 1250 226201636 226201639
    0x30606010c0c1e0e07030f0b1c0611040302060a050301031716110414090f100903080f0a20070b1503190c0503250e060a150c02030111091903150b0a1701090c090e0705 73
    0x1500c0d2001d208070b40154051544001d40c00400005e1005d040c5034700c440030318100c81c0b19800c0080340032450340009500d03000c0c0f00300d0004101c0424083c0808240030b140441021000500005028a07203d036548108900c12902c3c0340c0541d009040f4400300324000c12841c402c8540701a4100803c245e00d540043c404180600b030804900381c0000464141c007070315403040c20312a045a104860b00c101c0442c1c40360783d541000c801078401c002c0ba1000a80741d001544800d5034102030040207402c1c06188200142c0c0182d05020041d545001656804503094408202842c01c18017034072450010709003045010702008400e500301c003070b81b00060b9003404113031746803400e50800b5181c51040e802d0700400c0c481c4003101c0002d441c0401a51560804c240c0440007006200204481081a158964000c1001d040020412005d22009240c49418000103c1201a0f0360041d980744000811440030140d9403882c0303c0c100028082141403d0355105081c40c01c1004a240c03880003000c03407035424089540b40913603d585610700d0748103c9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 226204136 1250 226202886 226202891
    0xb030a0b06150406030b09060102160312050403050a1a090a030906141c05100503210f16060b03060a05011401080405010605041109030606010c0c1e0e07030f0b1c06 72
    0x281140c2d0b1210a242c1c20410101c10039a1610350714240140905207195015000340340300c20201d180e651010507020b00c99a5041941840c1038036503650b0f5001d940c0c4400315402040014800070001410920500800764011003002e130901d6503403842c1040404015011540c280c1c40521b204002a4000c40c440d030444003c2e00700818682c2000e0390007440380c0301d80d08032031005025800000313400081d254031007400351802d8807100d82169100c0c414961b459000c000f0140c0d05445c0c03895019400c6607668001d018903c090788980b401c2140c0300844008446000300102c41050700c4050042d00c43c14100002540700310143e00a20455251040c90059004442c142c0390401c205000043e06120094001c5002401e001d0000c21164008154840c915000910891b01c0380c003989000c9241d0703611501e203405805030014034014030145003150002c9009103101c0c4004468030f001d05c00141036504116003511402c01d40d01d010802d0781d1000b40807401c030741c1100c001910480c00122508889500071307509401c0f0544c0607000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 226205386 1250 226204136 226204141
    0x60f1e0105090a2301050a0e1c02030a08030406151202040f09050601290a02031614010c050316090602280819020601080609030d020d0f11040f05040b030a0b 69
    0x403940c0780300e00741d0342980010100d0f1000548003840b81d50343c4003603a13985940390a008a41001110540302c0c0100c04030000d8003010b0000c1e2540307041c03604002d800a56110780310101d01a81e01003130420b20145c1058070b1045011040005100c0c490141091801180484015031802c1c41c0101450b0004544040e028564603036120080103001c1e40080d4400350060100c03000f43d070790303260b0001c144004030311000a1029409030001d211070459090340c2150a075070300a54141880104540c6021340107090540f01440843d032942c0c000c407030a10400c06088101e6072020398a19101d500c4405402210f98080e0411005040401550343e0203d142d2400051044901c4203028890882c461800361919000d810000300042c0e4842c00552132402000b0a0001c0d02560b09582c2d80e0b4070900d48406044a018070039800402111410720400d50080200d49003409002400001036111482122504403000003042000241807054107140e0f11804c00810040b202072004215100c0400d8507010041d50081400200001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 226206636 1250 226205386 226205389
    0x30915050c0d05010312110c0f0d150f090c050f100315030c24020a051504060f0c120b040c050d0506010302091002030a0318050a14010e01020c0c09060f1e 68
    0x100c45802d01142003e0129586a00700380000011050300740b80130444000401c07042a002045200510800910104941d05080103101403440101002c962041000c040c410b9085000e201c0c07001c41401e1410002982d18031480c10100d000c05a40040740f1914000c40401c0c095958202010f002031068640803030a103411358010b42156009410003888101c80003004100200306614200d80b03c6400f550204034040e0070807040c0d8940500e140e014055400030011001c8018240d818150018414040001c83d407100d090010110340040701310500055004002c001d10715807500503840700030000c480810255680d114094401d10499074030000780e0b0344480c0064810380c06079040c1c40e900e03031011748901010420b02038001d4a030786c0110425404a80392a03c2d001d868070188001d11041c81c1d1100050082c601103480b15040302e10b001c00c02e51603964960320244400e10080c006052013401c55401080c2041d110410407600c2c00c0003c106034051440189010f940c0d941d174034200c02c50095184006070b0f51110600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 226207886 1250 226206636 226206661
    0x504020f0a0c050f01020703030b0a0e0c0403110319030807030c030203060f010e0a090603140d1b060207050c0a080706020f03130b0a02010207020a0e04020f030c0f0f03030c0d11060703091505 84
    0x4441c4c9405500c00720f103071014960103400c5601c9520086420250260311244d0707007100c19809403100d031600c00301407109000140b00c50307002c1c0c4903443c1c0003401c4400c60b00b40540b0512801c00d441e00f040340054810f400748903003a901800390100035140c50070203508510f0000c1c040f4410005200714181003203407090040c600780d12008261000350070444400d12901c0d0310b90802c0c111000c943c074030070b10144c810314410b041800e1103020b1007e0311030290b8000d01100c40b410b0b201d840c0030307420500081d12240225082c200d06070b922060340100a004c103a0103441c042c2d10304030000e42040b26427400318005400400c060241c99101501001c2070ba080005096114000c04808a0090003810030003900304110403400b16401c0d109910301403040e44211a800c0e01c141400c070a0503151013180c0d6070141c2143c1c0380b030702141a6241502100c20131000c05011a814140c0c80c02c030340d514282e00400540081294005008001d400901c0200d50244482c2403d00ca20803050b03032840c1c600301c1d15100c1c1c41c800c0ca07920004a6000340581 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 226209136 1250 226207886 226207903
    0x1020c0d0f05062505040b03060d150e06180106050a05010809150403170a0c0e040b03101104030303110708030109111b0d0914030a0b090309030d03150504020f0a0c05 73
    0xc100d031518030f4400c0058034201071303010844200ca00d0002507062030a20038011502076a0341200b51700c1c2991214400d0003e007118500d0100e0307800da00a0034000300401c0711310404221444403402000c0310b0a1a002e4144007404800107620075904010b010300640d150012184226142032030410500c0d41c2d0084030a050450f10f12005400c01440c80501081c554003002002503003106102c4084107848001c0c0304012200c040850b900401c0c01d281003801d86d89410b034001d00c10400c02406441003c1d036004c460a0844041c10040d405003180170606000740b40d030501c60240c500d0b00101c0c4035464101c0c0380e01c400703006000510070b0032071060b00c4180e1180e0750441902544c00f000409040c0d00d04454116000c40c0d00d80070301141c0072000038900c510000c3c2a1a9011080c100081c01a02a1050512070746440541080040c130710140ea01c4200501c24503500c0410521403101d80c0350740c0c001040f1101003081e0081841035440b00d0304c99401844814000810803044580c24826401d10608181140c600181400c2a8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 226210386 1250 226209136 226209143
    0x1222020d050a170c060412020f07032006030f0406020904090c09020c0d09050105090603101a030708010501020a0b0601111e01020c0118080712032a0f09030201020c0d0f 74
    0x10440d20808010740080c6100c0c00718803070040c8450b07001c2040720481142c09844100140c99001d000401c000c1002805020513840c020b00c161681e1415075102c803880c2c030034550b10858410048160074000c44440d9207001540303840031920303149503080020084840c1c141c050000303806c4075400140c9407442e58641e445891400d920003941720380240c0d12007080c0000d410804400b291401011314000450b8400c0c2c0f84c400984005031140c5050000c22000e204440d04000d09003218110801030104800c4002c60b1440f05009101074816560300e41043c0c001d0100c034040c0e0200381554010103242000609804915900000c03c1c82d01845080385038010724600040e041038200300281c81c09110503034040640042510000580082c0202d620032b03800c1d4099550b202d800a09903030000e02402001440180c0180d04140e51840c011901c8140d80b103000e400394460f2400158060740e4400c1c2e2091950300101d854202182600b80556007038a5600080e440722503030341101d40b00341c10041800c0200b02130701d400803440030340 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 226211636 1250 226210386 226210399
    0x309030d1106060f0603070c060e060a02040602101e0b010215090601050126070e01020f01110a090b0310060e030111040305070e0105060703140918041101030e03122202 74
    0x440e00040d0403440500c1031040039000d4940096150700701007000038004440940398902e1a92069011101222994070071070b855503d603020b0407402c0904100c0580115000307400141d4071850444042c0c81c02d9191a034000305030341050b51400ca80d1410f14949910300201c4030001c40e81c4608a0300403810808920015100d5806a2051000c40140000c0c1e1505075042a00c40c10601c00700307001d10703084143d095911840c00400305400500032030f115000d60900c44d08180101d9558640404c541e500307446421210b0140b080001c12904c00b00c0f5407100c20f09004054840c00c3e9483e40c204008074010300c1905010f00d0080c00403480c0101c50f2922f0961100c060b505003403e09a441d140c80346010b0b0746401562240c00f54011401001041910f0010304840780158076803965400c100e0100ea4918664004490050340701000800c0c0704450000d000d8000d1003188501c8c10040c0c0d600c02840050100c40741d050480107260320a0001c0042d500c50900c04c15003016400c0811042140004004040c43c0a12840290480b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 226212886 1250 226211636 226211653
    0x150906050a03060b1209100e12070314030a050a11090f0f06040906080601030c05030105090304090507050d0903120c09080a0206070804050303120f0a0c08070c0c030c06020706090b0306060318030903 87
    0x2ea01d072403d42c0c0281140300c2502c0000300040210419181222340c0d03000f8540025201d000910000f0005068052180c01d007410a551046901004c6400c200c41001d13146868004120050000c0c0c8140000d030416483c2640c2801c804401150400000e051030600031030f002800c1300c0107a0b43e45001d4400070304401c0340500c5000e031a20580c0343c40321401e2004032101c0445d004040344500d01801824480c0260354019030a05182c5a0014044d11000d80702d082071040400864402a04901507455094001d455075010b800d0140421000c580101011408200445000b07200045000c11a04c05103901241c2040d00c40001d030410301c5e660f10650341f080750301d8030000402623005681041e109114810b900301d0310a0503034170041840107403141c0842070f0f4001410900010600e6000d801d1110400b030050905002a64681d074500c1c10240c071a070007590141e07200103410043d90394440c03a108054400413803c02e0850030300c0c8000c14ae080c00040c4c80040d000709149444102040108143d03103d00a005048843e500d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 226214136 1250 226212886 226212907
    0x3021f06050906040203040f1205040b0d0c020c0a0803030c0f09191a0309060f1f060216050409150e10060e04150903020c0f010302070b01081006150906050a03060b 72
    0x400345845094010400d840c0001e2191401c1d02c00d4900c034039080460705e0b0b2031608594800c049281e400e0960014001c0620000c141500f092024108003110540300140c055020400645805003006429120b5402c00009200141c404419683c000803d4842e051b101c820328030344d818041c0036140083d0b0b000442c9541c0101c0702ca00400441040b60b455024036100d40880c884400618882102d4900c01da500560201c1c0300d0003651a0550360218291003070b1103400c08980032b01040ba5005900c00030060740071080c60104050b10208040042900301c80070401c802c070995656140000580c0c1c8040030365039800003020714120070712102c2c8004480c0e00c0100000d42e02d0f4071801c01441003e60302070740c0780d03621000081e952402e2841208000d41e00b68005011250768001000581d03542008420304160b02484244002101258014080c1c0001000380c501d00070380c2104003040f5151a0f002d0f2004600903007401652640001c100020360340c07a840e04c3c0740c0d502c0380303113001364060201c0b9809503d80200005104200 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 226215386 1250 226214136 226214141
    0x1e0c06070f0206012321072610050601021e03120a0c1e03020f042423090301020403150b0a0905010605180f0303040315060f0e0a0903021f 61
    0x188030640300c664403500d10714030490f80c0b0b4000340a00301c4100e54028410a01e1020030304001c100000092182c000848103030312030550b10540c1c25408040b82c1c03041006112843e50920b10b0040100503600854480b401485081d660f48040b03685100515a102b0120344c05074400d005801210408203a41c0c070603541c0608150703580341e002d070100c00d60185000000c11041c828a004410008910781c0e20300390340045036034039045c00d051142d02d4002416402c008020f500003c24000c0d0008000700d000b018015407054030202c10800420714007000f0009244101c509030440349055441e0444450505901c8102440109009200e0340e0400791400300b06405440d281c0c3c4040e00321020080050b9462031416990b0034686007920001e004542c0411400d020080c10300b051010410300713031480100302004020408011a003107511a41040c2c40700c2c8504055500c01340c44a014840c010300c403100080313036100c0c5400310592000001900081080361100085021303d031080080c2e050f0000103101124608080f0b4960600 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 226216636 1250 226215386 226215391
    0x10050316030c0b0a0c03030216060c090810020301210302010b0a0311122e0603060203010308131a0406030c0e0414090f03041802070321060906080109171e0c06 70
    0x2d20380d150020204807021440160b8080c00280d0325a0001290203550a41c082c0d0002c01c1030340e01041d40c0d040d5040100e2018015040c1d150200c1d211128428146030034a4206500c0307105124445004200420504a4080072140d41a070041881001021603203401c9024022648086900020105e0044144008901c041c00c000f00111001360219070076a101f0b5489124210010005030324000c5200300340000034502e00e84400040d100080c54a8580e940c1004030b0308217800a0352008004500c4841d41c420000300140500240c000b5440c02400107101580d241c41280581da0800d52607119400420380604840785802d000100f040c405540005c51401460074101c0c3c1801d030030b01c11102242e0039014080200c4090380c0301710b503111101c4d826a400e00000780d480184110100400d4602202c08080112200c1d0f10541d0040b201040c43c528218000c030031b581640d00802e070682d240c0380c00100003a00c291550003440d41409405501c0d5544100d0212008040180c990504880051140552840841d1061 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 226217886 1250 226216636 226216643
    0x20a02120309010f23040308061503090f07050a0b0901050a05041206140610091406040f2403020c060604051506070b0a0501060908031b01181b090b0a09051005031603 73
    0x800c0039031403181c1440c0c10030380882da081c0d000003120106d80428418040c00b6805100548102032070740d00d07043c118002d42c0c421515151284c02080741e80d85196800d1041c00000e2508a805500e16803c11f0102800752144480d032606002d40001c0c820081e038050004c1e28001c20120041c0103111402c2e0800d2005065020f8082510107440700020307010745040c003116002c0170a50f80e190400c072400c2503207605d03c00403103c1c06251b00031401d000004240291040410250038901c0740742d16503200e07080c0c202c107825582960000c1031600502280ea0010000500103038042c6084034046030701e403070b1022441e034100100b22545405c01c4002410105000410318294061102c54204205c0d03a030740c64008036401e40d1140504001c98008100004104240845034520780851a0000075480746087c0800e07904110504225003065400054228000400e021100203140f030241c10f1011608650005a0b00c01460240141640c0d40e00041419403585200110281401401702d4500a5540d44120108440d41c4400c6 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 226219136 1250 226217886 226217891
    0x6010216180506060414060c0102190c0b01060305010608071d090a020a090b09030c120f07060c0302060711030d0e01020712090e070c0809041815050108010f0603020d0204020a02120309010f 83
    0x46150400720708440449001d003036104004c2102e2410054541d000c0303c40011150740070b01100d0303155501806010003a207418cc80316a0703080c180703141508910105a100070181403602c00100a03035600200c0a640c00701c40c51074101041903c078285145140003005c40940c0201890080094141041d801003801e100305031240001e00c0e0f44c40100f501140302c0c0503080350701a00410148182c5040614124041004020540321903114004d442440c1c42c41300c2c2d0150f030000c2c0034149500d0915806021300394010001d4948185000c8920340e50700e41d248140c140c1040e18907911003c454040c4020b505a17001140c2c05085401c40300b1360300600920f050311034040c0a000031684408070700014051f2610900e13135a40f0814190411780503504100080521030001c100c03802c3c60049620001d102845c00410b40c040608001403903504103803085007120b21190f1003036500c40c0f51120032f20150ba079001c1401045a41282c0242c0c0d220310407002207090880c0c0e00002030300d03207901200f80110014103421070f000390292480f04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 226220386 1250 226219136 226219141
    0x1e01081f15030605040c1205060f0708091b0103020c061005040c05030103200d0209040f03080a0c090b0a031503030504030213050f060d030504050612010306060b0304021305060102161805 82
    0x3a0021120788100750001800e0000302000040c00e01d40000f580a4001c100c002044e660f2042e4080030319a00c0c0b0001c42d001d403c0031080001505c403140c00c568100515103004c5415141c082c0e003140e950580c0407180c422500c016142c010380c9a20a8046a407844031400c203844041c100081011401e070524059244101d041030040d080162065040c0e904076600102c0d41185d0b441d03180c0d100d007001500310380000d420102451582000da1950003c02d80030722710501c0340c62400055070030014440da60141c0111025804c051940c1c080a070b0245546060f51045802a552a085004150700415103038100010a9102560020038150450090000c032802600c804611444100c0444100c50040314400c445034a10804908141003070800781414074401e003410f0b481c040d2500002012500112902850460494018410000917010b1840185203481400c0e003142403076400038001c84206414030822941d6100000c9650303200b048100b0114600e551144082500d80280d0319a40350511003204140781000702 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 226221636 1250 226220386 226220443
    0xd02060108070e06033d090c120503040611100504050a060b0910060806040f0c08040b090d08150112021303060b060c030702271303230406030e07090e0303040209070e03030706051e0108 81
    0x64040d90784ae440381c051441d183c102901070700d0002884961121070b2144242001034240c49100352070085004100804000c10300b80350640030b5405140b4018003d40640080c80100100360801d5802d840e01410889515655070004c0307002840d2690071440d1140c241400000c18a0300700b0303000c60080740140401012541c0300213441d40e81e400c80ca11703003d0005202078000742c2240c10488001c8150a0145001102e400c8041d001101b660441050310500081c000010010401640314000c200d4005a81da981011540c4008644a01904202038007602c0895907250624085001c06a09005045114510360134080c2000210235400e10080f07012959602485030b020413840c1e507080040c2c0414003a585002d042a808034054910040c5600b61441503c1000c58011034a003e07a002801080d8011078403490240100028820060002c0302030010000c0e40009a44011044800807504513401280b40d85801890074541481c92a031001c2e42d0004e600049002c83c00480c0d10712000e0142c2c4e41c8030300540d12515 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 226222886 1250 226221636 226221659
    0xc1602030634081501030207171c05040b040611040b0d020a0e040504050d1d060d0911090c034c08070b04260d02060108070e06033d090c 60
    0x900b0000070500c850000341040d01481c121610f1544180b40160903c045582d600c010202c50b241d5030a00f5a03808900d0340b400f812843c40d405444a6180000d00690038542c485044441020384040d103640d459020005041d280070b82200c00030b1200700312145c2e03aa071505410354000d4100074148030021316010b1030b02520303103414010207009603044030252a000340301d00d5055415100c0b221086040511400e03000403642d80346e00240c4003102c00c40f40045014040341c507152901124900220344100034040902c045803050350143c0742d2011514104c040c40c0c46c1d0b400e00300e94500b40214603141540480c0750310100d24100010a2140c07680e44039801d00c038181d481d420040e8a8000ca806441c111003410f2008100c03900d14019808059015000083c00f030ba00e41600c03150402401940b00f90140e031010300104407840003080240003c04104400e0300050402c44000b0381c0f5030104410a0310f000180010740350040b0504085c3d07126034148441c4c101003030140040030701c01400c2c200c401070702c0d10f001c1900b0000d07081c484035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 226224136 1250 226222886 226222981
    0x80d05060a05010e01080a0e0a0317090706050409090f0c140918030a03020915030702150f060a060507230d021c02070509100503060c0301050f0a0803030c16020306 72
    0x50319414000e600b130400450790500018042d4003003d0f1529103200c0460002d02c5820b1005000e60384080c00e107200070341c0f0b60409031009840c0c60741c20b0b8424002080070302d40c0f14080e1010b55004400128003040782c0d00380034200342c1140358060940e10100000017003405030024034105c1200c01307503020001c40e510301d04cae410700000030010307480c6003900b00f0040382c8511446a40207111202000300b451041118040b200e80740703500115042d0303000da0b0003c800d00c1ca4481a0301e0005038031070340103405005030389041000300e600c8500501c00e80d01842000300e549010050014802741e40c1044005091701d684101c0b50260f582c03101548203c0003d805003001c0c03030750a007043c1c8284100e01103031600100310461600007400b00300b00d40100300350403c6110600105e61603405000c11030150b2000c10780192254113060400091100c2e10042034410700000c2070800c41c03a6004419242c0c0400c9038142d00d030310f900343d0285c55500f514045034002d60600071181003044c20f00540d0303e14008910214400100c07680310640040b480707500ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 226225386 1250 226224136 226224139
    0xb0105040501050c0a06020a08071e0c02040e0331050609090c0c030d0f0c09050f0d1209030f060509010501050901080c0d0201050705010504050a03020f0307080d0f06050d080d05060a05 81
    0x4010601c1a5402000141442c60404046507200e42654903010300f00d800c49004031000a400a090260541c4c1c8210040d10380c07850100041c1141c3d080c0c450150500411030350080c01141c9680030642c090205200303958010030500e4291214000188070300f80880b8441084280c0440e042e40003162500300319017a9040c03488050012011911929050401a04183c1200350944000c2009078250301440c0121029034013121808609242d9202c03000c0d00c3d6540c160030080c040c1c103200d000760a4954130514030481c60f50300f00403400450020a01c080b00c0541d9103400c060145040c02c6815001c00030a0b6028038880c20039400204003a076210070411118840a200d143c2030341d484a2440131b038501d070070003540602c1441410300034039001841c5e50f92801d4900846083d2255007101e00c0d95400c1c560103100b0724031030f48100c0e0051441d000c0c0a40e1165001c0c002d010340c102845075a1a403515020303c4950154028040081074203e910060f07290403d0350790f01403e140c070401c40c180703400300f40103091041c4500240c030300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 226226636 1250 226225386 226225397
    0x106050603130f1205070203011103040201020a030807030e0f03041403010b0a090f060509190c11070e10031a0901060501020106050d020607030306091a031510030b041a070905030f010b01 82
    0x81d4200001410b02d035050003955100341d100150000200c2030303042c844d8510503d4840039162203850040608462100ca81458174207010020040141c0c2e01250380d02c042c83c0c1c90700300b01407a5281ca040490040600c00840e0405102c0c1d8280034980c3e110010141c03040351f00302101302024210020906081e201d5500207550800a40071050100c509250002642c504022000240103596900040d440e68001e40d2044c0214021400070500922a400382d110000340c9801d0900400b500c01604681d15511441465081400140465040c0f202d02e914080119000702020008400d2440d942944580c1521421455842d103c80003c8950042c0504002c4030001000e040600f4816003d21a003640902070840070135070388240105482c40103116810b4048080c902d40729045c4540c000381840d2180e88a242d134060791426041004418490240500f40e0f0750141c0359041d291035901d040074068003030050b014011040e0404115840340c2c0541039100f26a0100c0032221b01e0500d01034120300b01c03030010310a50b00050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 226227886 1250 226226636 226226641
    0x3080705160b1c0605010503042004023705090f120102071101110a02060d0f02160c0510110601030602070f06020c06072706200a110405011d0f0a060504090c05030f0106050603 77
    0x160b4011041410746004c50725600001c00c01d41c00200cc0b688039040602000c041550001e0b10300c0090102d24500091001d01100010b0407203401800e2806180c004910030000c44400c0603103903c8084088017103c5514000355294502c41c0340c86c007c0701d070340c403442103000a5400c0105031260f000003d003c4d0a027500904000d24054111391804090030411401c800350a4081054882c510351199400544034060301e0740d07140079030070175040007484058070000b403041087c0d010646140c4800400d0b06070450f507100100598030071452400b8070074910721040150040c1d1001c00c040c0e076620b50106000d40328055655a007980601c0046440140b1a40c100c0c02d00d00ca04040c2e130050080c680a15444103c0d42100401c03a4005205080d20034542556401c2c1203410031f00302d000400041c207081c0030b03290140c164115644118491881c069020000c002d20550f89074454401080c405151a80454060a400740c07041c4441c80300340c21302c81d101c00940d1040e10701900c54520000341d40b1340c040c444c1d1030a807840200451b1464 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 226229136 1250 226227886 226227893
    0x17030708040b06120610150c0201090b090a050901180f0e0a030c021201020706021206010509181e0108030306190609030b0c1b0d032403080705160b1c060501050304 72
    0x14000900c0b082e00004030480c0c1402c480740400017648103404444a08080f00e080602d0105503040d0310118a00384440c0300782d0840181e03042685001501d03017000455403664200000681d48003091b0b400640c001c00040300100d04101444076142c00c2c00006142480070000480d402000c0740d0758480c80521917048a18a400021320452200001c0c60004140c001c4c840f143c1489242241d03c0b1100407a1050344c005142081c0808101038250700a000f400c240d424101c810002c500b8070386d487c00c8200c00c5000e10000040055400880c010482c14803040603280035030711032070f0040d13807030b801984e40c00c0c40b88288101c082e012840c85040b00013030f608903540b50700b0000d107183e503910071003e4043d02642030170301c003030003040d0184c14090602880140d80e0001840300480d408009001c651b0301600a18000044804c11240f010401a81c0c0c01100c1e400000b20381d6640003400d000381499860489000c00c80e040110020f183d006480217070200d000c41c00c40303000342440c3ca1100601141d10ba071154a0101c0c40600c00103020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 226230386 1250 226229136 226229153
    0x30304030e130b09090703110306060a0b1617030103030305060f060d02090d02120703020a122001050d0608010c03060b03090d0c08120403080a0f3305030313031703070804 75
    0x10b042410110b00320707280800003661000c0c204c65040031580003031010030911600300504000d54505401800c2c2c01e06108001c00c1422100e40607070b1801c03c00002d110b004100c00080724251070313900200103c013810401250b54529500c04e110680000c0d080c070010601d00c0c942544605030920300185003e203071504c442c0c40d9101039000b00c0100340d1b2107036a4210040c00b40c2c40e0b14024110303540c030368005402540d0851040019402094012220f0900c0300341140700010780100605d24407008484801d03400c0082e02004032118450100c0c003100780f40c1043c00c000707014941500040035004854034140b1601c2c0e1580038030b05d0140012a03000010b0707444004403412442c0a00c1f05100c0090207058500c1c40d02c0c00e8480c41300c00e00c12041d1011400207400408001112070740303201d9594142100401130040d01e03040a030300c0380c2d1503400a007000200802c9080b02030302011282c900340004d02024050301d40b00c80a849442400801610083c0c4110030031420a4007581080303021a032040203543c941d040291038076101c1400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 226231636 1250 226230386 226230409
    0x21c05030a060e0907091a15070605160215040f06020d0c030e03120406020a110312060906010c030e0111030c01060b25030c0803041b0b090a060219021e09040f14030304030e 76
    0x4030787c410380849034613000341085416641c201000c1c1c0c3d540071442c251301259001003009002c0d44483d1448030030554007182007841100c0c4500c0c808426181d034104200c2c0f200450900611807440000d40029034181a0030400c543c410944041004801c0c03407000c81e4880c4200c0070304c0c2d41c01d212160001000118154041c0c016540145003483d80d810040720540e145920151040d064910942c0030025a803801c01d4100e44d0105007841d190a81d51119030f400380080d519004414144400c82003c024200f40402c10b50341c07414140070027403120950b80c0294084c1507100780c0090301c040308600c203198000000801d0752850264556950048c81d4031989803500940c0003c0c1c0300701c400705d000d02c13a1540e072075100e6185000504003000a55640d800d40c1400c0103000d920642c044804c0d50480018804400c103810182d180d025015103140500c81d10455900f5500461070700304561080c4c4502c2400705001042c401625058491b0502880b00910350054136075900040310010000317440d070302c200c2e545420041162030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 226232886 1250 226231636 226231661
    0x303011a0d0b0a030f0c29031302030616080c0705031b01090803010f0e06040e0318030f0d091508060a03031103090d030e033a021c05030a060e090709 66
    0x40e905441400100300550982c0142c07000304081041d60b05015802055070010403c42c08692051060306201c60408103401040110707d11f0040005410240110f000b02c0006038010240e440900e46106105070060400d603041000480c07440000317440446000c01c582c4041d81100066042040703043c048910782c54459403000841d502c0d8009840025040006180a88100c0400c0703100d130350600380c2445030a9401170405208a060036400c0c00550340110448815443ea1414002c0759007041c40030a00d440c0440c01810481d1044042c0302c000298403142030420740d40690900d40074000414030480310280d050b608685c1c442c1072403504000081c0610884d04078000c00b01c003a41d0901100a0000d400300c040140c00341c0c08912854500d85007840c041c01300450000c1ca03c04401e1290170a4131103084800c0c0480e16003914141c051405655045c0200f10031950030300c1c0040300503036120740d02c1c1c1c0040441d082a110201218100800411800012038400c0d20800340c000080031402c1c42c01984c2c401501d01e003003000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 226234136 1250 226232886 226232891
    0xf0209030316051903050d0f0218061303021201050106110a2a03080a0903020415031106130515090f041b031104050a08010e1203010b03152209140303011a0d 69
    0x4d00303102e01d40d414074000e41b111034079040980071034001d07210500b003e41c144c140304001045070b0782c901000f001d075000030968201e905c3d1150015071151030411900003030340c41180c0048200c030100c13054100c1e5058910503130700d03480c0031044c0d003000c1030759106c03d058000d050f030340d101581d2140c03102c2c1c40100c0c04504c10054119070344603560703407140401d41d80b0030206000050201e5009000b5030406000300500d80c400c20580030030292443e101c80c0744e40c10500c020305104072000250325801e01c0d0002e031300f080030f080300800d030360350301c0318051641c014a0740403180320f901a2220352400c964501d42417090300b20000081c428000e03189103820b000c4004120550058034038400c144408142038440c4440a40074181140000810380e4800d03031254580380000d4640c29203035108000501002030301d00c041c0c07500000700c45020896080d40c0346c0010096003070482c100710f14842c008444448080c0680005c2582d501402204c1c07402c6468603c01c0d9120300c0300b4042c4030000041541d0351042101844c00030b05c08501d0a5500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 226235386 1250 226234136 226234153
    0x1090f111c03081f140a0b0307050d09020307080609210f09010e04090b01080f07080316021302070605070503040b070201090305090f0d0b0705040807060905010906082d01090f020903031605 83
    0x419500655070841180750020760171040c19824031801c0d80015141031450641585080c080c02044c600c83c005041d1000350302c40c0800021034400304203040c0a80601000da0318581782c41c0304681e90311010403003801012400e000800e0b00500301442111903103484000b04501d0b200d41e900064580386034509803660001d0381c03280401d000c00c090804250181a192014260480c0c450040714500034064002c0c10442c1c101f00060308240030b401204000790342d8141c65101d070400300e20341c00780c00074024188007824040c18207003040002540000110f2040f0300c6403030b00d0f030401d848907803080b4201c5d444450000c0101d44204001c03a01c84ca130680001c000400c005121180350440342c1d854840d040001c0d070b8184082007000c10144440b590a006541c094000b078a070000c1607501e018002001000c3da44160424072010f007000c41c1c0b030300c4001e10016801e01c40d418030703080301c0882d500601c5640060074415060301c0c0d45400640c0f9480e110500840f10b100100400450806402c4402003508000c800390444030392080d44d10 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 226236636 1250 226235386 226235431
    0x6091506030e0d0e122b030203090c0d020a08010c050a0f0201051003110613080c090601110d0302072d0c0501050901051911060c040305190b0a0c030e01090f111c0308 73
    0xc1340001b1a0014406204a80000c1484c15407542980250040c1030041c41040040b0000040e01e5012207411148079041e60228000b00d00d4a4403103401a1160b9401d040010050603080f00060030341102907030300c48545011080e4200e00704c03081520000120101c4910810115075000d09148424200900e610b00d03010761072003443c0702c202ca641d1003a4010303004100507250038541640c0d03099201c04d0a0070081c0094954103619500d403880800701ca1309140d4003140c41030a000d05da0038901c4020302d01c10103a00c0c1c03040030b00b64002c43c100688a003c4074800c50340b410109995218805503140c808045e1150340c102090030340c6900d8510301240c243d0082161210401c0d126001c100b01040c00750048208a95039241141810f41c14402d14021900c03085003080302c03040008002d0030940764449603655000464000102085018000440484400350b00704520041803000c061095580380c0e12414031061124200c0092200b500700340614442400704507141d41c00803a00980d025a4020709864150504020540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 226237886 1250 226236636 226236643
    0x11202040e01051207050d031b0b0106110729090f041d0106090624090b0c0f0615030d0804030507020a030f11030a210c0606091506030e0d0e12 63
    0x740314407600000d01c4010003181c18495810075501506101410300c0350304140110780080401d81004040040031f441c1c40380c0990b1030341d80c4407052a5100c01400300650351264000d1548841c180061041c4c00f0384d0400107a2a81c0c0207410036840ca81101800c0201020300110510341d40007100340301c1d0030602c0440c41c0d080740e58583c420040071080e00064140d0035140e150080e403c444642c2c2004070120715140c41030107619840c003a80c50700b45a0318200d0f00390510503a241151070340c1a030b900054010070701003103019000c6404600760358110f609204940240e60b6192803a00070b0005000c0c081c4d010307004989161095880b40d40010340c001d009090461411441c2d50100d0031002d090b43c130640e0305031810000101046080c0400b20800c0744114000c088541840d114420740100540380d0110650481c018080c42c24001c1911041e03494111104000d45561a846040a040c601100036101542c50b200480d23154042c1c482d450700041594010540c540c51148182c1c3e4841443c0d501c0755010f000000d030000f44040c01c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 226239136 1250 226237886 226237889
    0xf1201050a0603051b0a05041e0603080a0201180c050105250305070b0c07230709051501110d0c060b010c050109110a09060b030a0207080c0d0207031a04080a0e01120204 74
    0x100008003507281d400d005041ca44c1100300c070035611802d101c0c0d22900d96505200f0101fa68400c03980003990f00049548000c01010003071208003801d003488000400e200e1006c02504106000360000e01c108610701101c2c000c0c0c815841402013268581810a1103994411406401021807042c901da155090825100c920103010107812000128000390305010024485080e0341c000f445006510b04002181c3c1d2001ca06800c1c008400c50780643c00c02080c4603400042201000a02d10341e503040010742041d5596980500700b01c00810f0102c1c1c0003903210f00030783e500041c0200b1700c0211a030f038101c0711540b2035440d0400740800c01d4040703042040036841c0320007180d401e10501045a00c1014025a400c0c2110244a40300d0015031108882d06c0c5000300800074401d0349d004995110352083d5005036108440c3c07400512600441c00003500c0c9116040d544030406030001240301c140da00a618085138401c4800b0305103400039045400511031a018070000d00c12900a2034003118603d81410940c031010b40071200d03102241c202c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 226240386 1250 226239136 226239151
    0x1206020d020408070f030c091812140f0405090c03010513020a1e0f020d020d021005130b16030e0c210c102d020a020108070306050303030727030b01050f120105 70
    0x1800c00130804440c090380300408e5598014404091013040102080c030700c1e10009000c01c60b0700d1898080c0240f080803880d428403000f4100a803118903412110319141c1040c0500350045003404049010881d24106803070480c0c2d0b009010014070000300781114080c0d00401100720902034605203800400e0f2480c00e8591a00c40207940f01140850103000080c40c0c403460f00450000c0d5080706425507892607001c03490081d00d811340c84020031300342c695040142c00e0414060b0060404a149424004a6480c102c20003101101c681c1e824802000300383c3d801600c403c0303120f0140d680920b000e2030310100d840c0e40c40010428940380f8030541d01c44e001140c0104203c040c1205256000891041a01a1513054410f0040200b0b852180e03030b6a002d043c51902965601f1111006418070a040000402051107600014050031014003030740d880f424185005407410f13501e48159000e411159414480380c04413140514126900002c0815040e46000140000c00c3c110300b0980b5007184904c100d0074480070023400365a0040c0320 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 226241636 1250 226240386 226240409
    0x219020303220b041206140f0718080a051c0f09050906130f20040506040b030c070507060305070f170c0d27030f140d0c090e04060b0a0504061206020d02040807 70
    0x22545004012585441e5035076480003e40030030700000f06248c100c1542d1041c2c2c103041c00c1115034003169801e13102c60080e9008030014400c94850310104100400e01410b02d207107190320011500b004041c1039444a9040d213401000500e43c10040103140790403000c60307401010107060005006500d411100c160380c10b45001d07001071b03034035942d80e8020344440e460414241d10070140c1d420300b03090600c4000b0f06148502d10a0480c0c80070041f0202d000200e0000c12503154650050440d0316503552820080c0140c80200c3e4098081803005088840c3c00d4040c2c0168200c0e885c1c2010741060b55902c0003604240c681061201821455440a0f45105104000c0101d6400c0312810000311100d0202c0ca00100036203188407400e400c0160311500010b008003c8020b81705400390750325000c12304100041c0c1c121a910055401500486038400600c800d1040702c0d848003503030f40d9041e2101a02c1d25151418401031760440d01c5040e010342010740711035000c210180d0290181460713803480540740903600c0e00070600d0803d444e04010900b08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 226242886 1250 226241636 226241669
    0x20c0d03090506012306030402040b031005040b0a060303050d09050c061b01060504111e1318051008030715110c10180b01060509030703080f0405010219020303220b04 73
    0x801086a240100b041d54405d0ba40000e4030a0140c01303903030304501480d000d280040701103801c641d0745800c4800f040c0405001c072280b14150045200c040c0c1000e0f582a141280c0c004003080c200c0c0c0c03043c02800c0c156074041d241c1034a0140807540d01d0008080c0501c040c0d40501441c040030300c066803100014041101608101c81c4841d140e03009003400c4480b5039000328411407400c0c070600c54a0158205a42c011481d91000c1d404417040041c421405224200040b18010503488010031102c104c50104440700e415803030b080205642e40c3d2000c0202800c64024175003980e200303100003000101c03482920407c2e48508080854407032415802c070642904a20f18510140e0403000300d4481c1d000651290b040070410106880b014402e0948511981981c18000c0d501040f500042903280c1d41c808105000046d1b5000a600e56281180c1d40c0c2514160441d001e0030340140a555090340903003041c900400c0c80c55800402862400c03002c150758100d41090025080c1c1c080012070000909100064080c0004200d684d04003d40d40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 226244136 1250 226242886 226242893
    0x304090b0117060a030f0609080d061508010503060a0c0c080f04060810050904080c010b1002160812031302010c080d062408041101020a0209100305120a0e0d06020c0d0309 75
    0x9180710000505808220b40030400d20303560300d50301301040707a802606601c0d92030b0807030400030701510303141d0f0010b40528000141c1039070005140c2d004030211600c240034441c501910b40030441d42e200e0280303d05a40740d8040750205070380350b440350700211f0003240900701001d1540c6503541301d800540040d200400d45020100d400c00a0381d030407100035a070003035540c809000c45900b02000a0001c803805403020f482c0302d4011405900c944c0c400d40c8580c0e07500c08010401700070306c110548000d6840380f03050b0081c0208082d0710030008080100060000458a04e00101400c1d55907404081c131044504110030313410003034501c00e80d9000c200300800a1800002d0702201003030322810010081c14000740c2101140e01c60300039980030f82c0181c2e03003c0c1e8440e4101c1d911042000700c803486003004030319021240d030300039510501410510908195500141c400c580c0314400381ea0f001c803030b940791b0190705000711a2500046a460740030340400386850144807260300c0c0b00390801401c0c16230900300503180035282c1c100940842c1c0d0710540d20003030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 226245386 1250 226244136 226244147
    0x1803052505030619020d0209040207060f0c0c051903020a0f030f080709030503030718080102040b0702030c030309010215040c0b0a05090102070e090d260c07060b100512070e030304090b01 82
    0x1034807081e00107004030f041c114020209001e2420300307070300140e5011950100c00107213038049170303644a07000300b0035511540e241c20914014100030100748041842e02c0310a9107694022810040610341040140211015010406183c1d8040b2242201103015500d080070020340445103020f00580603a861203406c04030080003420010000e08000d00740450400208009000002100d0344104240350050400000302e82254404491380c000c001254004100407640a14100103015040d008504907115440d00d642815100d02c0381050550042c0c02820202c5840e4003080f40d0719410520401124001c60741d1140054401c0d004840c9260025900192030034042d0303810070008001d0080e2641c01d00e5681007a060099807510003140740b500384441c0c820188080000f140d8102c101000641d040440c610b0400042e00c101d074007a643c2103c4942c6000e40c00030717060410081e812014013860f118245020345604031a0032003100100410100b082c01c6000c0d9206450500140005004040303001c22500340c124000343c00d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 226246636 1250 226245386 226245389
    0xf12070e0a0b04091a040f020a0314010e062107090603021807080a110c030a050a08090a15022809081b03060c09030316080409060611060718030525 65
    0x1c074500341c840c10311192404100b11400c4541c513480000f14801d810110080d1800e88200282e4042c0c075007030442d8400b10207900109004034803a41c0c1041070301e041d00c0c400e00e0107103828061403184c0344100f80003c02604040030a4000e0302c00403500b811400c002c40704002e142101c05d801554055444d0003080086080c07100d02c043c0704c1c0c10b1142d1801c03040c0c60480e00c001c0040700000d0140f004a0b40710100708800724180f20441d0947c49842054960342c90340f800000d0942e40c045a1030b840001c202c503001807188a0701080081440f0341c005030181b503402d540c140c204043d400250f0801101a50702d4142c0d89404905600d0403a810b04075280d080307881d0325010380b0b1428003085158003c40f150444505010341e40d4041484d55100c4140301c21a43c80341ca401001c00d103980108156140340e0314001107000f09021b91813014008943ca10316040c80400d880b10003c50b121f0000325403a01d400c1d803203000400c0119002e0100501e41409000718030300c0969403520b03442d15040e46510a8018808043c4046040001c1d0100713040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 226247886 1250 226246636 226246639
    0x902032e1a0a08070f05090402070813050a03030c02041a060a0215060f031c0903080c0102031909150b0f0604090219140a0804050312010305011a011803170f12070e 72
    0x7410812000310260403220001c001354200000c3c0b207501142140280241d40ca030b150003400441d103518040c6030400d0b113a801000b442c40b02000c507001c005082d161108035801500d5266071110384885069081c031020707280308100241d800d01c1c070988041c02c549821000d082c0354005540105580313001ca051001540102800250081448442d0070b0110780f00003580b001d40e01c1d000e1941d41c6100c005c1c040c08840c40a0345400042022070009140800240305402a500924001036440a80d50503808500704036282c0030710042c52050407903e042000c40f5160300600400c2030203003841541140c0c5400081c3d081c0c3c00340e0800b07aa0b4030390203d200b80500010020028507050316090100315460000c443d00f465004014042003086041d200041c2006801d0003035480004850321101555612403a009010342440c0b07038418081844000000190743c4602e030707110246c81212640e030030705508544034105013654803080b00054900802c201c04d40440100f0052803500f28541c003809250600300001407060030003400702c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 226249136 1250 226247886 226247939
    0x7200109080c150f030702160510090b07110307090603110405070203071506030f08040504050a0c09050d02030120120901050106050d0207060914030d0f050108070902032e 75
    0x7841103410004a00c0314030359007112a80c0c1d10144202c6402c2e8544918011100d00d10b5000c4240001c0c141c00281021180b0b01121401090035264814802d0b0761310004912800142004404c0044018260042954500548140310710030242000300380f911040d07910805074035959000403c00d00858030341011003014122004e20581c101004001d40d280241400a4a0245004070b044032134a45540300d41c009561140d81ca4422440d0340c02c0400007900207114030350240e81408002180b00c003082c0b144980000385502c51002242c1050144800e41703424500c100d8141d07694101d08400300a820f04108040b80f04903403401d554407801c1130414903110002d0b04492290b0704280051011940260640300c2104d03892600507243e0308541807074000f502001001505107110034080a25601c800300c010800100300c1d0400b4001d07007040c500100d0480f20700b44141d482d15000b00c0002d20104072160000e42d04600602055056440c903540d40081c0b8645400c05048520a803000400218022141c1040c41d1001441d14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 226250386 1250 226249136 226249139
    0x319050708010608010e030d0b01050d1a151e0a020124030303060819030507060b060d05040308100b0904050a0b060a030207110a0b220816210c030305090a0b07200109 73
    0x105d9030750b8005c031003030340c00d0049c6c4820b002c1102da4402d00680d00038001c41d1000344001141c101940b03ea905040035281e000d05810409201241421340031205000008041c80c004030078a5480c4030455005079200c1d40c1195202c1c950101350185030f40c818101111220341d1000300d02d2070340c135002d8212201644102d0882d0402c6c1d28100030b000b006442030645942508204d07551b91a80e00c1c003440217080c007818140e4070040c0412624800e02d400d0307201a128034802e8581c1c40e0175455070083e036011518180f08100e2807803400c00545500e03080c550005a00180c1074070700840d201c0b500c1c40018020781c000c03141120020f03602054000c00c0c400c49506007802024141c81c110150f0341014070140180c49404c0116101150040703940d003c0d40342d46229540101052001c4d0360321070070b0080407007200b17040511401c403814a031000c036480040c10000305900c805901c907204450051440d40c0a490075041f1841c010b07401301c1c6c1701e400015440c00100060006510441039501c1055650341130074103c0a100ca946410000183d00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 226251636 1250 226250386 226250411
    0x60f0a0b030a24120b01050402030c0d0207110301090f0c0b090a030807021201061d0114062208120c19080d090206070213021201140907030506031905070801060801 72
    0x407240c22400c03811021400ba11801a10700d5a002c4803280c001c01e809210780c0c0010195444030643c0d408070702c2040091a280d03a81c03c02c1006074081a00d030081500c0d004c010f0524102000e038000c001842c45565200c942d92600030029085900600e41501c00b0180310044c0d90800c11590f8003000506806000541080f5080c00424084540c0340001000d4000c005401c0b01559101d040c1440300c64a80700007808015123840d6010b90207500c480c01c130501000c607400003040c4503045008110803100090006800d1400c40009254461001180c070134040f0241c240100f0b05040600c548102800320b160364555484810b044285469030540b00020000c001030380311000642c00804480d04405a0500450710012500008140f84900d410080d400407107440b00c0b190401072600544240102c19203034109030f80c2c2c5e51403449000c1c05800400c580c850000000200702900071390140e07401441c003404848046010412210002040702420350b140e034080d400421046100f40070301d44c0078002c01c1c0001d21190800380c1c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 226252886 1250 226251636 226251659
    0x7020f030a0912060920011d090403180e0c03162105070315120210090b03160504031b150c02090f1b0a0f0206060901031a0705090d0605060f0a 63
    0x81d201c00000303501ca400007130101d20b402c6244020341003100341061407a14240d09031035050800400e07001ca4502511441101440840c3c0501210054031180495540d42d908840d8101d00201001d07851030351030705c0071030009840650035108000010a180c3d403070501d40c10314240402c806081804021410003040d91180102c4680039a45440343c0c4085200e8070303000029000392801d891940c0c1d2000d0006000500c0400d0301c018602e80c0c50082c2c413140301c0910080411540d18040307000d2100124400c0000c621076504002c45441140424545142030503100d030f4a429181002010400c03a070807010909100f1a00700203d58040301c03450303007401c915030811540442c14080b4010161040792502c10009900ca0340310b43c14201c058500e0548203640d50813061005484910180f884900502c1440d0001e006400c0000310141601c0e005032604400c03d4a1002901000f9001040c041c10004180208056a2078880745214520711410002c205031804e80c06101441701c60b0300516105080c4042d00300041e08090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 226254136 1250 226252886 226252889
    0xb09030706050609071709010209030d02100c0203131a0d1113080f192102070e01050a030c030b0a140a0f0b040504020105070b07020a020d1a06100e0409021305040303020307020f030a09 81
    0x1180450703951100147e0f80240640c84001da090301500c010020700320340c0441c440441c0c2103511810010704030514401c90f42c3e07015400a80c4250600d9003401d002080c980e000502aa0300003078415880c0c031201d454100184d0320f42070354581c10001d0105107800c0086800d44d00c20042c0240710000d00040103850b01d0144d42d83e601e5001d415010a081e0390341020b000b9032041d03900d00c4a2407000d031420103040605000399190020320038081c01d03040450011680b45400342c050011281c04c155140d480604544076400b60030380280444400c241e448100c3c5503071f151104400c500c1400f02c2600000c410b0180c00c000810b07a444060018802c44c5010f081100607030f001410744050307a420035a1079103241c1c0d50403810783c50300c5810f980280d0f00c5402c50460404001d4000d4107034401041c2d078103008401d601c45600b8012071200c100702c02c902003807030341c2d0070302d01a400e0642c011034005000400014540010112080485130251410343c002038002080051003601040340ca11542e4003a8000d514000154a009203000b045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 226255386 1250 226254136 226254167
    0xe0319051911040204060e01020f01050402220e0a0c0512150c030405150a020306010e0916030b030321010e06010809061302150309070e010605070506061201090b0903070605060907 79
    0x86119140a0181c03005081c0c1c482c0b1070150045544585030040500440c0c60160018010300c41e040d0340c032200031418040e50380107680c050300c00c045599801d00a100104848038400c44490395441340f80c90380920405c400c1c40c074140540d6001801c207040c0000d10000042c540001410380d8007000d400f000b034030503038a240303039102260000c46030b02c0b502c5a25080e41002a1410f025030401c15403000d00c080070031507500440c05500700340ca4050708002e00d40140800c52108032041245261000c510106083c0680c201022880c0000d040e40c0c035010907c4191a13155511b05540000ca0758448014850300403d0405160403000074200041c061504020641e43e4400c0108154000d030351080251085440f610030207604031400d4410300d07880789445030300c45e6034803a1244030709190075080a00010329640a1411110082c1d00315010384440e40c2c1c3c040030300c00070100c418200c109d90b40d6550058004990343c001c0141c020004500916902c10142c2011000c0c0d40003c0c004a01c940c900c001804440354111042c241710048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 226256636 1250 226255386 226255423
    0x60203160f051006050f040e100509071508100504020408120a1808010e28061a060304080c01050a0605010813031701060e091305060403050d1104060e031905 69
    0x60501c1d050104800e48040141984a05a4218211003140c0c04c41d2069850a0301c5003410078502070104000e4483e070054140302e03604154000207042d007407508076075440004142150401541e03a090010744400c0741000400240c000c005106005081c07104210003000115000d5080c2030410640589031080703100e400881c01c4001030024030350f03030003010310345d204103040300341042c103250388900086c080c06801c210954035024a1200c07468a900c0c0310040c0140d031028800d0390302100c0142d5074400c0207020100c10041381040b003071000e402d0b5544a5005503c21341c0706001c12500d40c0b180c520084c0c01d48401401400800e400c000c41841144d80c8810110750104400404030304110703a505090342c4103076102c410401400c05040c00400d81d0342d0062510860501e0540b9070b00300030b507504403640341c1501c40b25800900c180c1003030380828003281c401e9016000c88e903145070000450181c2c2d0010900c0c1c40d03025905c1360b0085868070020455a00d002d00202c07400801801c0c40f50384403421036540a07100e42c40c9031640c035032844 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 226257886 1250 226256636 226256677
    0x1101060e0907120311070611010b0109260a080c16170303070e06091011070902070f020f060c01050114010e090907150c0204050103200d031e050c0a0b0a060807060203 73
    0x41c4a868402c84031708540041e0b0f24895140d0b00014622140000c2006041d820310070703040c102c1e51003040c103513045407003803282150012196062203103032030040c40048a00e0310a80313036603801007000b80e030007024040340034401403c101ca040d001d005141607880c0e001581c001b074014490320500e0f001008982d4000d200c0c0c504003201d0913005c2c0018806019001d400d58000014041c08094075401841501c03481c8280340448001659503400042a407064900042403e404074080740f0050401203403103074560030010a8541090600c02d0f0050171624241c3c05200400c61040a0300640d50304030100d0303d0200320980b80c402044ca00400c4080d5070390b9482c840c1121680c0d400c06a0f022440c07042102450143d030050042c00303c2d5a607418404441c6001c0006d407200c0f000740c05d901d0340c0341d032400071416080a0340c180c98a910741001030520b2242102c91200c00006d1202c00c00001d03136461014045104c401d4410358042d1040d007442e00004003118999008003821b0780c03102600b4407201da00081a0f45951101c0700d0b003644801d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 226258992 1106 226257886 226257893
    0x6131104020a02071404020405120c0109060e060306011103042303100b0319060609020316030e0309030a0f080c0304230d080d1d0d1101060e090712 65
    0x5134400c0700200044d50f06895103a140d40801070005060a41e5900400ca040c09504140411a04150582901582c00c0f10500c0d01030445031801c49152300c0030401242540c0f10140110307050181d42c00560030085003c20450740038100100348100c1c0302141034a125104540b00c1d80c128400c3c011a90170480f2070041d481144400c0c20020001c01544551408940b003008039210301750b130010307107894001c901d040050000310700903008400aa00340c001d5020b40241141c4c827207402c44034543c10400016549035070004d281c0704800c0c0c02c5400d58001110030324048145100f200071810315070202080020340d1a2404003800448104802e01c2d068075204c8900300900a810843e0062001c0700c24402000b19604a0307124030180034400c00d4154440429660785071400e200b2088120000300c01e0301800003203079800c0c0260b20040500011600d0942044403100f074981011780220001d07a007400913290140f = true := by decide +kernel

theorem cover : BRFrame.Cov 226079136 226258992 := by
  have h0 := BRFrame.cov_init 226079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 226079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 226079136 ≤ n) (h2 : n < 226258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
