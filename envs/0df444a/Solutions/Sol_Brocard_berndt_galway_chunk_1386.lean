-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1386
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:43:00.358212+00:00
-- url     : https://prove2.me/submissions/4ea4ecdc-93e2-471b-b8a5-3f2b07c03ccc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 249100719 ≤ n < 249280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 249101969 1250 249100719 249100723
    0x518130905150606090d0503072306010f14130b04050a09030809030403020a06120b0d0809090a110d020706021e0403021504150e0d050d030606031404080a110718020307030c02 77
    0x40d00c5003500300c1d0f814852103026042c040a00d098240c01f074402c4a08001c8195205005080c90b1010043c404842800714000c00c2010000c003405006402d00c10f004e0941485052020400f10041e4a0312a192003c40c074103400810b507001301107020000d00b042c0800e1520412040c0600300400080700029020800103180e0341011040d10300b41c07603005024403031480c5000d42c1180d06000514a40380136503601c0c09004603564604e108000014415810310340c464200d01c0400c001c030b5200801003c40c45081a4210001d912800115210b94904003401030711015181000d100a0041c0c0da0042d40000c03440807a01000307000703000500212442150b48031a800690350301c0359603e0113030307208640c15a03400c00d481510080c0205000401000003401580d0b0200b0292611890403100310110300100e6074a44040c814540d1602461601d88002c0c07a80c0806401c003944d650045120f030100000400443e0240184d801005000e003000510304902020340621080021200950003075841c80301081c60200d5a80c1c1c030384c3c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 249103219 1250 249101969 249101971
    0x251e0302030c120c0d0f1b0515150906060a020a06060e01210506070c0204020702061b0c101205040c08030f1206040b0f040b0a0504020c010605040518030a051813090515 74
    0x5000500350f015034084041d034420f07070900c0d40503047c410180310241d01502003000b501e01130fa0241000f80101ea8441050400450001d084240c0382c1d04105180d00c01c90721200b080b00e411a40580e9195a5a07000704030407030a20380078800003084a802d2400015a040c95105440e0585449070049000050303980c040040641180600805640203d00001c0507035005030100c5280b980041c001501e07020840d40064465032201070201034030315660420005000003003104110580c01500c000c52112141c0340c0c007600e07900f1000120300170703e51070f500010100304203200468002c05101d41242d0f100c01d03c44100004941110178002c00030005800000d14510f024002c003820000701804030341510b1000303c140005012000c401d00d8024103243c000042d1030f2214401010704081400001801e1400c002c00c0200751030f4041c0c240807580000710343c94040c03c074000c001c4616240070ba00306241ea4064890ac0340d4820214845000d621081c0840080c1c0041180d411120016108030152404004185e02200105030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 249104469 1250 249103219 249103237
    0xe061501030e100e0102090d030201050a0f0c090b0306040e07030804030b0906060a05011b0506071106150303031303030b0303071203140702250e0103050a021302251e0302030c12 78
    0x408480c3c80100301d08194810b41854601c0c900152800b241080411200042d0101c101c00507950b807010449410020b218081c1d24405c280e00901548182107401047d4640c2c1c2d00901500c2d400c00804a40e6590b1560310100c500c010f6030050f64021542ea0a0100498005201c00e80710441c2c02c80016220b40c901150f0144241c0c8024005007149041000454843c00c0e035007000f030301c41140390704604046003080204a120b8060780e550f6131082c010704500d8500b0010046e0041181d02d06000d03109206541c044107403940110244c031880007100c12420120003822880030100d40600000480b41c1c00e1000501c2d40c0c0d595400d1540381800601d1691809240e41c0c00c0c210340d50070040e00050b441c00d00040542d0f50f0b0ba800d5000403407484810988580d40c5000902017a8402c85955000a00c0c04c0114144403012600d104140314003142886a035020140c500460031030a085c942181c1406c5a04200c040312590040800c0411300600300d000a16000c0c0d076a030b10100414a007807145020079110111000220b0741c10384 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 249105719 1250 249104469 249104473
    0x4320d0503041415060103060e1311060d0218090106020a03021509010b091006022a2b030905010908030901050403080a0212070503090a1a0a0e010e040e061501030e 72
    0x110041422a0107410107041151503100c1c002e500b00800b00200035407000d411900a2001302d50030010000f60458038154004101a01600b0030000614408031214100d56000780803100030142e07240004e07500c0d03c42d0b10300c4502c8052010910801d01100c0d60078001d4010001da03004480c507602d404007a40c2c0c031a00c1e1040140164001400e01e14940e4600c0540b83d0010000800131030300c0c0014000103040c01400b142c55101c5500000320800c03000d82d04001c0100d50310400c0000529815030b0014403006c1c10f0389144043d0007490f0240f000083c03a202c8032480413800c1d00034242c040081d02c0b24600200060000e00c185800121741c0000803450440110449505080584ac0d0919191a5030756503422a000f0318400380540c0100c45e818070340410008024070000303100301c3c06544e40d4001402003101101454100c006c01c50b00f910f00300c6200c071400d8400c6520f82501c60038000051f400050048864040c9032001d15005414400311a031031040000b40140908560303e29440f019200100450480e040714403015070369 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 249106969 1250 249105719 249105733
    0x507060203091504291603050c150f0106140409110d050a020f0d2c1e0606010507020409060b12010e0f030f04051507080712030c09030c0501050f0409050432 69
    0x80842c40c011703064012801c41c82103041c902c1d250b441c041040e07500401a00031440000b24031501000074080950722040220380c125003800c1101d8143c24042c030500950381440b04254808401407000d000355001800c1501003441003128014481c80c1c0d6400c03000d0316488903810031003c62500c3c4000c0c026690005224a440d80c141803c6114210162032007a686801c014049170707031102c9080c41d0440180c1c2650051740146442d070b01e161050420b00007080c0031a100d030b8100d2030901c441c5130b078400219000942c04640203e4840220304050000b00300c04c5140703951100411802c03840c00307001900b08000001810b03003074648003001340400685030311540082c410010b004000600c020301d000004402007031152541d003800c20b40d40d6a80c21b440380d0311024042e104480c009102120150389070003140d0f01003a280c40c02454891456035141180e1106001b41c5040c0700c0007142d240d00e08000642510001c0400c000140428245400c000c480c04c44206000080c6000c442610307429200c0c080020440112044e00400e10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 249108219 1250 249106969 249107009
    0x10c0804050c01141b030c100b030705040f020d0f0e010c0201110403140f16030b0106170708090f01060b1306051303020f0d0203060708060a0f06020304050603070201090507060203091504 82
    0x20702d404100d01c80c8090300c2c045c018502e61140d900b0490103c0344010b0700842d610201203800b1450411402141e0715110308003ca04007003500e011901d0303404c58070184c5011a070503089100010107401040c1444542c240342c01c7c03008203805c08603023100d00000c040e00007c100404a21800700d090f5080d0044541107070408100070000a9034045629609403020019a800c60100b21001402c10160740200f01600b08007000c14014030107041050b80c01000141403e110b9410b01c203081c0b4014000080c03140007805081070005543d84400c0c800346a6030001d0380000c002d0640c0310311180307100ea0003418406c100540500000309000d4000c1d011211180e021003c45c0084615540c2000098403991250a4100020219010040e2810002240a904d0a40b01c2d407260307107401e4040c03101c454410340c05907102c0b0302c00c000e0130030420390003000312010340b02c0c00d41c3c02c541d03640c1d203500b4140c0c0581a6214020302e244148030001174000c0d8044050140310034122190b4104000488603045caa00940c050760395510340c1e2885100c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 249109469 1250 249108219 249108227
    0x10305010f051f0215040c03020906040501061704050f3307020a0b060402090402030a29010c020904080405031c2c0d02040e030406020304170a0b06010f03020d020f0c010c0804050c01 80
    0x486402407040307400e045c0550500c20f83d24801540c08031800c2c01000f0040c02185802120603900c00d1081e5003c00596140c0400180444030300c4942850540806008c1018420309122011860206a0032905c030702c0410000318035103401400d0301e654401107440e1a0b110000b40305030300c14055400c940c0105006081600c0e041490074001d46115440360342000101c0c0f040d1214006107201e0003010b0800503010740b908040321840e0030f040b0194120b5001200614009a8000b00d0303072045260195076480c4903559034a001a480d100300e402040c2c2c180b103440c8200890864907242c40360513030b0302603540110240344031405540b280520414561600d0ba00b03014181d4070300700540380d185600e0000b03101164102e4030f030b56081e0560740a40c00c04c000503040010107100e19154549400041d55a1000604000348075071580d880013200600854108070340c1b090040c45c554465010b4030030b6540005011558cd065001020b0507550040081e520701d542460046601c1c140111251846250003101825a502d40600112 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 249110719 1250 249109469 249109519
    0x50318010215070e1002192004110d020901050904050903040f0e01030203030d022d0904110306030d0e1206090a020a060c2102030d060803121f15050c011a010305010f05 74
    0x140c21403207806046249182100280c0618038010041d01d0203c8000005207103041d4500307003866001701c2c0ad000c01c0e50b441200d90720440b0864039115100589811110004a550784180340b10b0030f51003800d00007401031000000c0020011164401d001c0110bc0f40e94a030152031701c007000d02c8069410b4005020a19500e080d6030014250020503081841d06180000001c0b10490200c200104004401148035807950829124421088107681c4815045140400000fa0f80e508114410400c1151008129807241c0300c035450004125411810386101d0f1400306083c1c0c2d958a00990103074400c1800c100300080c407500861042d002a41c0207203001c0c4541d0741ca0b501c003105c031000445406085100030000001051120310a000160900d000a10f0742c40c840d2028031160844068483c809d2074a010429000d80b1800544071012114040003540208070000402d42d0300d0301030132010113025400c01d42407507281c5203028410628090240c0703040000f41d882e401c1c2100c00c03009030f0080030340020030800d40b54040c00c4218070007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 249111969 1250 249110719 249110749
    0x503100b0705010507030e03070c0510022803080c1801030504080f07050f0c040b060307082809120e010f0c39060c030516020a03050318010215070e 65
    0x10550394915403046a6404100207450695446013400215070745802003020706c1d810b6030011802c00442e511102e500044600c2141e20400c144413070020a18024004004044000801c0d8031506282e10b40c4c1f0047e10200d088124006a8907000203584800c0d5030040c0d4400c517440c03440c0b0380ac12000000046d0021b2030041c00070784140c4018400c000e9520690b80061440314414400740c60020268440c0380e2a04441d0b1019a110f94103091043c4007a4450006495008841c1d2030689080c3e1900e00040018400e034440b284100caa08006501c007910315504100303201031190120b800700c8010b5401c01c554403840d4280d601d00181000e100b10b1400d41c854800469142c1c06140850031610b4070070f11946096000341000c4a480d8203c0d12740781903100c000c80c1c554008290b00e04100c0000d802c41e5800410512a103080d00c2c1c050a0341c030903141c095441e1445224080c41c1d203d400c880c1e441038075084c0d086002c401603003200d0040c13180c013810b180114400c0701c1c45406031189407030303c0601d0340c045c1c0c0400c40d00a0a000c0b007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 249113219 1250 249111969 249111991
    0x60902040b0405090a0b0c12070f030213030303060608180d1d09070206010302030f030705030a210c200109110607260306120d140d090206030109051509070f0503 71
    0x42081650345208590140135204002e00c800e04581c0f42501000b080104034803800002804454105455010405d0b401030f03051900c403841c03201d882020390080c00b85051400130804407503400701c2015015803001c0140d90054481c0d01e0310707030f442201d000c2d0705d600e042502c1c4c071840e0004810f84200c035000350b501072120048402c110710002040300114000030812184540164043c0c0010001d5003414440c1510359140c07000039510701940354840356076030710604419100f00306100900940782402d804120b031440150500c1449480c100c420f0007844414001c800941c05031100c880380b03d01003014414802d400d030340040d01e0518200000e00b04009074114402c01d43e6901c05540d03228941e10f4074078482ca40503601d0600308a8503428038200744102e5400c412944803440d8040d201d100180f60f00701301ca80b44803091100259941d580702d071821070081c1901d070304000d4100d0004800800d0b000c0154108038400d40000e03800103510700018080080340b40e002d45058001c04c0b0020980c8210790300c11002980d001c1da446817 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 249114469 1250 249113219 249113231
    0xd1709010507151d0d05030103120e120c09090102130e1f0602010c020d030231090614120c0105030a0f0204030213021306020d050901030207050f060711070602071206090204 76
    0xf6980e240b40c036440c00d03c42070207a80e4401c0c031800300b40d004d02c48010003214000915031072064410242c507034401030101a042d24051007107011007a200d5091501c2182d400760101121007911508181d484c149a18094401e00c0a80b0000b03001c64014400d0b11100b22504100810852404800c1c589051001c1c210b5045c9000814001c6260404401e402000f003000c1c2c0d0000544050030030000342009450200701d01054010000e42c00541140c1c1440c5042e05400f4180030101c411030b00310005160b00ea54030040502c0e0526400068106036144032900d04036054071328204a0300d130007901340c0c0c0340c5413603242c55404508144045a0094419401400105c40e03240e0700500d4036490740c002444d0040d01ca907a2040c41c0f9000203015459084c100c41110044c15107000500c1c11a40b0400060180e005ea04d0640c0c0c10540d006c1607880500c10204001c980c084050f8058880e54100014000c000d80440100c0009a129000b00060003c0c030000b01c00041711140e007210342c4058806d40d01ca04c00f4284020050741c0c0552a95 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 249115719 1250 249114469 249114473
    0x9010f120b0d05030c1207020d0201030c0201330b040b1909120b04030e0f090a0e0a0b07020717070812090102030d060e15031903030c02070e040614060d1709010507 72
    0x240104500c1401070000b19243c1c4401c80d042e51401010148404c0100002c0c01f50343d00603158070003070300c840c03a40c2401c012800d0400e82404074018024210005050213614080840c51030522030a14001d00d00051840341c280d032100441c800c94451071042e40c80c1703540104801449201e0800400ba96609186001c8200719030351000300d82042410f0300103483e4111603c05210405030401c1000d200020306844010b107200b58400006d075880b00c010300108019807601c072514400ba00070f101000c060ba5000c48242205d041000303000f0b69071450b074003a0200b40c01103510241107071080000c2e4641180d450381d00030094005c0700358141c0c0d0a41c10003410741341544020300642086424601a004c0a4014010200e90915055045820b44501a80c00394041d420000c449c8800f2181d1018040c1e4442e0141004078404045c060220b140401603400f01441c0d0b002c5c6818082001a81e811081e01618071081d000901c0d144da0040021007004c0c042c00030041d440009581ca1100161005072030403030300505095092110716 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 249116969 1250 249115719 249115729
    0x121b0f2301050106030c080a0c12150e040507060809031e070f0605070c03020d0906020a0b04020d08070b06040c1106070804050102040b0d02040f0602010603081209031c05060301050c09010f120b 85
    0x13070704004046030310f600010092070360008181d5884450480181311003002800042c01140d414002044860f403101440e07054403544818500080642d480005182d2505d802d0158036200140241c81c0010161004503403162030000540b680002540d034201058a2504c41158080d40160000c49540c032581d01c204011500300d1103860302ca41881e4441440d5a4021315000703080c4814118500184581e43c9401d1000310790000342c0800055000b4103902d800d441702d00020b45002001d00303004004174400a00383c42045500c40d40940511001d5505214800c2d044006071202e45036820b0032072840d40010000340380c03103104013a055002401103000520b030035110900020320b03034881030b10501d440b5000141040504800c00b080c400415481c80200441c0381180d58266140c1718100306001c0c4643c510700030a55a910a0048418001c1220358155030300c903a04a40801416084800c03601c04d51915001442078500ca908448001405941e0650501c486039410b45074500034581c4010141c1e91040103815603114 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 249118219 1250 249116969 249116971
    0x411041418010b09041a071409060d0924060e0f0f0406090506010803090a0812030105060f120f220b06011101060308040303051b030f1e0d0504121b0f230105 69
    0x1403498002c1d41c0e07180310001030307075210083c060700204038052301d50888408515051701d52500382150241d0b5a405141500d001501c1e129101501540c00c0c14101102c4940380075481c0014244c5081c00d0000d542d07140904000c507007080300c80510300b0100b01e000800d40350850300216401446000c00041d01000d0740c8456107007420903000061503900018003600f4a00c0c3c005011001040007800524240604c240c035005c05000611400380903500100b00d0710040010b0409543e203040544506155510b04800488014803081c1d03a0b003c81340c100c2d1000007141c2e00080071f42c1c50415811800742d10751610740000458040880110640c915581c4441c080b00003102e00008000441c066550141c4030590b540c1200740b8811001c01d201160f038001c00000c541d0103d10342c1595034107150780748010b561850058201036280310b5000e65041c511700e40802c0000300010000c0f408014109561460b014044012540b00078102400c00541411095040040010b9001c501d00482e0890040048080140031610b2420b60300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 249119469 1250 249118219 249118223
    0x70b190e0706020f06060a05241603120b010905011209050f03030402031501030b0c0f0c010e010e1002070c0902030421030b1c03051803030c0a05060411041418010b0904 74
    0x84500100001c030b0341084001031044c0c181014090a0070300000007040e03c2c02c10311450b40a490f0400c00303034420600d03004400d5429415600c003140d5801c200c030f2120082281080341200400d00400101c0f101c03080d01d110340f600b1424103031504e0030894100001981d9050481024410151f241c1c1407141c00500240100c200802e07420b0b000b15280c2c18640704041c2400c00000340b110a41c60340400400101c0c0e07405a09503040a58890b203256a400403000c1128a48102107003d481c542c00d2480d000d80203041540528407208040c400c0e1800f8048000d1110b090344548440513140500790300042c002c0c2c10170350740103540140c8a010160310660703040c5415030608079444004004259682c0030070b1032a083c0044020f200c0101c000d01041045903640d030281542c00b40d264907030060814204002125202001141c0c4c400c1002802c80340301d442c07a4034020b035032903070300311001ca83e0052254400041800c26005481410040c2e030b18540c41ea60311941c1011030500100d6020b2920b64a40140041c0380d20b40c4400e05000758 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 249120719 1250 249119469 249119473
    0x71e050123060a0909021e060702150c0f0601060f1d09040b09160b07080d0e070b07060b04061212020a02060304060c0206070e0307060c0804050310050f1b070b190e 72
    0x8030b8800204108400c455010b01c821034100b0b0740804c010f079983d5001200000b06490800126080030011030b04034003440900a40040386c55156400402401014007000302e410f5080b54078a45050049a442e16828854040803413842c1c20038070380440c011180f0729640750326855040c000d038241a000564100040d03a0513590885400103000102034148a043c100030620700c682c400e030504e0421000804d2090090103482c0320340103d004d04814031540c009410000780c40080b10000c64442080d19032607407004e04115541841c0481d1504030b420700740100c004450036003013009c62401d00790701da005002600940c040d0450288981c00801070b51b6117801386004038007944000403500740402010385411000342080f41488035920000d0740c10360f00010380d03070191989032501c0030003d940391030204030340d00858102e503505d80644548400c4200c81355210368407440e06040f085c0f05a440d0b040d8a80035103000030354401c45c02c400030024a00030965411031250440010400034401c00c3d21a0040d104031403141c15004056 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 249121969 1250 249120719 249120721
    0x3010e04120c02010c060f02090406181508120a020708070303050a0801060503100b0a0306050405041b050d05060a180203010c0207050f180a09050115031109010b071e050123 76
    0x80441c100e001c1c281d80e695814510080351039500060300c980d1950200400094a882e0540803001140d0103461446c4800b6101348441c1d51100d8000440c01030800ca480d0a442c641140000c1d05003240e15660b046034230541c041c000100400c09001c41c40d9204500b020194441c8103c00600e1680030031a40e8002d50080d9191030305d034000007100038150103043c0e1058080000038000c0c42240301120744508215a07060b00b52075a05c40d2883c109601605070b0394062076001d45804108024007094090040b80300301084080c40308079480f4000c00c650f59401c2607000c1d16a6100f00300058002c1c0b11a800000058030784000980403010550020b429105503414600068104030b07030070001402c101c00c40f1010030004440580040e00f44031700048400c0001841001c03440c0d120700d600020302800303521130f0400d5000740601c416610b48034207081c0c134804402c640d0b031402005040e000160031000741d020b80e4585644150344000b459240f110140507030201000c01d03034140d50f9030182d007607a81e02c01d118000d5013010321091209503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 249123219 1250 249121969 249121973
    0x315010905070305010b092404030b041101111e0a0c08030d0e030301060f05090402160804080708010c170405150a0c030b040606020d120b060412140a0c0501120e0303010e04 76
    0xc1c0d40001d0401c006050500b0014090750f1201016900260425514208050300da041625054000b500310f807014180001004400c0c0a010300c56141703c1c90050316032003091600d4000440705a100c0007002c2800da0481e6070704c0761800700c0180c0f54034a00c886800464448110a840d4185955000c0d4040400d6a00001ea10400e000c02030040c00d6640400c1400b8605541c542600036014904000942c0304018000401c880507030344560640308114440308020402d4681c610308442c01d0391190250490303502c5912000201001e0501990300e24004035900d5001d851a0258646481072000d0f10807102c82c09000c8104152a1551540f0751050008043c041030501d240d5402a0848a006507024011401d010040c0040f0340c000819450405c1c00380f0341892800c1e8010341c100e0003002c01c1141c0c1d650000000500207a50f00703498001c074113018061104500380450140e402641d03047c07600801041607540920400080d03028120400c900c8405410108d1484466082541994001d81004080344605070038081 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 249124469 1250 249123219 249123221
    0x31204050c01020c0310020d140a090c080601030c03020607210207150503091e070902120f0711070311030c061614030408070e0a020c0609010603031409150a09030203150109 76
    0xc1055003e0000d000c2a00110010035262031a290454641640000e4070800b4001158441380581c99081c4200b40541895481c05029214101b003c2d0b0304102104004030b01c034400450b600341201e9120480c1c1c4d070054559403e1060f00d4000e81025a00c1e504003410070544c00e842c400c0020020321840d40640041410304801aa4116004601e6808c12509004120a200380010032084842002c01030010040005d501c1e9441c14126801200c9034500114500080390302595059006102280503181d0b50f5481801c2102d0651003920021090340c8031500c10400b0a101e0154811071600180654100801c8000030031484c1d401102201d0042c0180c001c1d000901c0710500c0c440c102c0d10b0078070021b0362409283c03003041641e9011a016414001620300041761031980207904481d024121602610316070300d0080c0317000b4000d180d544400c1c0e01080c0c0441c1d114030440ca204045851140c0002c1070720840301d62540307200c02282c01401c0070500380300c40f4a07070110159400b00090103441b45100214101c960500c003103c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 249125719 1250 249124469 249124483
    0x30213061a0a0203090f0409051207050c0409020d02010305421507030e030c0409030513061e080a150e07031b08010308030714030907060917030a080a090503120405 72
    0x8000c10410b108030390040e0390100440d520201e0460b5003c40c45241c00000400600c40d0110044c51072050300315201c503400700d4a0282801310300072001d603500f0013001c40505c03098030b18640300258844911703006500158000d0f809160400c0c2101040080707050343c0942c08001d6400c0d1142c40544015160009104280b00102d1500100081c0c60314803040c3c2c80d842e101c07896409200c00040a2092041c02c00304241c40400c00545c03085001403003481900020b080240040c0e218544440300900c8824000c10000d0081442c00b0310b030b49003440e5022041c0e44170f29049800c440090b115082054035000349841d415080079188014141282c42d110341820704210180c11034166404941d0f041c40f01c100e56082c00c03a000050700f0304581d0001c015641c0c0b541d803020100d80c032041d40101700100650200031701c8032007080018400700f51089910307400340c1d107502c402651940903d5004c1c01151940200031030300c3c85074456101c6d103401c40d0f4040ca010171125081e54405041da00101180d120b605d403508104400e1100402042c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 249126969 1250 249125719 249125759
    0x1203142e1d06190e0403110a030503060f01020c0a0b09010201020f0d02030108160302130b19030c0f0b03150f030319020a15090c030605100e010b0909070918090c03021306 75
    0x201000b0f00240300c1250b1480554030905810701c0c018000141814040c1c00d0a04d5030300301c40b4058480080e154a07016015070001d403219402402c0501d0801c44650001459100c140c8000b4149040daa1602106a025600c4280001d04554007800319280812003c00645511b80b4003500c050384960414140310304d03080000140705e0200c0d490510130805a210743c0608019408980c1000c206068108003080d42001101d08135442c013500700d04004180040c45c2c0b103400c140c07580c400c005003116503280e000403858001629401c0d150341c10507003420f0300ba28005941034950b66001e01500e08102c450b1446546081c1400004009a0030551148081100003400d9441c8400b402004004d24005a204c00e1072006640c08010110760351000428a643c510070700f0b640040a50300d102c0241036859003200209500700401e07450182680401180d0700c54054443d400c1510b450144017015117124000080141c90000e40942c1c1d0b20700c04c40004405601c40140000a00903c2640414424a02000c007a1700722820703c90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 249128219 1250 249126969 249126979
    0x711060304110613030b04140f010921021204150807050711040b01110706020709050f250306030b090a0c0501050412150e010203131203142e1d06 64
    0x1080001a040402d01c6103a240541d04281c803080514681c0c03401c0c0b011500094045202c42040000300f00310f8540c60040c40f0340c403e041c0c03000000d80d070020509903021350310010940d14031640504a100004000d03159014100c0c0b0448a440e6544c2108807525405500100d148644e028046024503400102168002c4000e1030700510784040c80e11807c0600d00c2d40f003041e031722454840e820001183e2081d80c0c0702400030002d109807880c19503114000b0b5540c161511411964900f450000381e19040100c44a038410141e000c070607407222001d245100700395102d01100d80300b81507884001102081004500d1486a940c00000f03224030582400c1c0588900c42d158016810404100410300091103400c064102d0141c1c061802000c40b1590841880030f0580c0c88810a4991710100400c00544c450301b0040403540c0c02480c0820030000c07003620407000c1d254284400c6400100c0d280101d000031031050014401c848560304100d5580c1e258a6143e4210f003071541c4640611004807030047c440001094910380c0103001151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 249129469 1250 249128219 249128221
    0x1a1c140f06100f03110a090204060e0108060a2714151206070f0c030507060f05011d07050708070602070506010b0d15050907260c030a06210605060a0f0b07110603 71
    0x4403403d240301c941e0100909002080c2c200401c1500c417408064064800307902c0c15500c1d9601d4040042000f10490441e40c00628a00c0105605003800c0030542e0542d8040e020143d001c0b8410070980b04080310100695084d20750302c658031602000c44a40c0c0324050884100d6141c802071a09003044020700748403400300000e81141c01800300d01c0741c11240c9050080d071141444015030a035405c05907500d000d803160140c103250401101781200380256100034142c8034403c2c8208034140000484413601d02c821100c0c0808141c041280001160688001c0c1c1403251054134098030f0b00748941d68040c00c129081c1c1c0188074540c400320b4643c1184600d40a00184039090102d0305500c6c1c0d03d82000a10641409004e180c18001031000145030440e0200c0c0ca940c000c010400c00c27001c2424a00c8c1d042a083d07000f03c42450102d40303006008a4682c0710714400340002c1114985683c0b20600d81e4507108018030020782029481711500c1d40001c1c1c0300d081003e10b100207110101c01607445812500f00301d54050002000c191040340200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 249130719 1250 249129469 249129479
    0x90b06090a06081305060f090f0d0203030a0b1513080c060c1b0105120c0304050114370e03070212060403080a09031b0501090311011a1c140f0610 64
    0x140d8401e040b14800d2502c809161214070342e03a503a50304a0a8003412a00030700e001c006100c1c0080c01b405000b04051403c4414107414180d009844150220540340180c1040012950046071074102001d031060003000001c0c94810480865131940c010401150410b200403001c00c4807030000c1c080412190002c0c0c031340c035250584a0005580301c129043d5054218941031859204d245d104400707442c00c12000f06806545418624060b610b01e4200315030444156092a80c03401c20707201040c0200d4001c0420643da160410020701c0741116042c144401c1c08160100c240c40d22400034440e001c2d030b80c00c040c0c10030040d55075a20a030044c010032072030400101d4444d500030b80a000010340e00045281d4021818500042c040c681071a007118403880003000d0564842a40255006000d019804100303142e200f82c9403042d004a4040d0918203980c03420300c61010b000441103d102e04c90414041070128005192283e5a08107a82c1c2d6078180b98031708a0702e014850390b001c2400e030240c2010801541760045900c0d80c0c810111031410f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 249131969 1250 249130719 249130729
    0xb07110a1703040b0d0209030a050703050f01020403031709100203010b0703090f08031c0212011410020601050a0902070c03051002040f0605090306040f0303090f050d120e03041502030d0204080106090b0609 90
    0x140c800c40d40e00d40c034005511401d45c2802d03815640d224034014144e40c10b826050608969902490209a03054010802c1c4040403541c14400c48084981c1034441c5001d0135018540780c9039845c40181004820b00850081c2d0407041c600c0d01c021030203032a021a951380c07255510308000b01031031129000b07050400c50504090009500000076142010803485445440740302480101019018501d904100c54618074000705002c403c541d009141c10000ba03404151001c00c1c044c1c12603a8650038494282c02000220703091180b003165800078a41035000700c4a480803d070396590f965182041949503000c0c090760200342031101400c3e000010780180100e261041c01c2c20600c0001940b00c201c09000203241e003035084140820540207800c07102010742c0140f2104012102030600917101c45000d6840000102c4010100703014203542e20407580d41a500000450405003080307031070f59100140c4c10566065100910562030842414002440a0410b04001040303041c6040d6564007a1403084d10440e00c2240140081e03003060f156 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 249133219 1250 249131969 249131977
    0x102070b09090c120403050403060c02010b0f0112140a0b010e010f0504061812050f06010801111e090603011202091303080f04110d03030b0907092303070b07110a1703 73
    0x200d8214006807a0f0301d40c0d1034000d1141c4240d94404001c020104014035402402410449008941c10301119030780600803422030b00182a4160701c854080c060503059440340c8882d44220140910020383d03041a03028082d10164100c425020058031184404010350380001003d14815080c203001d4130300c040c0d1000240250042c1d0103000f007002012080c0c030201c119040d03440f40080801947c0740d101460142000380e110800a08034202d80e114083c000914244140f080b94000d00c3ca0040030b070300b040080c50000c045100c212001441110703050040498540c0c8141c0114000d06140c611140000b0451050003d100b10040039408084208807208000c02d4001c0a0785521403035480107008569258580458104480d1080d6a00803880124880815815a011580700c82040746d52003629511400101c07126001030190601e00c008903210352103620807410105034130326002401c0d070f1a11925400510201e13000760700182e5805002500082d1207003008400360019107504502c18030030000c001c8107a59a481 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 249134469 1250 249133219 249133237
    0x415060804020607020405010303031a090603070603020d020c0601060801080106080d0c02060702010309050d05120a1a1908120a030507090503120a0c02040923010219030506061e0c0c0102070b 84
    0x890400003070115078801d0100da115650040003006070b961203080013402807a1765140b485150b801500c4000a610309480400e00c41e20008008080150800e6000c0340690800c0e40400c40d429024400926880f005003c0e05028112950b5000c901d0b6140c9200d0a0030b495195010250507000030120f10611588010740c1515182c0603511a90380e01a1403004800610300c0c82c034080c140d4058100405885540a00100590384184510903442d44615a40e1011606c55080488103034003002c1d6540114100881e03a003180520955014000035a540500340c2410310702c02e40320340000300000382800002d0f054410503401840310f160580c4803d05206c0441e90358000300100644da03d20105050a005114088445116030301900c1440030f02c1c2c092030b0030540d03888003254200c0d03842c0100300740250200c01482610301c0000d484020f070014248260040e80184005055543c000d40300b004040c04400d8651500402e043c504907506a5903c003500c1c419052080c001c43c45411508201c108104130032052050741c203a11 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 249135719 1250 249134469 249134477
    0x90f06050901020a12080702011103090a240f0b0a0e1b1b03070507050306010509070c11040603050610090b010908120a0905030d020609010606030b03060a0b0111030d0515041506 78
    0x3140d40c070040c1e01c0c11a1aa40080c014840071a8046000d46e00020306030190b80070345c000b4042c8140403541c3d40024042201c451f1a654403408640b00451010741c90f00d13403540b040012048002960140c01c0e0192540f485d000525280c94500c6101941044000c0c04024545410300c81441d08000603050185c00861a4410150601050b0b00c0007031060780681908072008401100d80d40e4110307240494407005e040c8101803080c06543d00000b030600302103182c58481c161aa5586420000703646c0c0303a42190016111300d5803c80d590b8100400051030403c210b6000303040300c4220500581c60000340d64280c8160b2903c00d410803035038900c1000f075400002002e440354559102d403c1c3e00da603504102203401e0b100719449150b042c844c600d03080d081c40390082010350284a205000348001c0e42c44902c181c0070340d0f0503502015010b0b0310110001e040200d00e50f004448040052604e0f9149140043e0020f146400c01e40310030202030368610074403a0080c03070001000c407500400d440900800041d034440001003640b92207420144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 249136969 1250 249135719 249135727
    0x703090302010b03010e06060a091808160f0b061e0303071e08030f1008010b062217010b13140708070203071211010f0902131107120e010807090f0605 66
    0x16000390400c420b03e0300054003c00402e80140c8241da0303164004c3d14a103001d840170045c0480e1f04c41c964003034807540c14109180c40b81c4c9074842e070f0395020095025142031a802d11107800c0350000a0f81541d030301c40b42940241c000d4007003414030340100700c02a4004403003103006a002c402d0000083d20007100350f414050f000158101c032500030b4100c0032041d10b030110303006081500000411045c00c110008141c06022411032016000380c803800b0240c22a8001642594411001d01030400250444009440c1c091801008401c0c85982c54089940b0895100a0b000c800e9441e500c400c052410b007031480308142d0006850074000200c1d48049501c41d168050004000c020300600052090350003001103405039980001c044078891227204000b011202c100c0c00c814240c0d401c0000518034014140142440b140e00185003801090011115100401c2d00c07450b49214071200384198404110b280d5151020642140c49211896001d8800100507440c000e00f60380501400e440c2c18007200b42d04911100a0f1030072410110b0399 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 249138219 1250 249136969 249136973
    0x10f0509100e010f0c03021213240209040905031b010203010b071e1b0302150910030e0c030703080a030b01080c1822090506090708060a0504020f03030f0a120501050603070309 77
    0x1410502c00c3c001001d9040460a171459035051340105a01c0d654075046911a4403180c40806c0902ca1024000c0c240011408280015031000001039a0141c2d00c181c0042c5088045e00104e0295004000e0a50781780c0c102044040c00c601001142d00802c1240000840c6150f04004000071940070b20f480251070380109410a84d00840c0301a02d15081c0e0b43c0069080c4444584440c0d5040c17014a01d020490040035401d100e60f055401d1101656421036009144010307505815008800501001d20350840361f1040d40400a007e8030188421000b96000d07030f030625503a014000c8042c1c203680154074024100040c980c10402c41d40c62410503982c40c2d00707000d0b0020400c030303105600140c001d02d6a00103051a01003024855840071581c3d92240b1801840b072019038000c2c0e2340d21030300b683d02c0e540f082c0304401d140d400c0100007510320030703c2d42d011a0b4044e10007001c000d41010114046481d640100141100d000f800284c540001c50300800524200d000149050201d981843c0202e1603a01010303240405250700c0d01c0d80901 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 249139469 1250 249138219 249138221
    0x807060906081504200418050f071805060f03091605010909090215120612010203100519120b180106120807060e06100501110d08070c0c1e08010f0509100e01 69
    0x204002c9511700380401540300c01500c41007030744644210200920511030000b85150780d802094454001d50101100315500c0080070380703000a84074a018066407064801042e542e4541010b44000ca01c0e4800f51501c9103405000d00d882e00b42c12414030f00c2c004081080800c03103a030b800110171003640c00d90000400c000400384041428000445408010f00c0004102c1d807468a414000080c8520002c036019a403024411820034200d100c10341e58915425500e445c1070280b420020f0480500e0114007007504501955032401c809980c000e881d04a406450500900c60450b4504038401c1c0003a00d484001c124651030101c2d503449210035004014014140400c11405001a035031184c0b02c1041c4010035101e1500d010304da8514852040c0c056103010684011002181c0031000404480c403d19a0302e50703640d540c85104065801001445048601103074140000c18105000500050460780e01c100d0003640c2c1e400c0c4a601801e4407680e00c0248481840e05003006400d100004468038a110705d00000140190050383c2e86d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 249140719 1250 249139469 249139481
    0x30f020312070e0f0405041106160203100e0601080708032b1d1002070c06050c0a060207060501051f141b0106030c140a0e0c030604020c160807060906081504 69
    0x300188441408002c6141e400904082c0825400c03502814209044020001143d40c01d4501030811446915920142e040600040000381c44201e407139017a0445643c0000d1070000000c00441da416114039081041d0036003041000c3c09040c401000e0300c141800c0103172980d664000d09541000d501c14112219100c0e030701c07003070480c4415840c0715170a00041804909407004110a0344e0302d046640700d10405914604018802d0300c43c8a9030011404103218685501115940c004503545042c034082d580610000170124401403140e148104004103080d0302d03000410814a2912524284c20140c04606030303817050340055148088030160100310385a5924041401ca030080d030940e03a00f41d0398030b440008030910080700300a6085414205820060364031036418046010329611900010740800e0000ca04400904809140d101d40041c00060504143d21303556443c0c04118280b00c4007420450100340450a02881902d000e048a82000c6049520f840b10007480d03080001c0210200300b60700c0308155a145d4441e0010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 249141969 1250 249140719 249140737
    0x6080c1c06081507020601171504031b050105041502121303020f070306020d060602070501090308030a1407030504021e01090b07020a09060f06031811042d090303060e010302030a030f0203 82
    0x25601481c1d074159090020005881c010017610904000086202c01400403a02200d40d020141101c801024003c407040080544110240700070805800c0413208960881c80c5880d000e400040780a0500c0e0506003c035a4101c903450141d42d004005034140e82c4208014150005414848079806444ea030500324217019000c55042450700840030300000b4001c00390040c00114000300020888556144000d80c1e0369004e62190901003204204200042240c250256522540d00350000c00c44901c001c6c86680000e0086520304042a070761400d0000758200122101148a400102e509a681c0c00c0d900103010003540b8800c1c081a2503000030b54204644401100c0b5000708503002081c00015155451090313102114000c960029150440c00311541d5800c0c50364003800354112642e01203418003031042c000504850b84103c10307056080300d14642c00d410050781c03a412400c0314640024805000b8500141900c0c80b582c08105030941a000501c0907913000314040640e1507250418004102c3c0001059007140510141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 249143219 1250 249141969 249141973
    0xb0402130e01020c011b0215071209080301060216030803061c020630071b020d0506010e060a0b070b0127090b0414030c0c1e0a18050106080c1c0608 65
    0x107018032905054010306a15040240240440400b5540308542c00034500c0c50000145d02c224032100340d002c11191050380080c424604a240b100e0200040d0342503503410081151026800401041600e03810b05c00071440040e458000c096052440d01c0c1c1c0c0d94280009449907104150000254039000c0d500000080402d5016120030b40324a00000e034481640d03410201c1010b8400800340903900c0e40c4210b1415407041140d03465840b4407150701c1490180c420206170b800c07a04508800c0302000440c3d0708008060090240000c000c00302c0c5441800c0c0010ae00c03880e48040082d8105108460000e0052129070b415108041c402c2146003550300d540b0b01a8122818640301e8040c41c01500b101030041c0c0001c0039101c0c2b40181060180c201d1000c449699910444007094031a401000d5008070798a07000160103c02140c022111a001c01004000340c1150700c2c50740800e00188850310031f81403981240c001c0a0040c42e1718140a9514035210300119050720034588039181c02805003540718402c50265110038084d14411003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 249144469 1250 249143219 249143231
    0x405210904060f050406060c0302100902010e0909010605043c02040308040b07050d0813020907110d020703050f0705060a21050103080703180501170a0f0524040b06070b040213 77
    0x20240000703e1060040c213000d242410004600c09005d0480d0580c100e916600501c10550604000d40050074011400c9040050030003001d009556800c040034042c520580c0001541803030001000203c0b010307002e420003680c109440700d5011048200c2c5000802003802109290701d800c1c548100004e1040ea000140010790124000c90483c0000001d400d000d44907004450b9040740c03241d001d8802e000304031501d05441030100e4240c0014144000917681010302800c2030b43d0400d10100700e2038100007140d0010350040e03105220400512504000b01140000032034040d042e068242400314685101d14034041050241e44000780c507044160b01101105400300f10f00c02c200b2940c584c5848951540b284000350f0006110540d043c0c5810400c41c10741080f0b0300161034110111403100c03240400d9203801890a120187d40340644441013501d4002c961281c4060381901e54200d01740340c0d64a0340784600b0003d50340120b1411103014119168982154243d03900020140700583d83d610014203050400341c0e4100c400c6003081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 249145719 1250 249144469 249144479
    0x815130204110414040b0604050f03011508150115050910120504060203061201060e070e060705011506020d0306050904140f16181b030213120305030406060905040521090406 76
    0x20b0040c0c800e44400141e04044c64409008001c20389403052440d9034849410041080140760010015114170300190002c1101201e03007540d507240280c0c940c45607082d9081038503c082204003004000b40903050804142c100b200c40e20b0740040141c01040342c0d0030701503c00980b1002d2003601400f414404d68105035002c0c800c0f440e0070714164003c0d400a40e2603078013840903039641e20350310901801403074195401d03000740d16407558a02c1c10480d03a410003110407d8001000300051404908c0c280940704071060f5a0040340790381460403000030704c3d0544c51961001054a001c40600003540da041500f9045034012481d81e010b25080c045e258100041007840d58035511589445a421245034100c1d042100c0c42031080c044000c1c4200c0441080d12818865052001040c2c1011214103000c0d602801c07104850b040c199141584500600e1840c021140081d0003050002c402c01042200f04c0c014000138060480c0d09002604082da0b9185d943d080042101d070103c020640c6802e0081181800d03140302c480700400c14000581c0d80d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 249146969 1250 249145719 249145751
    0x4053318010c0201021b010e150301050f0105160807020402040816081023090f03030403033602040903110706050910020334060c0509190815130204 65
    0x8420340c003850309202405010940c012801d09480603010b8028158200a036010101c500124070f0405051281c00c12095000392503004082000340c0034004034955031b5040030100004c07130041402403410401e08004100c0c0c14510054064200340e801042907403110840c0c800500a4000c50300702e05a1817003012440618254403024190450f002c1100f600d0400840c1103041c810307a0780c801a02c1394030480b003d404007030f0920300113140750780034011406507801e195070610544e007103a01c19102030740026268030302c00000c0702c0d4000d0b241030103a101c4540e80010080f05c1c002403c0005011300701a110f29035514402e414180034401c6c40000c580c48406441145850b040043c00c0364101600c40d13405000355880d0100018000800c031803440300c01d11014650840018074071102c110150f2052116440c0c031420303c03000142e441c001e4046000c500d444442c0c0b25002130040c41080300d40d044582000721320f404000c2018030300118000702052a400411005c5965800c0c001d62048507070a00290001c2c0f070441d00c1c015008074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 249148219 1250 249146969 249146977
    0x90904030c0b10150806030304090207050a060b0d030906050306030a1212050901201c0212090c0102151819120f020309221d07080d050708040533 64
    0x125802c01d1100340c0b82c4880c82e040340d4403540501381c1203501d094640201540180349003940321030002d04581c509900d5141a00136a000240704540540c400021901040198054405441410fa03a01c000c110b105d034070f00800c404030030711914040c0080040851802e4600344882074005800c42c404801c01248030000500400f5080000d5201620f02404949482c0060185a113080e1001c01e542003640c00c074500382003007644003521071144946a03c644203124030190011340704071482e4560041c5c00740707003030426a820310150540c440e0440d0080d41414084c03910880d00140c000b2034451503281108003c001d4603262081c0e140942041c1501913186004000e8a0405140340d00c020b40c1c5c4080000c003950300b042e0b81ea405204803041c0c0c4a00300c4002088174444a22980c682d0051100010034410903a40314070700c01080130030841207141c019010a0002020412090a460340107141c40341c0340c90015150400306d40501d000b5503109211b45502c000c41c5500103900e400c100c054002903059001d1441a540707101c0d0740 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 249149469 1250 249148219 249148223
    0xc09031b011205010e0f1018050103020f030a03090311031615030c110c01030c0e060a020106151718010608030a030614090903030712061d04050106050405250203090904030c 76
    0x40c1c00070404031000603d004050403074011080c291100d80b84c0030454100d60034024001e882c44c0644040000b6a6070103100d80c84001841c0000010303041d415801401104000544800d000303500000d1782c140043d80c010442ca04503500098081f5001500070002410100306000654824104a0300130400515040e66402c0010541d20308018021090f44169078021022840c002150403e1800c007415500130b03084a0720b024420300e0031000f241402d000107a2180c00400d080c0e80184c1d541c8005000f140048640702c0b48086d554180b0210206444215080b10381300107020562114102c240000d100c8000d421050103000702d402507075100c420500c0020010300c42c0b0300c038807070428481ca200d911381790038400703201070140640d0780c040d528660ba4004241c4540a800d0503104025548074000a000c91850981000c00c11260310600701509090900328295022901710074031440c40c0c0f0051100030a110800311001422041170301ca40c00e0041007042c0e0450240c04285074108140e8000c010406604c2445107540718 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 249150719 1250 249149469 249149477
    0xd03090f0503010e0709051306110a120b2b060501121e020105090d2111120c0d08040314030c0d1a01020730060b0a080a0201020705010302030c09031b01 67
    0x1559950802d4280d40b02100c8880070b40e00b140c0824001c02c000c40d00700036480016100d90816130510f81d40d40100301c4600021901c004000415252070440d4451404141240d80b00c406000640c4036000150004080140d10b010480c031340c0d80c3e4100742d44ea9820108107001d4020004004a41c0c0d80c0c0d4140003030210196040710209100a4114141e030300245060b03c000b41c040e540d55007410281000e100400202d40030542d010b2450418071000030901100c1c0ba6080004c0313a03266903603100d8102c820b62402207960840c1060349010702c900c0c041c000300040c000001002c0c51074258055100c1c1c0c04c040d20802012004881d032240000100900501c4040092404868500e820040c0e00038030140301c002e100c20042003a00603004003200700510050414090800817118200000740c2d5001194000c4450320311604942b9240ca034041050b0314900020b500006081104c0588441d0030940d0000f900e07104207000b06414180e01001181d184501c0e00196861503001900325005c0c070b201c030401da52841241502e014005 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 249151969 1250 249150719 249150749
    0x2414010309300c0c05010302030a0b0d060c020c0307080c01050a050415020312060609010806040506030f0a0c050f0919051801140405160b040e07050c0601030f03020d0504030b13110d0309 82
    0x1640c401c4031075280b690b400c00e0b100c04904e07041800441c06540003411608109480c3d0350b2404180d550f0512200c2498844c03d00000e942482c0d04020f0704243c503803c4068441c0d04170703420412140c1000304c1d1000b42200e09107003c0c1d94405402c2c2c000d1760035000360741044030b0035070080a60601058001001301000b86032482a85a640e441c181044014400e08150600091212021600b141440d81005401c448001e040d10308400503503040344d10b00486100180c8000420000810140c1440b01e9020200c64080d18460202e103402c150316043c00302d11b0030307046451a60b2000000c1100e440301c03a540c0324212810000340014100e5401c19031700030100b61003e4a070350085000d41500041000c3e1742c0801c1702c1d1602482401d19103024100000d01c0301c0100b00b14140902001240c4903440e0a00045028511940e14042d2402103424000e01d0706c0103241c55903003841802c220910200743c4400c4844c1c1d11031910110108051042d26003400000140c0702c0036501310315014214002c26800010b40000d440c480c200d081c1c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 249153219 1250 249151969 249152063
    0x80a05041a07150516120209031204090e0601030209070c03140c01050a1a0d0201230309030a020c01030504020f0d030e060d0f0f1407050d061e05042414010309 70
    0xc840007500c0100c01d117040b006807009502d0042c0d05040c40860041c070011700b4506540c0110303040844000148103c004002401d20844103a849a200a00c06541c001c01c3c0c90742c150b5010600301c800140444080c4081484814201403242d08101c18404162045076210468825400e0180009992a00c13226003000552040c2840b0f150300103034070740002000d00c030303072040c85d44c00648801c03903450420380c81d4040c1e40c608440020b07000c20095000d201e450005503560744040800030304080030802954101405c0006001c007590342c1c64048480c00d10f0441e2180d44c545440c1c5801d86080f00d01a90b22030b00b081300858990407200c7d165000c03114180580d6414004e144d00050701008541c05075034031a09551701800032505c1c3c80e10070006490f0800b4002c00001d42140ca80a4029181d1100c0310102101c0c0c0800c941401642443e015440c2030a0817041d0210310b03e40b102080b000041d01e14019081e010402c11100d0311660710a401121030103810a0500301c56003810030307911070300b81c801c42140054038140940b5200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 249154469 1250 249153219 249153221
    0x70503072907020f2e062d0e19020c010c050c0c010c0507140d05120d060e09060406020a0516061b0207080c0907170702011e0612080a05041a0715 64
    0x34120310150160690114891001400c81201d1020034814590a2038003034242d1700701d100c2d28010700707450780c142215065910f4403240c402c044601d01e03d00001101c07100b0080c00d0b000c95031564101c8003405410f206a8a0407000d000280582414400198240b81e140400c850700080141a100d80403000c0d1000b02016000658a01c030030002c00070300d26806594108100c8207190120307501804001e01d1280300d1100ca403100303423030b100001800322002c2c140001d2014150805207e050020070090308500002d180c200402510303140000e201800b16500056043c0c1c006205d42c00302c03403c14820940d5000c03100f003d410450000c15203145030300d400c540300700b011004281c0001100801c46195400400e08002400b003407012103034001c4e110400748180030003201c500319201c001d000d11078182a8000142c4e0f00c0b00710300c40081062451a162081843c05100740030310703443c03c19518450303030300811940c1d40e13603a0b00c140845e0395115541c0720b1004404d0304408032500700c8224008043c00c41c00b42160540740b042c44e100145c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 249155719 1250 249154469 249154483
    0x131e0902130b03060c0a020c0901091523010309020402040f090506030f190f020a1a0d1508070b0304080c0f06010611010216110a030507060908010e03040e0c07050307290702 76
    0x140c3c03681c0018009125005204014440c40b000d601c140c402c3c803141080820410f007001c4e00155445600c566400c11000c0320400c206008010481d05144076078030203e41e40d01c024a00d01c1e4918101751b00c9440c52400e42d180e5404817001001e0b20000929510342c1d42c0802c900514041c3c0c1c1052090051b9504450440000900001040652810751240f1240d980c1c4002c8025079814040360000f0303140f400020043d1443c000c43c0d0b0b02c00d5a20141c550381b0b00031a4040c4040f10146481000c10400841c01400a48030025500c0181c505041406960351100c6c1890003050023884042d880d54410103001d081d0070b0030007042c001c1c100c1b20640c44a0709039221903490300d4244d000709140e4800000c901340e2408089101c081c030072006854090030115400b5101d8564505000490b04940c0c08118004c3d02041100b009214900080f14513001a5007414180100da0820b0b07000a01503d1441c400420b869051050038030403960382903484490303036404c40c0f07090000c0c41c2c0460085184040d480c2e450400540710318004103445e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 249156969 1250 249155719 249155741
    0x1020d0501080703020f13180602040302100816030c09080a050a0203100506030a0210110708070f0611030f071b080a0b060d0506010501260f01030212070b0405131e090213 75
    0x50140c00001001f44200b0504240042c0b04c070544845444680110820191809600034a005669141180144a04580c16847c400d0400602c00700304050400c850220140c010614607011508840209c03044030b070003049403c41402c5001c1c6e030060f0820040c0000c1c2050000f40300360292540c00500c01d54500072143e08441c0c00307401d9000619410300501d030200e901c8000c8aa24105089405139095505280421580001145610085003808203103040e0350303600c006000c5031400300000310b05654083d032071340184030303890200320004503c071400c0110302c5554080d07503000c0446d200c210b0380c0c0d01c2d000299036078004641601e8000440c408600181001200a4a03060b0404002e0a0a0b481d1400440309440542e84604040c000c03144440c2c0c900d0040110350b070044103202403001c00c41d4114010440041c5000020405a40c800f16080040c0210541510700b183c01c11607031440d03141d1500010502034410100300d01e90107186500c0e04403031512103920407202e10f402650280caa85207041d10036000c4034a10199 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 249158219 1250 249156969 249156979
    0xc010608070b0315010521090606010813020604092f0307090b0406080403141c0501081615050304020303120112050d030507270906061e0804020a03020105031f0801020d050108070302 80
    0x11304507a55010303400a010100302c00e80d07200700b62034101c100050b01c4036054030381c1551600841c007032240d40e40e404165260002c40010002c1146080c550018986118034442e0380788042d01c4842c8501508900b91000c1489115002600c0003e02e02c50036902140e4411204400810811000455256002e000703850079190562211400e544079520140d84180c1841840001084208480e81445e075158504180e0030304420b20100741d80d41020703401400c00c88060482c500000c81c04004004800c0c174080030021400e0141003140e500d0f16580082800c520a5010201c6501111b10001411074041e001c0c2e1a2101d015006452074000c421000b1400d13100d055510030b0000d460343c0701043c4541c440709150b0031200303600c00c0c2d0010460b694660580c1550f01070740c0316501060102e01c030b051090300100d8110346100d00e503140c601c0c043c2c5016030029000c91080d0001904101010002600d0700c08440e282d12203841e0ba9210800300b00b0b660340c0185020b507020452211911303040c100005910080001c049081d6940244 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 249159469 1250 249158219 249158251
    0xe07050604062007080c13150b0a0c051e0c040c080a0209030a0515063609010e0a050c0a300317010603020306090606090904060b0f060c010608070b03 66
    0x40c00b10348080544083c4140071450880c0c03400048002c02443e402484031402410041116a0402441640020340700d0341560400e4022205104070102c043d003903030382c580d081540b2a42e40c054102d5600c6200341c0c00801c98895500d210050444e0200300750180340342c60040b21902d41c018000d101c103444802d68807901007099200400d00082043d00604200000a01110048400c0e40c0783c01d0b10f0582a640c10600d01c1c40040c06020396410050300111403050001c0d1038001c030a00701b50b9111440019000b24240b0481c0b003501242c5105000c0d0001e04c40740403d0011104030620909003180c81e080c0c0c104545104282901001400440b4002c030200c800311100c440420f001461401c0c0160103403c0081101000780651318403c0c011742e0001c80a010306000c1d980141c80c1d00d040001d025001801600300c80c86050b0503c1104104d03034461071456440b56004102080e102c0480c800718010740700c00801180e0200022485940b4080305600c01003ca0b03041c4030440e0155640c4594202c00c80c40282c0303126a607100014 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 249160719 1250 249159469 249159479
    0x506010e070e210a1a0907062115030203010510060e0a051c0609211b23030c150a0b01110703060c0210020406030e011b052b09080408010e07050604 65
    0x8a0f035001d0604900949107020b6050f996600c0c042c3c800311104211001180070311110f583c4c104107000190181d4246006100908520b06045140010110694540798070a14021070408501c4100645d0301900900840c1481c1055103102c3e0064014440002c032490000c00903440c00c0d0340d00404071074010305512424604030130004e0544200841c251780031904c400d0305200045800a04407040140d480a6007200300f00302100071300c0c1c1042e4266041000001e001048041110b00c90707219040070380d80c80d000d000120440710341411402855500360650140c00790343e103003090071483d00500c603001180c401c0240c01407000064400744084102007a10394000d0f01c2c10b000144496010000000c401c0c0110703041178030500480400c0c2e80c09a0082da00080e01e0b03d0350450840c83c240a4940d0210134480c2c015010f40e44900010b002c0d010b01c180142d50644c5a001a002178003c001840c0c0d810840d294082c0a8201c02d4200380c40d07590310602c9041750035841c02da1101100c10020030000c069070340c014980b501d480c2c646 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 249161969 1250 249160719 249160759
    0x50103021b0a23010507120b0111060114011e0806060f09090c0703020f1f0c09030f0602091309030c08091f0306090605040207021c03020a06090506010e070e 69
    0x40d124581511488104481118030810203260b840b849400c02000c20300090355030381892090302e00e8546007070381044140b2000c2a005480780a10b01a80040043c1d040c0201d00121f0f81c00b00d110b150200c980c05450000f10703841e206441100d42100c07082c1c0718400c0c42400c2e09541c0707400d0180540080001400d9101150341482c1c55401003080300c402c4102e1908082c0f00d0340000704041e4051780c3d07080e4a4440010b00b1820140c050220000b02c1c081c80002d84041c0f1100100c50030240700d442442042183e03105204c1a00c10300448801c005140c1195a190310b50081c0e2400a00950110709510311a000081d14101405154003500c446240e01d0baa40204496240d40c43c3c0259800003072415602c956041810704282c40c91405a4200801541e4045865803401011070212100740d040030b802240100070010150301c0c0e003030355003010a14181e510454581281000c90a02080e00001031a050404050b50700b80803001071030905a800910003660030391101d400c00d442c0c030350303000c0d40740c035040705115031071491140c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 249163219 1250 249161969 249161977
    0x130302010806120303090607080705030f04030807030608030313350306060f0705060a060501030902010804080307090b030a0207120e0d0f020303160503041409010f0306020f0918040302010b1905010302 88
    0x20300740c83c107001e0681c00d040f411500700701c402c071407594001402c115449521600444c0c10524600b0a240f66041010300950840da0080020703060200103404503006a00c0780e07001c0402840c002055a80302d00b05410140e00954494030282c81804640c9410014809020cd01c001c00b81c0001c02000100400c011a007220340c0c00c02451290702c82004c1c04141e02c85a04032005200d42e5100340d010305401c1c039002c49414201c5d1a260002c80c100b500c0c0a02440045c0d8001c0d420790b4205400c415800e44030f640b40801101c4880c40c81c1c110382038240e00070051001019417038001e048241d21501c4110f14608100303004840b8403001d05501c81e40300c1d44109802d000320300a0106c00cd0000e0016040d28689001c2c00d00030351321101c00302c1040b6041d0344001803c000b610681d0a081b00780040c116428046949403035400c002c901c4d628040070740396035400502043d00c1340c110070407900319102c09410050f6206d0003202d41702600c1021036040d0059400e1515030020b918040202180100b82898102505070503c030044009400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 249164469 1250 249163219 249163231
    0xc18130203010b040f020a0305012c090109021f030c17011806050303040f140301110a0809070f03030c051b1509040603080f130b070302100b22021e1303020108 70
    0x150301c10040042d61504d0142e0603510128800c01b6a44510307510004080314416401032200105607034400c0d04104a500e4090104e484000c080b120f96181c1e07480c214010000d80a000f54094440c03820a5014012500d0080300305069460400000c000a00162070b80314a03003a444015019090040c0180286103030f0041030241200700c00aa1170361a240803920390780c4550481180440c0e440e10070018049600c00b01464010107800a10007002d00765003103c100d000d4004101e0510000100103806e5420820520f0b008040c143d85150100c1e5903414090034000100c601640c0e54081c032a0b070420505a440c410302040113000d0178001000e81d102144800f90340040700c505611540321440000400e504c10007810102654404107035a441844001d0a001c907a140d0011071000000c0c045000420f40102d460040364a43d6240824040340e031900150286e0034240710012a40c150a1628150000302d41c060a9000040403025841c2030101e044034081e400f07001c800851040540c1c1c03003400154030803070500703400031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 249165719 1250 249164469 249164471
    0x114060a030e07180b031b0609060c1b101803080a180b040608090d0e06030606040512010606090f0308030415151d0105090f13050f0d110c1813020301 66
    0x1c4804626800c1c43c410751300003061651030383d00b9404070b0741d894803c00860040450061200e00d4080081d0a0840d2072151001d104e0000442c0c5070340c42d61103140841e16040c00d04010798200f070007840984408100316800003400354191003000c00c9804c2c014591000035800c54036926503081d2a50b81c40f690503600c00b02c103003000c00a11030424074100b100201c0240180540013200340d1907a0811500611040d8010040c208540c4018000e40344507410080c40e604a0009855590752603880c82c010424611482d03202540080c21060724001250041d44070406032031441e910300c0042d9a9480d00340380c120a0600000e03000390f0040020400148070382d50110182d07118a800442c4c410004003000719000c2480c7d204c41c0c400380450706030205043e50700d031080d405400308880903c05400c011840b45801e04009044020910301200404107201040048614003c40b501c11140c01081c1580018584d06122243c001548a6221900c45034500500304004644008801c00c0b032a41e50507107074140035662803105903015 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 249166969 1250 249165719 249165731
    0x6040e030d0c09090c0503010b041403011e140901020301080c01030e010e0601030f1202070b07030302091504151e020d0c260901020c0d120509010905040912170114060a03 75
    0x184089005940d880d600030748404440901d0b110704d444c240c4458940c03040410a007040144030082c40c0c841510700703460040c90360044803040140424010042e0401900c40c80000711054580304046d80c104105500d0716840c40401c503160034816074240c1c00207000d9404141c001252412103540300742e1081c000c0b44044000031810b031003450400b17810144280c0042d600c80030305810b80c0040c40354100f41d5203124a00c5100038070155251240910460044900c01801c01d900010018099541c1201d10390707000301c030341d40c0c3d03140c1d916074801501074814031411841001c1246c0459220810240000a400c1d44031150058a45500000003c55003070500141c111090402e070b1a4500078956030707244400c91201107203815569038038854000b9142c9450304007440e1141035080c40120014107448083d0074ac0328182d04109031510076846c0140c40c0c01d90306402c00d40d0000c0c500340d1014140300143d80b0718034040d07000c0d440740c02403210000c408444010742405502110b01e845010900941031250007480940100e150014803 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 249168219 1250 249166969 249166987
    0xe070302040204090e070f030305030103080c0f0f0c0a08060c0909090f1b01031a0a090b0d05010e03070c0b070b070c080f1210150206060909070314010507030f050f06040e03 76
    0x300e07040f54000100d4030355a9154010703540800c102103405400300302680480c0c1480c607503000306648414000104034003804106196240020481c11509044640a031a0b01c21091409140c0d24034550b500e0303a2094000f8980000c034008040f0716940280004242c3c00e107003203098004c1c441140b034083c05140280c400d014800c1c41c10007003801808444001d9114030040484220001400c2d502981084035590031308400030603465451901e01011210041c0000c900460054005070045981e844003174800c0d4200b9040085040d40072005000b904e11421040100d103484840c0c01034240a400d800810071825440851082401080c04e1500c49116020b12403810302040744c00105600a00c40c8041c1d885140010b204190405408080140c02d0981100300550840390b0025900c11015005a01070782c24040412030411040c00400091a040581200d10b01103c00e1218000d100c02c50740c8a000a02d81001c05040700f00a000e690f01411a9255240c0f490300c55600308030090200010105003480f041001402c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 249169469 1250 249168219 249168221
    0x1a150a0504230a1401050604140906030c280807050604060e04020d0f02090909030a1d03100608030307031808030601080a1401140108181e030706140103050f0714040e07030204 77
    0x40f0400c03850f031000c1800103252843c1000c541041c0c200c9441403078140428010700302c3c01c00303440503100d50403681c40300b45031505004682014128800c858002e8603162070010300440465502c01700c580c4030856240c01d80d030b0b2182c15a8031350b03010703000b5181c0c0000c0810042180a10881a82d4103c000041c001450010303250070100c1102d641d50b40300030a081c5c0100d94408249081010664049810740246190800100c40140080306c550821140406c0f00b003030805032520200000c4590085c002e604000e0300e500c0340b420030707900d0b04111905000070b41099880b074814000740842200e16030384032407010f0440e102c3e00f0064480d640300502490240783d6500c1e06842002d6440d070000c6c02810b002c807031646616000e030001000540000d0090700c61031503a0380c80d01e400644c001014001c00d00c1054038071440c05141c00e076040c00c3d4880c080c0041c04081c244031074000d6070344020a03054120307072040e0300b2100e1505068280949458291140c040d42d0481d04a800c480d900341500400240307407060064070405501c1380d002030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 249170719 1250 249169469 249169471
    0xd030212030405070f091e09030e120c1c05070f081005071b030906020705040b0303070f051203040c1716090b040204030506040b0406111905070f020306041a150a050423 74
    0x1b43c4040d01e407079103600301030b220b010400300c18018810280110354864030007820050301d0f401a14003890010400300c242a00078000a202200f008040da401c04603c0100803251248000080d282d03400f861034001000862104000219126100a000d00c0e070410031040004140050408042c0f1402c080501043e075564032850846500c00c4d100d040446051130402032401c0d02c1c642202d03008600e012800c0c06d0596000040e12601948421ba01d4803610076803521604100020f90040d03645503000c0280b00800074000c40391010707240044001d10508258402842c1d40c0c0c075101c0c810200c02d1b4002102406081e005800001c00020301030400f520f060fa903507949030301d411700848007640e604050308103100c1006250301a41c048200f24482890401030302030f00c0e940000c8050080002440000215501000142c000e40d401d129001000d403040c41c038290a010360000404bc451031848210440020b0382514000348003414440c001c0d120700070b0f9505100c03d000c0146040d00c03100d8941c0442d03030000200444460701d19 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 249171969 1250 249170719 249170729
    0x80a0b010806060301060605040504180c090509120a080708040201090b0c0114150102030f07020d0206030a09020f01030c09030809150a020a030f03020406120510091107050c0d030212030405070f 85
    0x8902198035044001d824442c01801503131099061900401c10140e01c0070035142518000c0701d0000300384070080c0c0d8840044240490007030110360300410014171284298009071042d04400251010010f40c01950012031081c0e0002d00081040c8034049184c0b10b100d05156079025106042940341c3d50b4540810304600e0f00300480300c060f66034680d031f441e03065095002009500300314140d00701d9214174603032070001c1d44034040e0103a0040260400f0601b0f80c10f55603072149003c00190040c11081e40c03424100c00d00341c043c0c041c3e42c000703038044d041d00721482400b54824820303070700340121903a69100e80c50304503030761610316900c850031403540210341c0140c0300102301001c40103000001d4030350004c0800041a14018100c0c018000c400f100303051041c001040ba0540142c0c40b20705010022900158560f50410304100e84040b0790404400b2902c0c042c03406608829610041802c140038008490a58100c3c204101ca240100e40300100143c01881614624000e640c0c06035401034400c50545480944803110a031282c1419882 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 249173219 1250 249171969 249171983
    0x2072a1a070c03030809010204090c030e0c09040c05010f200a031403040b0c0706020c0a03030204140616020405060a081209040507030c0c031407020a170706021c0e0a080a 75
    0x42001299110030210300480039811600e81070101d10b0b01c0318074003044244405402c1c00407800000d11280001e5040710081e006000080100414005004004003c804000c640034440c0541d200403502d8040140c070310076139106085c1001c0600f41401168601041594a018411440b03000211241d030803403e070500b0a0400c009000700020341c1802403081c540c403000100005010028800031501c1c43c0b001661090301d0b1500c650381d070a07091074008000d10410740200064041e5020150815a26400030310841d032340f00c0006001119520f003000030340c2c4141c90074a4119a002d001c0e8900506260b0070481d0300401c001c1c4550203071030f40c445081e81042c112030816011a880007171111030303034030f0907202c2e05400205a150800400c00e003050098901414404068203100094040c000900f200c2c40880b6a84d542c05450260b00940d245041e0303196960545441c10389005180003c81c1e25480022080e208030744410b000b010184003044203403550701070883c038240c018079030242c04244c041c0304002800e4900d10540c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 249174469 1250 249173219 249173303
    0x906040314060f0c0a030b0105120a06061806081306240315140403080c1e040503120705150a150b070501050a0b03030a03050c040f150801080d0804060207 68
    0x40d072142025001030489646080800c14007400280b140107481c1340d8842c03800c002415a10351801071741d0500030b5080c00c0e01c1c0d180e5030038100600084140c1007601110b2a030341740c4134003241c01c0c1007030300d100c40110b4001c0d0b900041d1600d000580744c01040000301e0216024030f80006205441403900d800024181078480502c0c3c422076010000c000c000d090710b00803200792080030805103c0d4684610600c0c1300c068005002c00c00410049030107824840201d510502034a500050030070010700486205401500c00c9900c2030152610300461140351000700d43d042540170020300042d40d036024079240a8040034001c0d031001592000ba0701e80310501c41c81240701504018014039220169407400c1420340e940100403001540c1054845c0b42c42c0e44002050703c0c14202c0505001c2031650320307030407084a94021540301503280c0c81124170002e6603990300c0a4000600341d0075a20a1007607a01c94a01a0340c0c2c140403001e040004403080c0010f0701091041d070190004602c2030307404400040108861410400c0390403d0549141c40d003072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 249175719 1250 249174469 249174503
    0x160c030b04031202040b180102120309011d06010b040513020702040f060513060b1605192f01020304030212190b09100b030a06020310080304080313081606050c0309060403 75
    0x4a0160325420000b5055203024141000941b090080c140f03035804694031140140d419a00a2000000c85183e82c1096501c903e001c0425601900300035030407212403c070403811064690030100d1010b040c3c03900c52400910303091500040c411611150f0451401041c0c0c2884074500683d643e00485940d8170766050007244041c1000104002450b0b03a00502a0b0f00b031074103000304281011101502c0f44141c2e0000002e640022030b06110741821399840701d030401b0140301c02c1c40d581000b6960030390481c07040607a61000c48402e00007101145003612481d0041c007580c424003041006241c04045021119000d0f41915801001c04100c11144070b8240000c8898000140070481c400004201c4007030403001250342440a5a90700c0c001c25201da06100025007010340000000d40078090562510008207034100889564964804540740c80341c008108030400700001d49000039041c500060900301031100007010341d0449207005001d6820398482418210680014424242680e8420015200139809190781c5216417440c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 249176969 1250 249175719 249175727
    0x305030c1501090209100f1202190807050a0230120601030b03032106061b060604050604111219090510050105042a021903051809011a160c030b0403 65
    0x580144070f22902c140002841d90b5038003001000703285018102030200f4400f41c40300301e0b0260300582c088041140000344860b40ad419010320754a10303802541d1043c0c07842d150414116050722500481c1c2c001a841003200080429904480303410151182c0f105000c2406650b50030103ca800840180035044a0304080103042d503054050203207100800c8001c0e5242032040700149003a00008050003d2941110001030140d031100c408589111000001100b41c90f16400600e07651400c044130a540510300303103800301c4c4c1141014003079241c404040320b2509040c0040709103920012000240950310400c007079002041c020f1003130312482c40e085005101400c0d5600440c80070b00c1c00c0c1c9034180d211034081d5140c10051544180d080e0441c1c0c100c803034107142e501ca0305d030410f040c00c900d00b07e29107152000807548088403004040c3c0080003003286119003982d001740d1080c680200410b1000074030805d0f041116260b05543c1501d80d134230040c03d15203030502100d00015002e45a503034910f241900f007184d03030030700e1081400241504 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 249178219 1250 249176969 249176971
    0x906091c1b0f06030207050313031212090b060405040303090b130209010e01060c02010507080915040e07021209041512030309031106040c0b0705010b1905011403091b0303040305030c15 81
    0x80c0040010700c01e141114903194200244940f030205503010030701c00308105061044802d00201003885080140e102c3c142045130122420032030010402607011800214641d02030340c08500d03003081040358242c2d20601840003402c0018400c4003010b03550290000041e55056045000b5041600d901284280d0382c0306001c007490041c0c104200c0c1e081c91030010080c41d0760017102c44020540c20f2030410381300c0502c3e2411640d01d000b4522a264001454130040081801e15006803049501c001c44502c41d60310340720411f9850b00c16229860700c00403c01c000248260400e0b400c600c4600819410b107050181d80c651768884d00c0901a541280025210800c0c2001c0c150b20020142d00702c0201e2024103203a0a00741d940e00740c190150b2060b10806a40400d01c0c5040c02002e6022200e0f01c94064002c052180d000000d01001841500405000c5000c41c0c0500c403001c1d4108003600c1c4660000802401c0d86400303644502c07055141d0b80ca005a26200401c0302200064051028005101030745008000740300c0d00e2504a129558 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 249179469 1250 249178219 249178253
    0xa020111040806010b0702060f16060c0e0109141302030901091208010f050108071403130606060c1509140a03030e15090a030e03010b031509010501050f150906091c 72
    0x14280424000601c0110f0b10504403015a101560303650414400310742c050040001c0000150408203585070700401d82001d6180c0305119820422021280364005d4901030401f4265500240800d0001d0048400e0405d102c10405401020061010340880d682c8041c2d03403044071000b50603516100c26204000089a01d0b1405814504054441d58104448405410403601c10141000061000305007018000e180d4180810b0000c00c41710703942c2c9450b460310f1058200201080312242d00e02440026503502c514000e20314a5480b00c54070100d544145500009008440800e0390064090342503450000c41c10082007046030b11903203000c1541552504030342e0515911065900c030b0040354604101a00d2400714240c40c54503030608120344440c0a01000c00d0040400000680e0144240e43d5481d40310108a103203180b25011500c024000c83e0388510a01c01072460039544260001c000c40b11122980b00280e020701586ca01c040c0007982800010030004109182551502021480e17110602c000e001c00c00b0307a4091444 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 249180719 1250 249179469 249179501
    0x250f06210b150a1214190c0318050f0d02160302010e0a050a0e0a1b050a12150f030606082107060b09040f02030105060d0c091d0f010608060a0903020d0302031905010303050a0201 78
    0x46448251907075440344003030460041940d43d860340c031f51460103a84034400d03203200c09400040140552074403903136032002e007030401003140702d003080d4155824800541145240c5001001010052450f03006540c0c202c000c1c0c40301a88200860b102203160303194248200b0003022b24508880145c02c0c1324011100b1102010591025000701203213002d0340d04e4215084551260a0786446215030ae44006111700030129444410a02c8000b00710018420200c160502e0a07039010368070411075a0307540e52107a0740d5004820781400110003154241541801c560002c2c140b0940501800315071648010300140007140222030840e50b074003030f408110003076040c244a1243d00c0f031400e9a00b04030300d1165484c1c040c1c1454a600c0707a20320007512400d00c40122050070b1a2111500b03182c00c1206c000585c07501080c0d0290070a401940c001d07100c0c50002420303c010764001c440030319402d074000d059007061441c0124041c0d88002c1c5100048598407840701c0b0038451621170ba42c0214065601c00b61210420480242501c07400132082c5948 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 249181969 1250 249180719 249180721
    0x6180303041e08070507080c0109060c050c010c05070801020c070e01050409021305070306080f0a0308090610060f050c030c15150303090d05250f06210b150a1214 71
    0x40c00c0e141442d9408801049070400000545040394081c41a644c00605a0003140400162140c00003000035080e94241c0b1440e54003901c604007100c0c40380d21201d011307200e40d0090003050b003654083c00b00012480e0256068400c029210040c00e826644840301c02105541b00c000104840303e04000b0240c05014200c0b0309000c902940e8000540010780c00c140c101a280d0307500c0c04503c03401d000b58044001030074140c05442c03000da003d042d0180c444401550a4020440b1440090050340020036400e1003040c2da13460b507031880c40c1401c000321000c141c4480510103000d03040005042c00d1070204003400e5080500001040e4644440c0d001d4200814041c2442e5003c0555204034030440d40c1c0407043e1140510700751011040004d0909102c3d00c1c200101c2d0fa03000394034546111001031280320301602000c2d90b1041d002e2859032907445008480c25012a0000701d01e0144481d10102081416042081d440707000421900498111105500d40ca6202d6004200410584000d0000300e011a01901d099403145d601c076613a003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 249183219 1250 249181969 249181973
    0xd0c02100f08150a0504090f0209100b12040c0f0321020c0f150d110a0905100c02040e0a0803010f0806060a0f030f1a1915080d11100203090618030304 66
    0xb11180502005aa1003007051642219250181028000c100041050001070303840d04040c0300091420b08103074056030100c80000c91000b09449054200c2c0c548040062800c804000340c0381064002030300448900b05103900008103603441d4800440a5402401440d403003454500341010140c080310042010344d0010880121580e8030b030b5969800b004000c3da152028001c0c1d0103105034080c0710b071903210380e03480d03182c5024200001e030184080e0041c0d05140c0c0341d1011b590389034400c000b19050629000d10014400303c160b1401401d250704003010980780101203401018099440c46213076002600201120b6400d040208140c0d0000c0240d82d03001041610081065400c1181800342c600041c08003400411a0060f001d0130400300d01c0452080340206e804800c0141004d8800703146e80c500b1a07400c0c0c1041410105004098083c1108410403110380780e0040041d284440815140c891402c1071000640c040e0705689950048035000552151030741e903010b408546009000d01e6580c0a13035155120b005d40c028010000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 249184469 1250 249183219 249183227
    0xa17060a030c2601020409020408060a0b060714150f0703060506070503030408090102030d0603061e0e0a030818070e091509070b03130203030c0105042006070b07110d0c02100f 77
    0x2c181c507001d140b00b51480491071405103c8998040c034070a4030390301c002800240740d43e40f135001e803083d160b502c4159511a00e468119030700381c5908143c042d1b8031803020804840003070500c0300300d0583d500b200010307035070304445060768a84100400c5410046201e01c1000f044200c5030b05201f0480984012172f1741c3d609004950700c50715602e0000034402081c1080000f00c0440e00da000300280c80c07102e00e8092080c4011784c0c41e864107201034181e0b03c0140f990030729042c1d441e040d141d4007401115902000d480003440018826202120000030140544512100560905020107414450380f00070f0440c84098442d9814001e4241e03207480004091451202241814040500b0005c2100412520581511516510381c500d00b29034640d400380d00291f041c440000e44500d48031042d0042d510907405011402440d41c480f08015454041d160151548000d040001d400000c040c00c0595400440c10b16050080110f500c440d9440e00d0300c5c0350103180c082000c40e10000704510305282c3e00407120400340340c80003540c082450003034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 249185719 1250 249184469 249184493
    0x50c04081b0a0e0a020a020106090b010509040b0109120602090f0306040c060309030509120d0e1507030804060b060310090f0b09160c05030307051c020309030405010804080405060a17060a03 83
    0x3160002030002101c403266201c1202102600e070100707542c6101c2c241000054000d41c8007a01c8070b03001d9401c10f0f00005141c81e9070b00c9402c07201c5206031509480d00c0681c0d01044010020082d41e41d050140c180e03000304400581c9110305855602c40c640040c2d8644d006000c1081d884120042c1764800e074400003c000c001000c005046d03003111150308000c0340d0703000c1c0f524043d1054010803043c29049030002c1883d842c0300100040300e110104c80d40d213032800000195000d10441d0080090303c40c000f82002c202d1280080d104101060340580a6140044d08814081c00954030750b00a55101c04000a9403c080c0300182d034901c61030341c0d14040300d441004011411404030b004040300a018103150704040c030120399506c1c06000044650383e03100c0282c0e903480c0b50650000d0020b420042d0100b990010f00001e51030a0245882224001c001101c000c504051400e401140c808800620071103000e82c0602c00021940c5401000c3c00c80c0d55a41d44600025000303550303280500f120004d0085100e50010001003000c0f405016044c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 249186969 1250 249185719 249185743
    0x1d0f0f060310030602070b0621070b130504060801050f070516080c030d330b0301090e0a0b04030201060512010c0c0809040212010305060f0c0307050a030213081005010504050c0408 79
    0x4551a035440000c10900c40b012035002071300090000401c54100082c0340c072000d11908040758040e200000c0914241c0280e03511450b1030700f0075401414144051030301132015102001500c0e4040c55481d071201c002c0340c16245070398400e80c02e07a91a03405020568110100280d44002d480c90001e040c00e40c08201142c190740100c0c000f42c000351002441100302d1700b0500496820f440010414081400038502c040354000705030444c840c96841c42e0002d019140940001001101d00c916555030440c1d00301864440141107000d2030b44000c0c030131411070b01c00103018414440d200c0c40c000d03000003500e01d00c0c1409105440da25203000c640c11b40d15045480c0d4001c0e410090000300b00e03401c00d03001d586030a00e03a408030b4001d120781702258244010090000082250020381c26102c0c00301d04154820680350843e504ea10b601090f80c4c55030114405000e00240e5520070f41c094078414114100c0f038803151f50340d01d03407150800c05c2402e01c0d01e89103500d50005101d41d040c107001f10b54102c2d070312100c82494586000000303038850107a401c40f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 249188219 1250 249186969 249186979
    0xd020a03030510030609120e01052107020703051e060a110712030b0607200108130807261308030901020a0206090301020c0f1b030601050a0b0307110d1d0f0f 69
    0x20500f20410303495200041d541c800e1080100b003481d420102c0c0403c24100c86400054010000f4000340d500c6038007902c03103d02e0000900c07c003552080c0001034115070002c140340c0440c46512400000b06008000c0810203a040c0d4616800496503082f00d5400c03c0c41c014501d880c00d0703050540344018a1018000c8500c1240c005808050003040c0040442c090956001405d500010200304003082c4112810340302881101c4030010380b920000c0c2801903400303030011204000070202000a04001c0741d1600000d1180d940b00750342031f0511248801150070740d5034190480d25170101c40402c140140c402c0000604001e007070712600446c1045145030000399141041e1000a0241c0e80c04070340c0d0840d0392001d4058400b0b00b502e600a8035484911082c4103961104421141d0300140460b071036080044c103010a80505840b00039140c18007203400d01c400d0601c20351010b00003c1c20090f10724070100d8140804d00035030301100301c40c0da1180c1c0030740740120690088031088050b151080c040d0030321055140c0e0b107034102e1704101c64083d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 249189469 1250 249188219 249188221
    0x11803120c030e0708150a060b040b0d0b090f070e1509040b0a09020f0918060328050706050301051003021c0c0212030408030a0507080906041b030219030c0501020d020a030305 77
    0x2011400f8041c4480e8079406032160040c04035440c2e10115031900501031010450103150341c0d01150100340c40c0541f043c050104001c03c401d1101449031802407100c4082c40502180d5030a0120201d140d00078201c0740e00c0030955610040c08a004d030300144d5140790400864424100c42d0340e64042031700d03520900c00300b64400d035524054015180c5460300140000e200e004001c545076404d0030404199580300503d0f46100722070400c2040d180030044104103000300c0000c0c0041009044080e45605034088040d40c09644004c01e00080c00040d0040004d03001400c0e0076030b10103440307501d4003041c841d801c008201450103050040c0485c441d03419404c1e04410308540c0e09400428902c2c00c100c416420080442d409000102d0700104110074400c083c4021409004415000c00c1940d64030390046071003200942e001c000f160852004038000c10303040070310780c68080d4603200d444000540c2d07a80041c8482d04400750403012040345d20001c0003800b041e40680e2004210078006001c0c0c5900ca110300035111046035000405041d510302c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 249190719 1250 249189469 249189491
    0x702100e0c030102180f030a11100306050d030309050f070e0c07022704150b061c270b061f1218051c020c1311071b0801180312 56
    0x2100c200c0400010b80215034807089070075014003c4049034200c40c000c5c40100c106600c3d9003000503922080381d4005801c2070a0b02c0000c8204000112001100360406488100215040c1c1e140c0344002d440d94840d480009441c0383c0d501d81070341400d80180c0400810341140904003c101e007040340e05e540c00f0f084e1451030341c4d58010600c0090341030701e00c1a240604c004201410b040380d180f0f8800c000e1b8003840c000d480f00d20042004070701f03c1c0151040030b00490b0f0005801d10103070940c2c6203a16a02149800c00c0071002c5403011010100d42c08d44002056000040d1405040c00f00a1118a40040d600328405840c04a49111185006d4001c07203100842c940400c41c03e041c1c003d105200b1340d03020881c40700c00e680c84004004002e051095035801c00701d64040864442119144501b400090280440140070f1300451401c0c424110544c020416128200603602e03040084c500091541000080100350280303c4504841c1070080f09421144259041111b1881d15a0508040303604420204000f40b01580b000c80d002400d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 249191969 1250 249190719 249190723
    0x30c020d050105010608010e01350705040e0d03141b0a050c1c020d02060106080a020a020a0b07080414010b030309060d2004060e0616060213120506040204050f0702100e 74
    0x80c0d102500951910001041d000e500020207412120b0a26800300c150f40c80b0000c00020008178a4800c07217148403401c5440d41c100300c0100072094000280f09940003261f4a80100c1c0942c0c4120302d4020b039503041580710a00c030036010701c19104800005605000c00749001c004c903000300003031094254041480403541d40030f2544076004550300c2030751000650300c1c030040c10030448030b10b09215030743c1c107003d40114450b1129583c03000950b02e040b19040c0d6190320080d100d4048210003980f103908440118018829650046001c1000c1580503a410750b449412901e81420400c104070510185c2514990400e260007032a90307030000c240c822400c0e04640302503680441c11860001404448201032070349414940502c402c640000c05401240c1c3c0b541c44030000000c4000c10400c661140200d8070342c1c3d10026460301004140142e0103850130056040044001036200c0110a00741440fa500c1120b041e4480300c104011818503000d20754100202c50407030801828402c0b4060346840c2d8980c582c04a036691519542514581 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 249193219 1250 249191969 249191989
    0xc030519110d0b13060305010614060903060403051b0102040b0c01110a0806090622051801060305071e0f15090504050103081b1c0c120903150b010509130c030501090216030c02 77
    0x1010130100b181a40e40d280540c00703840c9620848486201c0808603c84508082d0708039003200000034080d22a59490395419030b1941c21486c44024101c0c00c0603401100b824091000b0320103400203003a895210035104610609440400c18100f5a00d80d06024a250b80d640200c1c0c882d401030340845180c207482c2d480e9008145107819a4400c0c014105a8002c1d4110520f50f43d4000c600a038201c0c4040040f0918409100b8213a50341c80c0300060950344001000c10284101a50031908080c11011401000d9170360500340400103103d070498030141c6e82110303400e14495000349403d80100030a541c10310241d0314603120700700d09001e240a8540c180b002031107450295001445505401c86940100d040da00100140c0208100291581215013401000415400e6400b803490001200e5009204001102d26054840058000103103101e040c40b070288008200c80e610030810042030071500b200020780340d1a54400805541e01a8404144540304004c0076202c1d61a01c01402c40c06601414005c07056442840841d4100701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 249194469 1250 249193219 249193249
    0xc09040c0e1915080622020d110c070605031305060f1905070804030c03020708071214030304050a120e0a03030305070210270c0b0315030609010b0a06030b03030d0c030519110d0b 78
    0xe00c9800c2c0c01c0b01d00040754090005032250072030801801231540045074203070ac01c00710003000d50750080c01c040103620320070801980c1c0507920290307098410078280c0d200703480d1007016580408420f502c2ca00304807803424a50240c6c101ea086c0c99606101508211070301030070710100580090304104c0015000402d16008110480080050000329400e0ba03544d00110203880d4208541203414010100c03034000301c40d00000a0324046ca80040c060035200034681e035500074801403100c40c181404040311035501c2c1c0e40c1e03032070198100070741c080d44010a42c0d01c5d0031500282001c092184000c01c3c545803461303000003488494002042c00e0085060014010441d08100b4845442548880454a8000f00300300c00b00d1075480100c00d9101c000c0c3d046420a4a80365130f80350070b9614120740305404c02d540080406c02e45110790000500d01c2030143c113591a000c1c148500800f55070421040302e02117074468003400340d421191489092015520780042103104010321280104c0c0c42a02c1c51000303016260502411a41d81e1802e00c41c02001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 249195719 1250 249194469 249194509
    0xf060918010f090b15091c05060108010219020610090509010b0603190606022113030501020a02010c1d03060a0b210705010e010503060d0b0c09040c0e19150806 70
    0x582d41da14000d4000410b4000d40781100c1c01e021181038207081c020f40407080c02c6038001c54103003850400d009000f5008804640e00041e60075180350880407560034460280680118400980d403050041e80001428883c070566074115072004003003140b11801c20101c8803d403280c02d040800c06031601e14000d4094000c610610ba8442000001d10100c030030a108a03042c589007c41d018403540740d88a0040e40c491078041c8512a00715041c2a80c2d4011074114002804520140804001465200c2e100c40703007203800010700b207070141c1e6551112070001d43e04048084e004c562400e6540a402940c40c1c0440e0712028042e013090403994460300b510505984040c2c030300e10b90110034500d000840e440300741d0355555201ea0344a4980418540c0b200460f50b544940c0840b44581405811801007806c65036800f6a403030402014450619414044a1031642d62801014101040c680e10703448220003e604221402160094502e0140201102046021103d014840d410591818040c20b699505400301c2c2c05005200c0c1018010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 249196969 1250 249195719 249195721
    0x40509011b02030903060919030309081323120a0b04061b02060a11090d0807020a0315090b0105040c1e1b1212060b040b0a110303040c150801050f060918 67
    0x1250700101401c44c51030100c08035401c4d0380340c0c1488140c03100400c04050003c0050700c1100004240a43c0102e140321344111491440c1c0500d0425050098006cae07004000881000e01e81c800c0c10400411006122020480f2020030000e0b00c0c020513903603510700500003401c3c1005100000d05000c800e80c13203010700d0129590341d1080d24200c404000d4580380700b207400f00039041c03905513080307206d03170711842a1380f06180702070004207408900780c0ba184600d0300241002ca074811204c81e404000103440c2d00c0074030300c4001c240d600480d02c40c0300d6180800b403200381600f007180191302c1d0000403e141d07a8051003031101040c10300d1043d8003d0404240448020000a0751024101601d03110101000126055a4499007c80d544e800160881d501e01000380e0b0601d1048000d4140c087c00b0500400c081c582c018840c4085a04182100183e654102070a5420454054415010002c810014824110040390426586241c031a81c251b0500c400140b52075086d883c0d0500030a004640c0c4110b9407508805692211401d6040c042c43d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 249198219 1250 249196969 249197021
    0xf07030602030603100506030a060911030d12060e060a140d0807051621031b021801081213140d061a100212030121171210050f04050901 60
    0x10b540182c40c1580284140b0f0b48040c980c500ea442854083c0d1401005004010600d0711800040c1c940180c0940e14101018081c10311994100140d5112613042d84071600c2030b80506c0b840d501240c010b80d00000740d80031900300304021036483e041c1c0a010341d8806615900990f15a00c049103200340003240c02042c1c10000034414091141c00a0341150814a40d805550120f40b9020300d4022842000c0c12080c03100c600341c6203000040c3c007a2807090301508050490000350b0a40ba00001d82c40740140100800c07038070103580180300383c160611071408021602103405283c98945042188520317554410354903031185c1a0f501c14565520170702c4040103681c1180061082010480c100d060483c01e038444a40b0039140340716000b2800e4000300318130881c3c1850341b90440c00d5a12b0000351180720001d064501421401200001c80000c1032088081030340720100541355124002240d9003007181c1c001600d103901260309034804100a99420208004c80c2c0000d540106481d22a031003058050f08940820410402e400d03604005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 249199469 1250 249198219 249198221
    0x3091203080406050601090b03040201081518190c02071206061d15011115040212011508101103010b0a031b05120a050f1611070f03021809030307110f070306 69
    0x1002d540283c208000c261074050040d40e140c4a10300c80da2240f40401d00002e0003542c011150682c4c0000e08c5401d074200d500003040010480003d90200241a515400074854030703840401c0d007a00600d1014008103d6490a2071000c5d6840c030700341c4038600c154501c0307080090420603280c00ca03000904000074240c0105401c0c4c160202c4105040702c030741c1d1142000f024a038030250300c603035007000346074115101030301d00c0324100c200070010800010000d0b60403c101032546003d4074000d05c00c6416a1590244010809090a615a040c054402c0b4062452410008182d1203544844100c80c1110b06280c80c9590f6032002c0181900a03111780e001a800840031412501d65141d00308004142a45138408108540d9903400c2002080302c2003610910b030321009100010f14414169a2207035190b402a081c80c0d00c0d41100040d00d145441c000d80c0228400c000c1c01c00040045040052140704520603510050f805403502114843e501c8c003000700f1758001c0060441344030384005818043c141c0c103024480140d0300880d8407030505078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 249200719 1250 249199469 249199471
    0xf091e15030f11220506010e010e04020d060e0c030108061f060806010e0a06020c031009050604080a1202190807112503060905010b1203040b120606040e190c020102040812070309120308 81
    0x113102c0350604001415030b61207000c2c201207100b0705031180c83c817241100381804025001400e000716031980d103040210b41421a0f0284034481c03060f1010142d0f5a6040c04182ca08001d805000240340500003428900e220340500240002c1e5000303071400005c59500c200040390384d102e14180940d0404c00ba41800320b500c03507011580803140324041d004c035004914040764400c11601c0148014280742c0003440490001208000100f108600c3e80c0b400c1905501282034400807640906101101684250805501c541c3c000300071342c0d803000f201c2c180706c0c440c01d01040c021510f55010804681e01e46001c0d18042d0303008805421144040c41e04404100490140c51611314004c0c8034850810303114600f09a0060000e001c001308407003e0360a12a03800341040703506143e9444500001c0c0c80d0960000081c0000b0407100308903001103104906034800540d4110454030300c501203544042000302164010001032100c5c51f070000301c801c400c252001c415940c8200707908045a0400c0a60405d0106081c600c8480e0107240d4400403c2e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 249201969 1250 249200719 249200779
    0x8040605060d03050909040305131d010e150103110c10151e0e040f14030315060301050a0506090307031202061008010c0801090905070f091e15030f11 66
    0x100200c0c1c945804120b10840341d81e9006000030b00801484506042c044551a0854442c0c01c01605100d58040000c0d03860856402c0130f4012000061001100d40c6121017042c01011010240565801c003011800f20f00906020b1280c10b16407120019180319410b1022903913a1440e02d4103550300303031950042e00b0b0090111488070b40a48e28107440c002c01e03442d000381400403500007142a20101c0c0c925180c00100703140801401611030321079141841012031104045800c2411000015541e039240090150007400100381e51301c0c2c083d0700305000511264075203250100503a041140e80b152110754910000b441d19526800061181d0000c0c6403c030000c0d038000600360700070300c03200602c000360f1501e800c0c2a40c207e4480e000c00c000095882c07001048901440d0f4000411a4000c1041d101c0301600d0b803003103000303d07140c0da400081002c0c0d907014108903940c05201c94a10212300e0540c00d1100006039503000103100310502001d0440c00d031000c1c4040c00c00c1a212003d100c000805020316648801441c20707a10100c044480c9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 249203219 1250 249201969 249201971
    0x1906022104060810050d0f1a0603030f0c01020d18030f0203130506070302011b0801140303040509010515070f030509090a0b0d170d330605030a0b0f060a080406 70
    0x4080d0940000c08180c40150031038454581424940031040710035450250101c00c4481c40c130780011805440d0403403a5a5942d000350030103480e000c4280344c01ca40607080020405420080a0244039050b40c001c000c031020101e410403040d80f50b9500d0000f040c0284100b81080e51000e180c000003030781c90421032104000c03290080c4c4403c0406080d40c0c5090b81c507841102003000139883d54070024442842c1183c003a0401d0fa0003031000007480900841d41510440d004075918010614401c01041201400320703900c01045070a5024504140c608800316a000c4011302039607110786014040c060782d81c7d0751982074806181d00294400b0300c01500c1c0c28042c2c42c82d803046050300d0141402c030300058018507641c000c41c4004031000e49543c09c80e958a1f142d0704d072610340d94a81c40c28007520801400107840780c20b004440d13000d0b03030103012001740c510168900518001011142d260401c3c5030241000390796001010f40342e00c889035040110700c0043c078a0000b0000d00c900210213034000004600301006907809041140304038400c05e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 249204469 1250 249203219 249203233
    0x10300b01140304061e050f0a1a060f0306010c0b0a050402032b0f09081b040b010305010312030e0c06030403080702010e3d1e06060507030504050904020f190602 70
    0x4440071a41c08200300840c150410109000885541c001030405650311060010800044041070544d0019a00307403c011802c02c062002940040c030030300c9084402e4058105a4071003040c0800d50f9070240c0c854031813511401100040590340110b0b540914250301c0981a0082d1400f01800c04c003c10040c0d40681c000c1c4107500c182101103129282c031807000f04140b40341d0120380c8180703c022a00c04443e02c00704000c2003081c0071f000503c1c0c80100a26441c3c1c020350700c017810400220405000c00c540135840c3d503e0400d4102001000880c14150440c0c000c00d09519012030f2403500c6048135071501e4907103800079402c60380000c200070078194412441030080c0c40310b85c028072000140b03c46465031801044880c0c003049221400d0200503156140307003d9061000c403d00101958034070f07101c4500300c0318807a0194178844849035010044540b64401c5002a0100b410001e0805c001601c00070700d03030302882c040d0702d0054481c4000b1405564404d0550055140000c1144041e9038107000c8021211441e8481ca80240c0300e41c1c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 249205719 1250 249204469 249204491
    0xd05010605040e0c0304020415080109032715020f070e0411101d01030f050903030403021204150309050a0213021b07030f030318080c06010303140a0c021030 69
    0x900300c500300d40c0300f000c0c1488240c03501103002c0c813183e00103802203031712a542c1c051014440c0008041f0783e00a0020400018200c40c46083c003910304000c1318200400721a02500d06199001115680300c00e4070b4904c1c10311070b41c500c0d03a80c105078504125038100401c5031240000c000782e45002d03030120500ca64407400000d081156204280444103078401c01d000c000c100c1c04454030b0101940c607044003e24100c149408503a070100c040300c0b041262425250500a9000001000207054040011102203a010400d03103240c20720f40402d1844400e072810b8460308150301c444410090040070007215a0030b40e00104885007501080c01803070002e50068040c80c42c02c40d8070756049141d1701e0020a03080c04480d0443d0085404d03000d035030750032001800415000c01908083c1104840172a610368080d01d00c0c0202c5100400c60b81d410b6040251942c10045070003684124200415400240d218034826150b56041e51440310f10012030500fa540d00c0e0000c4550420203102550440d44104090103074190031000b10740800003d5056 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 249206969 1250 249205719 249205727
    0x20011b030c030c09050910030b0108031809011421032b0227060c0303010b070317010312180503010c05070b090703081822020901090503190615030212030d050106 71
    0x102000e001c5200384c0000c03c82c40c1030003058280d103c04102ca810700e10030b460ba034540171242c42c20780010308507a00c0440d45201d040c20081c10b00c011602c00f20781c9c001941d072410300c640c01c1d0b422514954500a103465891700074483d1101000c1c1e034107010031506a030340702c0441e0314139001c0078140480108805000c0e80d5006100700701510856001c0c0d413011084000388401c00c1d0b41c5a07160703200940c1081e00000108803000e2486030a00c0a5030180c5070940e0b4041e55040c282c200200544240156004c215416000401c0010b100600385405004581070804001c080d00d1110688102507078801c1d50107508111103540400e500100070112a4883d414254141c0c43e06280039aa0b400f0b6808002d02882c1c0030024610014808001d508120030000c1c41e20a4000480d00c01550100076688030701a02034022401d0f014540c1c21919503c0540001c0d80140414090340c42c2c428007444d02904044c0020b40c1d81c1a00400307002c2d209440f10301441d0082c2c51343d4a50801e40014640c1c90f40500d80303510081b41703004d001046007403003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 249208219 1250 249206969 249206981
    0x61106060907020c0418020a0305030714031303020d050a0b09034b13120212010908030a09110303040611060c0304030f0e1c0b07020f01020903060720011b030c03 71
    0x40d90703005022002c162400d0000a00c0c00344200510303130400c5014003005230b4801031070341c0c051445400695229040703854005541a03004d6002402e40c0c100f405498a90f05d642a9840120382c0c04440030620580182030240c10410b840501501412000c0100a0320712000030080a0300110b09079400c489a907000a6020701041f1811380407414000b030020041c00880311030f100251244a8801c80b8a0185c100981d001c2004035a4041410881d038602c2034000c1d4601141c64400c02503000d8024056041c03242c1c0c6155036031000030603090009580d009074a05106452901190000c009812a51380b280c0b03518024200f0340c3c914010800d60301c80e03240003900200e48007040c1e038040c0b40d058641d101c030440700f004203890864441c2c1c02c003900000a0004080c1c0700150701c0d9010f048500801c038a5175103003804c220003802c24508035002c000c1c82c0e00401044a4503180051029031100551038131250610101140b0b001308036040ca4407080e158242500080080c0c02e020072002c0090041e00e003040580715510084d4262a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 249209469 1250 249208219 249208231
    0x10e0105070c05060306061b10060501080609010603020c070f300503040e040816030e030106050103090201050403020f0609030307050304050406050d021305090c10090503100504150b1302040611060609 88
    0x25080b0401c000700d09142019541040340203114030305080e0030b8894102c96104082104019520a88401018440500c5014040c010a00c0c003400f10707141200120340c00d25418400e9030101035002402003c1440c0034440c20010b05440840180d049541e48500f045d01d400d8442441e14490303100281c1d00c21420364082100104e40d000d4081c40c00e19150610007461040003c01c01e65042c8001c010301c5844219101d8a07010080c0309441d40301013903410a040c94210b458641066041c0340c079015036000541e8008042d101100c4e8100c03025000b0340004808104640200000c03550076100c007048100402202102400644c3d0065908006041d03840f010003030400c1000f100a0b402186111300e1480c442960341155034040d400340d086540605541d404510070603405132035040002c1c101302051101e86002c4c000c0142c00746509a0600040c01c041e01e90b0107040c01c0d54000c5150710f03076607090101c006032034208903c40103082d00321b070844d00ca40e42e81034003030700c6000c0213043c00e0b1640c055800014694900120a180950 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 249210719 1250 249209469 249209483
    0xa020a0e040201120c110708030c19020d0605010e01090e0d0503220516030302060105151912020403060507030c11281218060c08030f06040b030a05010605010e010507 73
    0x5803900c4004450240c015005038100076030607500c2c030b00c000e0941c060300301541015590081e0034400c00d8940381c00d04030140c0044403550010001c6401041c0006440c0103a18031004010041d0116840041c60a54448000504c2c4509103000042d024068401280c100e5142000501c0400822100ca503122030b0000c841c18040741c810b0012900c0c4599980a0429000c00c01c038100c0052215501d495203000501d100b102000c3c080340ba070034010960b060000d18010f10003070380c500e4201d140782c5054001d11b01998482107924600a00e00c446030714440d440c7d003003c507840c801c4210b60780e64680c105000034020488000010034241302a4510b1140b080013a801c8444001001e07108101004400a40840d18500c050f400c1d912203140000100d054a4442000d06001351207030303102118a480100c040c007000d03034031403001d0098041140c000301d501d20003141d5001d80300e0014400300365913034000036004101c0c0c0d1102a4040c49040381d10000c0000552100055503800d80307860601100c500c00441c0c1d1031280000c01884c00e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 249211969 1250 249210719 249210739
    0x19090314030a1d0303091501080a060c0909050a0b0f010806010e060c1f0f05010611060705090d1b0f2112020118030309150501080303070f0216260a02 66
    0x8100100140d40c000085140200f500001d60100f110b9010000500c140f003600000240107641004018000d04000300000b08009907140c0300307400f0303203582d1440300140406407038080d914000762083c24541d028050580c0c0811090626441010003054450f44c07590181c100c5040d58045907010702c010754442d140c140d6030240484240014461240c111040050207403041400c94450a0590482801203644c0c5180018075280400071030341c242c0710306901c2001404104d8581c1d0480c5a004900681d03c0802410071543c2d4089071000300749100c0900f0400b4041d000c0e02d40706000c50400661940040b00c0b2364070042c0301d20603155090b143c2d0724140f12003010a900751060300c00e03000908060714640e0101032800000f808007507940c1c1e0841c1480c158402140000d80c0d403000d00b410004d0702c11160440300468023041241d90304100d0381c25038900c0042c1220050190341d40345c0003c0d90340b00f04212003940d0002680045e00c60390314800c03012002c983c0a01224502001c00d00059515000140c0c4154644c00600c1c43e050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 249213219 1250 249211969 249211997
    0x1202150a05220201022d060117060a021303080f07050c01030204080d0e04020918010303090603050c04030209150613050a050d0f032012030a0536011401080105190903 73
    0x1d180b00d000400c03030541c0501e841c40703070010441d0f405000721900803072402d15144c0c07910382c4164200303281604009100c500c992440c15a51a002840c0d40d0f0100d6004001030342c0700282140340003522070a5100503d181c0740020100400384000d8060b1100c54410000c98940d114802c00643c180d02403400341c500b031540860810000d407846280001110b08000e08014079101003040800c8000c444950b9001e0480c06501c010401c0590105688004080da40ba04010508148130a0315151055100186c421049000400c03e0084074031402e00d551640101030550f10b006110124061003500d01c651031142990303042c00149410b00090080030a540208902c00010683d03800341c03035110880b040a13000d85c561003002001003000304099805040d400c01d5141d1a071411818010943c0c40050100b52280013a0f0f00c91000c21607805000391201e000b50308880c3d1076a02482941d4018584500d6039040d5201a50002949840652100e401440741e04a00c074014000c000740321082d6010010000c0000b10101d00c0140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 249214469 1250 249213219 249213271
    0x30f3309073e060421020c0612040201110a050d021b06040911040b0403030503190b0916031515080f01030302030a0804110d060b091e01090c0c1202150a05 68
    0x101c85554582e496505000070030650b860036604540441c1d004030000104040710300106134401900e24a4802080582e0051021428901606500015403107106010038116030048001d0008034003640200c83d1561020700b452542c2e400703800d4044026008a907581c05500907001044c3d000480040d00d45032510f45030124110007050951018840750318180000301d04908400f00a00046000b641c4a0b0388a081c5030810740d21280309060508561464814142402d40743e0346080c40c0e006410860b000b648104507003065025000005074203100480300c40d0040382141a00011480c2d0159a40d00c4c4580c907039802c030b4114003003542030002501690003401191002c51141e04010ba1081c400c11441e401c2e000044003103286038289803421100ca80d00c924890405080801003150301c5111110088001803002e0701c4500d00701018080c00c01103030b07203c048040e40140503240c55440294030964030000024820740094450904c0c002c0c191940404101043c0c80074054000d150085966896151404514501f018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 249215719 1250 249214469 249214547
    0x30901021b0301090f05010603060b1c030c02190305070305070b120406150e010b0d0e1b01181203020f010510061416080f0a0e030f03030f330907 64
    0x50b90541d04c590f00c000c001022000c03d20212031040c800410110300303500d004015900b180300414041c01e20580e28105c9004045802d070a000e0301800d0904080c980da002081c0013481c01c240c03a40030003100110010030881d002910000712400b03401500c030000c2d1244101c0da440c0c8162140881d05096050209010404990200110200640712855980d6503a003003418031800c00d90280210160100e10481130001c02c0c09030070300403400709000d0b08810321500c810820031400c1016841c10000919401c290320840343c880c58000d00345007801d8a460603001d1a000b0360b144000024004a54200030120350000304100d4404241c541503113441c1c81210081e51440c5098015000456480781c80901c95001701d20994010501c0500110311f4603036407071961030068440620324503064000c1d40240302d1072160341d40c00300540c0c4e00302d440809401015182c500b29044440c0d444c17140e40c8240251500c4100d84000d0b1005140c080c100c05560000265840c11401e8400c080d041d010a01156021a84098a00c80ba18800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 249216969 1250 249215719 249215773
    0x10803070b06150306061b060709090506010c0201020601140607080f070218011503020d0b09040c050a06050f030c21090106051804050a082d0a030509060c04061812030309020a0803090102 82
    0x2500107d0400e8101502d0300000303403401c00c0800c0010009100b0340100b0b02446500202c282001e070991056940001c0d03454405210350041d90142421942050b03803202c0455509542005183d40c840b202c1c5d0748004416800103104a11409a0b01003030111240c055098074100c1d03400c03030101450817040c080160041d5004d107543c40c0c209661842c0d42c000e141e8038441d49074000c0d801900000380042c10901030012100c0703150010400e0290a1020040442e0840d0859501440e00000383e500e1b4611a403440e000c0ca41345a5500308603040d004100310002030150301c8031049500c1102c3d08400d0410b1400c0f024441c481c00e0300c000d07181f90011145200842c01e903a005113802d02a900384901d400650344034003440381003031420319034001c00700041c410340032035150043e1900031407481c3c040c008905098407102e07410322a6105900034002c4000500c03e01d03c8142d905031000380002034880240040e2494018010071062100701e10400312a0404502d1103030000a4405641041c2c005180896021100c1035103d0015644 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 249218219 1250 249216969 249216997
    0x405030d050c0d050916050d0f0f02010e0303040801050f0112030804120e06040305010203190605030a0f171603030f020432030a0302030d0b09060d020d03090509010803070b0615030606 81
    0xd00310815211340328491281a00f030010b800740300450082d89258020507803001d4401e41c2c0940000c000b01d490340c181c15001680c040c201c0340caa00300910040c0c4500c119048020b0785030002140000d10010103403c081c0c031800c41100c210416030f03201c4c0070040c4490202c2c00c001d400a082c1800040020300f80b610050f14604040c140401d200c040003001031069482a001103a0903500072051280142d2402050000e8581891041c4400c0d07080201081d903420301c01da406400911645000004d2040c1c42c030140e0300c2006500c414968a1200070643d90190b001e90308110002803900b0000c41118000e0f109480595194003241c1c400d5081100301082c0803120040404c0700d04101405501f09039a04022011110340300b90041e54803100c656a55008a69900e8446401017004004008455440001c0d2008a0341d04403001021b2861500702155141c444d900225013042c070030000487d601000001915001748203091020590f50f0744070078000c0402101040c203407102810300100d001071034200050050303900d5200d0703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 249219469 1250 249218219 249218227
    0x8120709050406081b060909060105070f050a03080925060309020f04090b040c0b03040b0c070812190c1103030105041107060903170109020a120c090803040e010f05090405030d050c 79
    0x8002000c0f03400c0c2d0342c001202a80542100e084281c100c0c0300508140c00e080b85c1803070420402201180c261030004203224100800001c44004010440d05100c0309513130040304468007503404e031601924004094441c1c0d4040d04c034003014a400c4407051000b11143d00f0303a910003912400c0c5040000d0300682020781040764086407214009005032124814480002d01030080e20045040508000300518103030381000c0b0300c154003041000046108032404ca508400015a0955211100d080000060084172211651620340000340040b420050540d0b000c1d81124000410000c02d200d031041e40e41ca031540a244085820034001040546040d80c4402d0000121203003091500705075544d89002c95129141c124007140d0329540c2400c901c04d954030541d014151100085103410b42c00d040180809d00d8507000d040e00c0c1c6464000380e80c6914072a140040090a0940440e516180c81d0100e98104002c00d015642c4000d174048000070b150700c1c0060030540174540020143d8584107104079805c0c09008000c0c407492000100304 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 249220719 1250 249219469 249219479
    0xc020a20060d0614060406020a150912030c020f010608070e0601030219080712090f0b0415060b09090702071a0a1b1a010806070e120a05060f0f09070308120709 70
    0xa002850b1000040e00b00080003810000d111012506000c4003e004400a210038004141c0001d451014a500b010300c100d4000c0d1181c50403805424000001446902150b040c0f040454043c0c010030402c0d9071507000e0300d1364004040451400c841e01442030404c039a0142d441040000c03048031000360030035010b01d409880d001d03a40c040c082040301c0310816000091080001c102c0c2b96603000304240342c0030b0f100c990148070910b8161100960a260500c4c0905201800804982044101c1ca240540c90b41c0100080c015160350343c074102040c4c1c014446040c01440804006206284041860303c107540e220003506009590320f680342501c82c1c1001784504140802002900304600d0000d061022544c4603c0c600c56842c1c400b081c0700c912942d41a440301c00a940540103100c0815000844110075950549a0342c1748581e8004c1198941040d020340a840d41c0512018403482103001007405101d0300800711a10075985480f14980d59610003480050a1028140324840c003400a4141d0540c0101480c6498002e4540310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 249221969 1250 249220719 249220729
    0x4020c030d0504140709050415020d06080106080705090112021f05090406030c080d03060819050a0b01090504050d0e0f040506040b0a0b0318031e160803090a14010c020a20 75
    0x9030b03802d0f6421381c6040000000032804020420203082c00744001e00140c1050766480d11030f1200a81c2420001e0340120701c1582505465120f030f4020a9510024408284d455003100c1d156000c0740145401103510b1000412145c1c044c1c0a1301805c80d50141031016841403142c4220021018228520308004c1c08000b048081e83d0346015103809540903110811280b0725040e9258030b001c162603204014182001070070000040085509890030070b204641018041c0360346007460810080c02d400900c0e00d11100004143e116180d807040380b0941c81035048030b50141a50300700b9a1100710754122203500024640303160849003000e41006800c0b9001602c0421070200400024540c038215410a021000010040250102c103029540e141044068081c5190901c0c0482c81c0b4032a44d04c0d4034904240e80000a0700c02d80303000c05559411445a00710b0800360301c0e81400448141c03102080741007070303450100c21100160400e0040c420340201c3e103010340061a042c0b40e2a5200303484488541e0a07040403165100700c64030031380c4031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 249223219 1250 249221969 249221971
    0xa05041d0d0806120d020d0509011215030201030c08010e0402060702060705190201020610060c0b10170d080703230403050408010f060302090c030c1803121903060b160204020c030d05 80
    0x42030b101c80c8650b1410b0720501410180e40d0076442010b52213220140401500400d02e44038400c1c951401c156103810020040e40c405000384443c1c1d88040c500b4030b08010651a404802069903c03d903000c0c054440694000c8421040c00c5c0034085421081002250041c9040c400510130244007030801c5082c0044c0d511658148503019040391414a61031407482c04540c1e06104207079104410740c0c1d200e541d007802c08200410100400d900180703e18182c50201c1c0c01c50b100950503d00820022502210042e523180390261518124040740c00410040c41c00710344024080e005048001032500c50304141070841042401040001400035410b0000421001c140c8c44021b000d9482d91541010002c00e900d0710b14418460010401480c1c1c911500080c0b062000c2110303004215030240c2105a002c00310301c411400020b0409000c000c00218680c4000340e0b50481c0079203815508542061510100f0140da80c89542081c1c038801c81d94000600102180e4034801481e11754081c200b290426821a41440e528401002c11108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 249224469 1250 249223219 249223243
    0x20a0b090a0309090509190606050a0b0a090e01151d13060e0a1b08040c05181801061a0a02011e1d030901080106030506031c08070212090a05041d 64
    0x410110401d2640007070000d0010600c54804005c00d20b04900e02c141c641ca2107408400c1c081d10b04080300000d00c07000741c02c94005040004e0000034806c0e500c0051b09e6199001c0c3c4480808983c024000040704d07285a0103442c100c80e031024191804080301d042c1120209808010068589002e00e026140f84c1c40791261004200c1c1a4240011802d0810f0701da04001a4010b00f4080b0782800c0ca5251110000848426002038915040100c0d564075039242c104880e518039040581c001c12250354009004c680004205d002d40b6000e646181e640d44aa0700e81c5090340d800703004602c402c988040d0707055094080e4000038000d580c103510002401004041045a22a015403400d02c1000d4481d280003160240d403a04a62803120100004c0d450b00c3c0d5071000213014041d0510807102031660390b030005821034800f03100700c090740388101b00b0446e10342e0000070015080c24401d80f100c0b4010310900d0b41c012030b1180b820085030900d820040c1a908c04515100401c0043c100d4030040c81ca222407210201c0710030314010801d03405803203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 249225719 1250 249224469 249224473
    0x60c0203041a07020604050402090a090f02070308180705060c0118050307050606010f1d0d080705150c0a080c0d110d020a0212040b0d0c0315030c030c06051c020703020a0b09 76
    0x2407400342c0510010120724862042c9030302c20800400166a5a8121412220107440240c2c41d240701c2c400084401c0040d5106011050610b5000c65009007180e00038071110748203440c0c02e142520f0305115040003c84498821516601100c020322151a00c40045d0880144d600c0010070724111107044d80f0720300c840803003044620f54000b08800c000c029043c000250311660a2800300804483c030f80c8000c0042d00400a43c1700404a40b04601c000d035122049884401d40e00801015500c41c1c1924002d541d03501c80f5141105814002c002142000d03841c1d0301200c07022030241d40d41513034640301d000390760800382c0c4442c00c502e2160382e13a03c40d01d0f4003076034211018044103000d03a840142c80c1d00440c80041c4c14240740b41e0808107442070811050202c420302c00142ea44e00d402d1420f00141c60000d03040241c0c0204004294550b29a0034403c00004101e1079411500c1074a10688048210380e541d10020386040c041c03062205041e5611205012800f14503038003134803e0328020b1045070711103051900d581d001c028007520208410303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 249226969 1250 249225719 249225727
    0x40b060a0816030501050f10140118032001050315060d0e070b040e060306011a0309010908040f031401090f120e0a0308040501021c121d0d03060302011e080708060607060c0203 77
    0x10000a108499010003803a40f03201440c82c010381d10b4007002c601d900502120b280112700c445076603449050643c08200344804107c12040d12410b03d160380d00000851214171a146c1d40e2a0b01d07644d441003059a0180f101503080440300581c540420403250044c4000300c0301c290781d80e034410300301a604000800040c2914001560740f0380c28880a40080c1c0d00080595007e43e11100040000d164440f0703425800040c2468100d4580c0c8524003114050110380102410034400801d0104445030041685011640700322a00c0380f07041e1030100780d40e085e540070070409400140d0101c0c41e100030030302880124090000b54600020001c00e06400201c54071301c1601f080d5582d0b03501040610803541c0402810260402601300042a07246c02d03d4000d03c50284080044165034417450a0480541c10205054856407008207443c098250b03600014020403080c44107a002031011207c0000d002d401c4e40d0300804400c0b159489030460360303440205558514000c0c2196070400810000080814824070406400c1c82242d0302560796 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 249228219 1250 249226969 249226973
    0xa0b190905012c070e070807020c090c040f052706011b050c040e0a05121822140f040b07140309070e091209041109100f12020909040b060a081603 64
    0x2c940310303003c007110050307020380c1c0140a140c5c4c45005103644880c0914090030b4656072a14100e040040030040540c00003848001d22800030560302c06082a1002d000e00300080301c0d620300402c224040c48800706040d10b83c0181c2da404401000640d032590121040c1003808890340b0310b059480c0140b001640039241c0341c024903400c01e1285031034007030041502160401080070a82c6521110f8a0725000820040b0344c1c00c2c00940110481c040d200e00100001000b8070030901d9035211140407140340b0611803003080d02494004200c08250b1651314182c000e445070400d00f40659102c0c1c1d2212813821024182401b4003c00d103c4c1401c141c400c44000b0751007461106c1c00740640e289032419260600d440078001081c6508000030f2a0300c035000700002d55440100403540030601c42c1168118031554858840b030203403c224448605000682c025400d044802815656108140c0f0300704103810407401404c00040e0300a85c0c2c000410085007061148581082e401801401040d643d9244180b800c140f070345106021001c0a02c1c1001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 249229469 1250 249228219 249228281
    0x503060c091c2a0f030501140c070f080c12030c090a08011a15070206030108030c07210f14010510170102030405060408070f0b010b09040e0a0b19090501 67
    0x1a100ca1042c1c2191101120b580d103018140c141003a03800c1441c5102c400f12000380d201c0106400603e400310001903030b1034817420024068455800034540c2d19807200301062440383c500c03080740c8040307800c0601c40c0804005580c1c1c005084d40600c11183c041e01c00d80e83c031181d01a01040c001d40c090105035407510791301c202e00010b00106590075030088841d40d1520031107011000c814242c24074490030450f10500080000c40700010140100c0e00080e411040200c00414036071000002490308001010460f03184550b581c41c0c045104500c5201528590a5003c00d1740000c0c0003030f181d020a09208072400c0d8407040204c4652400c50b0310880360326014078201007041002042c1c0c0c0100040c00c5815000a500d140703065104c2c640d55a501400003810008001518000e0000802c402d4602a90101c0501015655900b1620b51340d00140c5d0b019206a16200c3e0407800010002103488d915075000b243e105190b03644499540d01d01803034512400746180c072449c031200016428403a11610907100802d00c2c0b01c40d101070840003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 249230719 1250 249229469 249229489
    0xb1c060b0a12150e160c1a010806090d0c060f021c0204051503060d0f0203120706050106111b10030e100c0318080403150f0e07031403120109150503060c09 68
    0x48030381c9030400e0a10500135540c030f5960b40700200c0c45100d61141400e0800301c0d102c0030200c00c041c01c1e04600c0209000b6025950545d0f9040301c040c44201da4007a2a80e0354280c1e1140140390301040070500c40900280007030140d4002e2440c0360314081005061101100c00c114aa455102c0003180302940054203211920b04082d00c2154000b4800c00d66040d0319108000c1003a0300c103150000340c0100700200e200c0c406c56600300281c01d4032580c0c4d29243d03074a0716054036080000c1d2000b030190101140300341c0c8022100d54000220390100c01d142140d00000d080c8540c05111451044594110170151202c00c00d10841004100e01c08030381c03a4103880065000d10b1800014103c4440b028188007401c1c07000040c00104680a0030f50b81581d81150000d184500380a030711000800b02d0362102281e4074100902542c1080c00850300c07004403400740000c00007601e581c07444aa200d128008010700c0f81d5020600500c4940c1c0307150b01600d40c550110641c00c142176115000646450411919000702c0400020002c00a041c0401d4030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 249231969 1250 249230719 249230741
    0x30b1312050a051e07020a030602070213020a0f200106030b06150702031c031d150907050d1403070605010e0103030f030c050307030b030c040f020c060609010b1c060b0a12 75
    0x10304005810070010083c1c404c800f0301180101c1504c0b400c51a802c5500219416603900512502203e0350301d01c3c01402941010900303920440b08401c2da5440f5034041e0003124030303621240d6101174400d0703807194043d110030b100c08010030940381502c089241520700910070305020718041c010003c130354a406820800349400e0540d81c0306403508240f0a05005850004100c00e040d00c544290664020549400302d00034051561800c08028605400c04902c00c4041800c034540f58080c0d1844205984030603405a40d2107040c0310b800d030012101c170b00c61804141400041ca1900c0c00440681e441c11009072243d20130b4450a070005030f449800c18004104160300080c88400a007490f0606000103886e40102820300e010041030202415111950030490742d90600006040c90740040081200c3d00031f001482000b0740000c890003c0354441c101c0030900615100140a0484100c4400300d40307004100c00c681c031184250707240d00351402d60f242c00c0c0103d00000c1d420081c0560082079540e4044030621582400e06807556080c00c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 249233219 1250 249231969 249231977
    0x30b150a080403050c0c030115030b0612030a0e19031103070f0303020c090c0c0d03020318070806010b0a17040302060417031006030b0a031502030f01060207210c030b1312 75
    0x5260641500800d40c030380c2c0705402d820616100c2c6405080141042c00004030305a05510f0503100e03060032030101d01000c0c20b81340101441c0c5480d42e10602800390703260009414000d5544240502c401c800e200c0d88001c030754201b000c2c00e0a04c030545104480701c0001c0498200301c0300720710010900206810104250b0006048041c1d506462030703e03580380691641240c3c04124019403480c2c000480c0090b82108a8007031002e1041141c50084544000900941003030714141c06245801c0c9100039880c0c40003400e90b043e90b2418000e40402e03413900000c0c0c2d683da4403042e100400d00028800d05e044d0443c4038440d0707510450080d00a004145042d1501c0450b0302c2d02e1181042450301c0c02c3c41031100042070420110161007090400103500c0000b00c00095a000302640024440f0641900e0042540e1668000d107010340540c40c80b4400a0342c03210800d0341c585026001d468400c007210201c18030701507402c002052000c0d0262404030001a1645c40700740b8402c1d003c0b12881c01403800f40b00031508019006008441000345894 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 249234469 1250 249233219 249233227
    0x501030b0603041e1a0709050406061107150c080309010e0118031b03030f0f15050102060408180415030b0601080919020603150406030c030302120414040e0c10030b15 73
    0x80e540b00c4c2c0031004400c45035510090300903002000400500c2d80c1c51014000240004d501e052a4000c0c2913036002e0160902650401e040054290f000f542412962f0f80d18401800740d503400d00c0c00d610000e034240006002000b00400c111400309401a0047d409220b2030000850100d013140b207a9400c2d154600480407081046c0180500440d500241c82c0c88148018440e0341d10401860030704501034103180c042e00302034526050f0080d0203d00700382d11001c41d07450712a0003100b00560f6000103986a14040340c0281104130100030010b0003100500e504100c0e148005c10012700c1c074000c00b82451035020507410031264040302d0400d02c00190780200c13001c1d0b4400c0011000340340d0080e0b403851865019501c003100078058000400403a20039101c00c2c555500780d00c0060030800801d56242018285095244400e9002d40140c0c4a5500004802e00840d400d4803031155940001890f15800c0c04010281b8040c0d040303160080092082e401d0341c60710f4100b008a18950760100d01e03240e04e11300704000801c0d54805500760f100200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 249235719 1250 249234469 249234473
    0x41a030606070206030601030e070602210705120703030e0d0c1109070f0f0302071407061713023c0a050a050904030509010c0b090d03060e04020a050f0103020405040f05010501030b060304 82
    0x1c0304944a6a0781643d0309502ca46441005030050b110480c1801c985004110020802550014683c50b1203480c5000c00d41201c0b08007030f2a1301403840345040c00b4126802458200c1c03403040042c1c0050015138801d280010343e6481c5a0b500c0d0303042603200e290380e4000400d400a101d0a20000000c021105441203480406030300300900081c0c045940e150040c000e1000841503611414000d030f044d41e601540240280480c0044a40000c1d2146821b000e0200458030f01503108051250034070f5030500c12a034402c0300c0e40c2d100c49250200851649020742e44890f04642c04041141c0c410140e0302103030b60245c001d6010048000c0401041130b5481260412401000c8052003001507030f50750303c50590482e4042c00c2a81e51040401c004840300094014040e01803401d1030300707021023403c0c001248221882d15940030402c0945400e581d1514420545019500c2150300400740803d150901d02000b401c0414100145402d55907004207050310840219511645d58442c0100403e58241c081c1546030041101e019103103190907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 249236969 1250 249235719 249235729
    0x3011404030e0d0c09020406020105130b0402150d0e07060e010c021305041a0103030e0a2715170304050a1406070f060605121606050c12160c0308041a0306 68
    0x140003a04000750404600b44076112100300454841d08000200c007040d48407080709020354000c0c030844005600e0040054030025294150320803590b8051141d00c042d4a6507000c100485400b0a40103403c0042080907403182c10080c892000300009030f4018180d620702c0d000011703007001002c7d28511b060040c04c112070401680ea00307416001504165800007803544540c10081d0f100c820700d0030030130300c442c001c4000803062542190354200c40d01d10480d10071446940341d009550140c141e1b84640004400a462032080f500300c1504411040800030f403011031030a0391460003109210240e03104042c180c200040c1440350741088003000e8060000c41d600c03840c0420300c00c00400d40c070740b00d070240c064032030072205084404100032600014000c040041000c902e8202c07007410603484024010b802040000110030000d580380c010f001b60b952001d02e50707000d8008119007146c0c590070b5078401c0e000e0108120204014070000ba415071f9001d80078502501e0a02d858500340034031010503440300302c4002d000100920030000d0030760b20 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 249238219 1250 249236969 249236971
    0x9091a19090503041a12060a1a09120601061716020d0c140601030309050319080d09050a0c0b19030b0a05040f14090c0f1e0405180601030b070e030114 66
    0x100c0c40000c1d840303019050036400c0d4000d40e004000c0503001148907140b5141008090018100350f480d0b0006103032a00001c011000d20a44540f103034010411142558408841028181607003002e014500d428111030f0741d803801c0400036003021000c00d132040c007511095509440c08590020b082076507a11003110090000c1c0d82c407aa809a10002c02019000c0c0200b00058000a0918180d546007200c030307556140d00e03000d00801390703a0150307900900c18100001c20310340c02e40451031085d6401c40e6130300d490140d40c103e444000c0c0071400320030740302e41c41848031240001d005550440028a00c4d510400d8a4000111421090f517103040540030030141401c91600e9140c0e54480c5034411254211070016080070101250405404a81f00d12034226600a0800a51007404181010318100880c2c0303402071914618100209543c07031202444401241864407411410141d20980d00714541010b4011240c010f40e00c02c1d4a003480903001120a01ca00c4006d00c14260b030012410800140220002d11840c03030408040100050 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 249239469 1250 249238219 249238261
    0xe01030209041b0602011b180b130509040501050612070b191e0f02011808040b030702121b06011703032a0d0501150516150209090109091a 61
    0x10740341020404000c0b10070b11018020514000440c003060352204041d00030031000461041440c40f03c001c402d4000d10a44442a0415020501c40e1040382030002c11140c43e00019250413480581c030502055a6541c0d040719440b8030300c00c50020409282607018400714401d90b0311000c2d10b5500c9203c0c00d01250460b0001d40d002d80510310f56000c9445408841114049a9072054548402ca41405c12181c55406449808a00b94540080c025100c003202c00c10492501680080c01d070701418081440603c4441d401107810809a00c11101c1d0020341aa0b2410290300c40c11058103800030b0f40c5400300c12024140705982c010040c0840d15142542e003280301d1526440010110601080340548245c4000c40c900002441c03003140c0700c400c1c0e880e007400e0180100200021f00800519a0b510710b1388001a0f8440c00440309481030207441e500d010750032692414001d91044d9914840141c0030700941c6000e03100c4203c0c82e4020010684041610b00b554105101400344030b504041c3d003034848408200904e40e600c00a070880380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 249240719 1250 249239469 249239479
    0x1b030807020a1203091503140108101505130e01061e0e0702061902030601110607022503051509070302130902040f0e0717030d02070501020c070609031101080c12042a0e010302 77
    0x1a0101b90220020301080c4e0103562240d0100d0000706400c03100185e50040c0b010209010032510140b01011070451100d4820345038840303513402081c04d0041164100c41d80d40c880e06c4001207079440d02c410004e04d403c04d2100001c80c0e1406950010000000c030080c095411107528005040582004010300d410582c000c1d4513943c0a5070000003188c130b50f900c9014801001c47da08400da405504065800a4542c40c2821581400885c1d50300010580f40c2c1e071003000001c4036030120007480640410b040143e01c416000780170b54001d000d0340d140000176880d402d15050b803101803801c002900c4a03a070b01c10041210040c102c0000400c7c42c012426214a00000341d80d025206000d411a0300d099499081c1481c40c800d20030f020503d46e0001c07640f5400c000c81500074141d000b01d0741c000c0d100c0558403407a089610040ca440050180340001401000550040890036003091800e20f4a0b13140c0f50101425001d221810744084a004d040300c54140a001c406075107109260180341601e020b102d2030881600031001040c040a840f41d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 249241969 1250 249240719 249240749
    0x5030703020f0f1203180102060603032a0109050a0309080606090a0506030304080f0114160203030133080a0606141902030c0a1a0a020403120305041b030807020a120309 74
    0x150344020405441c3d100052044440c0001d0a04045c1c8a0700001d110448100c28800f44098941c00800c490b8410f4002600542c2403034002c500c4460305c0c1e260a9800c0d01e407042c0c00031124a01c00d200703000315600d080c010700c000c02c00990140740003401c10301d140d030100751242c000206000310341e90340200440e000220101c02149945907140024114800c0e940400058428003024652414042d0050f91800c20300035050001039030350302c0c84a000103101425280041c0c1041006000300c0780a0045c19188211303000c2d94481200e11a4908221b00c0000b03c0a40003083c088410400d440d03c080c0a40030140034940341084400c51070400029042c000c154015500c0c0c8416115032211500c00c000740c9191101010485d01983e406d03050403e0381c1840220580380030f04400c0f0000d01040c4650084504485d8001c51a10740c14070a844120001c0c04040c0003101c0a80025a14101e44400c00c50024041c6010340625a690b0744240704000b0840c01641c0100306900c80f00d000440481d400117107407800c0f544c661840f1707006 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 249243219 1250 249241969 249241999
    0x210503130204021c090c05040509060a0507020715051c0b10120906110c010507051201050d0c0f06020102040611070e0c0f0903010510090c08220302152a040503070302 73
    0x281c0501c02c4c00c1c191501245001c0120310b032041e04001406401000c211a080d03444100b88416108120b83c1d03940c0e6584804049030410f8207035841241e00242620503250780d95100c400007105180e034080400300003080030402e0203c680b842800c0a8020503090410001041c0650201c4c2d800c2c3c0020351084140403109004400c84007480d040001c845501040400ad95400c042c0741c04400e40055001d000e0700d40c0381074001a0145e002e00203d50840d0089402120582e190508200d00c001c2101070031100386240500015124100c1070320311001d404150005070b122070406500401701c41210070305007429407103c0c01c00c00445203900805a0000740c40c3c441159511420080301c6014407806007000d0f015032910040040e258007842c0d4040507500c2c4071505001c24600c00380200c070180415141640d4014090501000c2d083d06000e2420b2080e1080c01910300b100340e00920340076120b40480301000700341141c04180e6540741080400340b5825a80405603070a0a0510000c02d96403042c40c000280541010040024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 249244469 1250 249243219 249243221
    0x318051f020c10110f1f0509010b1026061e15040806010f05010c0506010e0612010509010e0c01020303091b040209060a0c170a0c17070b13210503130204 67
    0x9010009480ca07640c0364440c2c00d00804541e8200010380c04c0c0d0084500b064013a110115041655800540302607031010605400c050051201070031680341c0b0f40d0384025011407604c40020f80c02c0c5c4038a141d1603c000c1c0d1070a40001c241403c074103c5907000c044006c0810807010f03544c0d0488000d81c00100d05000341e408000c07000441c44034008454103102c0ea14003c540011400000a0607038140e45804a0301d4141c03640e101c005499650380e241000f40b403900861b005000000c1e440c0019680848000d20f000b80380c00704141d00501711038003540c0b03030801a5151200c1840005007088910050070003071008514619008060546443d40a414854000c1c04105101e0310350361150140c440c0900001c16060b9036540c4554060b000341e1840100300c2e922446815940414403000090300c00040c400c2d155204180c2c601e036252040806070094007003401e0028018a07020034420304d0b4180c450403054500b140c00c003120382003014885203c10102100d00c1ea040602d45d43d0b10b54414213482e040580c9188101c007002513440060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 249245719 1250 249244469 249244483
    0x9130f080409060f0b071e111519020a020303040e070905040c051201090219140d0204030305042d171c020703020f0603091e0f07090203040318051f02 66
    0x15203a02030200300814081c40c60760140c4102e0741e20400c8000015070f5001003a40600a010018044024404800f0300c0c41540036000d281c841e1003240b184062000c103100044555002c52181000500003107810b5018100c5172071048142d03d080c0c00202203444140d0300107a030b00e100b14000c3c1f0900c10115000306803120f02500261002d0b003401003051100808050004041340c0114401c4c0425001e40800000c0341d0a042c801c440c03040c842c050201c1c0085003209020340b800800c2c901e9000908000708000000301001e480644059407203a521583c1d110300c1c1c84811003612164500743d503094100d00030104182040b01207840b04030303080c40c049601c648407200f07945810444101038a000c0e108010744805801580403a107541500d10880c0c40541c2400d4603c1401024082280d84810503403104044d404025855060f110a0148610855556501201207141441c48990056440c0ba4004c8180000c260300a112402c446800d40d2480780481c1c1380000107485211100000c07a0040000111003140d00c0c42840f030741c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 249246969 1250 249245719 249245723
    0xc010603050a0b0411011815120903080618060303030411030a05010c0305011802030411010e0a090c0e01090e060a031e0501140106022506050d0212190501080c09130f 73
    0x5103a02d03201070f09180034642c0044074110360f4036503810f8034102198090090b1045000c00d14010300e4150341130091000400240040c010b041c803580090140c80000c0c503000d46040030744a5620390f241e609000003448460301160203043e984043d10b204004540d2000406e030381e4002c1d00301c2000400c0b1083c030710200e8142030600c00064401d5080103105045242c168000c00c1c12034014512050080c00f030718100c40100c2c00155002402c0d6180640c00200c02d40c031a00041482c90801411a4503982d90386400c0000c80702040740c5000401e405601c070040c250b2300821000700612003014074603903915140c0006071400d80d0360700008140c0b4111420381080716510155490070f02e40e00500802c04840c00801d409104282441954014841d0406401c0ca140703a02e91500c05c0b00d0740b05080880c0460921001399015084003031405000c5500784503e404c4000c030307050241c1c040c5001d0028041401d0601c4145410340f01d05800c1103100d61f008910041d5992a640c0c0456841022101c10000703412452900350552119041c2c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 249248219 1250 249246969 249246973
    0x1303051e031003120c02011704020102070f06030f0b01050c0c0904060b03030c0307050606030304260123150102030c1005151225061709120c030c1b0607080c01060305 73
    0x108102e4403140aa1034050324050030b0109041c0b403d03280129403000090301c1c02070004050801140c0c40b00384101141350020300c1401a269029190000c40c4400d501540c0100c00180d1601800a08982144503a618461082c42c01510700380e607621076241d03281d602c4041e0a0040000100242c21300009500c101000c8030002e05a03075481d404441c5081d070b030340c000712804c1e00c850048a010460520380001181c088480d8003213078820a04854046c0b074111001e0610a940d41e548a0801c010340e22100d03920f529140c1900c071031100d40ca040480e01e96041d11014400c0a06542c01085058801071300003e186c400d80355520004512030340c1d40a801070f440c040c440340d107982040740c1a03c070003c604404030300742d4450810000c196103141c10440611180c454030344a131001048030700c042c01601101604040350300c4000982102d0406503040c042c4450366003c4908a80b03150400b213000c1080c140248518440a1810821000021381d81000a03517284a12040204900000242105090400c0d0810801103803c141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 249249469 1250 249248219 249248221
    0xc0301060f080105010b040e060d03050c1005070f020a0809150f0c010507080c160213021204050c0411040e130f06090c050a080105131b0503030c0a05151303051e03 72
    0x141c460010400c0d000b40e40c0c055007400008107100842a082d0b8049480006902c8050b48904003403000c110756080040e410003034104121825031500704507003506842a100b001900e80f8201c64020400c5d101c4400000442d0000b500d800007007134840c010384130200f0046600405400c0c1d02d44c11034600e407181002c08041003002040d15032064070b040d44110b1040c0950346640d00341ea9a0180343c00031a1058080310001c00651401c800f016060440e0180854254104014a08550890601c2a209040301e04850070350140840b4001d40c2007a020341d803230102c0c0309a83d260a0a083c1032a07103c501e88010203482400d044201100c051103010210f201501d80c00981c20090b020740742c1008043d405250003401d00580601c1400100e0304014403401c0d12400301030b08020f42c00c0940d0384e540400500e031002c0e001100c42910700d0101d2207540510040c800704044200805408100340741c43e50274200304e98080d4580250b40780400c07091384800411221a40d0f8546801d9980303484d402c10440551451506110b548030000c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 249250719 1250 249249469 249249479
    0xc120103051507020d140f071a01081c021203040201020a0b0112060c050405060d051009061409010e0705040b0d1812080606090604030602180d03020d110307030f0807020c030106 78
    0x11401800081c442c280340100c039601d0318030503640d80b6404104ca070000ba01d106016284c90448102900f40031032010001880c050250310340000c1d0500007103c0342c01c0744000380010004031408025078a410748aa901d1a402000c4440c006502c8180401500c845820000006011a803090100802e01340e402000c1000658660045011000c0310680441e0094500028501804c2c0120700340c0381214170081101d89050300b01d0701007401908029001c1220000340da40d0110b44000039008446c05041d1040904191a079094104022484103a01144071508500240005258030104503400e45405c510250340d07819241145100804440c90089200704010203400d0400070645440340c48000c40c1ea5522030305440b20005c0000d948140f032101c1d0760010003000100001110340e0060007545000c0100204005841c101150002c03801140440050b0801d00313840580d142c00411321040610b20780000c60901c40d02e03503006001e4540d007840640502841400007084039108028100c10340101800034080c1e15035503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 249251969 1250 249250719 249250723
    0x4050c1009080d031b0c030e0402030a150f120b07171305160509161206030f0c0f050f0d140a0305030a0f05090a02062a1f0203070210050c12010305 65
    0xb030040031500d014812885030914824010319464200e03030900719003006880481a44c1c19021000c0450920040c005890410360300d0b84040e500c185a1540085060603500000b0b07180c10540350041422510320700c030180010040c0030903201c8080d0340210400c0700c607150300e00c0959a0740124005440107040c000b04000c110025043d00210681c820022140d210b03155200f0b04040c0c6d2450b000321900182443d002420304109501c94500060350341c00c2404800c1a60002c0f50191419508181d694600c07080365282041480425000100b1140e00071111b064140300c00140f600203008212886043e109420206100495196000c40001d000490302412414980588190800c440c12000103107070092226a1304042d014840c400c2c1d4125002d03040c10315040e800c100070354000220b141170403031640c0c50340410801ca60104c140c1030004000102294601070380041111903620001d00d9196005005020743c0903000100c0c0c66420034016000b20302ca03591507070034070114014100c08003105a0700c1c1000000340900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 249253219 1250 249251969 249251987
    0x30b22051f1118130207140a02030d0203040b0708090406050306041a06030a0b2710020d0b0103060e0a09141608120301030b0103060507020102271e1804050c10 70
    0xc0e0040c81071510303440c0e6844050007000107003243c841d58106140f015203060264440300c01c110180040c2090400d456258054034246801202d65203c45108005d615007040040d041d040b161000f5450f10381080c11461407402403140040007a14042401e001030342e0350360400c0d00a424040c01701c4e4a6450281032106e94072070003440c1c103c0383c0300e850008500e0b54240815410042d6800210403081078542d0340c084c401d030050b410f4a01401a070001c0d1240454030080c04102d00f460310020f405030304d5004940c01901110500c0a1140c181071401401304661645d0801141e841182c5c0d0760000340c0e440550410350307003280c03200350b60f00914000d00340e903c4a09090544900107898480f400c6800c1100e21000340d0355148401e000103088801c1c400010400a103150300810f611806034400542480d802d9020b00c0e251203801c04c00c145003d8005e200e0007034a400c01803001c1d41074844403001c45207450030130300106a050003421441032100c0b400c1c10000f01030043c10441d41141050180c058944115818030003003803450 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 249254469 1250 249253219 249253273
    0x30f051509010605031f0b0a0e0a050c090a03060e1f020418050606090d0528061a01120c0309020607060204050306010b12010e1f09050601090b04030b2205 68
    0x1000c10114070050014862002541c4000c0e00800e00d50403542c01340400c140007a03880240280e00c139106003405494400800c0c0c01002640008502414042c581c581500c000410002d0801ca0900945200d60f4030700b030340390007200d402c0080050781c44034101c042400c00703a01803c0c584441c0e0a203410214152050382c010003c80d0002c81c46906c2c003c100ba0401c009503207059800503032144044c042800d803490450a07003510180301c2d900311000170404ca1003186132541810031540c45519807000000c180003c600070142499281000002054074440002c3d0141264804051043c4da50b011140315850080c0c1c0b060f800b2503001081c054444006240400196010f40140f60103401980000500034a1034003e441c00c079440d52504002d560b00341044407104910050503098141c3c55201d04c140d0840798007140e6000f410100d040403805180c00f0700054000f0600c0e620041e40c443d000c0000700085220401031603003004548c14003401d1060f82500c4210058070518002c1c0641c0545119010549054208841c5020b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 249255719 1250 249254469 249254503
    0x3050f22081203010515030603030408150402040b01030903020a06020f040503030d020a02190c0302150f0703120b010203272404090b0405040231020c0601030c081f090507030f05 78
    0x60b555944100700c900003880f81d2500280c0d0418040c1d0907496210140d540210050f080b6400d180e40c40e0800e92030074440100c00b15261004806010a5049c40d0040529060082c01c0500540c42c03259070095540300081c80107800306501181101117201380c14220f82c000e02c0000d04490700c8120144019009602a601d860050320406c00c0742409060b541410b02c0e00c041e0445c002c088d103e0300e0f64090000c49800711100c05540e20b0200800d0866003007070400b500c0114000e03501e17050042c207035880300300481e070314042c400d8199030080c420030703050000e83c0b55a0880712000c400400700650340c40001c0b40240007801540b075050320321010190751400001d8040c00803075a402c00700344890500d2000b4401110002e40d0040d4009050704005c01c1d1065039940340981c0b4065500b2001a036280048080080743c22418402086412440041042c048107000c0c900140c02c03900c01411815400c2030041d43e103401c3d03041e207070305505481d1150380341070044c103000c601c00035600070f030590302e4074101031500343c1d02c0d40a000b404414603 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 249256969 1250 249255719 249255733
    0x30309060a110708090609060304260c0c040f0b1503070801090b010c020405090c090a1a0414130c0e1e090705030d0c02040b12010204050108090105040b0403050f2208 73
    0x502450142041242800b40460b1400c4400d4842e2403059000a05258100000704106101900c0c2d50300254401c82c0075488074130422a009030048600800040310000007801032007810b02c0b11102144012003490111070009404a10000d02c0c1c02070954000361540c800010003502661001c060021446000395588050080ea01d904040301100c2100388c209002501150760840182800d0b031109401c1075940b01101c4400c100840020f101d110100c4040e4805615007004011000d1107648200411034212001c2c070404e600101c00b100005002000c4220b130f07060700d0200c0010b1043d007810b9400684500e420a865901d080304034000180b445070180b0300f01040340c50000c0c404c00c0c8042208070540c0d500038080c004407444070380f044402c80070030082030f41d02680d07030b0420740c9540e654410802c400740b1070a400540c440c4c0c540000586a10f200614480c41a4100820000000c0181d030300150b00c15414285107072078000d0340034003a00a0080c2a0f1860351001a40202d08024114200040885585900b05c48079 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 249258219 1250 249256969 249256981
    0x1203080f0a11120c0d0504201522150806120d0f030c050c24180d030504060f0e06010e0a0908041406090315060103050a0501030206031503190503030906 67
    0x80b9200034044002c40320051008505240c4407681207604510141811400d280146031a02c0440d80113642c102d5440c0305050510980400c4108501ca14500c120740740340103810107180c2e0782103520840d1310050040c410420007243c0d01d40381c01000c0f0302800300a0f43c8a00409640700014020100a6503035074440c0032181c43c1c0032102400000d0289070490b055480090415050a09030040e191044005090100034040350310240c400f0030840c3c02e403030540c0d034250303c80c02c10701034580e01012406041040711182802ca6a1705c92840025082d802c81450303c1d0008686e0340740d050040c014904403011860301814000941801e00b8002010b50513942c9245c0f03034407038a4491003040d0003214803c0c0740041c00c03c00b090000f007101c00081200ba9404000140c03000d40b4002c12400001d04002500c40d40e07209101c3c5000038008156403600c1050303407002c08841c040104d541560001303a20f501000345108217802080c04062019282440101007000d0b07052115195620b007440c1c49a200c0c1c100301c80d0301030580315600000703030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 249259469 1250 249258219 249258221
    0x11060415081515090f040b100302130f120f0305040f120201030b09130b060a030209190f020418020901110f1e160b031b1201050102010b030a0209070c0c1203080f0a 72
    0x25090518500919000c11307a010b2000040c0142e85070382d0700070303968401d101c0130340c4030922008074100040c0d03001650f821307400c85c42034100c5c0060740020506510104045c0400203107148480d269941100110303194503901e18046036680710ba41c0003c80d05150308000040c1c2440460001064280300b600c06110f802c4104041c000c0b1000b040342c1c4004401c2040303000034049148051403a812404c007030501c040260710b85e0040b0344424402c0e25480401070392912003910348101d40c07091a400b60807454055140c2468540d101000c40318000100440590020f0418016802101c0c0081507030400000e5032407000c00804429200c101400c43c907235204611400f01000e4090201e4a15034a2203d4246080500c2c241001000c0c0d50304014145011212001402d01c6442c1178400600000c0480080500b415810003000a00b9180300c44000c40c00703035004c9200c50005a90b81c0c243d00c1d40c00300180c80c00b28500221030904000015040d801001021914844c007400c1c185c0c804046442260a0b48803292079440e4400d5442c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 249260719 1250 249259469 249259489
    0x280207080c150c041401020a020904050604140703080712030e070602030c010b01080c0a080c0c0f070510030504031205151e090603070303052704150e07050c030403110604150815 78
    0x144241c0c100000e1100c840301c800005d50215040c07040b181d1990907540803820380241901c040c0c0709030f400041008200a80b9005005054088801800c5410700e0355076081b0702801410310040410308401c000303105036031280e03204e0001150040102da003001d5951002a49944c00740e92602070035400e042400300c2550154001c14066019620f0716854000e00c0001201d02d041d000d422285514400c102400183d0010008005103001201c00b918000c0c4c07074101080400702200c800c082c1494203040801020079000103009280d401039080200340d541c2c4550840c03428040190400307a1262000300c007401030404540d44204074041c00c2c4e50a40361900d40700c0406554045501c00240081c404002008021106400e41060303120b8150300c840107221050005026182c003140c0380c0d01116000441007020501400e48207403c07942d076080407490718030001c031155164400c1d404050060103501e92100301c01e0312001c00f264010200000b0010600440410007031500409482204c403509440c0d81860003482c1000d540 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 249261969 1250 249260719 249260731
    0x130f08031309090501150306020c1c020c010f0909230a0209150f040506030109090302061f0e1015020307030905040506090402010c0c17010b030712050303280207080c15 74
    0x40381c0286800b00c4103028203002c0d4070441d20365481c1c005400b0942954080c201c061441440c1c051303101d0070703481e0340140380170825403110441e80c0c040c1c800f000800ea0040381e00a442c0c0c1003861714078181890030200359045c200c0d942c000e02110703140050031030b500d15070004500c4c0200c007800280000c507101d98081400b42d000e0340b10280e92040f1002003401920b20424010003845c03080d1480507003400c4e90781c0001041d81d04240c0c402ca200e40d84071038a0104050341441180d0344444d07407005009001c2d00800b074003e100041d0b4040c00080d103c00c0004285040380c1074501070300501d1f05800031000d11203003503002900c83e0010311080300400c016030404100d525060064070322400c405802494641c1e2035800440700c07070341c80c01c40c2680e91543c070f0200400c00420103400d000301c0716021000401d803503000d0070915240441d00e51281c00302180c82483d1900241000c42165000103070020f440c0e040d1110440d01120182c84030702e1340c466070b610002e95001005070981c0640f1040072480c045d240c010443c9900e82907004011501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 249263219 1250 249261969 249261997
    0x5040918050319020109150b010f0914040903020a0602030403091a2106010315031b050301050609040b3c07020d121505060f030a0506061c20130f0803 66
    0x48881c82e241d01d040c1c014030041d0184004580e400407500d901d040c7d04812214070b40c10640315010b801e62960800c000000e221017078a04421081c5ca81a2011000c05600740c806101d19160307102c0d6414544200a40c40c012900040119540e00b49480d01820f00340440c4203811050294014258001d00c224007680e81c60070035540252003c0700000c2080359540c1c8000d01a6052559402080d0400d040c1c05040101451042002030300588150080104102d015403145210707a050508101864484400054001e984401c7d040d00646909242c00b0703040b580031281341106a513444030521200c01d280001c100c0d0042d040b15503007954541c3c1104a840d4962040e510010880c1107e41020680b010b070b210b50056401d4404420b956502c40002508540c00703400045070111000c0103204042041303104d1950000c0c1d0848a40745440d402c1040c64500305d1256241e90041a075601c2da1440d2250503004180101c0314400b222541d50800641d041401803441c080c006042010b060007140d24075001088403016a94686 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 249264469 1250 249263219 249263227
    0x507080703080c0c0f010b03012412060605090c030717093a03051008071512020904020408031801320912150901060b0d1805030a050409180503 63
    0x1030544003604060840c6a490f0000c000031050b001e014030500a04680c3c0d14004100c03454403200301401d540b84d081b00c45803204941d00f0410101c0e00c030220910b0031501e002183c44840045406c1c2603008001b01d6005075001540c020800000b00c4c0031000451003512692180828010940d0070251000300844080b109507000103440701c134004590540d0001c4406200c01c5c02118841c40c2841940c05203080910400300e034451091241021024445a0143c80058014a0798902d002e91203911161b076600319400703103c41006000c4003880103404a51150b100500700303642d0760340d440351160756a5005c030f0f00002c82c1100404048401d580701e604003580c07060708002103007200910a0180a203900e00f0980c0045103603003c02441d422a1144036047c2c0510741c8100180405600a2100013181040280703080c2840e40361010034482c0e00c8003a070a41f100003c0003000021088140c00f692201c11513a40c9010b030a5100102c1c88848150b40440100140e0360003d000344180707001c1d0643e460502000050003402030304140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 249265719 1250 249264469 249264473
    0xf01061809180503041d09010504081c020f1306030f06080601090209010509040c050703110c0112090f020d060e07080c0306071b0804090c11061015020307060203130c050105070807 79
    0x240001c020001035512480c0b800b0340b1607450900c0d560055004001e0034800c00c010541044c001480e680d4003500b00c0000740b04e28a440c2d590a100f81c46240c195910000d4802480210394565038186c854014460036015a40c9a00c0719a0810402c0144030f9400000d040c0510400c42540031b0042904803080f0400404a903420041d00d0000380d0803014100341004001d01020250359254000d081c4403400c47e80702c080d41d460040c2002002d80c1000501d05001c0e0344100000a580d9030311a0700b0f458001420380000920142e14a40022610119440690300540415214007480f27150303840190420f080070200c3c2c080d140d55034412900d8518081d060780c1d042c0c02140001d5003060284c49500c691070a0704c9641f1600505036035501d10590440d41203a001103070748001013000300741c002c01d0308a01c019006008192500e400541c50301105400c1c0508820701c900880c9030164070b030003002500c0000e0b50009055407a46400c00b0501305060305140d00f512045124240010154003401c100e40400c1d0304648181c0c5006a15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 249266969 1250 249265719 249265721
    0xa0f060501020c0a05360405060c13030210110102030f061314040b04050715031a01030e100f060b041205060a11040320150a030e031c0e03040f030b0f01061809 70
    0x31b6061840008000c46414140c42042200220b8030500303114039098245414082d103131000c0200500c00b8010304101e500c1345e20020107060380c21a58103c3da050458030316620200d412503445415501250300110512100d040c1040ca0944240c9068403100404041042403905882100e5444c00d00c0c45808400700b404100f6a0254aa02030301031011101010350b2024442e0905c0541c2604c81d00007a6104000f214450340c038405514448030074a410b101d032595030760110f515800c0403814251031554030000341da41d40c1519041500104070120708103840d181d80d0a0a03210b5040380610840c0c80713009010000b98810154072501d400ca50344c1016150400d801c5541d141ccc00754030350400120340d05491090030600d5a54442800d0003001c40098055202c0c002c40001400340d840e0b42811440708d410520000c543e515143c42804807981840302d02040299010700c0e0607042d417266410070320543c2901c0e040030080c4151070840717500401051049816603a13031217008031104410086d070950352104000d000c000003041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 249268219 1250 249266969 249266989
    0x17060a0b040e0604090506090709050604050f07050702030a06060b21071407060e0303070c120c0305090622080a050d020d0906050a0e0d0b0702011404020d0605130501050a0f060501020c0a05 83
    0x2620005d141981c0d03403149840c101007140c40200950050005005400381030240a8220006503014410f50614421004407032000030041403c0040224100095540c00c00c51840d00310742090040155980f01c0c40c00340026403001c185941e080f981d60b0340f250042e0119807003942c07081a9650303440d0320f003120300841218291b00000c0b003520b07010f843e000e40703210320182031001354005c0902d80c40e48030355011203240c9103a00c4400007444000340020a2034000100e40c00c40c04442a01070102c2d501650b401031051002040b200002c8420f02282000e00d0100320380e00001f808158080c0100211000c624076041c04903031b01c1d1400d00030a400203034101e0003002224001c5010f01180030860620035071418005c00400c0e170002040390b05031440c9070040e00b40414160203204000f0300200e4902c01c1384040c54150003003558480100c40080007071b5034a4001481c50b00d40102d00400c0543d0040091040381002c040b5071010703005c12644104070718a80940066190700000303401c0994000a08090300e09844c0004000e00008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 249269469 1250 249268219 249268231
    0x6050309150114010e10080c09040216060b09100f03020103020304230a140109030e060c0c10020703110904030c0b0912070503040e01060c050619090c0617060a0b040e 73
    0x101d824076032a44510003500c114040c100003003031807804030701400c001010450b2031100180034540d8003601c14400750f4001c205030ba2107074034022416511104400810700174403c40203a0100700400c20b100c442005074039084450b84000444458a00e62550300090104c10307868032800c0001304c1443ea040006502a80146070300c0ba002e4241c50a0707801802803039082d140c002c5040e0345503c3d00400c00100c201300e20089c01a200801c910001c001c0340e1b14540c6c0103040705000e103a00c82d218460125604826400401202212503400341148080c5400041c01035a903958500040361a4001001c1e80c1c001410501c071a144100c1c1c140d902c148120400d03440b12844240b0243c072003501800751102083d07961100c54001d0004a01c0740c1c00440e9210b180c0300fa2105c1c0340d101a0849420852007010540c0429000168030340c00411408218140846119070341b03009181003000240324013040100091581d40082c07030305000441c0c0400018055807540100100841e66000e01c1d840c04c2c10a000c1840078124203080554403130303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 249270719 1250 249269469 249269473
    0x6050712121103040624050d1401021b0106050405073216110405010302360103060911040c0206070e01020313090506031212040f020d02040906020307111606050309 72
    0xa103044207000c0c0ca040720b8008080d03076400018041000380b40d115624092100004c250040401541801111000c5100b0144680501c1748480c042c1701c901410411030030001c1008640da0f1291030381a60b200f684219074403600d075103085e0300010107080078006c2a108010b00d076a8500400d040c114100c600c0444841c9000f00b10056810799420815000000c003080140003210800841d60352500d00061980c00000b540900c1c00c0070700400c01615410310604010003450100c17035001d141c05140c41a0311400c1c0040380e4072010300b08000000c1c090540c0c800e5089a0080c03c0c001c864002000a00040e9982c200324000142c3c0640d000624052048400040940052040d41d180c0743c2c608101ca14019103640007000d0440e5560240462840d0070420900940342801c49a41002e0300b0008a01404038001c0c40130b803058408200200c11560360501c99010785a0041c02000a20361904220000350011074204000c10402001c52225401c002503940b90a001c00d2021507070a420180f003161242c1001e0240c00443c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 249271969 1250 249270719 249270737
    0xf0608060625030305100603140105061c051f051c0605070210021c0507021203150f0d12091202031f1e0507090b040b0a0f11010e070e01090606050712 66
    0x480d01501c9142c0c00d18001d54021a46090100c1d0006100300c1035409402494500b0350108044412011114115031085a110b61620301c41807140c0e8440c803440083d100c0b070602d080c04020381041440d04149099403002142c103039883c1c83c4c50501c020040d8860205045852050b0504002500d50f0005644040148140c9403201c0c0c0b9249108103903000300e1150749403610301d405181c08540c1e0302d2180a5014200340b00400050400400202e000c0c40060710031010700c840380d0382c10800c3e80c940e10185080100081d03c4410300a05030b0401c0625821414098070000340102000a026052254265801900100074040030f5000c0c0128180d040e2444100c2d04c040e80d01d80e00d9004451212440454420008034000324081c40d00304c030300030070250280c0c000691450082c00140f01400700c1406440303191000d410051150010701500340e072001d80868200ba002e41c00e00c03d5092503131202160783c80483d01410001e54290b600c40e40f0071400d40301d0900842001a1040c0640350114182481c81e0840c500b0328100324001c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 249273219 1250 249271969 249272017
    0x3180a08071403010c05071a0601030612050109120203130b03130204020313060f0203072c03030a03020414030a050c010c0f020a0f0501170103051f23010303090f06080606 75
    0x1007004542c041503001600041c1114182400e01850704688203d00e009031400d1884d42d911a070320781c1801615000000301c140083c2030359029901003805056820001400042c0b2450554060180094200d9660100040030b070340705400001500c01e1a1180700807420300340c0c140b0345805e00b2500010b010000901594807080c02507116480198007900010192020321a114205442501d513420191422284100108024150322504000070f000c00c0c1100882124101d1005011107041c84a4007641400005070302004250541e00400c21110240845400f8100500401d0703183c01203940c02502d03c4d00008084101c41d0321952000002d01d21aa844440c0001e15801140300d138111500000500480c02c0000d000781d6821410906105c03034021030245640d030440d0f45043e1150340c03100c030316003280c03400c80401c114482c1503400c000405c90040b00c44100c4003a40441180c0c6484080c4416008a40c04000224900ca490761603007056070a05c0d1a840d199880348000c2c44102d074820b80d00c01300ca440040740d500364 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 249274469 1250 249273219 249273223
    0xf0f07080a110a030e04020711131506020c090c0c0709150f170705040b011205090a11090906070c060209091603110405030a06020c01020918070f030e03180a08 70
    0x4510302409100da01c40c500341c40c000d400d81c070b051106111140e11196800c400264442c141401d02c00080d140580c41d800c0c2440d01036400c40007410040d0344440000350106980310f0035030120741002595112120802e541ea5000d0382c4038801c3c6690180c0118210000a180200c6031004000303000d1290f00f1a0340060f0345480d030800700c40b40220003205124402c103042003441e04204075400602501d6801a41e41c0440500442d910700c410703c9080d0060ba111b1512003580d80c050300c54018010180070092050380f4008201c00d4a5040c0c4160480d250912044001c074203041c40b10541d485103284100400c0c1d2901d410200740d40402c0d11500441d40141c003042518825112400c081e030140c0481c4103041001c5054070b2018064030000d0100407041a02131004200ca03680c00120001e80c560070010040c0c2e43e007000301109019120b80240150020b2509000c80d585030032400394248205015616a600400304540490986008480082d0709610500c031045803503c0c800011070032038000400c09c162a030740d202d1001e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 249275719 1250 249274469 249274477
    0x2003060d0c06171510030e250e13020a03110a090e011b0e011b1a040302030a030f0204061d040e010509030c10060b2d04181401050303030105060f0f 65
    0x200051085849980d500f840f15403416003014402000705003c50104002c502d02d4040c1d504540101034403424442210001807105410a0846400c080000c1e28028050143e4103054804c01842d200c1d4100010780910b80311014400007507000b407902445501d1034850060362a0513490a642c049280c1e180001c00f10b06510580a04c19941c00010403000603041400307580300c14504804040c0701e1103854070b04035685d1280e4400950014696094011071550030001d6817840c180710300c48032205a200c00c1c08285900000070301004001d42d5014006a03c509050000380d021b640300d208041000b0f80c402296010035801a0041400003400005688589645203400d4400a41d00c1c440d864100180b000000b0710103000c85425140c4d14102032000038030300089490603215042101044440003e440400e203200c0c500044500068401900d49480d250380b44482a1120030401e10000e515044900d1056200b150446040b120010040c504581c0780009209403540240010441100d00b046012100304002020b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 249276969 1250 249275719 249275729
    0xb0a020f1501080f0c030d1404030204090c051003110a030506010203091009140109081207030212040308090a1d0703020c07030c0b0c0d0809030d1127030c042003060d0c 74
    0x10311a07945000b00f807901380b204900c0114941c3e001150b9461654400107145c00390741c0d410303151004400c1c810620080180c0101d800080d44076041034216010301048181c0c01082d618115003900c803510118009508030740e814400480651000c3c00004041c030f000354031039580000b040c0142c92034214000c002803030503500d130109840403038202c03c02840070100c0303612001405802824024102070405c9002c0c0e9480007000c9100350003100001d0b01d82c0415100f8070010520002e0702101c552116142e14020300250402c5580720700402c03040d080010202e000c0c4d140c074010301a01024002c0140c0303801e10200c001e5446100200d075030784100d000000004070480b821100400754100f4194031150026001402e1509119041041261100034016180000310444a0003911484001441e45d01c0ca002001280174803500380c04204070340b504d445452600005c0802c442202201504c01c0b4000e2082080101ca600c0b200028a030804001c0500300c401030a0020f41c0c020034001d208442090a50f42c81d41081a019040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 249278219 1250 249276969 249277003
    0x3060112080307090e04140f0a02090112080906040e090c040c05160204241d0405060c090d1509030215010605160606030f0f0b010501020c0f01050a030f0c0f08100605040b0a020f 78
    0x840d041d081c7c018080850302d0480e40c03020344207104040d00041c9849038180100904248550100340c06c0000c1c00c821140031003800b0b0034030b607281e941d200c0152a000404554203800d50203990741800f0185024400c014070902d0720348809040c04454201050780c0c510301c1504a0708542d944159094500f086425141121840c415543c0030a007003500c410301903018025a440020040d40a2000061010071259805000c404143c0d8403000c10340c0c00200701c240300e1000945410703c404502081d5034a80e400407400d480c080d800f11102c0c42101c50794000325400c24812400024014081001400d4007120a80d41c064003400d8041134290310394503603014440c0700500c00c54028541044000421210a46c0c41340145024000b500c41d4608040110307244042c0d612800381000340001e1000000340c040d5008080c0d003019468100040f107040c2d47c01802101d042600c032400b00f003410002403110044004000140c81c0c6030750342d41d0300b800d1401c1080c1d41c00b6049581c1c0c0e00150b000340004800c08120420244c0304540c42c0c251 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 249279469 1250 249278219 249278243
    0x70c030602032806031505130b0411130905160608010512070b161b0e01060c050a0f08030619050307120c08011e0e060f0610110307060f060503060112080307090e04 72
    0xd0403d4010051140c10703246e4a007440c040011a604400300050550b40016500742e0945c1c440c6806600042460f041c564042c0541c101d20008907499445180b00134032850407100c11419240c01a00d80100607c04c41c400a0781803001801503041003500141010f5400c005c40c1c1801e9217a124000482d041024602e180c00001180102030011000c410090080103026500d03000341003081064950b2014011002440004d0840c0800c0160412001000d140c000e1221070b9144102c0c07410303034065441522442d200e1881c2e01e5881840711200301000003101d900900400c026442c110000c2140c1d481034200f928400b1550a001444100a010340400000d5818280d0740c84845441c4c0d400407101800320002143e03201d0741c1044107502c0d8451641b9080882100c50484103a860001159055114260440d41e0300000c80c0301c20400510303410003030035840480c009000654503841032560369a02403240820045660b03c0800101c2e202400841d0881440d2034007903103240c0c892404084810703094408641c80c00f0544 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 249280575 1106 249279469 249279473
    0x141314150a0201050f060f03150a060e0f010501120b030a03141c050405010b010c02030a030309080909010303020d0206060402160206031005100203040911070c03060203280603 77
    0x2600c4540c0c1d4503a001d078000d003c0c00007540c0b140920798014002c40d0741440c1168100b1050403007c1c000700401150b00881408a03603002e408002090b5540901007131702d0030003650861091171010004940e6500d808001000341a2500145409610348071031222240d0b00070420500d40d0f41c0501d4140c0554100c0749582003a8814281d0700051014000e06010300b0050b90f412052107940914004c00420050000568004501141c000c2d40354004e03107407140005e40250b01040045010300d82c4542050051404100c00b504280c20507000740e0f00c1090410311540e410056103610000903a825821f000822800610300c000c8004000d01c070380800b00000c0d0455051654a100400c2c00903d0140700300c00f03940002e074403076019000e0090140c1c20100c1800c841d041e1075044032411940304100c448180d242d502c5d660000c3d00041d002d041000303008551540694884800d4001441c500078001070744600c2c5d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 249100719 249280575 := by
  have h0 := BRFrame.cov_init 249100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 249100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 249100719 ≤ n) (h2 : n < 249280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
