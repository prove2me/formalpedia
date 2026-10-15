-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5465
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:09.614272+00:00
-- url     : https://prove2.me/submissions/50c69158-3f59-401b-b440-afdcefc05aa7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982733812 ≤ n < 982913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982735062 1250 982733812 982733831
    0xa08010e030301211a06030106090c03050702070b0306180c07022d0102030406051c0603021e01081003210c172101260109080d06080601063b2809 64
    0x40d0406090380030514a50300411150751f0207520800040c101d40f0000c100c2c1e02d55440d070240140c0000c0f40c901000d03005d0300c5400140a1084811a8403551000782103841d80c40713100c1a51100c2c0c0c00c000d01642d01090003446a0401601c0f03d40c00c903442000c1248082450f80b170594058400301300b9186009045420504c8100725840e0004155108080000c0b036140182d04ad41d140800141081e40c4007944c050a80508a0009041c2c5d1030b50030a50002a0b84d800101c0d6956540c201658045200c0148580191400030380314107845a5600c1c6070710350030700c5c00c1354071090640c481d0103841000080610f40c61000203280003030880701c030f4004121402480b86040c80d9600d0894841500403403002c841100122004500b5440c503001e5015160882d4010f0b6199203401d4507a940c500180543c0c004c0903035a1240c24008520b05000382810f20116002c140301c01c0b00319041400440305c260050b00035041480810900100f695035003070f1440c40e0701c0d458511040403605003070070340310400030076170f0000c02101c0c07800c013000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982736312 1250 982735062 982735073
    0x7140a020d020f0102101401090605032103180d0503010e0601020f0a03080603031b010204030203010e0f070614120f0403021011030126120702030d0801230a08010e03030121 76
    0x80d29250b0115060415140e22800503030034000c15000f00005503241401c510706078004841e45905a40e48604200010341e1204281036a50f01c04c81c10400e20301c1001e020105111a10b1f07001180d0010f11311407600500b0480805032443c1108010440c03010600100062110f1404070000c180c2c0444c0920040c03204020500d0281d840e0b40c403a8002804000c90b1a00007240d9440400071103034400b04444c10f402070b056042030b01d24001d41017030200324443c1d400c201c0c1c0506100350010301407542c503058901a18209140030780039107014481c40204d44045006116020140d036411081034852341d400c3e13510305400c0c9882d150003404c00c102c420944407114945800342c1c1604540405032819603500044560300410b0369003806a400c842d4880040043c1f081d030700003030201500c8501801032071703100740d0843d03c84c0303042220151502102402031100b5543d640c86140d8074020741480e08480c032400644810b183c562500426030945000c1c80c2c034030345250b01c00401002042074001034680c589051054a040e442480d6862 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982737562 1250 982736312 982736329
    0x406050f0112020d1e0506010302181b0d06090c0e0112020c070b03090a02031c08070f0807050a090b0f13150203070213110d060303020d0819020c0a1707140a02 70
    0xc0c4c004c49400030310004111191480135901203912000b051240e403a450016a80c842c240002ca018464013946414be160b07466a0041c040d05000b2116105214404880c1d04590802e24211083c1b50300d81c0301c0098030382e109100b03031301404040d941c850f10950014070005d0314009105c020706003140c5c4104028a04264080783d40001e6a404032510307036907500d55800441ca06001204040d5150194141c0b502c4c01000c9031501614810158444034280e9841c10005d496070200140d20b2400b0800e541c0006143d01d106100034400416141020144130b0744503104034126404c50042e98080c03d00001d880a1400148408040104480448083c020540e100001d40705d0180a100a0244981d03a0340d04003006000c1c0c0120340c1e43c8010007181034540c0b0420179000c0c042c242520003500980241c07100301e035100b48540031a600c54003501d42460701c86104562408002e6014191120a50040c120014002409131201011000401180780d8807002075007081c6010450107280b0b40305691220b00103000588034041d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982738812 1250 982737562 982737599
    0xb041a06160804080f070503060907030f030507020415181505061614030d2c0c120102220305151b0306040618090b010807032001140a02060406050f01 66
    0x32041c89603000740c90318034140c0c080c58201c2203040c002d001140504200008090040381d900314115456030300c5417503503e03881d031035240000350031014612203280219000d407004214883c406000003d11505d20b4a0540c441e51958010506800c02030750301080d00445400784180705000d26030140701c0f07a85800c00007584c1e80b2551001c0040a0560702d04030741403104c910b280280071004242981d075a00300c001500390091040340001c911600b00e50024210154000070002260942c41d0001d107020020074003084a072041d0388203240c081d9074080020066256099101109100d0b00084103103100c0d065181190801c41816800c10024640c03008001d40240c40c0039681101d04107080c40640d0700e4480344003290140ca00c44d00034404031b014002c480501482180c9c05030040f030b0b001e9607038900582d07203440d007241d00c44e0524880a00349030546581070780382446a0700c01082080d41410720005402d0a0600114980c01040c1c421003d80c100004001c144172560085030350041c80d10411407250742c1006400c0000c0320f43c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982740062 1250 982738812 982738837
    0x609080d2406050a2111030f07171608061f080f01080f0a030c030207150c120806010f03150e04030203190903030f03020a031d030703020c1215091f0b041a06 69
    0x40d850b407181e400a1b0700c02108004500c217841c2da01e20f400000708030060780558004002030340d40c070b581180d0b6000c51616140961403000b4420400b010001d000c0318410303006001c1c02d5002c8254081c03c0c104d881c03c0410711210003803d0700d418201349050503404c0030440b0141d01065060300406d03041a1101c10104800d003601e645400c11040b08480c5003001ca10302402504064020721344001680c2c01180c01a20f12125544074080300c078240030090b8030850f000d00341501c506004c228614a01e03400c1c00c1c041d800c0f03018046070342642100c210303a560300030241c0700406440980150b000007070421042845c040b090039210a15040080d078580c40c50350024140300c40484100c042590100344044201c1c401e07008241a03100c004602e03000b0504521006859038050340c0118050300c1540c40003265410071080e6110740398111406040343c9030f010f6800741c0c140e03000201420503a000c2d400160340c1c0c025640200e03400c040d40c00c580c0002e4000ba07001c1803104070384040f60142100c040c0c06144030700c1c90390b030502111010203c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982741312 1250 982740062 982740107
    0x81005060409121206151e0f051c0221070f0e0a06080a0f05090106050109050f0d0b061c0606050f19060315030507120203070605160609080d2406050a 66
    0x100003c0d0003080e05400c6804122040c1c01c50a00a641c48048580f402e2006040c0709462581c00d0000c8d12034105030000700005c11340602c040d010071000d0801992140f11040400361070441080d000755120240029030250709030102c3e081c030074030300c0c1d010041c02c41d0b410781420001513001c50791001030602d5041b03100e0030342042a90000140e041c1041e03040f640b842380b040d48050116050080e5154041d15041c05541c0c0020b14014000800746410501a0694840900340e502034640644844400650091480b0b401c10208418290031403151610091002c0c01048000350380c60600d0104402d407400804601c0c0320300102a044011108056140403c48126040000b510683e1401240c001e412591014045004400000070a19000d401d0045068030071030a507414942c4488040c6e17500d02482851004d42e8080100800016074203a1100b8001030040c0c0b502410213542549001c20345c3d407100c84650742440c2501c5043e0002e051a88400701401880c1802d60400311040c0005050401d141c19101c05000d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982742562 1250 982741312 982741337
    0x10f0b070609060f2d0b1e01020a05070e190b0f1e120615040501080a0605060406030b091e2808040302060301060f11031213030306090608100506040912 67
    0x240e0101026020413002401110065910003016029905802030359011030545a009400244111259540020000444150a0b02001101b403050140850561040d40f40f40808150108a0b000003410102d4501c1c82501d061803070704030003e44102c085814242448071141c030315514030904c0b611210050310b464205d000b04140c03202c4d19004c0406007a4001045503201c4603603c0010138400c0c41801c3c0b44903541c02c16000001030008890091103214210381043c203502d03002560742d4000e680c21032001840407801036101e07102c030b030350003402500d0407580c9900890022008510f4186030f0b9004e5240c040c060030016900000d031518005002c0071002c5a00c00c4500c00070100020f020a481c040c54010381500c0d100e40c2c441030b0150040084010720b070003098030f07006441103c0b200042110302c109a0080403120944480396644041800c4000c110f0515441d0f410110344101540f00ea0001040103200030003c209945200c82c080718000361840d80900e041c844410302281105091000050003880c00c0c1002045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982743812 1250 982742562 982742573
    0x60a03030c0c0f120308060a0e01171002030c0a021005071b03031e0e070807030c090c120e0309011b0506071b06090b070e010f080609070c06050c12010f0b070609 71
    0x325a00036182a0f0300810012501c50030900300d00301d4142c0300c0e858409031382d1203800800445500520403c403480c2081030040c0302524140701221802034a55045612210344128448140e81040782c030095134040116800271099030410046182d00c0911200300142c1c1442c035802010201c10b810902e01c04000315046804240c40381d444122484c8450012810075690700c035060010341854030f003020ba81c1c070403040045540303680841d448040700e6001208611403441c149440c070292940c07401107014001c8110142e207003a00300d40a0041c215910a0155940f40034610000d09419106280c245048418150040c00120005a49d94104215081498005a5003201400c7c0d40c0f44200000b0482401c1407000c008010400da0040e004000a0300c40c61105080c8030011500b404090b1803000000e41d240d0b020a14604101c003945402c079009141c0b1480c0301d80070751a0003003500c40c00da41122102c1d02c0050010360341c0d500c0e072203202d014007480d0311003540c02880d01031443c965010f0098043e2403541c0c1c1d40101800c112 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982745062 1250 982743812 982743833
    0x15080a14151309060207060b01052701030b12102909040c1d010f0902070503030f090709020a0207080d110703080310030f050618030c0d110f0102280305060a03030c 72
    0x80402c4010311180d00b5a2070620302a42080504480c0b00303091080203000c0b90f025505507510307005080f440f8102c1e4619001e400c080240722408403814190350f540300c07420303e07203c0c5506500c1c0f010380e50b40100240ac03d4104400d04075040d480c0e0f0340b420b0324201c0700040b0030902180152500500300700c400080c1c03501d9908004206034450342c46040e603800b05e03510000c1c003990000e10389412541c0102d05403e00c15620340d0f0042c180c0c0700d02e0034000c0c0940c00400c00104111900d102c240d0708252414100e40f190f81c0c49a60031022030340000494800b5078812081000035840400c04940140c2951601986200c05c0c1c41245654040600004101060200001e40654000e0360884000c41c0c220800c03902c8403009080141e111007013540c80345450000302e41c10044143c0700208940c0342003c01c400030b160800a1800884082e00d0507104003001e4012460100354a050900251402c4456030b000f11000900000c0070a02c2d1480c48200401072508040c10801980c1e0751844200440ea0542011801c21b0311914001900a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982746312 1250 982745062 982745089
    0x3120106021f0f0e0a0c0f06020c0f12010b031e010b150703050c033f0c160312020a030b03162907060c120b0613050114040f15080a1415 60
    0x61040700c17114000d100c0d015070660112890350000c12039480d180d9008030303160821820102d800c400c0d02c1440c10014140340140030310f02c58509000203807401481e0000b80c185212000203c0c0c0700c6042452100c1d40700e03020b1041521403482140e8038043c5c8001e0403802152030048500140c140308000c604202c5580003441203d00d48a105182c1001084d801da8a035140071070b41844402c4868035030076650801d0860501164018003111200034107000f10010006150b200c480402c80801c02c03012103044204560b03001500201115450109000f0064010305250201c11410304803180d207411001c00044180705600c080f00015010038407140030407070060316038500c03034054000d02051030030074010080e903404070046a140302e40003020b00c040011042002500d01889403040070648420000700a41d6000d0b404104028400350505810141d84100124841c001da90005000000251000c21101d0784003c030aa8403501083c0c041142d03121501d500340c3c0d108001003205260100d80d454081081c2d44200c41074035030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982747562 1250 982746312 982746341
    0x102120d020307140c0c040f0f0501080a060c0518040902010e030a1506270510030212030a080a021602090405030c0d0c02180606033603120106021f0f 66
    0x6640106140d400294000ca881e0301c00506209100310082d82803404031241c40410000500700c2481000400000704031a4241d0a013540ea01c034480803248540c0c0c00754500030301200006d8000201075050240941d030803a0008003c10400300101c269940e03881e4034004a8440c26600000c50f07004520060343c0c441503590001d80d240c81410541410855a01094502d0380d810010138800c03d0f80d582000c00e50341005212080c43c910031001d1038280754080d5805194004141011181d10079030b1780d00420141d03d1f0300b2801032016000090b0024000d178010110640182c0303504da08626003102d40380c103400c420400d000001d10521107100844d0a0060800584d0038880b03280c416103403500a12500505030100d640400c80c05240940f002020700d0b41c3c0030861520581018000501d0f41e541e03082c072480040312481240e04440c6441003010380322300318106542440408580115603500c501640705902840583c00f40c8215800301c1c9d10090410400b5844009603009104041003108143d82d0309400361402c110741410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982748812 1250 982747562 982747567
    0x1109010b0d0c26040201020f0c01020307140c040e030307030c0903081b151e1b091005040305030d1e1a060f09030d0e091f1505091305090f0309091302010212 69
    0x30b0030403030f07001c0c42c2c0a64400d03006c40b00c1d8583c00d070414031780341d10800c078800d40960010b0140801061814034101c6084040b5000d88102d035000500290072592000c140c105140d10100800404a0b09442004045825401c140380700d40c3c40c641c3d03820750314498021741d9003885c010420b11407245003003040703100450401d102c0c40318550f15022003a02c000c42200404200107280c0000403541c001d400f1000f5910b540f0041401f149001568810320802c54a030b507125a080220400c40000032400510107070400b03044141001c140d0142000003810b44400000c90504013618107420042121030202c0c81a034490001c0c1d615540b100c01d02c8041113801c0c003076250400c0d01400303800c149001e5207a00800c105820841100c0640c295194840a040d850000101d00b07250701005003400c2c4101000f0520015000e12646003d52400d403405010913200c4030a811020b01c0ca54441301441021803041c480c07a00d41b0541500110f040c07070b801c000000d10702c050103030000e404281c1d500c68100c15a40709100014402e02880407182c0d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982750062 1250 982748812 982748867
    0x1e2416050f0912340b0c0d210e01051522050705040302040213081216030c0609050d030e190804030206030a1b08160804020108042d0c031109010b0d0c 66
    0x540d100c01300a642200203d60f0040841c1035100c140554031104000300041c40070408000040e18564042e08400c10786100e41c1c4c115541c01c090902501d4042007221700049000d080003a10100d1040781240658440c4080c0d41c015072a00300a20f042d5002c44140081c003250325141d440307090b07070240700d1500041c2d040380c0001181140a040040700100700c5842c1c40489581c500e0742c4041000a00a1203408244900300340e82c0680460300c0740302d0900b000e070700132034001031404980e0384d58900d0003201807400c0340806d0700d4500303d685840003409511410044c3c1c0300382c4d0426000275500d00080b0b204500009101e00c0005c0041a55a608c603444a42c10f81d82d00c241c04905520706910203020480e046802e104107001c40070f804401035214074807081c066941a10340d05103c0e111603880006466181c0e11000e1fa4044022000f14241146201180c9860092880700221415424400104040081040d001e1404070b4010009101110100c0c1c094018102002445503540b0f40200c420280303078490308601e0b1984035840da = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982751312 1250 982750062 982750123
    0x403081b0d0e1509030301090e010b060415080a020a0905192d0f0302091512070f080610050d03050c0316030e031c021e2416050f0912 59
    0x5022400003500300d070501000c2489201d0082e40413100103649410034070041141d545160043d600541c0c0407000400c0d10741030380c000703e8283d401903400840d69044288203100e206401c032401f0398102009480135442c2c44a0102c000e1321854030f610515010316851040111409516600c281c0500400314034099a244035954004091a021455040c3c00004600019940301010051411030740d01411001c01c5959040a40c01c640910f000034580046044010030a156028801c00b805048000c500c100500d00f0302c20000d103003600007000c100404004c42414425940d4503401c01d50100d606140490703896400c2c100301030440c001c4003520f400c0780c01007031628001c15070040c0c40c1001180c015800c540f031400d810329140c442510764080780030160304070403000f0800c400003406480844603100119545110035400050441d104460343e100180d1455003840072504805140d5400a0b50703914043c2d05045900d02c070b442c1c5c0c40c4101c00307100c0e10074000d0308600d0000001c1407006c606015000583d00c00464100800c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982752562 1250 982751312 982751321
    0xa052521142a06151f0906030216050f06271e030c010e010c030e0d0c08161509330507120207060609230402100509060c10140702060403081b0d 63
    0x4e117407084085810748944098414041c0072a17034095514807240c0c03072900d00180c0c000c0d07001e508100040c21600c454407001c62410440b4124002d41c440051180f07280244403000c421400c1c1a02403140801802401c0340c0d4000080d2141d070326001400b80640509420003010720303503c21414620225401c1800a1880d5201948030255201d000d880a0240941c0400b45603100c0f02d0703e915410105240b21540c4011070842c034090250325680b028006000ca2442c1c440301000b4041541429250341c035085144d007000102c8a0b1704144120250700c0c03002c8214000f003035101014030046041c20070b50ba560000b44009104240300b003d00a580300c4210f540f0111414248003a050a0260a440c1801c04104411114190404601e09050720f404500d580e201e03a0b003044501c100c1060801e080083c2071001d030708150f40c1d4a0060204100c2f001c0145000f024515000c2c05540112207110f2600c00c504040008482c2c000c90304030307449545854050203581d69a03d003100c1d400c0d6100c8410794500d0707000c07402158050060f0700 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982753812 1250 982752562 982752601
    0x1050402011704031b020307050d261204030f031b0c0b01060e0a060e0a09020a09080d080411010e03070308030106180e010503030a052521142a06 64
    0x35040c2d20140c01003080c04203600242c900038002081e001c140400d152149110003681c520003820f5030085603940000404130702c0f0681c82034801c1d84941c001c0911b50301c031300301018010190310103140f070034503403000c01502079410000c00250600140584401500d440380d80b00e07042400000e4590b590082d1850300081c244025140201c541441400c00030400d076001742c4e11040200c03801001c000b00c03941003600c121945410101d00c00e41020100d503001c2450b8a5034006005507540c565194074500f894000458030381440904400706100c8403006110201314140300c2004844020f0a003006101860b00109280080691010749905004800450f81d507503c0401c1d1035424100c400c8525602e6110035a008852400f03100d0780760316904c10000500707154000c002508450307151129070114848000018610300c10a0707801211201c1e800705502502c0201d01d5074902e04901e0902c0c1481040000007035444030707482050100100794803801840e140d0000c00c05001d8100d0307610320701601c065017001c3e032200c101c0c0d494110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982755062 1250 982753812 982753817
    0x30325050105180c0102010608061f0e011401090603111e16120e191a0408030301080a061803080a0b0607150f110a050703120603050a0b010602100e06060603130b090105040201 77
    0x4c2400d4481d40c4140510000e507944000601419110000200040d2841d004040140d490003d00050711902542c4182d00030514080c9004800c10508001010290f65420141c02c0c140750076aa404102c124100380c420481925800b980b40300f02080d210401d80c029042000329600c0b034a800c8108100d02548014611801074694104201300d400400404258004032801c40808600c010028011035004090418030209201d615042e01d403820b681c00c41c2c2c4260802c2c800e5170b0080d1181d03001c102051003130710b00c0c60300100001e400e503104990b0002c1140303c014160001080d04d6481100455481d04116010799902220341c0e0400350703030f80e00151301070800001e4544a1a2401419003104000282103402c4036000395109403600c0303960b075000c0c2d418003050780e00c5440b141d40d11341c0040002002040b030502000e00a001225196150000003442d06403295180d004850501c05051010034002401d150021000c8401c00e4030b90b030b01c03401460504440d030500030308a0312461007400150501944500e000724001c2c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982756312 1250 982755062 982755073
    0x803190e030c030a0206030709120524060f010f050f04030b060901060c020d03050c12030c030414030a02070302010c080d1811040227010905040c030e100b03032505010518 75
    0x5410580c544522100003030f05070b04004009001450900021a401040c0f414800f103040c2c3c65986503080c540c0e2004040b5060340c084080c10940c1c004840c5410340c90540d030310b40c0301d41c14a01600401c3c0c5004031845146e05005030b036028980103034010026507003100003200d882a201c07603403410070081114003030f120300d401642d8040020658a1281780078400807130700600350021a080329038040764580d0240001040e14062403689440c040a004c00440c0900e015042c036540382d0a042c00d01c0c008007608070441080a62081007a1190a6000706030603040f290242415003000d541400e01d044148618496030300031903c0d04026585000c1d440f000808038500481408101e0b440c00d1040c0812072050107001812100300c0b9050080901080902c806400c0040c5021442655540c2c041010350720107201c1400440d40300c1703030700d0009080d0801100c241c4107404034050290007802c0011944030b1103051030349003c0e504c0710f1000c0120305001000c2070750202c1d40702008100700c0c03529040d100c800714040d0341150009e000301c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982757562 1250 982756312 982756337
    0xc05031203061207090c1d0a051003020d0b0409050d020d09030804090e0f06090102250f12140c0105192003090c0603040b010e07050403050d05070c080319 68
    0x10481406001691860301e1a01e6141c1000211001000000b1551080310400302d80701c0d070540a61010141c4689803000f00f070f40d0034403000b040000c60018242c01010000010003c40ea100d64855580740024200140e8808880e22504017a010384090150801d041c842d1000070801d0002c0c001c46582b0240c1d09071401044080c008554011552002405800b428401130000c8513141d4081406ca00d1103030121403c0242d00c602007414800111000e1516075804901e00400c0610003a00316400b450542d000d245009039640c940380b85984410026025900c20400200c10b180941d51500a103242944555110f00002c042ea13400b0349822101400000502c2d040e0401010690049041c40045026010050003a0000c14016034000a003d00c001e403080007444615a19640001c502950151181d04450340c1007004001000401401500411070200402c00100d0701c04203c0003688079951074915a01c00300c074201101030241940103060540000201100324000b02d003520b82100344140c9404411004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982758812 1250 982757562 982757569
    0x180b060132030624040519081b0a0506040608040b040f0b04060e010c0e010c02091911031005010c02280b0c0c030f0f0a0b0402120102120901050609160c02010c060f02070c05 76
    0x1255003013890031400130321081c000b5203407503a590305210a0a0b82003042d065511003000d468588035040c00c01910480c075404540c82d0070030003c4e43c07000d0002643d40500c0c04c1d1500c41d0083c4450001840505030f0594a4085001c0000b11440600b1043e088028000c0c141450b003407100081c0440d03e00b51210b50310780b010700c40c6018054030043d5200c0707c0c143c5504a1502554091140d00c540c002e2072192035060482c00b19580c852103103c0d5241c1965089845622131501140b00c0880d05001d410690600c130701d421010b80185d9800038261300c400b5a8074150f986142e1545010781c070302d40d16900204500440440d551701c0c18100040c031800000d908408070340000007048840d41d1200d11010303c0c58859084400418040f0700c41000a0350440d00c0a0b207001c00800d410b0840900b280c10500c10244481010414410002d80c24040d07243c20100441c4c007080241402015031f0380b6500f030f400a403c2031040d900618403d5a0003003844444858120b0001c8c480d41140d0034903034000350320000701140c443c141c03107502041904 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982760062 1250 982758812 982758859
    0x4030317100f05060c070b0d0e010b041401031b1206020703021510091104090204080d02070617062107380a05160611030406180b0601320306 62
    0x41252002c500d505061800303115483d0301c0100c100c95603110305040001e10304503e01c000e1a503400f401400181000b02c1100560035201c6900866200740e0408456554685804c0c074401d04407030b40204032403010001c03a00d02c840f03081015030060300c900e00700503901c07024456241c005003001e9120354203482c403145141a1006c41004151400b01780401c0001c810711a80403141c2c408041c6015900046041c80e0303aa0840744141d80c0700c0d800109181d0032011540071416010040030018010703a042540916030400c2000c00c0e00200204258400d0100c40110a140702e03085a50000c3c00686106a85400361120003407405074580d501c20001c401c0c240410580744004040103035081042007440b00d8500020304104880035000344a1602105403002458030005038188205c007040032608201d20b84910702030a102045546800c01110f04903260750740c400c00240c11704280e660045090030200311600d040d0703070815043d01c2d84200d8940b074614a04494a910040c4402662040e941100d140c014002283c054120b2032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982761312 1250 982760062 982760069
    0xf0b04020a0b0703120e120d0c0f08010b0d0b011b060914030c15060a0b040f0510050a120f0e0a03080609060d020108040f050a08030f060a0b030c0403060908040503030403031710 78
    0x45c02c8601a5040e42c016402071501030b0030742c10461314604516106080c66500c1401c52444099070385801018454200c50784024000e0181410b1410f503141908004e51442001041400703169034140c611490703030107241c882042c900116240b0348007410a1921000502004e8401d4030303405c482d45c9020040120000c02c840114915102500c003e400c0c080400200c020b020700a070798001804400810598805000740c0300500d10558003a40d031074908014005e81c08810f500302002c01008204030a06640c0104072a01b10340301c05140051031800c0c60209000502c44034000c00403601901403c0d2062682c4180031034001c150444040100b038841d03070204070289800c80d20080c042542c10000a020503203074007050004900507001c0d141c886655941d543c50660049400761400100402440503c0c00c11140d500003501d030340d829281c918100032320100ea1070b0066100080c034094a41d4405001c0180f6001030300c00a11014081302c1e1603940303e24010782400d224040c1c10040d6005007000a078050781c0047c400084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982762562 1250 982761312 982761317
    0x90d0e04020a1d0d02040509161e03030e0102010906021309050f0907060530011508220311010c0903021804020105070201031a1e040606091a0c0a0f0b04020a0b0703 72
    0x1003c6a0044810030484125002e5901505262215002d030700c0b607004640c13180c00010042d01100204103951031158100e42c1094007403681c807444000a070a55036402e2029030340c0500308444100307d0000100d001d404280c1005002c82d00200341c1a40790720b10b6a0b40e14040d10b801d0b120521055552009039a503000003180ca4403ca54881903003003007010300900c000c00750250240064002009004010b03490048c5410000781011341c544010003225440c1d40740404462034030705d0036002600341031152441c064400f8110039421419821000c04050241c6910101d900d440d4000340607452002c1c1c0040c200d03c92510041e030054100c0c1c80214003a00d00c141815104940c140c4500d4200388454004400800ba8601aa00b9840784e80d020300702c2e1a9280d50141800f0000f403e45866920780c2d500c140002d542c215031260f0300340075942905218900a503d2881d50019001d008a6154641d80c60054541074a00001400c1c200161040343c040c00f496040b410310860007510328140c0681e540d829101d09100f602000b400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982763812 1250 982762562 982762577
    0x304030803060a0b030f010f08010513031d030f010e0d020a170304060f05150102011d060c0f280306050f10080c1c0207060b0f100c05070905090d0e04020a 68
    0x190000020395040b0300064a103c0c40d0303649540b140084c82d0b0081e54120f0004944000412420325424650307400b030300c2ca540c020310250505251440088800c090010300380078105400031507500c48942201e000c0780300101100c24020841420340d00030001e040b600003a034002e03080100c008900000e1100e110039408000720a66070800600d010040d000904101d40603901d0319400540c002043c014240074502079a0500010080d00001a0031112460001103110b8101d4450341c00c0c400d00441d4003a40f0021004005036a140c1a81e402101e61080e4954030100300360810f440554041803550b034011414040c1c8040120a854004100110424043d2079600040400b103200480e071080030301c0da0b0400c10121407141888403081c400610f944050241d109084c1d400304651080c0b044501564109210595039030206010302e10210790184034007421141448000344000c3c04100e8100000f1000b4040c0e518108202d040a06900d61602c00300074100000905440c01c0008078030309407084445100359900d6044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982765062 1250 982763812 982763819
    0x405030604140c06220f15080405120a0917063303010e0a20010c0f08040f030804090e010b03100e010906060306021c0603020d080d0b0d030302041401110304 69
    0x1a0740c1c18050700002c218080d004000209032619405042e034807101140c0c1d007088004070800009824902e52012662040152040040130740c03004842c0e03443d10340c9140c00c8841da522414010f182c54a07680d00000c00d401c0008406000c00c0e44400c002003500c050340d503218901100c1131100c076501c440a0310300c0f090800071400c0659115000b2001030a070756039200110301811020000090031920040700c4210702d50052607a900411a14001c400c000361415008401c600d001440001e0040954440051400b00032500507014400104241c07001002d4030000f1441c01c4da264039005e4983c0d0068883c0c21000780c140b00492608038010700035480240005001001d0000b40e100448004e00f00311000c0582035540d4503440000308880b80114409540240b038090380c0d50229018542026402a070030640c0310b0b160220520040e520b1018a400044d0429201d80d1a80c9010342280d004040703440035aa413002c0b0920540003096010380250007101e12440e090202010310b4001503a030600c0d004a0081e082d0003c02090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982766312 1250 982765062 982765073
    0x132901020304090b120f16060201140f04030903080d0c1d030a080d020d02270a0e040b0a1d0a11100e0603090f0624010e0d061a10090e09030405030604 66
    0x1303ca05050040c11540c2041401c66464101031810340703642420703004000604042141e00707181c04011700480c4000c000700704104566010a02d8007625180d1440307410340c086000d06104010441c05503401901155461802c1c0d11a00020015407200002048082440c8040101404131090240b14050050103135426241e036100c441e540041d00b100c00c1d00354280010358580225202904e5145013082a03039a01c05008565056000001798200e8400d03040142c040c86070051007904583c01039401440d05200b51907078241400070b080c035140c0448200f0706020052042c4000080c4a0964602034030000e01913000c00018080503085002054000c00d8040f081b41c012424031100540d03024050006035034012210512403402d192040d20a140f6800c0e491481c008044492807111013281e5003402c000504540300c00c0416903007414100040c05180c0c0d103281400411141200c0080407050081c4420302d40010f55a01a1401c4210700443e20080c500c00b0000b11949400002c450950f10b00800030005659150741b00c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982767562 1250 982766312 982766321
    0xe030304021002120703080912030403170c090409150e07050d02193302150a0c0c06110c1009020f0607060b03060c0301030317010621020913290102030409 68
    0x1a0011440b44136001d0302110005400f8040140c842e44d1303504000d042c00450f40346802070340d08014131100320402c1800000781c0c00c01c80c00c041441484118640c0340e903885070750301001c5c0101c00c0c07090380040c200719104081107102410140d407d40441420800c01031504030480c1d03222024000c068111005c3e01c482d0340549030100000c0c1002d500318044424840d110a00c49a4210310150300003070548090116a02c0c02c284546c00750a030000e28802440151030710310010f0385103407010780a00da9103552628039130303141440707209600e0700300f40c109509202d001c41d00e45c6c01041341d43c070085a10740300b802018482e40c0d048002d4002c0008403500102211a504e0041c010000194005002260138950769140500d0341d8805000581c815018418115160761560801510082210324140c52007140c00c0014440307523800540b001c810701e07010300b41e0f40ca040c420803402100074450706000a5001280171420345c45621f6035000341140c1e20102e00301c2c2101d4940d0000c84000442d604001c0f0380540c0050106200c1000701364413 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982768812 1250 982767562 982767589
    0x6090e180d0c080c100204151701030206090103090b2d040b060103050603030403060e06040c060c1a190e0304051c11060d060306021b0d09080601030b06061b0607120e03030402 77
    0x60640c0341c20002c8004614040d8460f1500c1c20168021901b0800448c8122484002c07139003070b0502c042c036a00140309264004d007050000030310580002c00d106007180d21a5010811072980440041000d081c100e8010b40c03441c031440c502d180086590030781d2074028011011518056684140641d00076250340e00103501402e00103083c90b4051005100010102d80c190003255103034404c42c8040c4c203450074903050086200d011f0f81c106400344100f034406080021010008440070440d1080721031004c1d00e800c81c820036609481000340c0d0030b29040292004030403502000800860700c08a0703140500100001000304007000d061009098001c440c1040c074150309004000303080c3c020081c0c20004110762244d440d0422030700403d01020802d840c100550000141c2044021000061428982410741ca444110360f51080c05000081c2011249004121107032200c0c5c00341c0f60b04414002c11220361b4030740340c2000c60344c0348812140300b00004c080424260386681d0500c41c501c160440a0059859a5030300d4090010700d4100c0c03103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982770062 1250 982768812 982768823
    0x1090e03090d031407080409150302102d05030109050a050c1b03070204051311011103090112150b12060108010f150e0a0f18050f041b090606090e180d0c 67
    0x141d2086904101c080100450391007040801d80303950030200000116079001d2027a07014401d1001051000d80c0d62605c80d20b885183c0d500d0400318010702000e1080345000c40511038000304c1e1100340609003094110b005181a0303188500d0411803540c84413526001da80041c0c1d09031074051020441e40d00c21641d102040164a40100c0840b46407003900d070702007002c8400c2102d04224003800fa145003020071100301004c0754140c000346808521045a013001d9526845154006414095014001303001e241454114060384616640d01d9001d480c1e80d104102e000d944014400316000010300d002030065030042c41c030203050701c0076904140b032280e081c00074000f05200c2003001c400c140304804805400302c2d41e07500d0400015100c8142050300c0e0740e113400031094218023408290b07000c3c0780c01c1030200840600032800f00c940c019009403001d401c543e801e585c540760862040d00200e5506007405804241030350401000d070111000e180c0d04020694480f40c03030300e2903104440e0000c206500400c0d50054014801c407000350f80706000e02c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982771312 1250 982770062 982770077
    0x903161205130608090d02070b0f0903010e15041e050d120b03011a1008060d02100c080c01020703090e04051b1c11011407050d080a0b040c1701090e03090d03 69
    0x1040b6a100000198020320004013181c040000d506818040d01c43e288400340002c0809905115180c96a4007520400c000720080120f10782540340d07070940040140e20700c1c40017628065120442d40380c40c0d812048805072200e816000301c46c00550103025040300d985030450068041038070b8000c800c5a4224120961840440c0c4681030508181e03000e2080c2c8200111a4041c515a01c0c210424030030103d0b00106a101889109020000c1c282c6800c81014a00342d030407503640c0803580c2440b20503121101c60300c2c00070b4210035002c0344500c0002015402001414002d4485810341e03580c07101c41a1840900310b030000c0098003d00c1405c50480b00002e17002600c0c900003454400c80f810744140400c4003210441c01a60248011500c26400d941c12100540c1368480422400e842c126441e00c3e010750350b000d400aa501041050304c00038500e01043d501c20300c0c4007000140180300010001100800403040903c1c406908414440000b800b04181d11a101c41d1101d21070140d13007003d00400070042041d40c919010f0302800303440c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982772562 1250 982771312 982771327
    0x4060302030d09030c0b1c0209031504080903070b03041a150d080d0501080a2d020d0b0406050a05070917030c0607020f0606040605060423120a06050903161205 70
    0x500802d054512280d5410441501d5414881c01901c2c481e807148094040c00c00030220703845440c40c03038074000c403113034450141ea110340c00301c0441d141026a201c800540107003107052200308204100100354800c0c00320100c421403030725030b0340b4094544801c2d10010f0038904400200602c03410072030a0290700c404a211080781c41006100030400c042c0c840d090440714041c0015000345005a00c1c41017a01500e40d0000401c0c14a00701d41e242802c03a503052415031880c81c009860303000700040c3c288120010a60103429600540b0f140d2526004a03030041d202225858101030001c2c1e200500c0f40700f4203100710345c584d880d0502c240c070344030980a1004080b0118100c6000c01c01c44100e4808003001100c1c002d94841e8000c281d40c03058078410a060a1000d004c203481541044030400c09582c421065a05494802454403d1082002a40010b05c0c00100e04241c0000e070424442c0c03c90500131030801a4075024110034082d590702c8020868680c82200f0b0550041c2c81803100c00d601140344500f4541c009007007401c10300e203013101 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982773812 1250 982772562 982772569
    0x4050106051c030224070804150603080414041a100504031b080615033703020c010e0f030d0c03050d09050a11061903050601180e011d070f0e04060302 66
    0x315502c1404030781d10011000c00400d40d04000f0700d81c04811020f060707050b1a4080490900809000e4158810000da150105040c4541c0225104440034004803c22040d641c030300d82100e40340c000d44101043d81005100240e81d608041c000c61000d030b542040d47d10100030840707003000380100e024406501004814040400003c0c00540c0c1030008260003d1004143d0f4900050709142100c014142c50302e01a003c800d1003480d840001c1c008113904810700030310702c1d02c00c08100c1002e981d20300217281040c81c003007600015003803540114140202e04001e0340c507845000047c405221200c1980200750350182c6c0201c40007031101e8030501442005d43e02c2447c0c0145004014020350b425121040403c0e2442d4008486110400c4604c0c640e554007500c003590400e06002141071040c03e003078855903207441451b440f500003550303e0784100001c01911908440b0b000025895503c07c030142c4009000d003015080d032444c007000e03c5900c41c105c0d2030f00c10b100c5540c91810310749107100c00700c61280300701002580294a0341300110040c0d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982775062 1250 982773812 982773829
    0x80d060b040f09060503070e0f1e0f150a0317032d24060702012726012d0b10020102090103050c0c070b033d09050c0406080405010605 59
    0x1801d02d0103800900d060803a600c0840312554400c521a034080c0b01c1c00c020190700c8445031640220f003d5002c2c0b42503174504030320320104d443d034001c1b204018110404106c0c002c4000001e0170300801103003624801c65000403040c000d640111b4000070f010110140a007aa101c80da000095501007614000c5602c05842940c9540511030700c0c10070300c841d61880100304040c025002c0c12601421180c120740d40100f521150118000d40301351000030381001801c03e0030180700d4507920150f01300051005001102180e0303800030414080c80a4503c4c03424400d50076425010030505001c1c198044142000b80360f050038036022540052a920300e01402130707946925426803903688865031602c0c1c03000140c00150341c440d0814001011540e0090540c0c02410b03041c0841082101c000854800f0703503505205440e42e94844440040700c1c40b040c082d03030312059214484218250040e010400d810304e0181b42c000366030300351100800001d691080b610044200c0050104003c0a171081000b59001401240009603054132100410840e4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982776312 1250 982775062 982775069
    0xf061a2a160305010b01020303100b090a03081306030b0f0a0b0a020c03030403030e10080f151810030209090a170711030703080a090b030c0f0a17042301020c0a080d060b04 75
    0x1101410040041c40805c0c01544080301c0e00344050740c6540b801c40c1c0c88070000003c0e8080c1c60011030f800700d07180003581c980160310009960880d20440d250261640700248092550081c14000b0741400c080d201c650415075500c0503001401007100102d541003080f0b6503e1034001e000803401318419102191a540c07020300003032000d18001c0d51101c0345065004148049031902c3d0b254081080604010460001c0c02c0200141e042150400c40010740d981da500020710210140d603145040652400034000248150141c0d00c003103038800c1d00c82c072201e0354500d04002d485400c0d2070300103010000344449030390746980b84030000e21001d481031031000102112400482c0c500340c5079410888141c400010034044c0160012105030007001240f04c1c03035141d0316140c0070b180c001b400b6811040c4500c600c0410380801d103902400b110307030100d140740182000c2850b02d030a0181c0d004810134401c10340040c030b4010303ca020020600880301006848401000c40110a40d55000e1580c025110008240c0e03980c08023103280390050780108001c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982777562 1250 982776312 982776343
    0x10b042901170f071704381003050d0807050a23070501052a04140a05090f040b0f040b060909120d1b0503190228030f061a2a 55
    0x2d5203000a00a0300809800725a900c41040c078000b0840000d820340008000340701c03a800901103807c540b0f460014501c5002920f2403125914008120417626840d0340c02c41101e000714129440010a08000d40d6a00383c1512110000b550811852003024000e85d000400803c0c0070421101c031913000e91038000355410094003221640d445d5810f029010f640d4900c0c0c007081c4003000b10300880b030003003d80303250400c0d209620900240c42c1003247e0f511805e0361506d00100c002c2030041c001400c285040116081c401d02c0c111405c46480d001d82000c02e0741c0c0c0350031004180c0f08a6102c145401561914800c02c8401c0318000d00d240c41c18460303070840b12009170341076000c0c01c082d48a101c0c001c540c024801158090058158000c902044014801c2104501c0450110003568418440050740d4011004000c0b0350b42ca070703102036022440704002a5942c0346925610008420180d000200300b150b0703d030b02c520740000828150312500901c040c003003034074440780c03100451858001d0f00038800b01d0230070309003492400c02001c6507e4020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982778812 1250 982777562 982777591
    0x80d0c05030718050a090b0a170d2a02090a0e010204090903122703021005010609050f0d2a0e010e0708010e010f060c03020c150903010b04290117 64
    0x540207014400000200d804503c12282424082a8811a58840c0d0810b00ea1034081c107400640300e003440c200190020141014207402900216a07540c0a0341445500140885030240c0d4250007130700c041c440c4602042e80f0000040560340070010400b4025040d651010340d121120001c01d142407005000402c03040102286040ca28180540b110000307500c03042070141003030080b0845040303595041460780700e503141506980070380381002ca1800c145d0202014140d450301001250550f00160f04408442044803c214032240206c1030020940580200500402c860411040c0d0402d0300745443c240010480003440c0c901c1d1b82c500e4821038440c0203078042c5c0162203810b02805040d80e03002c3c40443c050306118462400301d524080c220b141900140c815541001008084003040505c280481e042d44980103040303021607000d8465680d42540710b12060f9104e98a000540f007220308080c0a1102000c1307142c03d81d05810841010191100d61000f03145a0401c14241003015445040d1401c1c240680c01041c0c1111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982780062 1250 982778812 982778821
    0xa14030d02011404060504080708180a0603021603080705091801060e1f0e15031501020c01021501051c0c060201020c07090b061e0c0f010f0510031707080d0c0503 71
    0x5041088540c00a02164108060b80303a0b041000b01e01980c0080d84000001141d5403281403d0843e40908503004222071000034442d151f105c500c09010000c1c1f01e040380d01e06c0c10155200c1081d012489211600d400d801ea200212101090040010b250701c074005c2c1c00e0191400e6820030004030744000c00710b61076402c51582001481081e07480b191000c90100203a400d10076041c00140305003031030340c503c892140c100140d022101000f07844400c2d000001c402c1c449100c640340d040400c3d003011a900705404441c0180b0481011040c607610001d40800c001000010020b0b1503420038050080f905238048458044019031000c00000961011440000304043c0e4001a210300f1035003000b0b41443c06c01d500040d007d505052021046589040403550004000300a010f10880002c9540001d07001d100030800d030300d01405040c400d9101c4190041e05034030290314810001640c075540c006030142c005000103045911051699040c10340310381e00503c000da004a925031704081c0b034000c02d9401c0c1d907032802880000030340110520 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982781312 1250 982780062 982780069
    0x3060207050111072d0804060806011101050106050d0e07081204170a02090a05061813060e0d0206130609051624081f0b070c170307050a080307030b0a14 67
    0x3810103c002c900ca00345003034556110901c601d1305006060419a1210f07056510f11030140c42c20020751540111100e031210758551740a080c0610413100f8a01003801e011207840075103c1845814140c80b03050315898106050300d08108010003094042c220b56200380b15001c90403240c200503000504206101940c2e90b9030034035100f8102d0404180d42a80d0b990300416110b001643e556410982c40b40700c0e00c000003206d5860b14000341c01c000040d4020a400f620300406e000c020560b200034004c640f40550000c1c801400411022030380c502e602d0700707000300680003c1d01144280c440840007141142c05040d021488000c25141c507818507182e00c1d40c940e090201c2c42410080b8030344105840c2610780318950364075048424140007801688000708103a049001d10804181041c0085a000000c0d010001e811500c0c1d05091400b601007038002c0c0a5141c0741042200181000340000003240c10340c0d03900801500002d8402d542e46806504054032581c141900e5940c0b80080da1124010790340200701c0c1c078141a04210800050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982782562 1250 982781312 982781321
    0xf090516050a020a0f020f0d060c020d0203070b0117100609020405040605030a03080403050f040f03050606030f06010b04060c140d02070e010501030b1507080f0304051c17160e0a030602070501 84
    0x503400d000007400910811900440c103803405a400050b02c2d0b018401070320010380c4c6917500c0d004d4a94440c000e00d000500740180d690001e0781d62901a0211103c0c3c1d601c032401640d8034010980001c02406200f0700501c05031245884203495104404200c405080c1020051025217101390411442980d0110301040140303494000c040040100381c015110f030b054152802800740f0401030020f000c0c0400011070003e291060811100100583c00311050015224580700ba2079420a03542184070303201c2c0e079803030006a00c00031503e270341203500c458500c5150a00c0c2002c00d80c0d40280d03402c01543c034a0b00c010104519040140b05a0b202c0c20825805420401d0410f041c1454680b811303044a41014074040c4981106e4642c05107900011100030203154440344507160480c110b100c0c440301c417100b040340030086c4010080002078600a80342d00e80441a00040301c814100c4500601040d4041030000440100381d2226034030300c100e00500307800d141c103030384003183d04002c00c00c010041d0f4401c4559560010b90942441001e109 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982783812 1250 982782562 982782601
    0xb06060301081b15040f0311120d0e0301021308060702060a020c0316020d0203070f0e09061302120c150a140a140a050d180312110d150f0905 62
    0x41403411541421042d641e00c50200e400303032180002c103066480f080d80d0340c8034240800b1083c1c8001c0310399a58803030f8880010203441c0d1004940030702c04003001b40f0141c42d05445070206500440c004001d45124100c0460b961800c28502e035415541c04c202da2541040000c07034100140402c10300601c0907080071040289810301c0207100c030710028811700080d181c0c20408011140901c110200c01d01c2e1040c1c0304c0c00000d0340003814100007503140c03080c0600082d6840e50394144004948001140d00015510f2665441e19440200c0c1c0203008003080440080051600f1b50180301d540528400b26100c070034110300410381d640e0070044020201c40c3c010800066540e0300142c600c008200da05000c50030310a0004d4040e0401303441030000c0c0340d121404984d88030b04a11031815601c112099480501c0a0440a55510842c1355101030035400200d04507036119040929004048400c440c040e02140b030300b042282c450009000c005080c2c60000360000300011049521040c8001401d0b001e0f00000e594103104e0320480b0044600135 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982785062 1250 982783812 982783819
    0x51c08160c15020f0615010f02101d0d0e03030306090c090901060e0a050f0907031e020f0421020f2106040c060932060409020a1d0105041809050a020603040b040b06 72
    0x401c50303180441d00750340e0350056080c08c008107080943c01d400e90031721380480c845d0a140d43c0f42c05c4040b0400c0c1c4113524510001c140e90070641d40540364040d0b0807101600103040054140c1d008001040c9181000b15030075a01c6140303046c0842c00c104001c4005240b034442a403001c0005590a650a01146822583c0400400d02101c40300740c1c1018100105050b004000c00c0a414556205200d00b21803480030510284401c52050841d030b01c0307116800c0c0007210380150042c1c0c4038044034130003a140301041c41c200000600d40c005003d0340720105071008015040c402800c000000c0405591241c8000b41e04001c400c2c0528419440c00b107800c3d04018000b0600042030348071002c00c0d050200440b0810500700c641e5000c1c0b01d040d400b10280b41c040000840c010b441141e020101e00c2d03100240302c4004c1a48100c0b01200070300034200d443c0c40101d03014011900c2d400f480c01200368140ca501d5804800c02d045a2007850036038419002d980c134990540d00040c180341c20469044e5070188000e01008100140508039952246049 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982786312 1250 982785062 982785073
    0x7110405091605180103060908071a0714030106020604061a0d0b04110301090b040305030604140c0a1d010f0e03070308030f041514040b060109081b0a051c08160c15020f 74
    0xc121844c4040c440601a10368034a00c0d0014010700000f2114460f42000a0700c0b4503205000c1c0c0440e66000841d0013000080b140341b0740c03005002034802200c2c102e5000d80d000303103000d8550f521500000e00030080c42c0034136a42c0c0c200744081c0c1910b905207646c3d502070003640c003080c3c58501801e103180c081c40c02c00c3c0d0f41842a4581060300d40007404505400fa0802d0300340ca8010703140d544070b4002c600100031060b141a0320a440008100580c2d640200500c1a03081644d1174803901101241117905000c9a00011030100d40c1c00c0014203c0d140c410881d5080948000781210b04181d030300e44034403240350f0081e141c0e01d102032001c07000c00c802d03c1142d80b0841110600e80e04200210b4081078043c000c4503001403c0100050010302c042404c2da0b110304101c030068003902064604458490340d1460000c200d07008064001d03a01581c0018a034540700701380884040f940c4410600b1040156a50351560340300401c43d40d054011188003002080042e010440640500d244c040100070014070044d10744442d51400c1c1125902c031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982787562 1250 982786312 982786339
    0xc150e1002040608180316120f111c031103090a021503010b070f08071a0108120732010f0207150218040507050903010509150c120c07110405091605 65
    0x200c2941a0701214500051840c80324030205d0034107610031a0b1081060031307641180740701400b503809009030030640180c03100f804122001038262007110b0401c801078034a030002d140100500c00b00c444040d0b5030741c90602c4c001a80340600000780d185034200b51080486903112814460460034207111a40407140c9002400341035600d07102280b403140c8500c42c8010301115441703440c4420004100c05940d90a9441041403108035030f505c06000c00d504007403269144510502d80030840c4014800200c0d030040d1b4015a902039020764003082142c8480c0d5004009002c40e1107441c1100540d8000c1c440e90303405040c0410056581c0886061040c041101c150004520300d03c108071013415494150400400300005a0380460340b66104c110640e1580500c01d4259059400c2004201c82d0740001304082807200c0380300441e50b180391a0580786074440e02035480703041c081c07105a10100d8000c0c1a00d50161109600c00c40d0b91001c03440741c0e5400301c0c090f40c0c01541c2c4e00200340c0c04802c6803011807540103800c402a210076101500c240e510b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982788812 1250 982787562 982787567
    0x61409060406090201030b0301021803120c1b030c030d02060709050103050118200726030c27180609012c100306051314060403140a0c150e10020406 65
    0x30060001044a40d44455010469000e5004182800c000400854441d441c5010b9601420795050f061413090040140c0122030103842c0c01582c103000d040000811034820001c05180c4004620455664140701d03607001d05240e40d40030000a082c04403280d01034159414460405440c0308140c0d00104e05041c20080103002c40c0041030f1a01c1c3c15400d19030380c00f280c240c00c510400703400d804da41101e8010362600003a101003400100c100740750000c003c10206d40321024540d80d03002c02900040e6290b12030518104440141c2d83d014500e10f050401000c580482e420900100007007003100b8019002003c03854980030400e81d0303d41460990b00501c03c000b548800410308001c1c0030a01c040e645109104c080c0c2a40200720390080180c0641302459110790b040045040904040c0e00c0300c01d10450848540c44090404e81003414003141c00350260b1790684400d103805c000001400700d260080c8030b010b800c10120003090401319401c00401c1c3c040fa0040c410001e403131a1031078030141c05c020030554001c12260042004000e01c1e607 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982790062 1250 982788812 982788823
    0xe0606010f030c1413060912080712210905190503190e041505100302041505090613032003030708120606040e0a051e06100807030209030712061409 65
    0x30100d24000659820743c41c01a102c1908240c0b80080c4070001284080c0d4848160002d2000e803101e94540d490131a544005034404800102401005050140030100005203403601071804407455040c840507072059408052078010100440654980d1101540000e0001c217004031000c2c0b00803272038201040300094035607580d207105402400041c049441c0340390035074074821000410042002001440320340804040310342d5506040c0601e03441160000d00016019004c4d1080718100e4010b01058003049505400640702600540c07056600400c00300441002c0396401d1070300e200550f100b590b0300700c1664401488202001c1301441404d010f07910400c10301c008070302c0070703015240206d013080b142c400345664580103d80580282c3c2e0041c001415284103010401c40c80307400c01031083c04102018080807142130864031400703c040e01ca041d0081d8820004440051240c4012944001181000340c50702a003000032901e0225140c0c070142e020402046100100842e9010303a000d00090342d5143c0746103081404419031141d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982791312 1250 982790062 982790087
    0x50106030212041e02060c0708060903040f060813020d050a030201060503150115020f0f010f0b01300b0d050705030d030203061c0f120c0507170a061a10020d030e060601 74
    0x491300c850800340d0025501c000020041e5001e01040d031240e0310003400170b658008501039281540034002c0007503107840000055400300c8403001d41441c440e5103480419203103000c000c1d000b29118010f000110000da03c0d4405c600d1b402901c901c000b41040401fa0400a0031910f540d0003151294102000040d2900c94a1014605480798002880c10821401406910386160020400300fa402170568900c1024011b41c440d00e809585800c080c414000d44400468003070030b0728824000c1c1c5440f400c071915919603519100314041130900000003889240310000a003065000c810440d1190712580c010701c010f00b0184a6109550b0fa181025411414800c00081364091405141c42c1d510000a1000b014070089980c44100c103904121070420740700c200a002490100d105109a0711846501c0700001c4060000075540181000c03c40901032a40d400d580e5540608003030212501c40d0309285c035200301e440d6a405015a001d15454008000c4400510005000c0d2203e10000d0983c40c1c0200040007003590700b158645540c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982792562 1250 982791312 982791323
    0x20c030c0109050d1b091d010b060f0a0f02011d0309031b0303040b030a090f0b18070f0b0a030603120503041a0907091d01091113180224030a0f05010603021204 70
    0x184170040d000e40440c0304030360040c400c0c0c03420a0100390200421001540e944000d15000b440a00a040c4c244115881405440400c0210400c10300708254800c1101e003403180c244c2c0c030010942e40c0c110080302c0c0858910050182240d000040c1801841c541003000d00054031025403803405001b12800001d88a000d94450100c5020000000030484540e950140b03100c0d0303030701c4402d581480410342004a03525a00b102c64550f0800c5100d560849030b000068641c007296031f82d010041c2c2d103500304a0307032074980c0c1c1041500c3c50a1589903c00480000c4c501640b5a01c4c420703666031940e8481c43c007403c014102084001940317215000d8001888000080450590142c5081c1c19020804410080c035020203540c02000a807100e5281003d4882045061088840c00038422141a60290000d4416034201d9201e1800d022140c85911602d000504000700100e01c002007100c2030403050550f141d00d5101d6907104561640340d00d903450001150020f460b01c0b4440c090210380c81c0440c14000c40207103014103000054030141c035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982793812 1250 982792562 982792583
    0x7031101120e03040303030501060c020d020f010e090406050a05011e0509060a09020c1005090d0903141501080123040302030d0e010f1103090c030a020303030106030c0302040b0703020c030c0109050d 87
    0x149900640303424020484642040052451014050f0b4407038000b8001200000d04040002410714032407480e440c0d41c0c64004206811200300d990800082064500c1614180041a51004240d0b643c0354580c0748210700903e03011525140903070128007168016003100c0c1a011241400b81d00c0c0b030028586c4078050b100d080e60009000e4544800062543d18664043d040c043c1c00043e82e9683c940f00414081d41031980706509001585500030965241c0e645000403a0002e90040010004a1008044403180c8212042035600010b1308403001c41c2c040b2026005070846079192401030003035050f09007072081e105c3d8040343e9101860819a4000b901c0703214542c0303410f40c2544c0350140ca4100c64004e40c170078046800b145d1740402c04081e0303000b4818500e800c101d07548545402111113251040c140070980040f80d40c0e0040c095451a82420802d6005080c00624901055401c2c04086018110f40303000b062128020780003401c442d00c64a04042c544040c3c3c602e00e60410602500800858540b4062030750708680c1300c80d01c1c14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982795062 1250 982793812 982793843
    0x6091207060b130204080a03090b0f0f220e090709060b160221070303180807031e121205161d060f0301060305180604050d11340f080703 60
    0x11801c01444541d0490f440c80010001920000041c5900e0b0ba070744684c44500403256036645005c00b0740038190400942035810009030420312100d00007001c40559012000c03e1501e4030f580c1780300d08041e503508007490503034030303030041c042110b81c200514001401010003d124850402044c50980d02804050440050700e160104003159a81c20048040c01c45184648861900c075601c0c10741e980d141c0b4030080c1c1c0450301840c556141040250340c210252030350840101159803542d50390303001841407040d148692040800013000062140b41001d50000003071390784e0f204140405c4030b060040f2180940342405100710410386840050304112a1142090f036254502c284c2211000410301c82d00c611007103002c4407200040049640d941560280380160181e00400b2028190506000d64542003034902400b16800081c0481034148504d1241140860705020384040d54003103180103045840101c600300001d10b40d914013201030184142510300801c0c2102c440700c943c0d45407a004a031600b2080c00041d110601035000d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982796312 1250 982795062 982795069
    0x9030c0f012606010e0103060f0b1606020a0206162c0a0b0409061707030314090a09050403020d18030305072a0909170708161103010e07050306091207060b 68
    0x2002e1a0028001c1074002c800d2041c1a80d0020080f60140c0c0031440c0303e014600f40d54464030030603099643c003400c01015141404081e4030a600059003204100c040c08604070001441400501080e99041c0c00504c507074100701107203040c0c1c440c2c642038040400c20424074030074034403108180840c0e040d003956440a02401b54940842c0c84403519400c20300e081389000400140702101a80280c0880c1c40c1032004140c0c0454207908682c65518a2001900141640301501c1349550408000c1c004904004c04500c11700fa518030054060f1903080340c0035405604441e050b2410311350070144c509908d44840c94004001811030380c0c050203e0054a8000d40702e421203400d244603512034421403495010603081e041c081d29907200305003000342480c0b000c202c03444040b1400019000c541d500644221a501816840c200321180c80c010511946c4c0ba0400d4030600240800d061043d1400e10510840a50348405403180a00b400e02780b61038501c01030b0800005501c808910031720428400c0c262840d180d400000854106843c0000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982797562 1250 982796312 982796327
    0x804020d15021306090f08070b19120501081005151518030f0601240e1002120a0306171504021905030d0507050c03010c050901110a060207240209030c0f01 68
    0x10280141c11100c2d0201e84c26400000450441c2c1e03000d09284142034607800503644500107031052052082003802a0341c6083c00e001040c210400302450f1085071061840741c00810360360203a1000354150401004429001c941d0300555501c0109031000131100e00740345001c039006c00924084104050400304e6040c0b07007044041c145001400c0001d0455102802061006450320400c0c41000810800b40d00400070360b0040d0340c2e26102103065038541b001084107030380038801f604803402248411030080500d100c0e0340002c41809400d00c0f018a54000030040d04190b0070144001030301e0b25407000d9522180759600841109400070303a020380d0540c4c0c070406c000c0b680c00500080c560550419a81070058890001480d07a00c40d000d0024180904200c40410180e0801e01d42283c40105090340068402c11000f680c950140810710034102c180c00440e002224180c40c0c10007280c2146004030340d0301e4102055510000016448081e840000c82030441c60000c009000942d141d400109140c090804006a41d00681c0a5a00d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982798812 1250 982797562 982797577
    0x90a09081315170103030f050901051c0518061303050c030f0406260906180312041101180b07020d03031b02010b03010e030f0f0903030702130f06060804020d1502 71
    0x501c00c0704503103440d0a0940820503800180c0040c01c51118507000303000c0d071000d290480390103444480348100a800101da107030f400101c2150500008204400000414004d80ea4000051000029050420590b40c1c11400390f611503051140c2c0c0107005201180c115521081c8081f54141460f0350744085100c08941140600303212411103400100d00010040c1c1c0202d28800354156158251900103083c9000200c141c2040e50828401d0707001078000b400f0581c1c6e00b6401c58441c00807100300c81c1071041c8050301e2241c43e101224112400e00c0d18203000310842d604141c10703c4901c900c0317040c803d811a003440d80910740b9000d8120701134071500301e01d64046c040c98000c1c0d118886400400340c038111284082500a4040c08080100e20b003e50700c4c003140031802041c0403050f20781c80c0011000c41450050001c1b50a070325600840c0c03001e68140010001d420060752070b80c444143d40d601102001c20510f076000f1880003160740950192042c400c001c010400140da4035800e001040c1c0c0d01c1184c24010780780c8054041e000f40180c3d413 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982800062 1250 982798812 982798837
    0x11401050f030705101205060406080a030806033d0506030d030b0f04050403030b090c0405130f060b0c0601080709020a052205060d0f050a09051c12020304150c0e090a0908 75
    0x84c0d540d4401c0d84d014a80c2c0e186c3d504400c40522658035000b040c0811100c1d28401c48000342c2100011000191040000c1c076000103005085442107403000022240030205241c003800814681040c510701c922003100844104c1142c0e120070881440c10708046901d590340740c00e400042540d14640409183e95280c1d014400707800144c0100028500b6150140082c040c61500a00c1b400e0490001401e5003070b241c00719429100040c00341000300d03000c0600c1c80050302402c01c80e1402d1585401c408900d02808001034070f0307010b00140040c005945400001410014280c015441c0075004000c1000300e55040303411109030007110901a100f41d01c540c2c02c07820351480c594000b5940030700002081ea01c0740000350018040d00e0b501c01010441c5072100e078152021190802002460364105845054580c4280c041ca804089018180413520038080200b500482e80200c3d41103601d04180d168070803e15000d031290400c2228282840f0700c040c030b0000006403082030b00a0509042d252615512401c100980c41915115032a08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982801312 1250 982800062 982800079
    0x5071b080c0601091d0c01121e1a190311010f031506020106150918111e0301090b0609010909050604060b300c09060f07050a03090314011401050f030705 67
    0x8a090001030260742e0381c100c03100d401741c402c070130a5800003082d14030a000058480360003904c1c400c00100042d119a40c2c107824070400030411040c0f8814036000d0b04c1c0c4815223850301c2d8400048040100070a04440e4440c120140821103005c0c80081d82d0f200d10411028070900708400350744001c001c200d000e82a43c4070702c06c101081342da02c001061030f015088001a035004481a5507840c84000088a5000b001e22842c40c12a101101d20102c0d44240d6000d118010340780c002c13162070860041a24a420942c00454410b80000000104a4030115120380e45800c081103401034079000c0c010000074401034050040f030980c1c0350f5a50100d8659235483c6e1013500240125030080c1d4848089911807411a000114841d140080d000291652000803103c03840c07041d03150700295800c0007003190500165400001c0380314065117003000840c01041d003c00880c2241032003a40d541014034110325114810000f440f0030300b0304c10307030400c0c480a204082c200805415104203994903000c0e402e03288001707440e15500f5840183c101005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982802562 1250 982801312 982801319
    0x302040c0206191103010504020d180c09050105040603121d0315040c050a05010507080f0417010c09080102090a0e090319120b030a0f08280e010201050a05071b080c0601 74
    0x31070554402c1441c0f41c0203081540c4000444400d8540d5906044d030361200403c01070001c0c0c0b0f4280e01800b4030382c0b02c1c2900010040420103000010480e0010140c44e006c81031030b4100000c079680d000f0315003d4182074030b040c00342920303503610326006070320840885050200d0310070140850a0014401820124020212910610864030320410072a040c1c0b015100180c031120003081e1030514104080441e401079507007c0c501496911000265003091111500b0602c04110009170040f001c2c4401407031815000000031800b81d0854050440c0c2c6c1540d1089803507134010312049049a0f9802914001c0f0355410179215403554400c8011421485012810320000803883c00c061042c9500c05d1456a44d2201c07013504104120780b03031040554407110b20200910140010811171b0003c0c8802c00030b800e08205007607612002d80309410580390a03035000200c2c100007a003064914010340d0b17824001e507074101c480d8070b0b020041410042c0c801082c5013584040c40c0341d10342c03030440c1c2c0e001000710f41012104400400307000c3da461942c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982803812 1250 982802562 982802567
    0x3020f1207090b09100503030301030f150524041e0b210703031706152803051f03050d0c05031606050f0106110d0813060603050c0901300c0302040c 65
    0x4a20f50458061041300300010200c844c02c071060025108010015421680383d95540345032007140010845016403214030260b00019640680342c0110029000d6400b5500442140120440e100c903d276441182007844400804542040050400071442ca004c14442072000105022603070120503d41c0308880010702860892020901c0400d4900c40d949000e110355107021403403914101a2001ca60081d84900741d001c0145100b00104801844ca01c001c0e0303080340da015013a0000000c80300050b4013181d22402086420011017500d007031112070300c0c000c804585046032641030741da04058a6030300c103201c00107641d1414090300f001524403188503002a0b1039550f0315490128080e01d0203450901c4601d10001c008204540034480d1015809064802840703480c0d12801c044410050291540c40034503010000a808622030380990005140a1130091a6040d90300e000c4c44400380b4141c1c0b040306420048452010091044001050300640c043c0008000d40014142100b0b9080103900003075025150a00c4e0f001c3d200d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982805062 1250 982803812 982803821
    0x3150b0a11031b150108060a1d0d0906200c09090109170a02100e151023210607052107080601021b0117090a0c0e1801140103020f120709 60
    0x3540130356901c15103510307005940074000c0c01282240d03000900020107880e01c55010f00e0b1060804d801060076181e00201c1c4509168003d45241c00090a151017803105980103111041c01d0046040d00c0c0800d481c5003280c440c0c0700d01000d00c0c1c440c42814400041044d41030250841d000b000c0d003082e88400b001c81203a61407000d590011082c2c9002d8094907121040c0007000d8491106c800740c070311000d8145d181981d1b1108003018001090400004034807000850344245049241d460714100281c04009a6800010400b45248103c424040703402d2040000e02c4040700400c1427500920035007010780c2c592004801010050f10341b00e5620300703904a0f940401034480d80c0a40c0c0c2c2405000286c083d80c1466266500a120441980f400d0901042030980c90300789010760703190350540c081844c0068940c100010f40da1818a5002c66001c0480ca0011005101410406e020680751140c0300f400200b110a1804102c104401c1c0140300c041e01c2000c0c007006007100d41d211002c05107500c40c07001003611241d03610b8560800042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982806312 1250 982805062 982805107
    0x20a0305071110051c0515041d100b0a0803030108123106080618060d0f1b030c0801091245050307030b04170d050c0301051003150b0a1103 61
    0x9901030820443e002c2d103503102d0b280c0a20f200c0342540100c3c00603941440050000114030000280109c05240c0070034030144001403a03d40c904101285803d071060800048020a0304079800a070400c10041105c5000000e035507a040070001151501c07110054010b00c03401d80c000c0130041100650542e10f5014540042c0380e80c1c2034800b241c5070441d0b0f5445100c2440603600d280030f84008420070440109440e40b82850554034011710400720013080d0500b5a481612129202c400b85e90301e0003158005108012209182d03002410043d4001c103c91904d5441c5c504810715040b09440501141e512448103501c00010340407007043c540d40c00348042161a052054040c3d0703c030007120460a003e158007090620703000c518003045a812001a24040d211500d0348103481c0b0314101442032140c01089402d500b00928010350780f11b00200c0030341c0d82d16580760809002c0398101c0e0040130410580341c1061086000802e51200b801c4c3c50800f240c09441d40e268032015034180c0e0680302d18150b10701c00461425429000e01000d103014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982807562 1250 982806312 982806337
    0x30708071808160803360a080109050c010c0305041208270a080f0303011a0c0f03090310230a0204090e010f0b04020702090406051e09010b01080115020a030507111005 73
    0x40700e5944110517204e004901c03060f00404503c1c1148546400044000e42c0a12075000941c00003203000c40016241c5405940855441e13519124014240201400400b0a100c02802c0c0b11102200d181e800620511480c05083d9101950500880c2400191020743d4083c0710181062100c0c0b009040800f9901a40c0e2395082d071269918403000b28407500c001c10b602c1c07020720f40ca00045046900704401e1250070811100b4082d01d950303052101030013451041001c00707811056000615031b00c030a5802814184030840303504402c503c1c10044006119202d01c003000301046452a080d4461307440e20400c1d036000c0d21403548907110a5040c20380700d03040c0074010b6014401d81844004200b003141d000105105c140d0245c2e440103580228840b0000300800d4068000c1d6502040c1015012400501684070401200042c1d4081126039500c02d070034001c958000801501420211054a181a03400e2900039500c1141c0d50b030050800c440884c03240200504180d00401d4030a00500b00800e0302c0106034018000d41005881c510b1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982808812 1250 982807562 982807603
    0x1c05220b0f060109080d0509030307120504090f0b0a03030c03030b12010608060a0c02120309010906050c0a1b080f0c1009141506010206011401020a0611180a0b030708071808 76
    0x14960151413201c1c100d45610000c1c1c0440c0c201400300703585c0c9401003542030390540401c000502c0001e03090200c80b00a010251155034440b070900810000701c0d200941950310399464590108100e540ea213034058101d0742c0c503241c031108200a6160441c00307451703942c0c0c0a03a00030219040c0c61841401c19080007054031260342c00c07500255030b1061018150f400c102b80c01c07005038010104500c05d00e8042c10045500480c4003001084200300c564520080328008c607242aa51407000c244005510750004024421490002031203100c0c200395160303030101c6d1040300c1055824440006400000c1030301031040c032007a8606003408002d40011805d10229251000ca4210602d00520661002c0360403a0700c009400303420107a00404441e82051070360503004210f1103810f410b6104003840c14001407040d024800c0440d481900a5031500803085c42e040e06040700c030030307464403078000ba43d02030014103030080959500203850b2400d034a050f2103400701a5501e1812015510904032240008205810b00180d403014200b8000207484 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982810062 1250 982808812 982808821
    0xe03091e0d0219030b04061401080129010c0c1202030f060f06010c17030709081c0507020904061103010806060a050a0506190e03030a120f021c05220b0f 67
    0x610803100814500da01580c4021503001600385019041e1040d114460403100540e1070f5215002d4207a41102c00310750054071407405901807024070f03021070300402014009110059289032100060a00c20302500042480c0e540703416030b1617115800c5201d180d6041034891040645442200b0b666545100c000d0740684103d800620b0035000024125100380c00c10b180c00d40c0140c0343d4900447d20090b00c52015a806825180c50102c6949504025806641c00b40c443e80c80041c41d10345000e045c80d6400301c07202809558034401d20102c0b50087e080303450080d030445001002e99220b26000009110420741680c0001c8003100108408000280341030103000101c5203081c40650741c90802050380300700c0c0669508900180080009509181116020500e540c109646010145408640386800c000c0c51000043c10011424915251034407440c2800343c0504020352810b9a07514001d001919040e50000e00300d0355034400074100d0421907450010400703445910310001e50540c20a6914414180c44811519030283d0128 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982811312 1250 982810062 982810099
    0x315060506090d0803040201030209041a010210020307021902030f0105041505090a2003072120060304080f07050106090b030c011e0c020a05090406090c060c02060d0f0209040e0309 79
    0x3101526001890081010340a0344c85408680002c3d0049040c550244041411039031140600c8603251340f0340d44000314886101c0002071509509240c900702d00da00c10018046000d0f0b020803c200c8441c0c8c5484400e450b00d0f802c1c03000c240741c540c40042c503003042d51a02003408100200301d443c51410f0320000303100f1f00264480c0ca06164403624402c10082050040b260040c281d54090100004580401000d4511180d503901703148011034210078500340000443c00311501041075051401d0488000794a0142c41d220100c0c0215900340700151000e0b02c16103000c03843d0204858100d0403120b40303950010090098664800d40e200c060400604614404d025051000005522070740d03980b0f1006010040c92100b41c01c45480540b080390340080183e8110f100070303101042c103440703600f07105014510070347d00050740f40e4282c00c00c610102d8660f0410000c00044980d2203001d41d07039090540c1c04007080316100240c4400400c010000038840c1901c4c15405c0790a00110340202c02020001c0c0403050000c0e07074441c46c0b840480030302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982812562 1250 982811312 982811317
    0x30912040807030303050406140a1e290316080309010905040b03060109020d0e0a11030106120c0b130e04140105011505180a1806060314040506240a0315060506 70
    0x30a01e10758004101040428846d800958105014007800a080e488841104d030074820112284010715440340c0724103000c51154040300141d0b00414a007000a00c20a031043c0c2d90414280c4074006c24070449165005250390140900030024401507030f0851a240c0e02d84510b0b40ba0313000000c0c06400300380040f20000b1681001e009681c0c0c0d11305d0050142665a08201846000390826000c8902e4950b44100d004203403038040000000040c000d0040081d010820010542035400d66003015800180344410707a00000c034420f1141095440710f440f01500e075000368400700c0b51001682d0012034844940c5040c0000e04c0b2041c07100740d002440c850003e001c07583c0c9801d2510901c58120300d5038400034000b04130f08008504010301e00c1010000060503008100d42e00e43c848000043c219100c81e140960f501800c010380c94240c800c210311015001c05240c4c0d5031806440d01c03512104000c08864404281c003e400303ca080c4206044034a200300200f0110303445890b07042003480ba2806c11403800e8110b1820380045402d207030074002e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982813812 1250 982812562 982812569
    0x5150106030912110f030a030b040f0c081824040314160807110301110417010b010e010807090e100602150112020d050703061e1b0e040c020f03030c03091204 69
    0x2032000c90f880c040741c0220b410f0060302c010009107014030295503812a00601c01801620102d540200c1c1002c41c0754100412070701034030b408054a034540800309411507000303040c00b580301e00e40110140320020710114440c03c0075101081e2840d031000e408080030000c44d440070b200d4003c50207556130a25418070700c03e031800b080c860018194111030300e4001c50000100920011301485100d900085080146000820b00755040c01150280310580414184886903130050a4a910034446000b44640700e90b440020344005685601d1038104164030b40016010b6000b5403c0c1401014400080c2d020b514000a156401024900882005001d01420b404161040c102c4160684845070741c0442416174070b07402c00107403002e5500111254000c080c0000042804c9121b0000500d61031030b0004072919041e21a04c0440d201c0c400196180d01c66002c0645d07034507a01c5103910400100036100040d490280c50800e070b18010810790003408070b210001c00c00401c03004200c003950066100b0360407241c9000048400c5042c6001c3d500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982815062 1250 982813812 982813823
    0xc0e0f0607020301090507080102071b060801050603060607021e03010b090408042c090a1502070f0209090114040f050715080a0b040f09030206010e06010e031c0219051501060309 78
    0x981264a6191020081c03032030500c024000217102c901652060f080c1211a8400e0003940d501261200500c00700c0c0100c9403001c00400406030300942000350280041c01c1c1801058000e24001c000a10180c540b041220030b0650001c056480b50309450f28915018501080d001d4040e500348000c491103401c00c14401d0740501d071301040716418242070007041600c01403020480300072140c45c04a14541009440d8045000d00310101c040c0a00410f135090200c800168071040540c02841004000081a402c41c404040d056040300d9140c06a210030031054058021002d009040403500c80a000400c0012100c0c2e1508511410507542490ba0b903003846a0034641d0140014081032818000a00311a01b40c1c3c004200350340020000a414064100c00f98100c9114a00450250b03102c00010b21070b681c818040c0b942e001800b403800100d94084c03000400e89440c039080600088402c103508410b5018020f110301202d080445107400580441d81c02c103c0d5948201c580c21040e940b200100119040d8401d000e01181c00d908003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982816312 1250 982815062 982815079
    0x6080a02120115150201050f0105091b190302040f0501051e0306010c0c09021206030c01020a030c020307050619110a020a1e0506040f081c0f0c2a06030c0e 68
    0x40e000e02028070751071501c9924075540c504881542240482c10800a405041c000241885220b800642101c4000c0d004a0b41c8904500c010452544c0f84070a0b40d0f40203c0c56001002d5048034560255441d0058081c4410051070b0302100700700099041d40a00102c404409004101907551001514188100c1c0b40300e02800b1410b01c0f80d40c1c2d1880590004580000061411440c0d608541c0c9480306d403a5840c1d00945402a00000c600d82c4207059460725036080542200501480300b11303140041c0d07171450117000050510075a04200d1301503590070b200c440010701010f400076a407600c003078003035075002a203200e03517100881d03070391850105103101c0004c031503405035405449415030718144540710f45d0b02406604080c0c541510594049220303241d0002900c001c0003104a0300d20024140301c1741070b00b0040b421002e9000f44001c9408005402d501c203c41c0003100743d10b401c00c6010317085207041512855142080c403180c0000114580c0c540d006050254004032080fa41e800c0000d0750110604465200182c0f0b1220b0707201342c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982817562 1250 982816312 982816333
    0x90606080c160204020d02030a24120606090507050912010204050612090a060903021b03060f15010c140303040317090d05030a090501051003020f100503130609060504050d030b040608 80
    0xc0d0030052520014080701c0100b0802554001000c1c4e07403020ba8042581a0080301348580e4502c00d005100d1000c0c0000001d40e6481404401400241414441c9061050300c0000640902080343e110304080c0c0143e5409001c81c0ca417983c3d0280144d8051401240102030742080000e9815042c4291029140010002c6150145107452074054102c081d0034041c05008240003800021500d100d4036000e54441c2d0040c00a032000c02e0410015802030079078440c000d4001c13030208a503202d4136101250b440300d09580369841a0200c0b030700494040c0d101650080080d02000900ea03030080c0000043d511582c0700e51346095220202e078400300140c182c01d40e00491285d0207481c18403081802200910f501004258001440740601d455140c291082502c2c584d41501d0240e00600a60400e5540c50101c50000d0790410700701e01141e44000d04030301c002014074001c180340440c140200101781d002a0031a41d00500140080d09043c20410b8036007140c00f04540120703240117440030490816018600403a00881e0140c9100b44ea0f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982818812 1250 982817562 982817581
    0x40b0405060d1b03050907080c0d0803041406040309141c14010b190e090d050a081e0702010c030e0712080f12040803070f1803080a0903061a0a09060608 67
    0x101d04058541034403440f950551200310051241100b120340d50209650406c001c205040060f0341d04844481d4000c00d150b000c40c3c0c0c0f83d00926a42040d4000300e1965280e540341407080441030100c08145040c0524010b00c0207040d03000c0c1d0503031f083d00d20358048649906403040c104640c403905034204031400d0500700381400224901c00034182312510a44000300306001128002030040e00101801580070300d0000e42070006403007007400c09a0092060006002d251601c100207440d40c0100e505000030044a9000114040c00c80c0c064030700c603140c00d82404001800e00c0e11029010b44000540340c3c0020b4a020550f0182e403800140e038004941c0002d080c0090300440d03454030012640f01110201c00f05c001003180b10408158010035510460044010075181d00303000f40d00030000002c030b00078401000014010488061499082c11084075804107410b550382914000607240c082059001400c520301d04007440c00d62000300032800b546400c046503041d802c1612080d80d041115504c0c0295400a03102c030340010440c20 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982820062 1250 982818812 982818817
    0x8060402030a0b040204080d1404240302041a0706051003151a060c0105040302060f0105101d030106080705010f2d140a030c170601020c0114041208130b040b040506 72
    0x22610708001c2844040c0401013400d03a0311039404442290b12056001c5103250340096481c1451400300c0c60b191030a032130040c002025070400020006003102020805003540c1c020340c100e5005100060b9695070f500504189003142da008003505807190760030403001640d0403040d0f00703c100690741d0225504506c40550a4010024001e25591201d007075605d40051b03042c7d0303407604090100c4000b80c40010a840c9881d260003820300e24040d01c0312041c8031050005100513038400d034081405450300e24007840d1144000c43d010300c1d00f4001016041e015480d10b074011901e100c1c045056000e54800780ca401d4060503500b0710481d502682040d0407204896072254100181032103140620242055103405120942c060542e4440f6034070016149022a0382d034501e05003c3d41d0031607940c214103080700e1745120302d5190280010b5101c0544150242c10014030700030b4100e8100c030390000e0b900581304210301407515a905282c00106580100000c140302d1143e1580011048e145d0401c480070345482041843c213103031070314041c81300a8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 982821312 1250 982820062 982820071
    0x19110103091407290702011202090d0f020f060a05030a05040f0b0a1413080304020f21060a0f0606090e070903081216140a0c081303030c030206160806040203 69
    0x2507181c40d40030020502c000c41d9000200b0918010f01030140c0340102d0904c1c403202020001c5000d40f418042902100007030410f40c2c00b100d40a08000e0146500d80d50698002e110344003481d81c0c000756469211050103020240301a413203100351a1805001207650401016005071100c0d4000290104005440b0717a59907001250401d21030b01c41d00403001800c1d51a0f504074a4200c42d10030364156038000307c621903841c0c0d80840381c2018a5130000d039218491602ca0a03201e1000030300c0030b0b00a201062a042c060780310401c3c4110454a10400020f400e00c286503450344480040d10b0b200700c40d40c02c01c01801c0200656228020441e44030340c841841462800210901c0484000c14803014444003407800408a685900101400c3e25440703114440342c90008650071880421801071030410845101e9010300f07a840d0011900c40ba602818541402e40c00c42c40d10010030b1140500e052078640b60140004105034100d0000a0454865020303110386564031121484411040001d440004030488042a10f43c14039a0007184c02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 982822562 1250 982821312 982821317
    0x301140c070f06110a0f020d050a050708030907170304050906062515181401050c040506220801150b16080702030c1807030f41040303020405040e191101 67
    0x51300d03401600148260001c0350041d020800e1178200c00182e640c1400001e5405445040140c107149120000811038082c800c002446640e00002007014110104805401002d0601c1c10342440b085031080c25480b07401c184941806100040049411403a02e030007a643c51416014001d50b8000007a544105051400700e0107480301d103203544500e5a0a48030f40150003012a40502290303240c1c009117000d00d0000040d500b41034290349082c06110f60700401008950803100c1c11110140c9907182d905560342c44402d0120302e0b44041c10440000070b08540107401485110101c60014010560790344d0741300c4401d1086403506041126024025400111248050103110f8009000c850003c0c00c0b0300e02080080d0704010447e074041c0305110030004001d61600940e05280b241c18014000886120004100406d20008411074074064080c0c021080d0348101c28141070503020f04191030141800d08000c0c009601a01900340070301d017456518a8200800243c2411180e06044c11091681c07054031403342c1b092042542070704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 982823812 1250 982822562 982822571
    0xb01021b0607080d02030f010f050d150b031f050105040b0316032306180c030a2607080a180902040b03060909030d1a03060711150903090d03020c0301140c070f06 71
    0x200c0c4c115504c0075500c5011950030610741541003500c0d24505000302e6001511960054801400180700040d609100d4500c40070003282e003243c404000382c01d181c5042c00180d18810001d55a0081d00825008a03040b900e040d10100300404150051503220a48030b400304480c4910180c0030000100c45052500403441b8030a410903010b00d08214860411800f51b42e00590340d0041004590440000d07c01c140ca00d031411401030880f284282d075001204a1000080c40f04aa0443e405845240c2e0b400201e601c1940d011138090790b21540c004003d004000894102200130400306004a0140400d100310740640788107151660655031068200400780b88018401d400e0f900092006100b0303070400303000301c02c5035a124038003604502c0103420a0503c4c150005084508110401c943e84541d0503002c190780071241071011031404c43d641c520482520758410301004e190840d0075100008241580810b000d00032603002c400178013a411a89050003036080c000e46026202690412030500010180c0e802c60206520910010a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 982825062 1250 982823812 982823827
    0x18010815090102040512010c02060705090a050f130e060f0106022103040320210f03041e02031e0d0e01020c010e040f0c0507020a0e190515030f100b01021b060708 71
    0x3c00904901d91b1586040e91604860101203406004d5030350b200c5028074050741840e04100c00a40e0041d05881600e010342c1404020070704030f4940d800030084541e484401400141501400070b41d0b2020b04030381c0980300c000c0340070001c07604900c0803c000c1b00d40400542400c802c106082c0c420f9180d940b02420880500c40900000c40e40c0c003020024403090801d00304081c0c04d00c442001c40c1e44042d01340b04101e603a00c4201c10010102d42d00d00340404e680d001600075005180740c40f2080b40b4038446c6903440002960510032007a180e50248c6124a1070322404450340150380400c8040c030801d0710541410640ca5015070485100c0c151154801d5000c80b0094070000c00124628061504640850b80c003a0046000a0740006154048d400d0840440340102020741607140307203280c15813208141141c0d1105d400031031620740022034503080c0650000c1041c500000c068520802d0404074240c2d44002c00039800716100d0800845012960020603070207031003108040b481356050040d008100e0241e0024004952020040c059a0f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 982826312 1250 982825062 982825069
    0xc070b0a0f06090b0d030f12060f0303110c030d14041703030403030b0d1203050406140703150f03020d020427060903080c070807142a180108150901020405 68
    0x140d0103101440000109030952500700020b841d079a40040e0032160404540160f0354450301c040e41c3d031081c0c251404000101580400b1100805e41c1e0610071001d5040030000b1501c06d0f240780203501200d03c0303500e0301c15040c1e5002c0b0300191260070084480303074103802a40c0181101030040c81c03046800c00d080c20310b0924040d1107901c98002000c05040e075407000d900c081304120426405104d5090300300c4040302e2207003104100d595466130103052010b19000301910b03640444c0400130756411164049403130000781d4031a4580100300500804c1c0007611000b19a500d15400035594180c0c41107202900e401500440c9a40c10580a01c00070b0000821080c46400240014240c1c4540d070415130f0310400d100704008100c1045500340107242c1c1c034001d030102c94188800c128000c002a0081c040f40c4003954000f008114420b254002507040003c104801911055210a04040c203042c107840840000011125a0000c40790503001d050314000900990711182e0150140d43c255106540e4155072011803600003600e415200c1012 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 982827562 1250 982826312 982826333
    0x140f12211309060311040e0304060309061407020a15050705070b040c050307030b0f09031306270f09050c0705030a110f0d21150b090105040b0c0c01020618060a050c07 73
    0x1c2e030040c954944040c000c01000100c203480680040710b00b40908031104e580c2c641c4078411480b03a9010305035160714100400c0900d030003003141c006218280384240c1c5807550010f0f44a0b202d55004035030b11340e100d035104109c0d0a501d108040c0501d45507520345041c00107541d2010030421018005403103032034001800080640c0d040210074043c510414100280b81030886407401c600c60040c092032941d410500c01e5504011100c0400011900303140707450600080482d2102e030400c804070034091800490390f03501203518580c21809000b2107200c91780030401070f030b2140f1022a81c6d0003084c03030050441d0400c200c030445d44d92043d54074115404100c4295045560588001c51404140040f0000401d20482c100a03182c0107507034000d028601030010034846c0400840803d2042001d90041d103961400201f03020403680d1194061750003170407040d106240d0320103030030b1a51a078483e03103240722500610503007001400c008854000810310a2a680017084503031200c44c4c00c00040c2c64001c1c190315907600c0078046040480d110707101d07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 982828812 1250 982827562 982827569
    0x50310020403030f050901020d0c0f0b090607090f0509072a120801090c0c060e070905010f0e0c07080906070807060c030b04050c0c060408090d020604140f122113 71
    0x50751545140b0303014140a00a5444e03800348102403018900690700814000c4034070280e454041440416858103100c05124240040c002024040070008013180000d126801442d1644072201d0311940c4041d0f0343e1032008240078031a08000c4007008100c910340074080c101c0a45907070f4512010004d10002041c5950003942c00181e40c00c003104c803991401036030864501805420703a01d50900c12002c007240042d00e42c04040000a00c9203542c0c890361001e113041441188043d068a140a1000b560b4a004078540f9036280d004010410701e00c5e2000c100c40c840440b0858210036031140c88075013410a0b04d0100f11840c0c00851064802480800c14000024500d00c03441c018004e0740e40700041c800711882d041c08100c40c0b0003810105540010003180d44034610000e44264002d91000310035036544001001701c1d4010030004c600031f4000c100490080380d0011244c030599030210054078100350100c9030380104000b80020f40181495504004528102c0038100c483d8440007181c01d9456920309610020406500b941139071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 982830062 1250 982828812 982828843
    0xc0f0d0504050f1c03051b072d0309051206190e010b04050117070609080c191203021b01022d0c120a020a0905040819120914061e1f0503 60
    0xc11441815094407402e1f821032090440c0102c2d00c2225011041e05100b410405480060ba203001100d81c02c94082200400c001340058034200756880745006820715105000d103030700c56001c040301000e0130313070340040c020348189280710481c8800340150303141d00c000b17229030030201410f07540f80c640b010100d40382d80c09114000c0a441d600a1203045035402890300307009007508007608200d02640b003081001c20010309181c600c0822034982c000c0404601910388555842e0303100074240d46200180c0824150046640c45c5245440820344c80d0203041c072700049813035650b06024203030f0744d84581c0e014001c0c241d02c80f16102034542210049070003200703002001030360301040c2403140c0046902c8041c0420450400002c1c2d9401800104000d0000741401e0340c44504c04d01445401c09620580c003c40c414005105032f80040c60391404190403c55031540c0e0074034007554542c084074910a80702d0803010804101e040c612040084c2c18900c5501340b2034543d440c600d68006541181218031800080303010540d680e081c00541a00f45c0c120 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 982831312 1250 982830062 982830103
    0x10621030e01080601121505040606180e0907090203070e090c1e0f030c09010c06090f020a060f08010605090d0203121312080315060c1902090c0f0d0504050f 69
    0x38500103003010070810001d410464070b007041c0042c50f600309170104001c50b021900843c4a6011090b0040301000c142c0c4002e50041c2030450005049801c6150040c0156080d030050b12219201c00c800c170031030784003610100c6284d80403240410949206034040c43e0040301038641a900043c224002410200056410b1049043d00088502040f0158807a0704c0620018108142c20030711003c01c0401705010003085c0751484140059140010307841440400d81c801d41c007881c02c01c00d1002d642881c5902c4d0440200c100c1c000c514820001c1286801000d6404010000c3c1d556040c0c2e40c2e003003003000c940c0c90f041800c80c00d411040c011021001690280071240241030304024540c0c90b519a5002c04d1a0032410f07034041854445e036211141c0103d2103100880e0303806001403522540c59080d090100d201480b41c80200703100c41c01100e001d00c0e10715050003000c20000e402140c20040d242c4421405a045110707400c0d181d090540100190359441321260006039210340583c09841080c4440c1c05058117285400282001c0081e06 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 982832562 1250 982831312 982831379
    0x90d03091503060803030402040b120d0507060507030608060711011d101d1509191a0901050601021b06040807031407060504030b071b0c290a0c12020106 67
    0x24840c01c5100761520b450240440703841e00c40c0954070b9100152000c2d014035124440c0c03202c240c61710b40c05150000310b0002161401c2d106000024140d80100302e04846403030411000c541c0c0d5901c1ba005003030680b00d8000103464142c0310828107035501cac2400d03a1045840d54850600e00101002c40c00620703842c218001c05003903e1740288040408903031000d8100d10342e92514603d42c1895210004034000750340102c9480321420341b541a10315146c1860380c414040c20800795103401c1c1c200410071019500c00d20801d0010b01c6035888104129081e180b04541660040e4403c54040b404070004c400300c2c582c04070000c2c108914054031928034508121311500265029101c1d40352030401d00008000355070003804c0d146445810f040c00c1d543c4a212003203010780340c0303000c029031191710b906020606614a011503034040c810042c09607031500300d81c1d03c0d019021065400349410b084482c2201450400310340195402e6a074004c0080c12664440340202c41d5000300d041199038840d400700340c1702c0703c0e01482c1910044500056002d802c9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 982833812 1250 982832562 982832579
    0x150a051020121222171e0903060a050601081308120403180e0702030a050306030f07090e0d030204030c09020f0c0a06050609072c010302070606091d06040f080906090d0309 75
    0x10150102c03a0216144004844c07001061640d07501503640710b01c204000001e011305014550065401131815880e405007844005040c840040101d00019130031740e02c05a44032182c00c030850781c0440b00a404902800001035103d06079000c0d83c0c0c621445482160309104485040c01130002c0201d80480220f070b070892244c141541940607a100a01c041c0c00032104034544200000d440b4003407010004140280400450b00b20354041c4800e004900c040000c480c5420b5a45000b800a000b140c503805099000b40d0500305d6059109000300d80590f0b800149211810345031162150095002c0781e044181ca20040c030414003c103005000c441040c82c012a00031506003000c008202c0e1141001d8422820301c440401c51103e401c0c0d21203880fa0b403908075210350382102203204005801a1080c044014601442e0410205040311f03a944202031000c01094004840d055900019541d50000e944c0600b602d85e00044010006a1540083c4051030000d0034240c28200c4417000b00b002c07491982000c034041040c10800303028202 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 982835062 1250 982833812 982833847
    0x1b0b0f0a050f091914100c1209031d04090c0803070204060902070201170408090301020f1b0c010c08031308070812070513120203010207140303150a05102012 69
    0x21003000041d07055060000350319a036004408071007a2115a20f142c80d80c2400952011041700b458034006071030b14941820b0f40480148024004040031903900d00f11007803e80480c4c410040b00c3c5a0503210481e000d040c41d54542903a14100303528903802034440d0b0365003001414a0318000f005044120095403100c03810710400054900381d03000010203038814450400585c0c2c1c802d40b220105510442c07001103940b10390400d81981d200303108000b070305980006005071244101000900000114255070054030609030b1f80c4a031604080c00c1d8050010700404141000310b4140001150018450955801000720079680c40d580b641108206880101c2c021130342d140c00c240310f844900c1e8498a240381c21450000702d1a032581001a990013031030886400c3c41304880031501c00f5811121403d0304041d02c20040403803041c0b516600e034801c4a606442d5241481300114501b40400e001007a20b000a20702108141100c01c100ca96000301c1d03020740940c2d6410003200032210400e108001c10701755520401e41e80e4030200729a141542 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 982836312 1250 982835062 982835071
    0x150c11071e03020906010c21110316080f041e05010210060f090f150905010611120417031b0606011106090a020118090c0909230402011b0b0f0a05 64
    0x91014061881c00c0d10500c00e1080c2030700c1e41203440d400c81d611040c00403181001e00850041546040c3da107a1120040c410080c1c850400e01c99031890002081c40c000709031603020b615111468425480e400000060400c400f910701603240004881c00c066030340e0394400707009281c640310300514040320605115a50703061101da419420722a4042c00403900d44803410755140070034404d0a201d82d50f6104020003051003a08800c1c243c6205a2074a04a1603c94201d800100003c0c0329900109901560421220001048441c11100b00070401402c1c01c0c900002030b10500802c504001050000f004458540c2080782c4448000541c1c4070300400c403e20301000050128015010b0010182c1e0059003000104030000075009441c43e828640201000700012020b10700e0003d45d002002003500380190301c1c1a856204040c201154a0020107201004803d148103c12684140b0340d0b400341046a0002001b55005001c01e000c80703c10900110442d060944482600100c1950950242240c5109201d443c02c0c0c0e500a05811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 982837562 1250 982836312 982836329
    0x210b1219060c1b021003140f010e130f0b070905030109110f01020705031f0b060a030b0f06071e020109090f0603050706051c200f0a2a0b04150c1107 65
    0x58840320f4081d01159021550300a100d0101e2015036a61710344a81c000d51240303190100701c2d01003402e103900300c001800d20034002c43c075140701c02c400090a00044944402c40c000d0700310604160010894444500c01c1000400c16414040c04800000f9151000d101d100c04450045010500c0ca401c002e08000d58002d078410041d04540c0165414800f680c3c020034403003e131090600c0c02301100d5a0404500018141c00042254000c50202d0914a116050b80101e0082c0108072030380414807104404104150103940c0015000b0811b40400242a40a526240c03408500504001d800c5640d41c0e1340040c2680c140c11444071074a510b0789800c004114041029001038001400c08500700700041102da2800d421030500c18a04580341c03810500c900415550391030f0841c003a084503658030907640c6100c90316540b0100310700300010f403a20810816070760010f07010350720701c1c1c00c040100300481400e8554007020440508140e52100000000901042d41032140780c001c280c041d10f0b1141c040425202c02810700d150382d4045501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 982838812 1250 982837562 982837577
    0xb04140309130e061503121602040603080c01050a06030b0c0304030e060301080f120a0203031b040503030706090201110601080c010c230a15060605160809031203010510210b1219060c 80
    0xc09981c049040301103000407c01164960300280000508102e4041d000b94100d46410000300510000c0c40040500741c00701c030b00a000a0b02c0b4002404112004d1344070240610781d04401180c1c8064280005640040c028078143e405145624005031560b4020b0744070f000c01e80d2052890b1b01d00d4400900000c1100040c040c106070810418000107034032484010b1000440c8040e000403000d800000b40c2c15100603110190481c5c2c0c82d1616403030540d00411080c0d50690205034126018900c0c010009155030582e010325001c1e04481c1c41c10b100554020000c107a04940c80355245c1007070064400310f00d0007800d5811301e1030014001c50060742031040e040722440d540c0e0385c150360805000f8059507400204554111403207243c1448000d6584c10134540030700400c1304040d854000c8680b0a46608460303400340d07050394030403180d1a42514800c1410350304065944da07404819255000d0340a010801d9500444409074040d10581c030001d02c0d81a2075061824500c240680c24094203200301c02e04c50188240e0b0124103482c107010780b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 982840062 1250 982838812 982838851
    0x90207260307110f070e19022a160501032d0506120a0302060403081e0708011e18020c19352a01020d0e06070c0b04140309130e06 57
    0xa171580790300d0040810068403400800e860505000c80c0781c540303801401c821521803030300308a044034034449184500c0c480201c0c0142c450a4003800321345041618520000c4e003014500d4040107501070130001d09104962000409514201c3e0350740036114001d4481031000240034a484d108010a003070b2071134020001988030000745000690002051038101c0c0d090f00b44002e840da2400c206400051a0021000000503601d0501c204036400c2031a85069541d20000d0704081d5070202040ca080302560b00c514041906104140e44c680020303a8000d11002c201003090f108003412292185a035011201411a02d20b280742c104000049440354a10610358005840080034640c041c8142c82540120144072814503c10070590030030569080e4241c2600041d00c000795200c01411040f00d009200001c00036130a40144030003d10b90900c02c2021030741c1e441d80b11042080980300e07929805182c50208400ca9094401000201030035030355080d003500c3c000c825403808104d21408402203405d00901400b00c68400324048a0507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 982841312 1250 982840062 982840093
    0x110a06080f0c161415060105030c0406080a0f09150e06040206070b070c0b011502060115021e0c0a0909060b01020c0303031f1214071401020709020726030711 69
    0x580c00007181c07440307161501e0002481d1038001040d010010410310b01115044449080890108815003140042c0005035451b0b50042d2030314403084902c4050b50344200410f020303040c010811030790400c041000004000001e112078200312100e9407807c0e19281c0c0341d001040318451840c014a03060144100240070340d401c083e400f0030f125000314040101800f0241c03001590743c03032060310080d0700190010100780b8956903420204141e0841401ca44005000b40e80005c91038403101c50f1958562071459008065070401000c2900044800c072020000303c0c06003441e1a40c6540d00c0e40c1c05000034114800300060341801c0da24014041700c005144031410740d00400d101e00040e98010040d80ea101071810380806040100c04401c800f080c0940e005a60302c440500b01140034004144a081c08840c004004c640300c03651560215094085984034460050b880003105018601c915009008060310400d4400040c03080741c2d80b41c0b03401d1412000484030f2010013000b00a01d041c0e0040e02c02e0741828010340904640455110708 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 982842562 1250 982841312 982841341
    0x10222030803060409031205070e0f0108061503040c17010c1d0307140f0405090610080a0c150e061804060909020906060a0203070b09061609060831110a0608 69
    0x12440307070307617100d010b00181030244801c5d81126045034010820b514005502a00612000c89131601540301e0041c02003c0754054015a030103a207008007101040303480080c03403410b65403000b08201d600c0d003407884e000261149455403007060361003001c2c00801d0070981d0410003403010101d00d44140c0110780d42208440c2c20b0b1000300e005000d0300c0c8180b003200c0c540e214801c0490b10500c50304981581141c90b100030410200c078007080b80f6014000034900b035030740a603035105260340d21221704a0141540c01151420440048040540d071803d0f503041c01c2c0058104c107000300040b01600701d225140f0241c0340314108940186010721403c4c001d081f807444200701090f00758000c02c44800c4000c01e4640580b000140320b0204500030010b83d004190300040030340c0c007850302026560b01e80f001660310040110403c55803101250140c480c0f003081d0340031903550584540d00d035060003005020042c0c09041c004498081e03240d80540d02c041c202c1485010b01080643c0010b00000d00c004100ca82c2c2c820000c105944040c0300c9848000c224 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 982843812 1250 982842562 982842571
    0x4140315072102130905010e0c0a1d011704080c010e071202040209060d02160605090303040f080a0903050d02031e2104150218130e060105042a02010222030803 70
    0x20ba0202c0001032041c10000b0310681e42d83c8900d0718022400081e0400b0181c120034180c9020294614403919900599401400b403070140c0d00109003e40001d1019010015202c420304070145010b00c518424403204e001140e0302a20240e0b98484001546410390500340100030b0041802c0c1c000304519890240701650240c4001d90013449581c002400f0074a560340d000c1619510044c0342021599140c5c0d0b84c042d04001460740310125102d07824080015044d64006c802d8a221f82e4000d4000440c000c908d5031110941d90001d01c0e61028441520000310204200708601283d5034100d40081d50307205030b80214190480111000030f801c0840401c070b200000115246016200300c102c1c44c8100050311145004070011000d4840d40390540e10204d602da048001c14040310b80a01025070b10500000301ca0341402c0c0645564820070f4403241e2000c4010025400d05611568801000c0885400e840003903c030555120814248040010b03034010800c40505142581040d140c0c0c3d8042aa44445e6840c0d0f50390354415010080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 982845062 1250 982843812 982843847
    0x6030616020c01121d0105160e1005160b19060e1603092a03060b030114010324050a0e0607091a030709120506010f1205031215060414031507 62
    0xa00b00d000c5140340e80044030540360a0207280210171900750b00714000c000448800c49000c2c0e000d040e0780780140c0107581032055083d0143c40500b48000e01041503500d0381c090b01003c0e54108894000c0c9020614800c0050302910b4190740b41110356012011070300c20ba5000350446000725035100140f080700c8203542d0400d09801c240c0c2c00c0c04200c000140c28030001ca802c080400111003891008800c420300c141c4a4141d0a0380d05c01d080421030105081d06050807038992800105800352010300520128440408d080c2c0c105c001521107076207080525500800343c500660307441001d25100c00040c10340d11000e00c003072603220416150000343c3c2c0e45041250880e051414141d1320f0501c40c000003188001e03100c0d038000c4000c0d0402e220308a680c00081d1500e1583d610f400d10415440b00d80640d408180c201014458080e01600540103606201d5503049502020601403d9611003809102c110803042e15800041d000a14a015a45c0b01c44240d0034241400e00c0c003844801c1c15041801e408001a46410012411030103d144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 982846312 1250 982845062 982845077
    0x3080a1a09060321120f06010e01031a03030a09150e0102030f0307030b09010803190905031f141303111f090c05041d010b060705060105010c0c0306090b06030616020c01 74
    0xc40c00303e0b042c500906904c0c04154002040400c040c41c0110061403400180c140f16400781d03450040c00c44040900b80e400c20f00103a400700d4020303450740c8280c00c0450b0400000401d154060003810001c1d00c4c66020341680d0011401030441040f02d968a02414403010401e800e0000403641401c00007501c80c0b0034181d0742d2000342404004108500e110380d114180f900c0c0081c03c2010b8550310b1300d070001c2c0d41e9049000410300030072900b40c01101c014030621131502118400f40092a20300c40c03100080c90b04100200c2800c44840d90b8141c0085000b40c10a402070052681c1e070484048080035040080040c01034110076951548044c039402e00d1100005245030481d5075100d000580c030f64003480c21800b0500d0746c1e0300c100d070302030300b000d40390f002241071101c2d10011199850002c0101e10001c81c10304c00180200000070780548c011400400c05940146110380002d03104074601e0704c03419200e6032140700711282e294080d900c2c58520400c1145a0a08011048c5c0090b540b00240e01000070b4010029a50070b81544614100440b2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 982847562 1250 982846312 982846321
    0xe070b030606160c0e01030b0402091501050a0c061503030f02190209190b0910170a12140f0412061d120a050c0a0f030e0603150f0a0302040f0903080a1a09 68
    0x398444800545200d005e0400b03a075a490400c2d84202d00243ca0581c403c08680700800c01d81581e01e003020011242c1a15840c0c1001400ea405440b054401d1703405440654039065110002c000700d2201402031486034484080c3e1504d0210000c0c542000708904400c400c01000b510405a0750340c80c0020781c010101011104034000c110f50001c050700301418410b0700503408505020801c0c80550402d8281d0740c0e1405c03c0300707440c900385078455511a103a4401400c1003452107a8420306c0f91080881ca181041b29504a80ca001740c204000c2d035a6600a5002aa40c2407503122084d003040000d0180c10840444044603841d0003c01c00d043d1a110f0014030300c00340308000005200701c030584c010400d8580b9075a81a09449400d0360a041c0860440c080c0c1104400003240342ea424107681c5001c500345c03030140e0400c10704081c9103500c10050120182240c0c0c9010b50004980100200507a1240520038030014041404100c1c0340582c500689022005000c8070380d00b6040c40c50380c00c2c0b244625060440d100130200e52008460700d8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 982848812 1250 982847562 982847573
    0x7140f0c010203070818070315020a14030c130506090619020c12101803080103030c1703041208151c02043b0712030e0406080607030e070b03060616 65
    0xe140c01680306500200030130100c0c503000712070306105d80b144a504424803114800304036145e2074980030003052000e0140c0d045106004960182180c0d0304242001b40d4580c003040340c010f00a402c125040171006200045e840e00c10558400190010a01521410306006c4808000b5805000358a01d510201d5080e850400100d4820012084222005441036210320314120400d0788400c5140d260410341403d0810b07841e42d00c05507a800c0070b4007681594902c9a96403e55a080b0f41a80d0203090075102a65180c507212401c0c0340c03800042d4007039031080c000d0070400d45c20b000700908544001050001c0700c0c020286526155240ca46061440708504000c2001025944c40003c0007010710b44442c00c1003d6a1164000c003981841030702c42100c030032821050302443d0b640f4201035607600c100e0140305c0a0940456004000038010100142c000500074400b20341c41d07844450361491b011049445c3e00c00a1380380c00546602000030712080001d0540590007920f9807a104010400520810580c00007243e0901e00034420f020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 982850062 1250 982848812 982848817
    0x305150409051e0d0905030705010c12090812030f0708160e12030406020f070f03150e0307061a210c0603070207090903180b0315040f0f0608071d07140f 67
    0x1001221080c1100310f00c443c55a4800410001020403109a00450b440c1740c0020008110740050b524148240e516603160032102e2840241c0c4000e00403d1600800e907110180000f400302c0d086001d038580c891402400c1f0400a44010304001c05005000c410b00c420501010001c013111000d41c20700c158035081080c08282c000c1482d14070f41c038070303400080380114501c0d902088046080000d60121014070b034691180c1041400c06110051807403080b2900c3c49413544140d003000f0741c05944281628103004094440d1020390741444003d0701100100758100d030b09840d01c036841d00c0c0d480c00080e014504d4181002907255a41c0003031510302d48264004000192014402c0002c10040c1c802c5040522050800c0d190150005800701c040301020241844041140144081039074031888200500c503422003404411b200043c460b06000705000e58569604003a0010b040c050a0001d2039030300024140c1c80d28003030303007901c1000340320080882c410815000c0c0a4016072000144892000100b0003541c1d45103851500140c0e80b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 982851312 1250 982850062 982850083
    0x50603070f3005070e01050a1209080d020d0f0515130e03040f14090705070302060609060609030a0b0a230f060310110903071502030f03040804080a120f030515040905 73
    0x11500602c42404844075500264020501900c8410071030854a0041d2214011007150100052103a80104000100d50b0440e1110031b01580e440ba151039803000c3c0e08401e070b0388800007174a0190b403145400381c940d0b4039610600d175000c014590702091050340c0e0340005186924165500401c951220700c01003011000b801201c00400d90303205045a41603407007041282e0721724a840090301c250940c40004100c54081d6045513141030385a40a0038641ea41d07102000000140609095000b043c10301110100780ca0400901c40094000e21031403069203019024031098034020006500701081e04084910502c0d8403c1100d0307085240003072050076a40c1c0d5640840d2406407211a00d142407800e020031040034102c407a000f400402c00940a5800c115103075091038540000040c5044c0040c0e00400003219024034581c00f0f1034101e8490814580361555602100385008240e103421780301003012041e0184810780194801c8958992401c00780308515190b42071200e04240a00c00c40e010399241c444e14410031a0601c0443d03140c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 982852562 1250 982851312 982851377
    0x2130803030f070f14030a1503080a0504090515030a1e05030301120201110a0819110102042c04050d0804030221030a060b040f03031b08030a15050603070f 68
    0x1a440d0000c42d46a0041050301e181c00494580c40c0c001200c1c1c1d2184050302840c0f5071044025140d034440c01040d100412101c10301041d003240c0302101100090003800200700c50030007596026110740c10302e086002124000750807800f980d1202c00c61004203442c0400c401d1002c2d03420944855a8000c0c42d4070709a625141140c0051590000000115a240440c03c510744914000e81c0e6903c0054031402001d41d59101a84025100c00000e000340c04031403040d0004000445410b01e003800c10745105004040c01d9800941190000d00c843c40c041503002c400410400341007040e0390103e0541410b00381c40309500c079640c1044403410080590005000d0600812201c03150002007407a02c08203044e80c1d640300c0801c1e0400e462061000c2d0405100240344400c180a56044d110342d601c071100d0f018515074081e103170a6220020194902c0841c0036903c0812501740103144110814480415a181d50900217508090300b6000613109071310074014080140c0d8401e21080c1c14804c0e03410101c1501198ad81107203028003a05522000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 982853812 1250 982852562 982852567
    0x3070c2c2404050402241c060e130f08031b0304030c0b24060d060e0708040c150e15130303030f0c02010b0d120e04020409020703080606180402130803 66
    0x8203000c6200350071002101c003507561005210068100700a0b10803d44011754840c6811802d1117040d0103940386621090900740c1050701c3e00c0c60a0032403403441d524008029420130307600c800030403200000c1d41110364424500c69242000e06041e541c0c4d0f00021016943c09010b181001c00012681008113000c07610b038004034109681c0324a010b14000f007076480c0100d01211414481c401142d4120b1201100c0c03100100441318010566200740148040c40e001031000003401502ca0780c0c00107640055440301402405280c0d00c03a910b43c42d05003800c2d16070740e0103032780b00750400d11028649101c5a03a0125041001071b0044802c49030360b01e0311002105c541c1c0207c5511044140c0c03000000010141c06500c40d0400340141e01045c0089003142c1001ea00701c980c0808007582042403001d60400141c20115000b100c41c01d2410451241c61007035000c541260410f401c14100b590b40001c0701c0c400c0c0b6410880403030340100200e603101d1070a03411020200710030f6140d500843c0120b8020030079540300c0907030150f40405004c003101240e8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 982855062 1250 982853812 982853821
    0x2131206020c070f081b0f09010e150303120c0d0e01050a0f0b0405060f010c03051608070218100605070602071203060e01090c1e031806020a1103070c2c 67
    0x10001c0d40800b641100c54421a4000a900782c03100504a0884a0240190880103003955100420a070100104c039400000c165130003d143e90f8484a40d4060980010140040d282c4102c0e28851404403180a40c0720750f200344440d031005418614070941c40100ca4583e141c450a03450350400103083c000c000c9040e55402c0c48100280c0c1200b6a0002c12410310068043c00052084e00a110846a00f583c41c0ca4000441c290001e40f20b500424076030008501c24074001d403901032100303498070041a003940120707450301001a14000b5442d00301041825200c0300800f10322113041940324050509590b10510b02440340c049503140031304c80305a0540d1081c0e03800c1020388120072450ba0005000341424007601c00da00d0420400421989110301c04d621018525840c0c0c0c5200180c130105006144c6a00802c12080644031100b920343d11001c0706903041e100784113000244e298404c00c00b01525164134424200076640c021700c92000440c01c240c00308400c071620b408660504c000c1000c2100080b41c103c40e22024858411000d11 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 982856312 1250 982855062 982855073
    0x3002030f0f0f01110c07150c0c0803070312020a0e0910091505030d0804121808031c0e0a020319030e10270e150406090f060806060f0310021312 63
    0x903a20750038901c008009101d000e990745000f501170070441543e964003032241481130030024159124010300c0744c105040100143e56a914145d00d0329004980380e43c10100c0c1c0ca0041641240982e001c18102d050190304000709901c000740122080300c50303076200e10021004145161214110071024000d42c132004d000700481c000b2a0001140c01b03101e01030003840703901d0b8040c8501d407107202c1007801039030302a000401c1194441022141c0d07040281f810942d80c4c068450000e4041000c000521006420344420040030500c2c105003003c4078403500c3c00ca01c01c6c0d0861031038400140d4011540b45078040103001140c54482ca58142140c41c40366044d07106421080761080c406c000703070b00002c41d01401442c1070780c5640040300840030700c00c0f584020711648441119440100390091505c0c80c0024000f0030240c0000303881692043e90300251207012102a070820f541d0a42800301e00000d0003100e90005003580c14a1080c900c90010030390704d848401d6068542d81e4040303400c120104040101c00018180b40a840301e03201e001d81000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 982857562 1250 982856312 982856323
    0x2090402151b010e160308030f04020303120420040e030405012a08030906240423150f18040213140103080315190614040902040305163002030f0f 64
    0x200707030242c445c0e09003003521544004a40c80a80b40d00c00c03009400d503219203041e9901c008001e4404c0b80d0601003071010f51030343c000c815106071040340100030400e6084111041030085043c01c15505005078141140e031000c4200000807034003140d0307081c0780a8400c1c01c402e109803640310100b200c0c030b40c12542c04154400d0901c0074801c0907502402036035003a030700592160030a94030310700038508069010345e0010f00302410364a40b41d4402d6205a1203800c1000e03035804484002c089105085401842e080700091154003135040118200c0d903400419038201c4c1d41b103480308080f0809820003c3c0001d12030901d154108861044d1070304803906c40c0c0c1c1c0016400096507120300d01141990011900a041c151903803004040c1843c0c100711042402e8448002084203500380340041710801880c6044121900c001c10000038080101d100910046003d04050942502c038840e001c911200c42c0d80c810a600c0003502e006045482007540105548420342c600080000c1075403000c24105001c0e24210703609802446804410188042503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 982858812 1250 982857562 982857581
    0x30f0e19032312130507140d061b090504020306060301030615030f03030c110c101808060114150708090423040605010302010807110a080c010e0d0203041404020702090402151b01 78
    0x510100f5030356a81c81c000800041d000010b000c03940f24000810000e0780418202180040150800301e10347c84945601080e1200b2034600c851341c41070b42c42c50501c040d80c0510f07180050802124150710f9030400100162031400b0600020380217950310904580a24101d414441c0110f80c4141d924058000da401e015005110310300045c40400d01180c01080301200105604030026001405503801001d605001c0354002c0d480c80c40341038541c0c2d8581021628074070401045000f000c3e0f0203150464404000c0900c02d074241030114001442a0500913100020151820b0300d5040805580014000058040b2842d60b81c0121103510845084c8805100c1408140e811880c1624000e882d0494152903900c0112503a5418a0496515401030028000055440c2000f03001603143c0c14008910000303100c001e5030130003449a050b4005030344005000c2003001300080140c2000b200480d411400c0540b41d4002c21940100144002e11502e1075609519201c0d840505413243c9610040500c0c510041c1d200265000705030108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 982860062 1250 982858812 982858837
    0x1b0203030a0501090504081801030f0e0c150a08160521060a080304050102191a0c13050301090809040e1203090c0901080a0819090b0a050a030f0e190323 67
    0x1304645006025503401b480d80800384070303c0e00300803d01003c042001680b0060405898200202d22200980182829508010003401d0784a40140030041c8844100e41302700000c3d1400c0c40b15145d6035411610580c1c0c06081c40c1208a01d804461000b21024071604402d00c4900b034a40d04031b103000c140e0760580c0510449040d140c1e02c8140c8e880b14009581c074003452247c5401a40700b81a4201e202c0022000c81c0141881101e00b8000d5041a090414040d40c04580400c014980480c0c00c8400101c8000c0c02c000510050300200403013981c5445155140c40364005907401291210314040c440e030300402041c4546848495104e40b2400c01c021070a4a031018840d41c40e12540707000d0004941410080303035107111294040c0d03c00f450b180c900c1c5c8820010542c840c0e400400d10a80b8400060400c3c01c0b0802050300c01040d030303107240e580c1746c445601808560120b116072018910f480c9000010380303800a8141c01d02086400c03940c0e102915480c088484981c9003203482040b10600cc034a0240c5054a005090360002d0751 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 982861312 1250 982860062 982860071
    0xc0d05121b2506110a0609060519091a1806010801060503010b01051206040e0a0f0305070605010b0703090b03091e0714220209150a0e28090b041b0203030a 68
    0x28034642d070000c40702d0100039548168804100041c5000b14000b01301500c207042a58901000c0703031110310448942d4082031714a42e84030b904109250083d101102c540c0e41980004101d003058070340b00c450009003031141481c0010012004500f20740e50300401242c2d003482c03503800c8810545e102c41400e17000c0c019920519010350301b400c0d00110036600400035154002c2101c481c00111f950b8070070410010b00102a03a400060040b800a100881e08290382080900c3c0640ca030b855440ca03140c913000c0119041644405e80090041c41140c0019070300950340d100f1256184403ca481c0d0b20791400d05c9040c49e1b4601d000203c3c00740080d20020304140d0101e807000840c0d888403c00500b100e905d10521004401c80740340e0403001c454a4584030740d503185d550301403d200c1c20040c000031140d00c40506030b461194001440c8201007041c100d80c40c40c4d40e10b00210030103150b55a400340c00d000fa002e00c050703140141c600c80c080c440c21241c5400c0e40071115152684410140d040c810072240000725122006900c0e40d00a03510084801e040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 982862562 1250 982861312 982861333
    0x8100f061511010e0705130b1804080306030d17060904110a030f1104060b070605070e0a030b101a070b1503030f040602010f0902100503040201121a1206090c0d05121b 73
    0x803901c01704640c00502202004071002d12443d0003040084c49169200e45102ca02c82e0100c0d01c00e118942c405c600c0303401200e90340d082c00001c140c40e00007400c0864081001170f4626050070001c0d41401a00410251003902081c0c40342e14051501035180c40030781d0780014421100000f032001c104c0c60408035500881a04490f440c0344414401600d0603800340e01d1840d402000418000b40542d44405e070321550b5881c003100c20300c0d00d40000820214543e802070340c0d03801c403100900010281c441ca481005108180a40d0ba001400f100030841a0042e100c024080c0c50703002700019a00507101c006241d035440c004007a01d641da0284018200660018061100158646500000002d000307114605650f81c000f0a1a050794464101c111466440204220704204013030515202e148550b014030741ca698203021440710450022402c0c0040948100140c801a900c04402c0c450090b40100f480c4044000555811481443c2418034a25207401c00c0b86131480401d00140381a1400404005011540504001e58041380003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 982863812 1250 982862562 982862591
    0x905030c010f05100609050d0501180311060f0420010c020303072904080f0a050903010c050415080f01090504081b28150e010905070b04060908030408100f06151101 72
    0x19a80a1000400c0305011b003400f040c6440242025a244900c001040d240002e46941c0e40001c2c01345022408243c2c0b855100191800c240061a8010542c541d050765514281e1561480c940a141002804021000b03001500781d1044042c100700e03075000f80441e503840b6018644003d2080c0016400301d01c8a540380c00b8950350300e550001880c0117079000b840f8641444400c2c1e145030125030103240b880c000d2000810044095407001e009041440300a41c8a0301d031100d00c0c04100d50000c541042c580300801403002c08000d00110503607200c905454054500146640e900d103480c4586100701080c0200c04503ca2216804407440018410075101c002c800088a0b20303e088403500d0240e840b800000d0052481d00f0000f032450b02d40360700001c054801100041404841c0d5180c1506041c459040500c1c092000101400103581001c0d03a20003c000c071000071440c0903c1d25140036201c003101400d202d180c3c0c1c0c8840169a0303140941c0c00140182c0321070310113990000d144120140c00580f403408030001650070300c0c5001030003e5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 982865062 1250 982863812 982863841
    0x3070f03110306090a03020c061b150702011503021c030c0c030b092a090712060905011707050d080d09150219030c0f0e030f2a0a0b1c0905030c010f05 66
    0xa6050b0020588210024100a0550850310a103280c5d00042c42c40c0101c040010000c110100c520bc40042e111800d203540c00030b0a6500b15145625030350300070b07282080161101d03407141c0c2280e8800442c000c02a0142d1038100da94122800010348890b406e4100801804042c42d4024029280e10003211a2112000d0684044282140b03140c0b5080507820a030b0106800c05405081c2c0c400c80501e4030b0711070881d02081c000c04560058000741d4030140e40d9401440244500b001400b04200f1031070040002c1c529140000f04a01a40900184903900115a8030091162504402c608a50200e500c00c0900703840c060030002908141c6010340a603044214a0005030700134403481138100f640c0da43d030391104140d24209403429480100480e4061040c1e0141500aa000707001c4a44200d05642611548090880c51941e0841689886074880ca00ca0941001490600760890b140500201d4601003a03444141046000b0700c0d00308409030180c000010003184254065015004640d4042c00400ca03944a80c0004139519 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 982866312 1250 982865062 982865083
    0x150946051009090c08030a0210060b0306030d1103071e020f0904110607171306090603060b03150f090a0b0a1a030c0705101506080108010c0f050903070f0311030609 72
    0x390140400d014184003030700440f02144c05000f204040326a600801d0b40307554030070b502010041c0c210b51300603c0749031160302543c0000d2081c80c902c503082d41401c0000a4949180402100030301c684074035200c2c0c0408040c0192045290000050301042040d24005281c4a1030701030100d00c101c100d044100b040789004801140a280c12104000e5a01c48903400e20490758440103041d1906000c0040001c0d01140d0100249071200254200d1184a40381180240524590f50050010b150170101c0900c141030030002a01d030b021030b004104a09503030a030400300f410f1603481032059412448036010071088400741e402201c65680300362440300c065030b510b4121408807003801c100503107500d200b0000b01d00c0d04210740005e494144c2c0618280e80e56100407200b12411510b05219204c01003c51200400455403c6403803107004242060081c05428601d1600420030403540241c2c10512001041b43d2400e03407800c21000d40546490000d555901c0d46038104014214482c0480700c2c402d118100c009003081501060100c0300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 982867562 1250 982866312 982866331
    0x30e0301090f0602030907170109020a050d050c21060708010e010b07031407020a05030d0c0b0c090f09042f040b04020f030c2d0304061415094605 64
    0x602c141e55100c501039400034000741c00d41d100d6100040303070300216582c4003c0824807010000800035980d00c1403080d110001d80c002442080300030300110201f035010982006482007100c6030480460720710641300c60f400948401e12a5481030104100000c4c0e002a580340c16980608404406c60f0b83e80d840391510b61081d07100040c005031403402d8090480400c5000341540602c01410020016152000710b0b181042c2040303c100003611070340d040424040700c140300641000440f205989006032080c04031310300c80080246c15004829500003c1c0c24024005850000e4021042e642115402c001442080030140b200c0d03028402c500e40b6210f09410719061080b510b181c0011080306085135a029043c903e01d800071040039480b5540505408a00005407000700a080c1d80920391685a0905040000c2142d0402c0300b04c038018040c2d10b0902c410131950b03200d0568994001ca503404002d40d1030300010480c148000d09a2401d510380304c1520b03150340040c080109a40444925840f01c4446030010b818159801a104402c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 982868812 1250 982867562 982867583
    0xb0603190b152214010e1612051005030c06030f0610030e0a06020418090c05040207020a1a04080610231c03210603121128030e030109 59
    0x14901c00321990780510800c414411407a005030200e429080300705061050540343c4240b07031160014620072100049845011411558108110384d2108400076009900c03c5040801b80b86207a4481c3e45034a01c80c00d520041841542401c1900c41840e81103805058403e00810f428001715090090980e4401c80d0950410304150f00c1d590103222100c09189103810030103444041c0803001c084100150b01c80588502401642da03803820310f26200102c6e50b81c0707250f08032600744084c0c0400302d064400c001c001ea800482e001030341d5201a200145071704115034401d1100e0b00c1c0d00a4912443c41c6c0100140c01116100340179981705680d409900800c200203809201c0c900e001b03c900380d0502800c04144811400c030080c0c0300000440165251418481c0302c01011000a6150f105854002d0510900b1401c0d50500c00003e1250a003550740e07404804881004820400c20184240142c4207010090500c90110782100c0d1589080c010441c082c90703843c0c40300107030041180600a1026410705106002d071035078001c04001c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 982870062 1250 982868812 982868863
    0x160c18180b0402030a0c260312061c140109051203010f1203050c150604060602010e060c0702061e091908150c0910090e06040209060d0e070315090b0603 67
    0x1c1281000740040c1d80601c910584a000a03030004007035000342503a0005d02d14141c16a94590242c070040c00e000414a41060040741c01080c403600499411540446040000030720380d03007008015075600b0310081c0a22100c1d000b501c03811641035000100c0c09018038144e910f01320071401c14080d64842881140f208410145003003041190000ca17400030305100785807031441c005c500c0300724614205080d40d003480981d1142044c02800c0c9440d21900d4010303c4103000038800118094803954581d4002801c1d000489800180340d421507651004607000702c84803005075075841c07a8802c080d49068010031070260090400341420422070441004841c120780815004212481c1038200503c0140e1000c8c0000701c1c1c5403014840600143d45a40c61544040c01c99514201d5861030001140b113003e0b03001c1c11250145204004e03030b6250341c60b640221120f0700b140c9100400e0900038141440e1401500d0380c0301500c7c00c140310300d603c1b010911503005903100c9030281ba06050140c87c1d4800f050303186c030b600c1d030300004c007043c0c1c42403242 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 982871312 1250 982870062 982870073
    0xc0d08041a0405130c120504030f121a040911030a151404080403110315011701061e0b0703020a0c06171e0a09020103090b0a0501171212090102160c1818 67
    0x9001d80007441c00080446c510b14048059820a40c0d0490124661100c021800b6520a1140c023800c41a070109200c0c001000940b44240780c1075010450103141c98450000078042052490b26040d40050111854a800b90030b00080c100028021446864204030140d0708454210a1b46401075405ca1081440e091540d601e180003000124074040c7c0600a2100a00c0341130003000342c2a00815107642c1038600c1e80521a0240d0844810360051070301c061000700e04410498000c0e94420584c0c4001440554031030b450704050b03142008001008018109411000c80c0c12540491074018400e040d810980305d5494040d00a2240c010015009090700420000508111030f03540201c1c815a00604002440954580b2500724805d02107400c2e244294543e001042810811f524030900c803811503014100026296031107607114462052036651000340c43c1c0202c0c0700ea1400394102c440b4480f02252520944060b481e2401852006210b90095100c8101001c0582a01070040d81140280c000e4a884c000001e980c42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 982872562 1250 982871312 982871321
    0x20030901081302030706030509160f15120c021b120c01030203180a12181206020d0209040207050d080a020403030e1002030403021003140c0909040b090c0d08041a040513 74
    0x9202d82d8210000e01c41015071070912440c405050140c1d0042403a244c00c0110794580340d501035161102d03d014400410205485000c54003e07981c10701441c181c0114120421181c41d801c2040d81008940341850605440303400107074404d020b4043c00302d07054400d00003c080080c0407911141010960300076001201040d03120342e009543c403c000d405280c01c503810f4000010715040c03840504591042a4a210042c015000403841c0884c0d8000650b07140303094100f00480304040c0004600902486e008140c1c48180301603078069a5004502904c11034a070340b242e041190340c03440030602c1d540220381c0d98004580c070355070309000b2a01980e806881d100c83c110f00003414484d12400701c230404030450006200100041e51003164481c100c50349683e000c50180031800e541038010f0006002114011001c11207500e15490740c0c0c61143c1d006800c0540000786030307036036422541000710010410341d00c070781010385000400001c180039209a40c06000c0c904200c80d4812607d4030302d44614068207910250701000ea07580003126800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 982873812 1250 982872562 982872571
    0x1109010b090103051b070b01140607021e03102310050f13060b04121a1e1302090720010234060204030c050405060102060f0a0c17010e072003090108 65
    0xc1407185c4120541401c1d01903005420203c942601e8500100416551a2031011020008968842c03410b00b081c0d00007072806510486004070138001e6605100c2d9a0b5041c000c00e940c0b81500304051106401182d01002c06c0c805c806204112026003501103030310b02840744054406c0e1000981400c0c1064030100401980130034450079504200d0b120301000c00c00140b00001303030004145844000855404600e4140c41d0920304421050388845180204061850400f1180311b00f18114079040b8030503100c2c0564030141c10800c41d40a034200300c802c4d05002c445a8041c910b5010350008200179800c0e0164651200c0c01c0c0e102c0c0b06036880550580c4841c0c0c030100503a00025004281019880500780b4166503201000d0760403540c030903500304000c203600300442e04041c09410344c041404d101501c1d891602d054400d03205007025120b0080103558005905119001d00c03400110790074081c01c1c4901395a580e10414212030710459501001405540e4440b002c0b50001c90742006444201002d1401d18400400440744102d0042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 982875062 1250 982873812 982873831
    0x613050f060f240406091a0703030203130605090d020f0106140424030305070b070513030b060111011b0224190609020d090309140d020928091109010b09010305 70
    0x22440014a040f02600e1192a1552981107446901d0800043d00b0150b0740e074071410265040f00b003a42010703003010046500b038a0f80b5050058494942280e5401c62001f85000180590300d80010f00071a80000121600d01000c65402c6503940440703242d000f130a13182d4920038114130b00703a009410f50345450039405c44040488207054282081104507200d414291656000f900440d200140f05414081e101c07005075801070232030510b40d20b0083c0e040910307852030400e480040d00303d0002d0300200700f00342c0c40303421008294165140284110840c0105201c6042805a5540c0c05031017075060000141d1b1400c0c4e503800003400503500c02c4190399030350712082c0d29100b0505842c00c1040d42d2400041550a490310141c102d001424100041d41c01640c50040e26000003500070441c1d440302600c45480550b5109085820301d94180e13600700b142d80316809000c4100c04070240000c00c0380809000f98030445c12592003600d00318003400204070401100d0782400186c840030300aa01e542941048103002c50b50190300301540091606 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 982876312 1250 982875062 982875079
    0x40b1204210c0302100506010804020d0204020c1f0506010801060c0609061b050a021618090204110f070302210d090f0804170601080f0a02100e0907080613050f060f 72
    0x508030510701041e81d000782010550b0b0031001014140c0c10405d20304800454801040719080c03410019105c0a00100001d2007465440641011501d454041c1c07048203c18004850300c1d00d0141c3c20003400000c001c541c40426500d0180042c5007584144030701412a83c840d180c1c4a120011131b19148054030480005480603622815000030342c42c8500503207090041c00da51034944030b8403c03281c02400e0200180340600002c0301541d00b408044846510340102d56020100042c210300b091010401812041e0704150070440041000300000b00e506008122a07882682650042c0511040d400d0403a1504251624004002d11081e05099140d0380314000c3d0074014180024503c42c80d035901c0e001a400742e0080818007450800684a1140c10041d0303501500f03c0d8005002040c00300401325550784011140a882134110044070440c4501402503003030809009030006e0054070346594003908903842601c43c0c0c0e0003001c0c00440c41ca42c01046110300c2d409882c1400101603643c07200b608004038451806404c641c85000d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 982877562 1250 982876312 982876343
    0x60a18020c03190f0906080c07030201060b0a17070f230c06190c020a021513030c090621050c040b06360102030414010302030a0608010c030f0b06040b1204 68
    0x3007014103050824589107440f020a1424000c003c0c07003038140320500340142d88105000c00754001000950100c1c00020b400c1d150340305424101d014100f04c1e400f10034007050005024a286a00c92a030880070960003801007150303103070003404036104584003071510f00042050518611620b02c122200607928040f07998182005448004141071090a13503a4105403117050101001008050154520400c803d001074000b0740460340124180d2400304151824460002450150003450b0882040c055600708403040191612400c003c0002c001c50701440ca4140c0007000000441000001e401d260329a0200103415407440e0714050101920704d806101d07500c01c4003800490500c040300306c00c070600e0230b81c400d5800c41243c0364204011000011024020f04541081109010060030181d00080c01e074020300c0e0060740c035035982d803004000705034a41000b80e442d400c0c00110b00e00780c0c1e419003204942c2a1201000c2145207030309010011301d40b040d0320800c901084280540e9054400c00c1c1045a4410300845454800300407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 982878812 1250 982877562 982877587
    0x1012020402181e0f03070b0904050a06240216030f0605070207090e03040f0501030b01020d0c080409091b060905131a0613060f020102120402060705011e021b0105060a1802 75
    0x14030303c00392034250f15854009002e8038180d490b4015642c41980038000050400280030070920031000424015174075400030070a0500c61ba4040402030081081e140003080300b41300d40c5486074008100d2640103106100c6402103010981c00803908807680150314200300506a0380e04005030200401702c1c0b0030340c000e204002820011a0080c40ba00400c3d41e0044d5980c0d03400c00050414144560304542c1c1058545501820581d070005500d40d80525107041108042d8910b01c0c2407122440b0740c0d001360b004141410a904100610807984c142203408102c8504065a1980303000c942809a5128007603128a555203d52242c0500d6031003001406800107107070800e0541007012503d941e00c0b008403074200114554040011035444560103118821600c001e501c4d2504a26960b0708400010307001030f100703100006200e400c00000350300003041d6a0101e05075500382e00e1003030100c0c4000c0d0868540c104101c002401548001841031180f10b2150a0003480c0c40c041c282010801203580c08203a0740416495420400e160343c122 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 982880062 1250 982878812 982878829
    0x5060f280807030b0c04120f05011b09051008060907050c0a08040b03010e011e06080c0c01060608090f07030b0106030209060d060e040309050d030f0e012d020105101202040218 77
    0x1d103100107100441c03030340c500b151100d00010514a003a000600041c800d11804040b81c401c0e40d070b04950040c4642c03100f820320500420341444403402042400040080081d00060070031b080703e070221400a80801d25807412f8451900445603282d000b41e900001950840c05100940161526041225001c4480e99a0384040381d010750028000e900703011004005441c0341c005400d0161a5800c04c03030310618510300101c02070030018043d400500c07005600180c400d0007448240c0382940d001600070712280d5603425010344926810742d100e003240e002c0e11178524041d03000010400101c84c2c1c05103100d6910b80c6082070031402904000181c0d40d02c02c1d401c1090203c0a0110b010b001c020b018244100d2401741044e00e00584070001c070764000c82c00b548070b20b81100d000ca60441e0051b0501d5500e418942e15484500c8012507002d61942c01c0d0b541c0e160382c101c61107100c886110395031000000ba039030020131054a0b02d28048200001901c510302c40040382c5a9100010f09054010f0980000c6034217100c40c2ca2051b5200045c00315 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 982881312 1250 982880062 982880069
    0xb0f010f020a1703151507020907030b06030f0420012c030d1e09060c030c030905040f02040e060f3616090e010b1209210a030c0305060f28 61
    0x80e001c014880182d94000c09496540c8088420a12042c012508a06c440c081c046001c1e1041e080500001c01e4a1b00a421818840c50018441d6a80b440c02c1107843c0812201914240d0302004080b40600d9103d00340613004070322240584501110000a0610446943d5002800c4540300700508200c00561810481c448451171140c946404a0880352000700301d40a14030020310403c006c4840401c0515003100d254402d40390189020356005030142815261a13865601003134004c7c1c80c024203d41040c100da4050b0060700c1006126600c2c41d251042005001204041d166030302c455031003000c400d11005840501c0300c400d0309102103180d50f401e40032881c1e07a00c00110f403101e15158100b001d0440c243ea204a4080123041d10032101016541010b40c2c101d03140c003c00155000720603064000c03645055007008812044a04245440f40d0325030580e0314551903811058031507000c0303401d00711098611802402000d1041c0009001c26050000100030807084118031443ca000d151160002c010500c072945000c1e9018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 982882562 1250 982881312 982881353
    0x5120303040b09030301030804170c0a060908100e03040b031f120b130308011a0705060405031b06010303050a03050a090209010335030402040b010512010603060e0a0b0f010f020a 78
    0x480c5410b00704040d444400600005450b002040148006134040042d182a0751100c1e064140c0c0e100042503062401203e03c42c4a6400729070b02d58001091a8406c0403c01660250b40c1947c2e81484940d6901059482c0d8010a62194105000a000340d0700010043c546c407a04030815549844c0b140170f14400c2c0e0460a81107520310068441c0d08409100c01000030076080140524a0840e050441d14010032002c810f00440003101d0003e44108141a40c44040d9800e0940050603039816042c545001c03a640e03404000b034600072088031807e80350403003c0030861504a94064135118500088800110010440101a40310403a600d40f0303a10056100d480c601ca000e944140d228400d0f2800e813070f15880c484020f8142c2c210401003c501c0c420a03d200410a498009a0655010a20951040059845008090041040c0c0021100005020390b1580040c02103038102c01c118440c42e12001440e40030b4880c079100c11350700300301c4141a10055502c64445008180b03224415144000b0a90380c894031301c1014418002c52 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 982883812 1250 982882562 982882567
    0x1202190803150f090105120a0203060c0d0e030408030315180906150f01020c060703050f0f030106030c03020c0d0c080904020a12051006020a06091e051e03180402090a051203 76
    0x42c80902020061444074040351040740d0b94185800041c0300b1181402160b008403560000b10300c03458800c1141082481c0c0c000d043d2001c81c40c041d002845150411520710b1005c03400c080d2207003803046000c004c0b02d0a8070b4410f40a036296a541e14410902841c0360003c0c1c90300440854601102e5014158141e4007844005c1c010385010300302030246210030045498a58030601c8001740c2e100d9160b0f0000f80381e9030038080940c0c1c04e5480b8052400c0c151a24000c6c4528056050800214040420030071802581602c480303440400004081c070804034100e018a0b450300030558030060b101c0c000e45028200d290742c1c141c41020f450f480e0280c2c903004101a40c1200c0ea00c0004220302c64902002c1c18410300503998000c50304519400320078a4090000c1d601c000c5944040c2900365901c540105000d070000c9084074203040b449104c0c14105051a002d84d07220305108100d210060021080d00c05420302004171040160740c49910541c0310011002c0000950042c88400d500c840e20400001c0c02d0748841c10f0700884d44c2c8038440510f4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 982885062 1250 982883812 982883821
    0x40c030e0105071d12010e060423070e0c07020d08040f030317040b0c030408070614071d0303031f0302090a02031f03120c03030e070e10080a0f1202190803 68
    0x2800d4582c0a0412400d11880400000c0312441c500244140b6002c22502150070084103c0303000c0c01825035049510075400f0304420482802200500c0c03443d00003044401d04030200700140e0454807070200d8098104460b4600001c5000706c140300c4040c1401d180014140304d900079203a905c0e5035a591003076202070075042c0300e004200241a00140c4903d12068803400108071850a07940e03d000c0420006d013401e00f00385005c008503090050300020345180e158010301c10400d094103c02038846640b03048510b103000030401910201c0d034000c040da540050340c00c041d00850442d141c071040304400c0d0b030113040c0c0801e00e05000203000016940e40c00c003290045505540043ea01d0401d0360070016031036240005440d02c00b0b0440400c1001404031088001c0310701651a104000804901d81200508050f2825411b1403045020104030000079141e05800b54140c80c41d0b0050232980c4006d003d84501498901801a41340c0e1103129001c00c0c2044c0d02500f0111881c03054516078002141d0420300a0309410013961007690210810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 982886312 1250 982885062 982885091
    0x50c1b01090b0910050304080c011a040f02270607150203060f06030103080d0207060b0618010306050d080702300c2b0212010b040f090c0608010f0b0a0509040c03 71
    0x100e001d03040c240c01c464501901d56010484010031213a0300020020000005803d2100800554085003803500003072014040c40400032403007086842180b481646000450b540c039002134422290080c6030100301140d98204030382c2d007a00040b841c01186410802c10468000001e83d40481405031030162200141c0700e08008040c8003900c0707461000c4a020707500c100014804118040150b840f9483c2040340543d4803009881d06001504000b5152034100e40c0c003017182c03000c5992020340d903580e0700000e81c1e04012940e55401005841e8061860252080d46c040103000054202640b0100844a0302498144040c031802c42000003007141c1d21030302015401064400b07090b40f0308000f41040342d260b91003003001025404010f01802054001000303214581c6016100c8116000390048c0c049810300400800400e00c018081724094046170500700e0704e03100d005034081050b40c00b942c4d02505a8000c02c20000519080c100c00c881caa0b070121007071105000c0d080c031403820140d0f9103001d00e400081003543d020a0ba01000070b407a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 982887562 1250 982886312 982886327
    0x5011d100e060d0f111806060a030f0204080f070f090507120b1801120605010801020309030322080d021c1118040b150c07060203070c030f03050c1b01 66
    0x65580812541040c050418010118503003501c0d90580480d940341c403400002080a407035184014424200c030f164a40522441500e2046658801c3c3e8802005260b90f450003460b2802c200c3e51550b1220082c404910885c0c805d601c20813044600e034500520381900c40111307034031f4030625405c0c1403a25888007105001030035500d8052001440b01150521660030400385c05040004183c00b610f42e0555641c00000e550f179103488a8401180b0070300d685d40805d50b110f1b24820305032941400181d4105040100020b1000c405100312482030040b80f000c0c60654480e050340484281a00c20344035011003003040d4450115480c0310042c000701c80c64a00042e920301d01200303d50480c11520303c6014900349000b44040751001401c0c12240640340c0c4d8510001302c00c4d10440001c00400032800b006070417940b508508142c9040c00d40091000c040c00c01d04544403e03584034812a42e910441000a00a4031210005c000144ad40b010116800b8880c0c107216091100d002c2c0002d20f440070019040d407500303602c801801102c0d42c00100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 982888812 1250 982887562 982887599
    0xf0f020d091205030105010818011506080901150b040522020d050a06050418060c03060806040507090b0901060e1c140a020f03070509180c030a110a0b16030c030e130501 74
    0x10f2680c1990302d0180041c0400e03000406144038011510684c412561082d0710503d01c1c3e0a005050650b49600c42174020035056080360820321962030b1880031030027000c5500d00e84007158005c110881c54182814248029440c2c205410700314a51030010f042c0422085002400c6981c4500c000003803a46040d03036040c8191820307648014000c900d44501c042c07851450a07041201c00d0781044003c188448204001c900400300c960008030540104024407003080008038941045a40701070060258030050420404ac44100f84a010003042c9003401c0b0f40000e040c0207400c451b10036081c080740f1307402c031210f40c0303a581d0f90058504640c034140e000761040000314600a10504c0c0e4188050f4000d00a550074980421b030748200c0540701140ba12400ca4807441040000c0001c0c0280c00c03005801c6d24038220040c6060b84201054a2600344620130502c0b01150344400b44003500c04c82000010781f400f0759801507c040e1103011143d14190100304011080a5581d1240568400b0348018008006125071504000110100d03170300c0c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 982890062 1250 982888812 982888817
    0xe09100302010e15130605090901080105160f030908041205120f090d050f19050105090d1706031023090a080301032301112a100f0f020d0912 62
    0x2028000740c1da00040303a030302400054502080c030b0020b6005550301405031280100b030906a411012610342d0b8481c000d0312a030181528007010b1640c80e00940d900381d600440d200c07050840c0000551004d035110b082400e040c0740b058100000d41c0d0306103445000c0359901a410901400e41d00e074201004000007000b201072601000480c082c105250030402e031002d80b0551400c64170410081207107030207028052028814103600e1070202d17074607025800401c0845002000f001d40b030305d500e0280003420142e00072075002c405840d40c0c0c0d40c9016102e480c0180600204019101a4052007480240a021030051040101ca8042800c150020401e1101c0c1070500d2000102040210b4000607150f00014107a01c05880c1503c1d80459481d03140e00e0101000c0c0b0925072456030a486560800c00030340d410040d0740c40100b070881c48801001c8980d14504040510104000c410000143d00101c85941b4410059000700c0740c05581e4100401e061060f603e80009a0704000e50841606981d050030000300021841c804e4040c18290 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 982891312 1250 982890062 982890091
    0xd0c0e03011a01030902040f0c111506030601050d03110a0822050d0807081215120f060f090a050f0c0307120b070e01050702031006080c04060f09020c011107030e09 72
    0x809160241580701c0b201ca9060548640814046503a2078000701c250840104040041442d0030300b004103142c4240803480d0341030107038001c00c3e00d031088484411803140780302400414269180105002e00090306003c29002c0254291008280b03001c01c0c818090030340c2c00ba03c403854031042000c003841540240c0c0407a02d918861410410081c40d1a0001a942e01a07009000d06440f00f41c1400c10500510400c070070301c04440380b0901003000307080401c0e056195080d004d0390981d010480000c581c50f81d411001540000c1c0d83e110b000084d00310008441200d038050000d8060342c094051550b690b03490903000c200d14a2854100c49100a16401e08000100c02445810414513440201e502c07840c101ea0006041101000503224a40a076640541c00b01e4940c04c0d401b42c2210148504a880103004010500441100d4059a03880051130714003400b4201c10740d605100040002d070b01d0501200002d5206044028044d5256203806130b0320400c43c4003806a00d03009488124841e145442001b6007440e00400c2e40d506010702 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 982892562 1250 982891312 982891331
    0xc150409150e011d0c0a030612080304061508100b151c0c090b0406080604150b03040302100e07120f05070305070609050109030b01050402030a0b030d0c0203120307021518030d0c0e0301 81
    0xc1c1300741c190308444201042a5110803103c0104c0107021190011801d1030302400024040000d220011882140921b000704410900302c203680c99088401d100d821041c1c9e2142900c480f0780e4096a101e4030851200404450801e0414140682190071003d841c0d140442940c501c6037808450380a400752120301480d001480c582040707103000841c02a070207440d04101c65440000c1da00c1c0c45aa0012038482000d142c400070b000d0f036500c00300c801680201c40450041c050203501c440301c410740703006410b1800e407001c01500d01c290428801c103180c81d41c40142540e0f0010002408004035600b480300d84080e500980240c441242001c0d4003600400d283d0340b010b410001c2e410010008103030010130741810340e0001c40307000d80d0300d0311142c9491001c1c1c6010801c0c0c6505010701d500a6042c01e070040c01d130710102031082e010f90700c00004035183c40d0350078001160408090303041060340110100d00b44c10941e40c0049010b81e03610010032030102051942d00f12001c01e00c02259145030014040390840c6071481802c004070028401041c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 982893812 1250 982892562 982892609
    0x1140f0306090d050c030c030d0b10020c0901090b010e0402030705071e030f0305191d0c0a1505091305101703030702120c010b060d1d0d020c150409150e01 68
    0x10311a45004c101c40418840d00741941407040714820806842140d88a0800c000d10300010166803918034402c1c90440683c0e00000c0c00070a101121110040c4900d446a10744a540c00180a600001c20b04200900503191882c0d0381c1c40c4040d5004195550350b0f00d480380d013907103400010010610611038012107007912400009901a180708010740c400e10700843d20361240743e6440c103100001c4010394920741c01e040145100c00d240d15500e09061003d80308451a03050f0b1101401940391880c01000741810040740e420005a014500824070740c2c4001e01405c50041c01c0a540305c04450050324031001e0400b02c142d0030040d00d00300750003942d00510380c00c018610b142403140010f50f80f800300c04080800103002050307485400c41d00794041c1d5101c07000500003551301e5041410070301c010300350070843c0003008a051081400d2400d0019011020f0141e81d002059228011130400c600708005000c1c1040021003040049190001d600a0704450441c440740c0070034050401030319070041d00c0160410139522005401d010b02001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 982895062 1250 982893812 982893823
    0x15121d0d051204320a0308011512090507260d050a0f0e0109080a14101b030218120c0f030c03300c0a1101140a2601140f030609 56
    0x1940030b04007000c04008600c4e000c8180340380001d0807850003190800c0229500c0301003030b04801c0078840c5d603c0714803582e00da50340d080038030105d100c0440016006050000d44000954044202c40d070240007221040c9907a01d035400084180111014051801150085990038080005001c013081071706000341030071075503000106181080c040803810070000b41e140b10040d902520522010b005414140c603140e4617242055a8110305ca284100750302e100709001c56070030b403c0032300c6140c01c90798900d85084200361990804034007940100200821a00c800c10324114950b41d83c4072182c880b00e090001411a0000c0f050030041240600d01c2c0c040d00030b40084030260501d54000c07641c5010b80b80c81c81a0103919a0b02d054007007941c40003c200706288883c0010321858504000100e05016901c0707036113504240701147d00110b030713400b0040165094084081c09400c4286008c0c0300405075030502040303582c071001c074400301111064030b003a40300e1205140c9004014245040002070100ca070141078008145500b0144951036840 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 982896312 1250 982895062 982895071
    0x2070f17040b0919031203090b01050901120b1902070b160e0307330206010e131e020d0b01060f11030408120f0d060b041701050f0115121d0d0512 64
    0xa1407940c4004c601e12124003d0400a95005441a8a40203942802030010064444180d400c3d12030784000180f2441c044240e103060710f0403100d40324190041591000d2002c40d0141070a00b03e243c5038000100c0f040c00c4ca03c06090035601441c030000d030b2420014503081003110004404020014501e902042a460000c1c60704d00703d40f0100781c5852444401d142582801452110385e00030052010b055230009540040c2c1241a0342c12503a1241407501c2d0b1078501c0d02040044e810003449001c10100c0000c0c02c4c09410741c001d000c0350001d0000380706880d00b681d603109198826040103012440403024540c110307900034490004001c00c00001c620f000d00348058565a51442507486084141c0028212181d205038030540f40c4840b0030384c0003800303400d49501c5110900d070407501446505200410701600654414050b01e4041c9a0220711403540b41d00b032924500c06442014034000900c40054050801c3c0880c0d44a6074950b45003a0207803c814180810700c2e2402d115013000c080040080c03d00400e42110f20034200243c00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 982897562 1250 982896312 982896319
    0x180914250902031003140c13050f071b030305060114070309060809030a02060402060d0b0a08070e0a051e07030e03130315020301080d270603020c0c01020d0203070605100902070f17040b09 82
    0x100d0103a035203403412140441d4150400c40c04416114248c03000d400c40d500078915122856003c1d500e010089640c40d00d0000c004040d058170058410109002c0d6110640042781807422a04440b00c0442030300042e4400d02d0700f01c0016890f030004201490744141c102c3e40140700c1d007000d1403600c5040c00b002542c031000500003034805c85001a040c0340004240d4003400401401400d04140c007039681a000d616a201841185c001c1d09410001445640300340c0703d40e92160079040d4140c6940381d6041d06e03180700c181000f449078052659400004440c2a81040a02901c00903515201c084504615040004030015412000460300600c010301006402140c2802c10020500d00307c14181155a8031840f5103110186000300074141840204049074150010b04545100404480c0c01c04199401269100107a81100c80143c1003030200d040000e8440d000240c02c000104019454240c54403442c0e422a844400c040750707010f84d040204002c004945103801c101824410549007002d2403c0800d001034860492698030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 982898812 1250 982897562 982897583
    0x70e06060a12061d04030e0604053712030909060b1603021002030a05071d030c120307060c020c010f1106040623010924180914250902031003 62
    0xd40d82055030000b4014900380d00004d80c081181032011001070002d4400364005418a658040716040400132201240c07405403801035050303a0f8540e54010b0703a05800700c0b84840420501c01441e1100c0e0f482004005d891000004001f08420340340281082005a00c08c40d5818203100f020001d00040f03030103135402c000c0000100082c040883c64100c0c20001c0c40c82000c0d80940c170100c24010403540d1544081c0c4502c01a440d23001060310144001c0e514420b910042590642c8040c04092082c100038291103074840683c4104c9007440c01325584c0506490469000b01e00680c48640800020360f800f4007003450303024660070f100e01c0d01c0c0b0700056003d8949000800240030582c039400703501b0b02040b01d16161280d01c1ca80c00000841940c4070b500030f0020b4031003041980d00d00ca030b61042c1010708440c0001d40c1c904840722081d1a4020040b0040301034050409000f05540284003201520302c20001440f40490035402c0b2510380b1081c9440300007160503c4655044061124030510810040e484003c2074001030300d400c421001e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982900062 1250 982898812 982898837
    0x6030c0103271a060103090b1f030f060b18150d0c0b0a0c02030111090306040f1103030706020d1b0806121207030c02031c1b02040207120c0203070e06060a 68
    0x1d403001c000300703a00c0000352079024000d080c4802e4a5202401240f6821125100d0f21a0001101980c1010101030b101080410110f441c01c6014030318410300e00308551604030126502c0d02c3e0078894140b4a28282d4113291510301e00c241d640303804080d84030741d800c0001c0081054141208405000c007180c5c0c03da140500c110542c91000c0c010400138090080c01c455034819561a070700c250040040d42084001c900a6007481c00340303170004001009484a440c4003900400d481e546546480203840c1d00c803003041d01e10451040c20444551801d00090401a01541002d07a0f01e5105034481ca08581c0d101d007450b2161210640341401a6a01c500c0c2181c200e1000c4422160102002e0b20080c2840d0380d16080710800d403000140d41d4101a0400102c00800d4001c9054403442d40c1e0b0914407041e60300b0744a20070307400502c50202d0400e06c01c0480c0c02c5003581c5c50002e0030060401c04c903650341c12000030640fa2203c02143c40241e040702145410402c0d0380c00350201d1482c4070309504241000c1205030140280442c280140701200070b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982901312 1250 982900062 982900091
    0x7290f0408090901090b0a060518090c0d0510031704050a09021b010516021204080d0f0c0209070329010503070509010c050d051c0507020703030e0f090c09030c040506030c0103 77
    0x1a080402d00034519036255a60b1511a001044684545400342c10030302c0c4000351850180050703c0c03020b0741c0884030b00c0e03450301150304110f400c020041908400c500c0a0010b9589032016100d940c1c4100b41d80c5000d551000d0a60605542e040c04401d5081c400d1481000f091066441715641c0d0f01c11a081801c0c007580707511080003042c2ca60703031411490030691340ca02020014189144101001004156001c1e1941d50000300305a4219108a002d005a02c3d031024401e00d40292240c1c00d600e501c01c0040c501031480306180d90009029500c26510440002c0d220320310f20550240981d460507400c503100c2d422100d01300130500003078100d001c0200840103008000c581c040c1d55034008d070503200c4081da021040c0d40010071000c030064480d0b041010200b240c08445851075240031518450140202095001420824a50359003220540c2c0403406450300104960b24408440c0c136000c094501800c01c1c002203d45441030b46c2d051501e4024546000c51146040906006103514040f448603005202864081801104040b84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982902562 1250 982901312 982901317
    0x1021804020322200612060613090612030906050306030c060c030d18060b0306010b0301090c1101020d1d0a02090a1505090a0b0a050105070818131107290f0408 70
    0x50030780c2c07143c01c880f8403040000405040034020501d00e00d4604805502007405001d0042c0c00c07030020700b1000032010810300d1404034050491940800c0350032485a0b16040d400050380e046a01001c860550000308078100740c5c0003509840901703141d29000307046285c0007000030780d101400703001c01e0301500e0005030110f48242d00384100c0741d43c0b00220000b8448a5004115a0070704180c1c01802d90b0345038600180c08451780343c08910241201e001e6098241141d081c010000300400090301000300344500c5030141090395200380040c5c084800300d040006226110880c0500d032840300050b03d241c580e00301c0103103440107946d46c00e5007076001100120700203240c0c8580c00411243d41c9841d00800c0c1c1c040d8500c0100400109540c2141200a40a0301c2071540b05907990010b5519009010000341000f1040c0f0004544ca0003000c50352150b4640100300382c0c0c2000d02c0b004000100c8491903c5e44580d101f0005900e014004075500a030031100d504000000031014048141d0401d41000d4000500441a0000301c3c007441055002e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982903812 1250 982902562 982902601
    0x170f06061e03061c03021002031e160f0f050406110a0c0b071b0312050901031517060115020a170904111b0a031b050a06050f07080108010218040203 65
    0x25100240200704104140380d82040302c0840c400e0407031070020590f0065000d0600c08040d41500140302c6401d10382007201c043d400c0200046c001841034449004242e4002e00441d01911401075058241d00c1c1009004140304d0201314008144002001c0e101e1015034810122400c44005142542821942d050024103049203444003400360061303c00c0100754550391500502007079114440f10010b02d6922243c540289072240320141101c0c2d02500c070381c485a40984001c00606105160005406e0340d40351480b680c0c880e80390001d20a161903e810036850a0040180070f02502c078a40868240d503500d030720029510b404000d00105110080029001840541000e07140300101c02041071041c12040700781755403990403221590480d54082c0c03012174640f0102003588641950135a403a038144542d8032a08400382c1d400700c002152070380700d1a942200401c2c118804c00b03000d1080401c5144c0641800c00b0010040c04d01a0800819a40f040082d40440103900d92a6007481303070113450140c0c90f40d54804c1802d804404901 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982905062 1250 982903812 982903837
    0x10e130305070516050a0602060106020703030e03011415130516030c090e011503061203120b03071e06030605060a021b010311180306011208040b0304052a0f01170f0606 74
    0x51005804040d040c0c1c2134804c1c2c8a056814403003240d51814220381d00c030404e00c64100541c000003410300c0403a01c151403404036800040c00100c4d0b020080611f055140004a42800b50300c51360f081e1200030352818240b20200d400407402e00380000e09009405101440710702c54000241940c0b401d00c41000c40c01582180300403c1e0b100d0b030003011503a4800c0890b102070744240c090000a454640042808241e80501c95082034056450310702c5080c0c903c29010080203141d0600d54103110f02d003800a80300840d19840d01070b0440c000c11a00f1032038906040038080d901c02d0707045203200c0d01c01801840205580040d101e007401e200b2603d0032400341c074460b00582c0105820200301004a20019500d0f00511310303503082e0208000b066044407a1070785c1c1c522000541e44020310005154043c100010000d01c3e0549014542040c011001c4d5030b5120410740000008801400c56161030300510a9401c105240c403000001000301b00f800c15039030201788003d80c180707100703c000d00301180c031400b510100f1840d0b150340090340d140e054940d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982906312 1250 982905062 982905073
    0x181503030206060102100c05091e0307060e0a0506030f13110604081c020f0a08071703040b220206070f050703080a02010e060108010b0d1712040305030105010e0405010e1303050705 79
    0xd0900075201c2c031048400c0d9001d440f6000505204124611400507000c03201da96481c1014181d07401c0040d1140b000030680c41a01000038002041c2ea01440a600141318a89810007054511401e0040c446100ea00046c85001c0c20701c03c100400c2a8a285a544031407016240089140107141c980c803502109000c0541150b4081004a000100001c4030303003420b01601d035003a816140140c0120381d41c4c841940303c0e20440c2c1007241b002c4001500b40019158a80c81a5940300c0e0303842695861400c907402c1201c090f1000d1003510140030f165103542c4003030b1a000c101d540059040c00040d40215202c0d10139444004d200d0f14141e0b10308000e20200740700e4a0040c44c0e02c5066240d440b0940b5a000307003e054400b980103840d00541000048003c014030070210036950282040741010071545a8004103c061046d031000c80c2020003004a00c55200031905104c0c9210b40c40d015129410b00c030004058150142225000d28030f080c005002c414400d03d030311035000c800200c40148940795494101c556005840c401031440c81803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982907562 1250 982906312 982906319
    0x210c0a06180318151119060902090a050f01300606061d09010303031d030c01020301030308130c03060c030b04142208030601050f0c060a0c090801060b03011815 70
    0x440745940c0c6502e0199843d5480c80c2071081d0f07642c1e40f107400740c49618031814101c0000c18000e8000d030703000c24405042c0800c0e20841000a0030043d8400444e41044942c40c0e5109454021490501405600210024010040d5152000c0f24421140f01801036880200c045100100e96100e510102000160482c0c08000382008514154025204078041e00c004201d82032200b041007040c90b150b04c2039802005040c40c5083e4a9610240d00420046042c3c0c0d100071104500300c85241801c00041c24004400000183d403580b440c100200340b488044c1500e81d0411a180700340001c2070300140c0d14402d036908480e000404e14402072094004009001141c0c1d00030b418040c02100000048000500c161426409a41500380c0c400c81c02c01030701d2100030000c2680000b80089245540b00740301030b000c0c5240e450b98044c074040e18120918600300048469901c0b49449220290f00d080d0b114140070b0003012000024054981403102d04c2000303000500445a02c642ca02070720b4490400180c0011046198084512507500d88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982908812 1250 982907562 982907591
    0x40b190806060301180f050f03030414070611030a120b130f060504050c0301140f0409060203061302040506160c0e040506010e06010804170c1606110f210c0a06 70
    0x16118840c0c280c000d04000450303504041c010401c081c2e074404000945c01503650380301c0440034880601680c2a103c0c40a0080c00c00000300300031801180500c0360a0300e0344000020b603e28041c6141c01c003804029032460085164000001030b07810102140c24644101c850300401000101006002c0c1a4000c0c0c0070100c1604007603e583c0117100804842809014454450040c0b06c2034410907114245600c0080004201c0d0401c074144a40c0350300c1008084a01103a0750ba0002819103412510584078298000309000c1c161070280e400405085204005604040c0352400041c1d1038001d001d0081e000c00b45000300042000851050000a481076513030b1400c04d13080c41d040090b510710090213028031200218010500070f602420301684590341c8110b90080703104220701042000c2e0880710340c0c0d64080c800c02c1800140142040646009410035540d03243c000b116010a06182075650304440540d600300502e4124020955204214541d2010b206a655030080300002ca1071300040004c0a40807600d400c000092820 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982910062 1250 982908812 982908859
    0x307210515011b030903120309050d0806100903170f041509031506050a150201020c0f0d021009120810090f0f06051905011404081207140f100b040b 65
    0x303980c0c03000d18048a1103c0640310686000160120380c0b6244200009401c44a03464070050035468045482c40f4143c0c0c55526084110401300081000c3d0410400e9606100d20058100e400520300146001e00c0c64071142d107005401e000da0706c0706000020342406c29001c1c0404840003801d00c03880c1d040384990b41e810010110074060008444a25003a0300c0d4500340e0b2024055001510301c000c6c041c0c0c0c0b0700d52810b92100b00071007c0301030a5007955000e0103c02a5148180416620a10042e015041040001c1002400e15551385244074841d49084884001300d03c02c1c0b89242d80b0060305041c00307812511401c0c10741c3c94070396040e0b00c5004d0103420648454082003190700820254040e0b424180116512141000104400c07188850321030018030f4010000da612070705d8051506030490113803078682615901401d050900b1260394581040000035654200038a08a03ca111110484041d29030000118011a201c021105142c40c5850300e4640d0003106607213540c03000d29901d0005040b103440e545a11110a50310 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982911312 1250 982910062 982910101
    0xc0804170606090c0901030f0b0d0b090106080f0318010509090405010c140403080d0f0609020d060312050a020d141314010e010e060f0c030405121501140603072105 72
    0x40c026107000c180c850a002c04010b0195910022103400c0c1740d0b01d1001140100300e003203210304000341c4440032100319803900061801c2c2d086c061407800ba09454800d0f00326003500d29917800b046456004480c041081400401965405070f403602c41e110900813803038012203484c081d85c40c0b0b095201107a42c05000810505602031050944a5180c102010b0805c500b841d54902a500c80644040004c02058007040c80d1980701c1d1800071805440081d07041c0c0c40c1c40300602260821070050080d80d685800c24003d0110380b00c101525041c3c50f01d0710754540303000c4000c000d40314162482d101e010f01180b140380031503c00c0036000b52484005182d0304582915030740c0d0803440c4607140e445e040300e01182c250501c40946501c544020030041c00c01070403880c90400580e805819035030107000000d0040c04103102c00f2884c0d41e20b00f41074155420840008040c907001482c03002e415441c0680c4154030204985e40141103d85075003080e1390740080c1a0038461240b1401892005003410300e4000d1000f2a8984400c00c00c0303404032004801240c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982912562 1250 982911312 982911359
    0x903030305010b1204150609111e030c120403030e03030a091203050705180102010204080601080a020a08030c0a08030406090f0c090c0305150f01090801020703120b0d031205070c0804 80
    0x40d660b03103070aa681140300d140d40311640c6003104c20010300443d41c0e480e01010703040b4101200051403592221500c044480c01102c24088010000c0c10402403540c8849580980010000d5689507041140c0c400000e4441c0041c448103001030100050103040c001e0340b003522000054030541c0c0e070301d2925165a400070030740d1440c1111078040880b01450098400c2c86441d2103031041c0d86407940791140030000903d85980d840034842c1159003c00001c60024030620055000341086002054803c0300c5104002492801d60800c000f250300034800a42e40100008079507040541000095aa9840d1820442d01805903100c0141c41c0341040f040300010003040e1902041260090541001103982c1c51030210305840c1c2c00c0e0b500f42c198024207803452101c6c0c0342400703981c1070989050510781d15035aa1b401c0200c0c2640c00c00f4105401007000800c0e032501ca18101d0041540110040324040c201c80d145580140c504015642d14407106a034a100046146015503140800d0b00c0c1c010089030346442d600c6508114100200481d0440d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982913669 1107 982912562 982912571
    0x809090c130303081b041e081603081c1b02010b0d02030a080a031b05040801060e0106201002040b07051c140c01020f07300e0d051c09030303 62
    0x9010103081f90143c511143c80c82090100030380d021080c982c12840a103541580b040b0000c1c0b0540342e00c034039280c0c2c1381e2040300c08281c8100305400e903040300c280c644054000000d40000300c41c80c0648842d802400350b26811002e121001424200094169100e21010380015500b540a840001c8051900040c40c054403012540c03a1000f1000340d20100d00c00050510611600b801140c018000c09000500c140d458104001c00122410b44040700c009041d00211030042c10500a21190b040303148000e544490f02da01e2101d400c0d6001c07500888403407042c4105102031f0881d01e4840703040030f84180c450104008032500d40300115444404c018007155802c0200002c1022410054200c0034010000c1c0000c030300045142220b500546403a2444080c2d100040602c100e038031072203c411441040d9550100700c4418030f000c1e40341c035000151503244904035a02c100a101c0c2e102c108402200c0c020b036010300 = true := by decide +kernel

theorem cover : BRFrame.Cov 982733812 982913669 := by
  have h0 := BRFrame.cov_init 982733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982733812 ≤ n) (h2 : n < 982913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
