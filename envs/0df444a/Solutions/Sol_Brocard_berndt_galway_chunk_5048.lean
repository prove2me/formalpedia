-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:34:18.933885+00:00
-- url     : https://prove2.me/submissions/d085cfde-d2fc-4193-a2d0-36074d58f512

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 907733812 ≤ n < 907913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 907735062 1250 907733812 907733831
    0x30c050a0503030f0417030c06071211070c0504150810020a081f260615040c0507050c0f06070c0e0f1302090a0f1509060305010605060310030809061c050901 69
    0x41e101e0040104c1e48052030001d22042101c2c02d0306400c050030717508410003039a150441e1402c1076810108103c3d00c0b003010529021444c2842c2c03080348509181003210280490070081c0340d0b0f4030045030748100d2150f03a02c216102c1c850301449400c1e0f012844028030046007140c0e40c40c007400c24600083d421904040c008a1100000a4072041c110401c21041c0182a80440751144c10306011240010941e0100c1920441d20f00c82036290060410010b4080d0140120000d105406882004181c40700012080c00f0400c0071f2010000280c8000380c480c554503400c13a2010a440b24100c08920140115100a4000a00c0002c000745084051100c203000b0110070101c06510799640006c5c5c28511441c001c0290000c0e50500010305446044e48042c80100720350038007003440c0000c0e0410141d04c0c2d02039008084495a102401c00c10000b00744100c1c001072609036429803c500e030000c0c9424101e642c034031001d4600b8200260100303c6650f41c1c4101c8680015407000c0240340015403c4900091600b01c0e281e00082d0729041769034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 907736312 1250 907735062 907735069
    0x905060f0c04120602030c13080f0d02160e0a1104030b01030c0803040302090a1505190e100506030412090503060c041404480f021005091e1006030c050a05 68
    0x90302503c008440510080f2095603c400096000804640400000740090000740b8001c040000007000c40400030126240e1000c1c446040c00d0a04d2a104150b40c07041410407501d43c0802c001d1000c640c1750800d810019520046640f001d80842d51030301c859a04001004802c010714003c0b0507042c0ca018000503442603031140242c960780c0c82103003c003a5206200b03800148107013919400c030707412104c4080da0100c0760070f80d5000070a2031642292004c440100d214501031040050801409501c03426440c0e00f01600e61401005c503400c1d102c042c0c4083e1034a0291019141014010008000101005000c5039a98074000700071281c1c0d81c1150103208041c0b80c003240d0f09c118924103401118891a07c140e1552052400d00c005003090002e48203c50312103221114845821029000380828004519150a0000e150941000342041d1800783c00b1030041c0c0c135020a11044040009045525402c1c0c1d87d0b0b8003c141da545403115203010501c00e8660452403d042003c000c00c084a40201c040314820380c0d04040c03070350711a401c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 907737562 1250 907736312 907736317
    0x80a0206071112070803130c06030209281703041d0117011e2003180c090f0f0a0b0405040318051804020d020a26060c04051e0102100905060f0c 63
    0x61126100040c0400300214007417100654102d100107015041d00005607a6415020f451a4801c4011030341c04075001307605040401d40220f602c040865000d00c014041c000540702001c03107020320442c000d0f0320b584402600e0300800445019001c024843c401c44074035114444c0c00d4600901070030216807465000d00e000c000050003215944041c620006044032000070105006207643c10004484124140840b07100403603001c021401480d4801c4801d8002c440004860324024015820b42c2c045c480c41002c1040c0058040c19294009202e03c1280709191521811440503055a100c0c0c1540070f4074220600c010150803840040309005121071031340340961744004000126420107080c64070040e00c08002001440d0481c03030503a4980c4010b0145d8591a00c0f0020381c601031884a0041868140b1008100c0019604102050b400051300041500e401d0814000c50741c1a4840704c4496540302032a820904035a00034050416400000780042009803090f0030030f55550041610300e200e0000e191001b10b82540c40030800c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 907738812 1250 907737562 907737583
    0xa031202041404051f1d06030c010503040f0804033503060102190203120a09090609061202120c0907030c0825110a0b1801050603011a0d050a080a02060711 68
    0x10410703042c0103000303010141c6001482140000c40c264144a2510f80d0800c0d058060724144040550b9014041e8413036980b4040500350610035403084000c440680c1c0e00004072540150310805100035802c062400040d6809a80c1000f000403911652024001000d0100101e0234924018501c41c030b40d01001103458035120070703110580181c00810703500c0c242a8400c4510284c003440602182c0c1e400c2c81511107000f10350002c2c2003440005825070003c008040240c019a4098006403a0421103503103801ea40c1c01042c001008000d020307004500314141041014011f001c1003d40142c550b032a1468403080c001d0081c072318100241e021403030002c0841d41c2c071090340d001342c000740b00d110301c00981c1c1201d00c031010741d402c40503800300d0030300340c801c040100c0c00181001c0c0c04580924410080e20b100e084d0248002400e64000412507030180e851b200030048001400000c0e240c1051069522118040b003c0c00d0079801d04062910280c15032100184030045140d0004080b48941c030150345805d100003c001e6100d8560901d111b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 907740062 1250 907738812 907738829
    0x15051003020306161404090b100f09032301091b1205060601211b0314130803070309140c0103061205030a1d1f08011208160f0209090a03120204 63
    0x12000e407441c0f034266404044c0b50400b014040d8603401146100d034050f4101440150712403a51007610708204680107558503c1d81040d04c004031314070301c2c0107103680c0441c80b0160441c0000742c041003c80340304503040f03070300303c85407000034403424505040100101c400c907010a403100c1e42102e40002c0040d245000e4052595105000c3d000d252282001100e002c0d1403a28400303608840c0c0320507000c0003803162060b413140380019090002008030001001d0100c07091486604141030082040182194481c04c00121203680050300580300e44551204400078504010700400c030000321a952022400e00085c03141ca441000d0340c1c20310410391915502440b02c90214401841ca60041c450042d2560040809208141c0e01c18100104074100e0700000e401c204202e03000f8502c95031050040c8410b01c0e88058018003405100d112040e0250050b035404d201840350700d24020f050002411243e04000300d081602c610150010a44001820b101125030340f1880c21250442c0442d215103d5070f551101c0c41d000752011541d824 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 907741312 1250 907740062 907740073
    0x10f140c1c0203072007150503010b090d03091203050706050601050703020d0c061407080a06080f0d030b181602061609120312050c04050910050306042a03150510030203 74
    0x254601c10207074201421030000d00128241c0049003c2040c2c0d12000d0401c00d110040048510700070000701d165803c3c1140c042000700c00c100500c000c0c0c04050850754041425208440c5000140c00c044900c403003941c10000c00c41d00c07040210024190311402500380b040c01110104003a03140c03480103407124820024006e0158100301c8210456600541e140e00c0c1690007500c0110b0b07812021302d001c0016040c111803410100d1000d909202102500341b0440000e40103400051059400702c403480790307841c03825640140c1056128084000e00c1c3d10303080204104184030010450003402c0c00e40c42d10759800012030040005100310000211000b40f42c0b4086040c8076226201e038508541010306203078100c01c03110000d030140160758404100f480b5031403189a205951000300e03a034403281040200640814040e06400f5100340703564041c00309030f40108003d50820750080ca0b205049a00700040074000329900da090042c544074000000a1014603941d94441104145082103590798150780c1d103948207540d010194040c2c2c000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 907742562 1250 907741312 907741357
    0x2040e01050910051c2f0d060e0d030603142b0e130501080c090c12060325050a17150601050f0409060f0f211103010f140c 54
    0x224a081e00004a1022011910340352000304408140040004c0c1da12441c0030800c4e0b040c403142d8846d10100080c1104a529500200b066411180c070344110700c0c5102d5101d0340b450004101c006d40c802c03032130b41e5443e03c03e41d50400c2d0030100240c01408184820b0318090310b5410303580090039011690200243c64a0524103600d2510180d203a5080719169521007441420b440140b26640c502e0301941021090743c0000c6115030401c0303030560600300e1084031940169440310500c51040c5501003583e11150809200c42c3d01a0b607160002480c0901d849499950300b28280342101140120515100580d00191108601e0303d50303403041c0c41d51800d60160940025049207444080d0814080c80303580c3c100c07105140c02402e204060150f42103540c005c0d0311450000c0d40c0d03032000308010700142034201e008202410b6000401d03032402c110060a04080d030603005100000380501c501b040302200031040711714006002040104102404180113240c0b00400f04103512101c0300049105940504541c1c01384000c3d0740f0f450a00c81c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 907743812 1250 907742562 907742569
    0x8070903120516110418031d03150c03040b06010c02011e0513181404030807180e0103050606090105030c1005161403071e0b04020d02030a0b1006090902040e0105 71
    0x5030481c14038204807003003007444440d034600f801c1425541e000e00504401e030030030401040111400840e100a54408414407200826008809850b0307a20036800c100c0d558000d01c40000f401e0164910f5000401554030342489a03050751180176503c154400e80240e00c0c0f9445030801910000036002d0006e000a009503100c00501c00d006c4801c0417250380b41c0c20042c0c1000d0b0400300001a04c0900d40050101e410404400c1000703000501503030340c54406110041b080360070700d620010031087d001040b02050262180500c44d200003445609001044007101c81481d07540c4906d0615110801524498070172b107800d0001082a00d00030811044480f0010600e07038201c452130909641c642c0003400440040305441c2100320200740401108400035280d04042c503950b2401d49441e100c8414164860207a004402c010140000c1a80a6042c0c00c140c0450f2910b4400c8401c0c170019140c17420560700200311a00304401c0c1b181c1c010f0030034012004e80340744e0344407502e401d07031035000b080102d00440c800c180100301110300410040c01d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 907745062 1250 907743812 907743833
    0xc0905130e0111040b070b010b0406080f07050403060f060914010f141c110102060f040b150324012d05040b030a12020c0f09071403090c03070e0103050d08070903 71
    0x807000001048070901c002007900a900f007540070204480000544030100010307240c0160150801040041c100350601c01d00501c000b100510901c1c00352031690204403254003c400b506e0003140e019405000081d041c403940c0026001c2441a8240030341000c40c003512035410060424140c07850b541800d448c040c5080b0101410078143c0c04000e40024074030014421010341e20045004050040501540c0250395600080c50540000c00d280d41c81e0000f1400e0200040000340072070780000041c411264045c03540b0000a00b40120703011506060105000b074445c08290215600d0704a41e4604010320303ea42c1280451140a158000d4102d8817241e4503509001d64500760b448600d042034003404482c60030b05117030b4941c0c4000c03020141020259001600004040c50500c025551200003624005582e00b0003540c00750251a8ac092100c011220210002c0d500ba1001c2000c0144030000800703c500302c03581d80032549070b80c4c0000c2c00180c40c41d01a203017162800c5801440024042c0c5107540d1a10309541c51030711681100e8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 907746312 1250 907745062 907745081
    0x7020f0604033c0e0d080a03050408390115030b0c0405120f100e0a030c08090607111305040f17040e07080604060e16120b030609060a0c090513 63
    0x808503902800d01d0030011203e4400c41501e2142407400201c0550006000d0741003400c5203a101d001d80b020b140700021100800d8800d18030080c00c01040b00d4840c0c0ca4061018041c05009043d292091000b0403510298100d800070070000003014003110f00c06402c01113007602e100d03012060b00b0903801e2038100300280c00241c100342e02c56000c80c211400c1a4958000510480c031392001460240d2041c8034180030b0300401c0c000c00c0803403403400900300400054010728545801c5000c90180031306c18003000380c03014820184100d80c102040100081d0b515026490810035010142c2000c0780915000406850005264070506024a8004c581840300e04020b036202d2504500c044041901500c0c180300009000109110b008d01070300c490b0312140f10f145020400e00040314039aa000d4a5101c181105111000380c042528801600c880e00e80840580144401c440281414000b01c0c1c0e018424001003002100300401c3c2ca038020181c2040034025070030280004c5a00030483d004a603071040c10841480c15824403588041c440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 907747562 1250 907746312 907746347
    0x20a0509070e131d0325020109062007080d08010e0609010e180a0609050f0d0509100c14010506191a1c110c071d04020d081210050907020f060403 64
    0x285611085000e1108000500613a01e0f4000304402ca0301201d42001141c0c11340c1d810003d994601007540009241d4038040c0b19287c148005807603441c0b070a1910760b1100e1099803444040700c0a05545840e040d60316480064070301c0000e2810800401c0c4022207141450050740000c05070030b8641d0904a04a403200400b82400014000c4a4071700b83c000030090140b500442d01440c00019040000e040860a054034282d0303900d166005901c0e001c201641100613180f84402c20768100c5060841100c0c191303246001420041c15158102031010440386054000c50b209250548018001070300300b00c0081d84a102502803041c6c40170000d889514130100190180c584103616050728600080c0030ba000b18203d441000e00e041140c88001101c0010749800c101c1d5000600440e807401003901101207032aa41c0e084041c05c000c1c407960025031180c0601000006440004003156070304641c43c20200080b2504e1105c5100c0d250084014100290b042c40c00030846618043d80040500042d903180d54003100c12440d0144031410 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 907748812 1250 907747562 907747571
    0x302060403080f0d090503030103121701060f0e04050c030a1b270b13030201081006230c0d02060115080402010e0103050c160809120d05070602130e070309020a0509070e13 75
    0x1252081e008103d005d9020700042c650744d50647c10091009082d004c050000e01405418a0043c4141a001c41e03045588600d06283c09800c030351340c1101d00c02071004e40198800d05080c03e1101a256460040d4081c201c1d50f9004c11076071203004010386c0f25034030041d9075002042d000145106001c0c02240d00718000c1c0a11589032490903190030703880e0b00130741150503203a102e408601018011541c11040c03032900810142054840c1c64507140f00100044551086441c084442500c100722900031081610311440030501030b03404201d4843d10080d03a8220074411f04030034810311030505480c0ea024071155805030343c0682d1801d462101000056001c0c1c40c0140c000d80707111008010005803811205420520310780710b0b0300300a80c3d50041d1000c224641c18054000c0c0c501d0741101c41c0d003054558100b0202d070480c0350702c148007503141ca09540049600c1151603100c4018070841d50108061242d060f4403e0200c3c1f4402c903040c0030060b44035014840b001000f1030f58040460181e02c3d038600c20b860021401c1034202d410000106 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 907750062 1250 907748812 907748827
    0x907030317090705120d09060e03030f090d0209070f09050409080a1d1e040f060807050904062d050a05090d12060506071a0a1a041a0d15060f0302060403080f 69
    0x100050002080918170750004100c0f200300550100d0020010811498185440e410040001c3c0d00c0b4400c11312054140c0800003800000303034a994a40c001c45a0300141031081910b4007100262103941013128650009410b4580410986014400c864401f03410403040c5080c83c00b4003900f80c03460680c654404e00110742c00d4410248560f02d621003200501c040b0860403050017225410700c81584d1012240d603ca0500b003550a001080000840404480080780c0600540d1224241302d00103000004101c00000c5440207050404039000d1031048403c81c0484c0100040c1d0340301440d940403207100703941d005010740202d03a0b25403c09100d42142d0b4800032010400203119559680082c6c2564400b19003102c508048101400c80880e0b014046640403054210a101f042d00003000e0440420824041d40d108035a60146140010581442c103a46c041c800341118000180303500300307070048005000c04420b003d4100314000c6000d220071504030089940c050301450405056a441400942100301c020302c5d201428020030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 907751312 1250 907750062 907750069
    0x140d05070201020a0207080109020303070204090c0b07111518060a050d05010e0709060903080a051e07240b03070e041704060e0a050a0e16020c040c02150907030317090705 75
    0x40c021021a000141d692241304800390424689034003064040c1d1410301201d0150700c4c0403007128022a030444000543e60300c41c1c035103803240070820b4000001c0d02c140400c010b010041d0b40416136100c0c04080704d52240350400605000380611071041500031488440c2d0020100781000c4018161711640c9050150805100b241c0307002c01c48009078400020a40a0f80038004260b81248001000d0845490204030701800c0d80c032094418403401c06050304000c0005402912441c0a0490041c280c0440e0116a81e415440c1400e140105c03100051790281a4030400c0d001c54038a403481210404540500907204413407810304898084a0700500558000c02400c07002c020011465004001500003030300c5405110480400740450b60000c0c6d040a1300542442c2e0080c8100070a00290341d40c41020500121903207214042d049003810710411a15401c981040410500f040d000314680200c1c0c1340d943d44e1100d1540d225000c840d91000c0c0c600c0080c020a04d00213204840d204101801c50b072215861084486c41665000070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 907752562 1250 907751312 907751321
    0x30a080402040b27060d05030a0e04290405060319060203270f010501081f0b031c03061a0a0f0c0302070e010f0303020105180706230d0507020607030e030406140d 71
    0x139030344003c0010b0000c40950849400c0d040d000030042c0e504482000069503020355032710585003d017040c441d0414104200d655036030402e0000e041d034402c42900484c01c40c400d2a98009031100e040b40f00e64180307030004440c3c2c100041c45c2c0c43c0c0032500f0907510f106995244c039001c000f5072005d0404606d14049407000a41c80b032a07101c10001290301d40c1d008001410034520600c0c01c481341a0401002d681146002180031080fa50260704030409042d0300190001c00c1c10002842d0001c0c500c903643c2900d4141c5c0751400c4054041e800300b002c50300f00c84100001f00300740d840b01510324816644010003040b010303040c64040a114040c1c0d0078415219004960009407900195001803409030f0181086411004091041582c280581601f140c040c091048489007500382c4c648d00c4080a0242c8010840000c445548424000c0c254400413400c0704d01d51a55081c11400c0c0761302800c0c0441d02100236104440102e081c0307500c02c2c4917480307810303550f88051800c080c1422000c5450005d8907030a0482d1130014420f10221041038441c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 907753812 1250 907752562 907752589
    0x20030108060603060a14150402130f05010e0102010e070b07021206090102030a0c1107090f02091903060e0336042c0d081605070804060c0c0b0c030a080402040b 70
    0x146a03610b0040101481d001c0700800c800052802c1a0720304020f02c0b106000c03260444c40210002e20110048000325000380181003425200d800d25403000030f210b0000041c1c20064840070390b140c0791447e860320016401e0720203081c903160244d40a41000c028407019140645081791001b40301d40c52985d1850061440d0000603202c01a0b941d50000070320124245900c2009260107240c18002c44d403107041184180c45045a10903000b940380c848001c5d206a81c4190b04580e03084100800c802c1c4040160952040303901410f00041310206d10340381000b05607080c00020b450703410924000303244075046003581e000990040040307203200c044500451081140d8441c010701010351020070008030788801109072001500d0180c20300c1912390300f00318090380e80307240e02c090f01592040d000341294000301c0c050542100e140c850204041c0440c0c5000c2004181c150740718050b1052280502380d07024015849040e03180380340c81824a540388075070040040c120a140a410426070241c00104001842c2c603005000c20303103042d82002e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 907755062 1250 907753812 907753829
    0x31806090a120c0f050a03080306011404090c05220506071401090804060e090117030a0c05150403020313060503130b040501090605090a1e03080105360a0f09050709200301 75
    0x220140700644000884d4001401c044451404461442c2c070744800d01d00c07005d400380c0d0403c501240e102014044030800c5030b00410908508014080c2c1c02d0b60001c0c55a085081d02006140020381d01d40001d402003140c0d201601c0c4014545442c000311660b5158030605c92602c101071954a5042240c04a090740010b0802010f00351103041c21055203104111000c0e40c1600512402e41e0401000302c01d00e680007058820301d050030b00300101c08141606107580740002030002a0142c000c000c0c00c00040541c04405010404005500c00d052607844410039135190204071120841c135001d0054400204180e1180da40c2c01500800c00040c00c21916111b280a03600e04480103000d650089900c1810401081c1120701070f040074001100031000300d030740c00400050045c0b046074440e5007500c00040003010b040e02da01c200d0300c0e0316800d00121600c107500c880c0803503a4100d400e10b24180c501850080294428052107102591040180c0810fa0911a5090082c8022000d003815403081d14421511202c500000351702810070ba0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 907756312 1250 907755062 907755083
    0x70605070c0b0313050c150f07050a02031b120106060c0803180a060b1203041a1e12010311030a0b0106030c0e0303070b2a04090b060d050a060611031806090a12 70
    0x6050642c80c0020030151b85001c0e4000745c0e03140071036051701c130300b552102180700e011641c0d07440702810710380e1522207804406545030007618103840c024041921101000031043d10000e80d0034118602e113900302e9686100303441c0400c2401c001540051446401140c1c480c00a11a400c540000700300364901e40304041d20100c0d4881d036515413009281c0b804507000801c6013000c100841c9130604081940c05034401e0882111900d05022901100725880c035072000b06d02c003945601c056240c80507802500d69000080c4410387c0c4910030081040c45609000c80d060000d240c1049030303c14164a0550114000c1007080e00030301c1084424105544103941c28801015031901490720800302c1e050010f2184100080220812080020a204021900100f10581c1c045502072103002901d070814401041180c400c1c46218139070145008100180c090940e48498142c680030b0b40c501c1a8003454964940e5244100451000101d00c00c1c814940c003403034403400828100300040d2802204035600d1800001440071312500f12141040c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 907757562 1250 907756312 907756351
    0x1208131e050a1a16060603051f0b010503270c0310050f06030106030201020709151d1b0a021009050f0109080301150215040803071e0e0f0909070605070c0b03 69
    0x2e0402201030020b00e0381c031405040102c0c8040300548940c46903000642c045070b000c0401e00010f58000d8004613000429128485503915003810f191000f102488a42da00d800ca00b00c11031b5204034180d0384500400c0318410500d403d040041c404050300081c8641d981d20445070002c030345071410b102881040c2011000441c0701d090088000121072001401140260315104c2c0400250307900084220454181c08800601e4810000f00c00c91114115088450186c1900c1c1c030308180e901030081d80c980b1840e40c1038011200e4518110a42a00384a6904a080182d11400f06984c0c640d005501205400f882035085815000010102030b0942c1c900c02d0058400f0500400104041194441800c0b40c404a40c8060a84500a10480d4403610b4020304050007940d40031001440e80c6028000700c842a105070b4842160b050345c1c105000304407501da040f220703000340c0d01480101c1160034595a064000d0303405802030011981028003c8550782c201701d030180c0c0c2c00c0060110005200302060002c5000d40711054844000c0e030f50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 907758812 1250 907757562 907757569
    0x14240c1504020a18180f030e040605090105040b0a080613050601120b0a0b011107031104060605040b04090203071704030e101106010b030a0e01180605010f1208131e05 73
    0xc0024051004180010003005076940160748058480000c01003920f6080c41d0700110080c928602c68040780f440c00b00252007030000c60407107401814801d80d039184126103400c1c00e000540b070729882041d4000680c600144101d203050380180020b17050140440d007070559200c00701e80c58003005850180003004486504c10601206100450141009101640d0100311300e81c0ca4200d070303000040c021680c132940c0e4101c20304942c2c418041c2082c100180c104a603a4241c0fa8285090119841e419547c0308520303107a80010840d000d241034400315201010090704051900703071101c0c06503000a081c20100310300b15195100304140140414041d5006e41e0760040006804428000819220114241808005401081c0200d00010110b055426000d040742d101e440d440b0140b40500015030303402d1010f500b85511144041c603071582000640e40558814440c2c0d99035a000c4915141c103500445001c0c000404110010800c0c401c010511180c9103090001416511014040507843c0d20184000045002404010303030314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 907760062 1250 907758812 907758823
    0x19030602040801052a0711130e010e120f0306030a0c0e0106080a09020f040c0905030111030a062903130c08060f0c13031b0305030f03012c0114240c 65
    0x100103a1521000d9030019480c110600345c03143e8100e02500d0005064081003140081c401c48590040c00c1500380c62600021320001d828103e008200d10361074032000920000700041c20f84050b60090000601c0e00146500004407a4802030225402d8864448028006108945000010100e40441c06015410510002c00c40c0d500600381c0d03004076040990103070151307444034008a41c12008a0b0b00041410b155402520f800546502a07503155182441e1030f1102d141c000c00940c8101c0c507003081003085949400e00081000410109030902d1550580440540c5002c64002d5401080d1300803004c40802c00e554070603082c0c0c815a004010190000c00c02d1100040710700110681254201e16100c0c00c0c001101510032801410b840007901d806006a480203615581190403005950004180c0ea40c901c50080f0f1080e06a07c03c0c400c4100081481144840320060301c00410032040700319500f04a40c0c0d281c01c04182110108032400340c4d1244040d240c0c0c03c1c10a2240304a0721070f030101361035080c0d10388903490030260910 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 907761312 1250 907760062 907760071
    0x70c050c040501060e09060d080a1d0d0515090102040503011b0813050303070f03090606090605011101020a0203031503010f05070201200310053312070e130b1903060204080105 77
    0x60b41010018004241c01c4203046010382010f4035441c103580d5a05001941ca81e1900358042c1a00d00001002001da42d4001c407501c0020040c5039102088901c545d080c000c1040d080d00018000d40c0145043c0b070310344001a06a079030030000b42e01c000741c1426101da001034210340a00c4c001e240250800b44040c0380385034000c0c184a9000c51524090f010110440e01d0341034803884001c0180e0700f04100e01c071401c40001e000b0380c8250380141e00114100034072515614000000c14940c02601e01081d400c1101011841c41402125202444e950245085480310178414640c11060040c0d107034155224005801522942e101762403150106030b00101e41c1c4201810980040016a210034102c040c0403c1042400c0c0000702800c404c40e00182c984130710210311000d0a130110f103601c87c80900c0f80403c451034442010001c4c000703490461440111000182c8849106072074203050400c51a030080d0304400d850407120305503440924580c4002c0c0540c07142030100403000544501d9500116040c0340c3c041401c0c041e0074402d2003210f610 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 907762562 1250 907761312 907761319
    0xb0d15090e100b030a0b01031101020c0d08250213050105010908070302010203071b0b03130b070305160e04020d021204150509030d0213091d0d020610030201180b03070c050c 76
    0x10708444022441d00c600740304012201c40350301c408400a042c1c82c01c00075485680d412010074001540c60b45401e503005801c0c80d009500510130402c01e410700b03103000316100c452207030300c9541c5600d0a101c1c080c0b0b0032201645001d0b00d030b00100903402102d001d030302c6802c0704000c0e094400100140035030410700094241d000d40e0300111400e07888006c00f8070050b600041181c0080d900150102d81b082c246400d114240b51541d00b060994907008030174402200c0c1e50f080e142c06c1c1e0038840c400504842d6a00c1804504403882150201e0130074442941c0110814000c107000913030040040d001500d884943c40c42c4401380da00407209250702c2d2081408100a000b42261b14200706003030008240131604081da540c03540c0f0701524070b400008560000f80e500c1d841607418030050007045060000c1c0400507001507500d00601c0c0b01d8003000e5440c022800f0001800d8804a042449445800c03840041c181c00c603001103404c0c5000032240c841201d00d056020494407c00390180d0b1207050645c1e2141051085482c00318180400881c9036400b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 907763812 1250 907762562 907762571
    0x1f080106050c032514100b04050f13050114070e030708031914070f030512150109090b030c18010303020d02070e150117010e0603071413020703090b0d1509 68
    0x7030004000c011191a16007a0001541d5960f880c3c1d41c0341940800c560b4005e000781c0c224442d50914400100b0f00c8608035100510070401840c0140c00d1000b40c6030200c410902d0800080c0c00200c61030030004030400118000c1000044001013101700002d5800306450010204180f000040614039003003082e1030141c03d40300081c50800c0c0d80a0401125000503000b01004d20100c1c5010b40b0700c801c0070341c0a407640340e41c0242c802000d409842c1400f822a90281034442611007604000401604500c0840e5450b060180d440c801203520340b852a000030130000d200d0301d6050007806c4804001d41d803440002c8919001d0380c3e0150001e5451858080e14000c40441010b0135504980401c02c2059600101c860f8840518802113480030009801280d030b4118070038000c1c880300f10510000c520700d200e000c50030f881104145e08841c4901e40761f5900b039541c0c4500325201c07036110046c25418507041840d5009052a50700c20f08101c942c1680720441214940c22411110080384c0e0340302c200182c401241c1107440700a0485020402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 907765062 1250 907763812 907763827
    0xf011a0d030c031e120506030c090f06011b0c06271203111507020c0414150a24030c0c0206030402041e020f04080c10090e04020604051f08010605 64
    0x12030000e000e0300050144035a11001900b414099003140103060340c0b1342c1801c15030300361300103010342103222500c0a40740261500d40002c10340e0030000fa10b510540c0c80200702007032607502c05443e6410740c40010600c5041181700422604400c02080c5400c1e941ca1160644003403550078650000c0c818003904014840d1507642555488029016402d01003d560004010048a0b9490304040d41c80516107016003000780305104524a03110a0b18400c030740079406960a4485d411142ea042000351200303548102050810000030032200000003071140d05406002d80b140708070342d507291010020480c0c0303041a00e81400c507070406031b0651079040c4151031010391241802170060010742c001c0388982c08010002030040395943e016820031810340411110942c91a5030030356a6101c8105804c1c942d801c10310602000d4807425400d1059450035510300c9140215542c2c4806045140c5403001000e02000b41052760800c00800000c01c1c2511010380360148007280000c80b2503031205440700201000c905a202a040010511441 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 907766312 1250 907765062 907765069
    0x2101030f030311092806030608370803183403061b0306170309011209080406030b0925051e0304140706140702010503090a0b01080f011a 60
    0x8910464051070001010f00c001c0d1400d440511071902d070281e1000c240740d2400c40030704003203045844c0c807082d010b0f01d9075019644903415000d1791380c240a000081c0d003201c100300d5088400c0f11104116804080b40064555001c1c400c1c0720080340200c2d1003500c40d074100004001642c801801407440c0948040000c002d0b00300324119003050030000b000d1007010768018041e80710f00b1200c40c00104e805581c0000040107011011600f41001010303c000500c00b003800c200c40090074010b1050030391100e8440b400036528040c01480119103010a0003c1c0f258406d40d18201100826405006007003e03082d540c8000880c01c211070704206042c0030061480070600f001c81c0c07a00c9240060100d90003100440f034188251a62000c0c2c143c2d80c00c11711014000550018044200014449406040c0c84984204402d5501c46e47d1500f2040719080660b602c502c098082c02c00a034401941b041d001140d104040b001900c403520743c65503400b00012020307070002c1100c0d0300a040c0200303811428411031030681064000d40045402c0300010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 907767562 1250 907766312 907766333
    0x8060c120601030f0e01050a020a0f032a09080d09032a0303110703050604051005011d0105010f05090319030e0423070203090303070803040b0f0420040f090602210103 73
    0x141810162581c01680f04c400c0d46030000d040f10350382c21000740110301c5c04100e14030080d040406044006400c10b07100c614414007038850070100c0390096a090403000c0c2201524208900b541598904003c640c01c400201f011050000000654041d0f0b90b100d4058510b00b400d6452540f03403d6000200743c9003a20400500e00c2d0107200782c1c00c4980c14145280308030f04503c04181410b0710360307002034503901030001004100640480d80d02c02035411641d0801a0384d03200c020708190101940a210702c01801c0e8001071005c1e60081c0710003118014180740041c0341c00721020100e820540c011010a80600086905200b05904625000c010910aa9041041d0040f0011148021111071019a00c1c041804003190341180f0a00894001c40c2010b8220707070303894986180591040d482101d055800c45a100c000c0303038880c252240c0f064081c6811901000200e2403c000c1c08501e0040c04542c942d106e81e0701c40b8403c00d9031015010301c010850140e0b03c01600c0d0310345045151080082e0040380039000c12000010b1002070002c461 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 907768812 1250 907767562 907767571
    0x1409090316030207090903021f0c08040b0919032316110d050d05030103140c011205100503370f200a090b1008041e02060f0c0708060c12 60
    0x1681101d0098074141a814000e0326000300456a08020b021000d00d41c0004080009010244000d80c0d1346421030010310495005c11361103000540850041004100012040d6402044e071001f61102844007a0300e2800b42c2c9000e05084001c01c145988030304503100700c14212040c096200890030310b400780303031804220031820601e0020494900c05140e80481c1d01c481c02180682070b402000c50301048020039010745550400d00c000c0390080c00510300c02945880208440000c880306855002c280e1161801413006010000c2542024000c4114001016501004104c0740c400700c4108541480c41d80011242c03240000d1412003811504103240040002c20042c0c80e40c0c0260b40084144982008803031102449000003520380c2c0e448507030750102203009039156100a8030403078101d464102642c8102010385407480e04490142c0781240c1c003070308000c6034840800d20601442c8028007a0b8940840d880c000b4080750031075181e450060344002410b00c1210420404290004a8010207504008000e010342c81508030040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 907770062 1250 907768812 907768837
    0x50a0b010c03080106050d020c070603151406030c09030307151d070b0306090705161a0a0c0905060c010b09040609060605010519030c4a130509120a03050114090903 72
    0x103070a040c01f4050380c19101d0280400c0c056904143d511203004001d4520b400540d400f0580780c0c10001104030b240c26000d80c1e100b901910650035a5034035404002c664000b6011150580003c00901c4000b422006c10340302c1280308118005010301000c500c3d4100c8185c00320141007564004801031044188180949130300050440d04052180c1d18000220703418001ea02d0745c2d00c0744008015045c0f04004030a2284116000c0228105090b5514607044000b62000340a10b080450103000c002d0005042001c014809040e62800114030000200c000c42da02c00c2049505542d01503a41803500d0400c800c0c4e0240724010482440e00e00d0030b0030002c1840c1100700416841c10b0040c5075540c10100039490043c04c86580d884140c0480407404814013550b80299504192000c0309a0250075901da0700059040d1041c5110300d0140840c448000e01c03080d2400203100180c040350b2240b0681580010111040307000b0440c010045d60041883c0d49450303000b51001014014051140360f0b60300402c1380c4040000285c5500c0306103427 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 907771312 1250 907770062 907770067
    0x40903081b0408060f07031104050f0d0303020f070f02120102090315060406030212030a090621090204022206020f03071a15030d110f12070f111003050a0b010c0308010605 75
    0x1c0c5914400c0e20442e4080d480c640a407208000000f580140780c244603018a40301404501840c00d60642c0078456402515400301c034500300c0460354285418007805861182c1801450194200d110f44883c3d081528201c07481c1d18640784003403c42c240a244101e40e02c00740070003035003022400c0c0001380c1c89a15034000700025842d14000268580d40c1d940020006640140c05030082d034100101c0e4546035400282250085240640c0005c0d14a00c12084103604601890100c0d6024210404a0014000c22807090364041d40900c502d90003100310101d41c00b9a00d60741070038120060b18080c4081e00380b0b000c0e00c10b8102990400d001050104200c4102e0100c40341080394140d1084c0d403408079000030203101c02259609441091040702005800425a81304009400d04440020600c61381c030036640e16016903002c482d030f2424800c020005d0520341800c04602e1050411440d611180004548150490780641001070f88a030300b0701c519260300b44204a0a04d0080c80e201d02d281000d51805484c07958184502810007500 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 907772562 1250 907771312 907771351
    0x90e091c0507020f0d0b01090c020708250603020a051813141b1e0a11010207032a1a0910090c0302121b0d020105040b0d1a04090308 58
    0x1405112100322105444100c14850003000824030341000c0d8049014603c00d40c0400e000786844010140341c1c0390f1001907000e0580c02c0c103040304040c0100703546401c1588510350b004a240441840400c1e00d440c2c0781e001c500d802c4888200c15044846599000100b81441000420340c403581c840d0803101100c17907400d401ca08140d20040490742041d5a0801c0809007480c0c40c5041080100807001a4015a00070701c1260603001780b01d08025491007011812503848a6510741c1704400c0240e907002d0409080c4c0c1d0f051800385010b0094000d030a981c02024100d0001d1204c100b0080e0760700301d001002d0000030810f12020800900b503a184005401004660441b8004110019401c400100194104600652402e10030f4400b1450b02d03070701010460004a00c6000d00c04601c01ca100d00c0064018008001c1c0403d86141c11300c2c440c107101444a0b29041641000780400c004104454004003d0541044900002030703d154142842d4415020413007406101d9401c214044000c29482444c0580106455507c01c405104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 907773812 1250 907772562 907772581
    0x90307170705041509020a1106090d020c04180b0a0203040b010b030721020906070b010503010c08040302031806070f12020d02010216020405060414012301020c15030601031508030a021b01090e 84
    0x6070345c0803103140390000445084a0ba4440e15403000d18404101300c40b071540310b6010380394a6041c01400c80c40164030000070105c252415810600c030a11005250802458458540c1780504000321407096203560000203101c1000711480055006001c03640544c5c3c1075003424079000f00300401e4003409501080d0b4a142c040e280d94941c0c2e040b100008001001389680f040c8600e0080100c02003441003030710a501c0c0030789011070140240e105c41c2c030482e4154007462800e074901200c102c403044907540ea29001002400007000240b0290003268685029241608620741000f000900e0700220801c420b0440e40144208404074104070b080900b440d0341102c010407143c0e580800b0030002e068189560030100d8600000051400120040107004001c0c1218595a180c010005913911200848010740101c1101c4140c07400903c240090342c0c00143c145804116001200c3c17007003101c3d4216030000c41746a0400108814207a03010044d01400005212002401040040003c3c020400c64401e8400e10280c3d50001541070360b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 907775062 1250 907773812 907773851
    0xc120a06121b0b2101120819030f0c080f09150106030b12010f0e061f03140a06060f0503070609080d08180f06060f221802090c09030717070504 63
    0x10100303510130b03101c8500403100c840d10300b064250801400318200000c11705201c0107440c608480d400480300341c07a00c7c040d0115050015454402103080580c0c416108140d140c050180c4600e203551591000030508003d2428590200054060f1540342d2040c4845000c0d0352441c00864115584e6003400103502d010400480c0a07c010342005000303551030f0441c4002c42640c158070200e0a40c04500880d0789079a612036195090000c020100042a400f0120420000f0f8a40d03403085450b01440081d60003410b4180d6405040d40c000c0d41042031203244000d028001410708020040c000c0c0750b02d18082c007800e85015481c644500d6081c910340100203c440000340407055451b030030b180c4145407808580c0d10040818503503468280c1500c002d44502c00c2c03500550080c2c41c20745400e465a000051042c0290820705030000d0040506060442c42850242c513020050303621031801900c2881d00c0030f4000d90f0b45814500b05400c020b4140c015851001c44c1140c0e42c080b040c400541d00b415144141d0f40010b25182c01e40598003100b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 907776312 1250 907775062 907775069
    0xa0e0a0b060a080a0b0403090e0c0403080a1209110306150a03020906064003050d0f12020708030a150e0c0901090f06120b22020711090c120a06121b 65
    0x34880c0e113520108010340304000a104034001c4c1d84110352683c80e00c49042c00c1040030303100c06840440a120070304c0422800320040c10780703e000e401d0408a42c1d90203000c5c841a03e05025003500c41c0c00080381c3c00005410113020142c1c0c8000025101590401e02c440013454030001404007034007030402007002551984400b0300721001d054106200000e8442d8041d000781c040440706200300380801c006100303809000d200500c10016aa80900905801e04902c50120760316003010b17658800b0481c91801c0b1070340e151001d03c003c00c4034074007072041c0039a0f91810380e0780c810954110070303440d0a5250450b001080b01c514141c520903088100303420060760300e40c1080b0040f18605107540003009401ca032510300142c0c1c29000342c0b0707100c1c6403503000c80c00340320001c1014200b206c1018022421510078400306100303001c40c01d80758010300c0078521030212901c0c400504804185068421241c8004003100040c6001c1c4d506003014180364407001280060001c5400d10740291004030b00840c0c003c00d03a428100003006080400d014203c0079 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 907777562 1250 907776312 907776329
    0x906010f120b131404060b010804121d121b060903210c061e130b0109020d0612030306062a08030c1b33010b1c020d0203010e0a0e0a0b060a 61
    0x12513103500c00c03100c00c0d01d01505d088542c2c5141c100b079005194020800c00b44604d800c1025807090240009003a6600210300c3ca4401c55401958108401c50ba0b0700354014020385400340040008151b807003540707100d1503041510a40305040510814906580005903489208a0041c0200300070440e60803980f5a406400c9200742e281c014a070412900039544200510907041a88081c1659155210141d0306840090405000c3c041c02c000148500049600203102e4029200700002e034180c1d88908044032000d06950440002c0e0303c0312003c0000b40e521062412809052070b18100b201041c010128400041d00d50008017512804800594074440200c2580c15101510064140c0121145007503615550403503211a0410300c0008108400e940700306141003610051608000140d080070220007094100011140b514080702c196030185404500142050480604026071203505040405c0c54011004180b0380010f4a004000440c0d140e00050700c1c0b28060300424052002d85815010031541021908003400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 907778812 1250 907777562 907777571
    0x60f070c031406040b06010c0f02040e1e010c1107060e0409080904020c2508071701111201140411090927035410030b0906010f120b13 59
    0x1000b035000c42c280744500e00c503050f0a41300e6515100151409480f001e00644a00142088400141800d030701a2450340d20320011561071204080c84030b4032904105084030a2651103c0002c010ac9400c07901c4c00f10b01c189220301400320617041490040c6203c00c4000900d110700c0d01e5101020a2081c081c0c111089600301038002d41d80c0c0e401c80301c815661206108240e079500c026144c0748041064081c405601034510b0170014007040f9241070134070068410071080c40d81282d5030340c0c4050403070841e25500400310400081d881410641c075095180c007829440f554054080c0b802c2c2840d0314400321b034000403503401a00440308a44161030305510703007410f5500000f40d0001c206903440550003046000001d400d00c2404811945510051b00d16112100540c4000c00500098015a034000c40114002c0540b070034449039030443c13124940200003914400d049400100480c3d80d030301043c0040c1c101000c41c117500202c04c3c2015800e0f050041c00080c1800c66084074021210754800c000032181e03459001400804070441410f01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 907780062 1250 907778812 907778843
    0x2040b040608160302041a030a0213030c03110907121503020913061503021c110312030105030607080c030c0901031e292d030a08030106090501050405060f070c03 71
    0x2001414191000c403c000720244280c5102c0d442402254143c50180001c5c0800d040714001d01042130300080c1000d40403030b07020701004c00c400d000c0c02281c2c00118015681d00c41054a10308100e100f801c50f8020040c00b481c411000c0040301904290800384601611000040c02c0f01c5000d0141e11050701e680000394403132811018005040e0240100a40c4240208030402c00c0c0301000c4450000c1e80e0081c0f20084d0400146421041070184100c00500071038024034811412030340010009080c00800b11420b540700700c011005000c00d0404010309540407245040201c41e07820280c4c075400a900000b80707100394041001681e0b0490303900c260003204d489207a20348842c2210211021480240040f08050f13420300c41800e82c05c0203402c1031408000881c55000e8004850502d002401c01049540307451209450f00b9100743c06101034500300305a00f4018083c4090319200c4d41400e000901440b19a0701c01d074100701c42440148901d80c0c5080440751b20000e0741040f2507840800b450a103140c058a0361002d80040c0c04880d060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 907781312 1250 907780062 907780067
    0x3030e2107080d020a150c1701060305011406130b0903030c100911010516030c080c100b031614090406060b070501060602010b011b060e1c09090c0c0317060402040b0406 74
    0x4003902c00100984000205a0b0f60032a034a01c1c0c0100d014211082ea00e0007080c1d40300c4a0351040e030700c046103840e10310030312144010103d511100a0744481c002a6070340c80104140510484190001c01003103801524000f041c1209070003c80c0c19009101200c400010002c110340d404204881444030100705842c020090f20406200504500d00213a0f080b40b04c16034001c03c0c5601c254200c2d0b00c075012010348035001c40c03100e8904a507068100c0c68100c6501d20b0801c001041008200f08995605941e4200440c2c0400c00400745410440d1041d035110200c0c4052409106005098404001c0030009030741080080e550790034404064440c940c00300a800340c2c0065004244001074105000760f914980080c0304004e246001160003000350440c04990740c4c000290304000a055800151120204ca401c8864110810480000703858030303802602d0100d035241c502000740f9189400340400c018035904080704000e074603803805001040000f2504503041038100000f034050b503650307068801420ba040c0707000b500d80c0d8070751002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 907782562 1250 907781312 907781323
    0x910110706020607021e1005091e06090c01080a020d18030305090607050319090803070522080607080a091505040b15101809050c070b010605120103030e21 68
    0x842550251aa01040703031800000c103e40200e4440e4010000c00d000c0e00541503a1070481d0350080c420f03000c2d40d405060444024007506007d4070164000e01154050f090404000341403a20b074002c5107400c01400c01100040104003900c165900303082c40000c0e036a5100e844002445900400a00d41f441c00308281096a40c0000b40d55040e403203030300c00b00708507110034075040c1d650202110040c0000c3c00800c0094070300003018148400e004c1c0300380d07400f094048007030382c1b2030a480d001183c1010021380c0c08601280c01c4462005030b01a00d0941041130380105040481e02034a58078001d020b032003403000391001f050408490b9400b81c900d40703030001c1d944280212146400c2d809403005480a80d103411140004c186a041c6c5064041001607000308824110030580409403100000c604070b8103000300d1580d60001e40601e003401003071720503207001c1740484e540d00103498030048140c8107810607010004c0920801c8402242c0c2843c2d40c0c15070b50581019015021250000754207022038034608100501803400aa0071048001036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 907783812 1250 907782562 907782587
    0xc081509060708010e0117100606030b0a1d0105040e030d062714040303050c12011403010c0813110409140706020f0a0515060409020a031b050a030b0406050c0910 71
    0x380d96441c2c454003001c4541c103200303004c4c0503460364080004210390203020307000240401c13004040c1c600110780007443d1130480d001c5900410209813a0364005190f894822032542c040c00140702280c0b409940c1b154440c0203040305018403401a0380c0c1c0c9140c201c04032000c10540c0c0d144a003104040c4220341c2c0720203562003060580d82020824424030f46420540c50b140d8000c81da001001002c0105085e920340d107040f005800043c1c0349188004040002407142140e0244450107810b40c04408000400b800c000c0c503003140c2124082e034040001c420b0a000108405002e0510b64940044031210340300402c10004008103000ca20040220707607042d0782054000000f01c0c1240460703240741c0a98813803c224440d6240c0300c400b1140014810740040a0701040708643e640c46580188024000050410b601d0f804a40a00c3c401e400c190b40c96840c81226040303503400c007a0200045c01c01030360704400c10362650350382004201014000901c0786854034000380028040b10281e50071141c0c02044410100840d070340141a00c050302c0c0c0d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 907785062 1250 907783812 907783831
    0xe0702030c030d24060225170609070b0a08160306050603040609020a06030b010507080315121c0905010f0c170418051608040b07050c010908040510090303090504090c0815 75
    0x3046040c2444c03495604c10101d4a10780c01400c001d60707400780050302003012820812800080c2090219004803100001c810b02000300d402401c07035050024001d40f0b09000c580c006095560704200c1e600c103050740100c00c25040307810300584030002c0480441c154050b01468002c01c1e005100841000248601d50b00014983c0d4001daa41e407401702c0d02c1c3c03102107083c4c40000f040540400c408006800000321800010341e0322004401c1c51080c8003100070005410450300c0561128641c1c440c10b11401004079400c0318215984a904215a04a02c0e0000103080080081144002d01110009000c103001e11144104a05210007002e241e5032a16034900745202617103103600344242c0d8541030004015040c04415402d0341e540a0702d860f51155241e603114151070500601d16002c04c4030500407945500024080c03011060b103d840f40c10345981c289018000c0c3c88020302000410010103000c1040404d422005507003c0c0c0d40c0079900030a019041d03003060105407039194444640c611882030107000622522455900408165 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 907786312 1250 907785062 907785101
    0xc0a0f020114011206090f060213141804060b0a0312020f0a0807020402130b030a061d0712110403021f141201060e010c020d0605010810060308040e0702030c030d 71
    0x6801282210441c901e50a40c03028020018040300030310180111050b842810003162241040d030b185000d070158172900b1907030b03683c0200380c81908009005212014203050003400e20418100c400040c6001d01c2003000005040c005c602150620006400000c82c070a0050702c5e01210642d0f92804c068004640c9079800014011050040804034012564011903a000350070f0300d0070701c2200d0b02044000e6000d04460030b401c44541d0000600c4007100c00285205400300382000592500d03010b4094010002d442a03901131301c9481c010043c00b2500035101504d0340038600000940c60307600e140510310a1240c0d4001070b50141070302c0540c1140c508208024020400b051340c4150790150000000012409551103c0c22843d0030b0b1001404850301c40e280d12420104149401004130b4415008211803c5132a9030035218580c9900c0144040f0704100039402d820400b000b01080110300d59101c0544600550086410030f020740300128032601d2081003904d421080400c1940d0742c4120038020b500044c0040c007021185510030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 907787562 1250 907786312 907786337
    0x804120f060f0c02330103060b041a091f05060706150f0305070b0a03090b0c07051c23040e3d050103020310080609072103090b0d060b030c0a 62
    0x1d015541e08407500f0340082007025141c0000c40f4103241c9180031720002c0c40c004e106071080040340900c400d00850240100003899100c102c00d00055550300741c000d403050404c102e941b08458484202c0558005084c2c0314400800700003040c0444020401c4c1e01055004201107084000d10110b94415131815641c030408403019070b51501013030300d640801c2c8030207462034000c0c003010848500000020900d00b004c525001030141c042f80e5505407400c0081d603403002500004125841008410064a1310740350602140000150700d03508001d000900c1c151340d9107141c98159400344003e00c0e280040d40c000c1c1c50484000072203840c00d1034201d52030b403c2e041200480315416414042501c610003005100100c01c505003c05210306080040d00654805080c8803003034868040c00060b60b501c20720040e8041e2502002428149140596034034020a07548450200180d001c4d84c40c0c4006500170001d442200c0b109481c26486611080b1908024201a0f000d1000c0f201c0000811501745031030b0005007000400d81d210302040518 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 907788812 1250 907787562 907787591
    0xb090d02280b150a0609080d0e0a15030b03030d090507122003100615020c040b06040524070c05100816141e0306040b0303130608040804120f06 63
    0x28000c01d16860003403900070001c1030010b030b0b4041c0d2120000031800003002c00c060101d401003e903903102e4400181415014804850180950340d000302203807a00034000d4003018000b51000c140ca01c80c20f03258000c183c0764844201d01980207400791b504000d00303a0b502c030401d00000d4805442950000c550501400d10045441803a01d0400c1240c0c0d0f8012a10300d200ca9002640640404145088551305207d03075100050241d0352070148102401d54020501804040c0e01800b038031700351000c1c0825200d141003040000041d01d4400554003101c108894900329074100d508090ba99003c146160502614002160f8051000c2042840c040f140c0070348032062034000414084404504c00c1c0d80c916040124007038513005041c411880040ca8904030580f0628040b803150081841c0c4041c0382044042942c0401004503518183c0300f01c5580782c034141c02441c501000089800340702a19030141d0814846a40040340034854000c5c1501c025001d800c080e02440c00c0740e81060030b1100b91110040b1405030410300c0030200e148 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 907790062 1250 907788812 907788853
    0xc0a090506040e0a1e0609141c020a080f0a0c1e1511030703090c23040e010207051f140910051510110a1a04050f071404180b090d02 58
    0x1600041c403480c1581000c0c40303c128880d1862000c6d6101c0c3e8850340d10801144540c0000081c004226009195001e1020023400d21551000d19031825500803400b8a07010a400d8408c40d90317070401c00d1760070a645007003202d400d4801541224000d0402d051840040f0700b400b0710320b594074101da0f01030b030150303a1160301c03507142401a2117602035561107881003400800e6038540a40c101a404602c40c07041084040e0b2582c80003034425415464260006800b005007040c20b041510074451f100c140e9034001d501d040256158903540c2e6190344268006184c141641c0810780115a03c801c40740038403059510f84500709101c4aa85d501c0524044400d03807440c100200b46c10031020b481b00074410101034182020010700c0401610868604407203290359004181c1407800150160410380e50301c0700c007101030071414109030902c207140c00c551254440300c550000405119558546004c1454190100e0b404201c0e004000010480f0501098005165041510500180c5400455800c2c103540700350b401c80d41104001a4058400c8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 907791312 1250 907790062 907790083
    0x30203270607080a0c051212100b030f101a0c0105070c0c0501032403030206040c120305040e06010210090c170604081206180103030203070611120a0b01020c0a090506040e 75
    0x2034080040c40e00003038090026280724002030a05c500040040c1e00d6540c03d012607110034802c880400a07040241240002889801c049c0c02d2a1000842e42000c0d08a0b0581c80050311440300d0b4030000000031040d40e0340468900250034001c41070594180a2a00007402e03811501d00d070b40d2030f5404c140004250f10310510b00707948010740203103030380301014503050040d0014443c0d07502c000070ba40001886174003441000c80802005510036401440303d45001c2c00c1c05001840c0030380091441d000c01c900a0310104c0e41c40400d59040c0c6a140c42d40203119100d0f600103030328011f8500341c0c00d56002e003089103410502030f00007040812a080c030082c842034407000100480d21000211070080c1141001e00c44280c403891480061980040d002d050845270000c1c0019217112a07800340d2084005074000a10103003040070301c4c091b242e081d10070000c000f41840807032a035183c00140d00900030800742c2e039251000710b07540c0e208220002d440880030304034000f0943c80e080314034040c02c0201c03203880c081c0c1d080185801c0302110010710140103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 907792562 1250 907791312 907791319
    0x23010806010f0806030a0209240915012a0c0602010c0e030709020906070f050c01030b04020c0c0f040f020a230915070c0b120901052206020d0e0a03020327 68
    0x41d04030310101580e00f0440549041e405210725800700006032144414103010303082e107042622448001c079000c40c0c2c0fa40c0344c44d002940540c40d10b07028001321080d001d00040c280b40007428400040460907500300da80072030300000c59006450300607540702440300d030442100649022340d00a200c40600c4150580305002c20070000d6030140d014600422991080794054a441040240640d04d80b010a4844068800030317920240c0d00342d00301c10801d559a42e011700c07840400600c15101941015025444035440d0369103180400d0140800d2029000c00d075a659025101349520200210b4a544202070000c00c4c0a142c1030141f80d06445000a28401644d4442512402c5100901c6142842c2d036850f03040455803c27a004c104c0f22466000d0340420055981406800115841d0703060281e2031070210301c000e00b55800a409900e01c1d14407060811180804c0004a007a2960404400b6070760f6001d00010700020300000680c003d1a0081c85030704802c00d54003100500101149489656052080c140543d903045c8174402e09170390 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 907793812 1250 907792562 907792577
    0x1150b0c191a0705090607030809070305033103020d0f02010309060c20010212061014070807150605130e2a030610081c110a260f0a030b15042301080601 67
    0x2900c42c0140c1c0ba401032140c000e4a05030cc1c2e032170f03a451303107150082c0791250100300d0348040718800c40926480410740c014402443c100d02c149541c010a02c3e40c442c5030380c05405010350060b80d50035a4001d4000d80e01d0581c0c011001c001d0b0035074100004200c0e144030341d2088403a42020403040c402c24814001e607076000a0ba10301c0c004540c0c17200420402c140300344580c2e51040c807a00c4282522001400009014580e0058000300d584808603c0c4c02c0c1208079800c06c5080c240e925044040c4820f485800141501840c4d28100192514040d910795160407200d84070035a4003002c4d83d8060382e1161040e921407000d0342d0203404968894460a40103c8003ca0b14000c0c12402c1d8040031404098052502c11030441d15200d0421448040c034100140e410b0150424080e0780119203555407458510903415040c5021000780000ca08010300303004040410b00c00c000c0c2540c1010b4030f0303110390003140d5500310701d0804c510302060903103a98580d00c02c5916103410158130315104203046c65011b202c25500400000b072049405075140305 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 907795062 1250 907793812 907793827
    0xc0706030b0d061e0f150b090a1a09090f011d190c0c05120a09030609050c06030405010b010e01030b010c0b07051917070201150b0c191a07050906 64
    0x30020032480641551204180c21190301140301c0d4481c1107240e12144121803070b503500c250b4080c401d030741402c176003030811720b03e0680c8001c04000400b61100c180c64882d459540d170354071010002104a04190049689025840940ba001444442c02820b15503c10ba454900596800030710428280007442903e905000e0390b43d24040c2c41100c02c05680d488a0005020204000101001c000320782c00b0600d1140810240300500050040400c298891074508426086c6401c0000030001d040c4034003444010106500c1751049400c0100034082e4900740f11014082039202d150604219000e480c0000740c280c0400c980b4184004030f94402d0041d800c1e00e907410b840b400e0304104580d031240c445400042c01e40c0204001480b0a2144500c2c04000d44e08500380741c0e8500190030038060b84601d480a0141c85501036a1400681d00c01e240994050302c82191044040e2036128101102c5035030908480045c028000d002d80d0143c00304001032010101c000503982c000000301c0d5902e198080d00c05110b02e11106501800912014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 907796312 1250 907795062 907795067
    0x31e020409230c0715020c0f0c04020309100506040e011b08060603010302090f060103060302190306451a0a05090c061b01200a020d1e0c08090a1e08030c0706 69
    0x100b210900c00d056111704445001401801c80c2c0020f49081c005421401d001901c007481040a15150f1030102e0742145907090810100350340f00740798074008080700d4803007001992036030703407076000d040036440c480000c0c0842c4100040d05a60517034215100c4000c607009078089601e07400c040060781c3c1039a034060a26405510303500034244076194000d040074100350b16240080010780700c030b29440f91090130406d02104070700d085280143c00e80e00360150400364001c411014055a0100c00801c101c400b14a201d03150b02000c6031100c41c5800380c420346c2d0242001d4058003140c0422420b105201b4480c14130b0110800c815191080b02d5511003000520303155000d2401c3c0a00184450300c10800051241c044000180c511101441c214582110881c168110180071400f1015907805100644450000e4608107281c1041e0000c0c814070800c144801c3e00c10040c00c1c4c2c8c0c80f5410070440104461205100604c5294400d5a40e0087e6103100c09000c81071000101c00d4800107046c01e000802c1d580b0041d071744409400001c2c20000f04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 907797562 1250 907796312 907796317
    0x2060703090f021003050a0c03021201030b060105070503131502010e0c121609050403110d0918020903010e01061a122418090714030616031e020409230c 67
    0x1618100760480d0b50000682d11554000e500300d0060310085100d24180116030304480c00610b50001341070041051a1001c22124000c5d03054a81c0301601072000d84030380004031080c0c0100700c002085448006480158000c00d01049801c407042c0b41d040045514020b00100e00344c854000500d000d990200d000c0041d103103002040340e1940a001d80844000b0144048021203050240e44407041c5103a4070401d000a00d68010403480e03801c0c4c50070000f00f25a4115030b900600b1940701d4415000500c11303604142141c90740030f8041b520b4412008000340425208003031610b0003842d1511507159141c1441100804503140a000d803400303076004d4880f0f120b082e80c8030468407850080d6150110f94500300ea0b415000c841d910070300452041d00d00164001890b182c1404003903c0c0030026040810312540b101f03100840c81e54006283c640c041c0405c1c0c0b07040f07082c0c5600318056000d058820b0100040074a8014944a00d0130a90b001c0e0088418140060018550b181c200100d8101580c0e05448240070759000201c1c1004440d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 907798812 1250 907797562 907797581
    0xc0d080d051f0b09091315050a1b080601080901110403150b102a0816050f0d020102072001022505180702010b030f0c10110601080606010f030c02060703 67
    0xd5810105041c0c2d810030301c0780c160081040f002020560700300318102003840d2640060408441e051950b1540c44401458041c01e10149140380c4510000d06144c060350003e201080039610000118211980c01074100c00301298003d0000e04084001b800c81030050181a0415030f040b85103518107811600c0e000d5080c0403954a82d51040e807076420031030564a03071000300f4440403071a0342c8200180702c259050700c001c40032020076101d090905100090100e00c1c0a0116405800f03903420302924008145401401c003001c03d13030b184007640200c0881c101155010340040c00f0341d5205400c599424182c0e5002c094911015107401c90048c1c1c000b00d1111000d000c1548a10100d82d000f00e40d20f45500d540348001500e2000c00005041e251000b0414800d049409000b04040b0140c2140a0200c9110030b0381216550140081034902c00d00790b07001c1819002d40510300c030100701c0c44841e060350455a181c0c0010f541d60441503d099000905920b00558032500c2440742ca40b0440b03486c1e0107813006840306642100a06008031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 907800062 1250 907798812 907798831
    0x1080606012a17040b04050a06180603180203010507080703150803070b100e15120c0d060c1b0c0609270c03022101030213110702060c0312040c080c0d080d05 69
    0x35008103400700c0f000302600c002c08086400c5a503480c00e000070b00038904401e500840911010108410700d86090b0180401522100c0c58000b800c509540c01d1074405e03420030000650554640414000040d074410301d6207104a000d510107001031a8000b46a06800a0a100b4074000da0003d101c03101c006071079200500e4100720400c8034000101c6d2121005c8100b50000d84818401c100410015501d5041000d0700d40400c40c100c2026011050203103000c560242d04004000345515601c40b00c098105000d03400c0341d401d04400100b07003409a805481c19074981e51440c00f0b140086804074000044c00103219841401b02c0a00c0c0c0d2110440c280e08200303c001514074810110181030f001d0144d90344022222840c1141c0c00b450350340c80c040d075500d940103010507840c0d4450302c00d801c0742c00c01c000100744116110442c0c01d0240d0507149617541d0014003080358114099091000d00350035103482848107105540f100d080943d9014000e541c40c0400160810101d0066602d004001c20401c3c805000e051945502c96039002d81041c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 907801312 1250 907800062 907800083
    0x207030b060d0c06021606030b01020307150e010903110c060403051905070312031d0c01050a0c060605060c0d03060801141302120d02071a0405030303060d171201080606012a 76
    0x15515884150426045100180d0014000444040c42241b181c001454681030420201c6c2c3c03a400000e45a01c110280136102040340d000035400042c0790303804032841c003c3d500c00800c5507080615000b400c01c1041e01411105104500c2c60b1a0740d803401204880c11a0792000c014890f84023810a0f00c0d01d100303400d201c2980e650207101400808201c090001014030700903550300103185484420f1046101024900200440e80440c1d540031059800004545e0380d98002d090641d901066468042c0103231000d500419040080400c4407015810000b4101c0c0131404107031400e000407034031200b0311400c0303c010403650340b400103019002c54540d03440141d001258600261a03450905804404540b03040c424010380c50059100041c01c00291098150305403452980c0c030b04032460103103030100281e5079010290169119210104520381000a049103c3c1404d4101c4680e26407103400094600055881c24894281c440c0241030001c8c08542c800c0c496500d01940c1c1013028100ca0032207000c0340c1c2d404071220030100e0360030091 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 907802562 1250 907801312 907801339
    0x5064014010b060d0903080901150902250c0509090a020d020907020a0b07020706030b031507050c07030f0506010f050405042d0203061312090b09011d040c03090b0105100207030b06 79
    0x210f0b801032810103060f20000c2900d410600c0c0c02009101d0081004a82d80d140814908040d040f5030420001c444000c1405a114865030b0314012180340041d454561451001d00300004202c24280070078121003045030644000c4e6183d4144c9900c40d4094403000350702228220f424001403400ca0a0180c0004d072501c101c1d510054696101005844103840360381c00369014140c108005685400f654054480075406000c59045001409007030001c090805800d0007800b150750a1450b41c104004d400841c0c10501d003401e0042c3c241010350310340c01c0a000340d1000f98020100480c0341d0805000da903003e15888614403c200c5100d642d45400300d0100c1817030102d07200f0340b0b81c41600560340030400140a103d9501280c0b12050f91441c02c11540c0c0e01200028040c030050300e0b000c000c002d8100e0140d5103080c0080c04d01184030300015030720070a000407110121f03902034074080da800380700d541c16070268200500c01c0c40070f500e43e030340ca030380030001c046400314107040050307200c0c10051002500b0031014070382002c1c0103012100007404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 907803812 1250 907802562 907802569
    0x20405040903080a0506060a0c0602031e040818041e0b0103110409020c06060102010b0319030507020612071d060403030e040603140d080c0a140306030a05064014010b 73
    0x1580c20350000f0026820b0004000d0f60b48075840c0c0001044600302c0c50241a40000341c09051900400303072170294040005802c103001030754071009003a6810201d6045243c02d00d040716642e0041030600d0300b0891b6400d04803c003801e084c0b14582c1406609056030301c82000c0071507154041c00c0900603440c109600c0c1d840d820101c82c04e60000d00060444643d02613200c01c0e14150030751802e41c00134489411a81004107040040c1c074040f0b252600448400110b48081545082c00c0d50f0a10031090002c2d002000010211981c09040d40020b0084040e039440c44100032104c4440100d81c11a80401030b8090005c002c20000240174070703902005441c018001141c2720b0f80e281c4031b528a9480300c00c030140d01c60b0010074080d0070f007a038044c0e6501d500c04245501682010f00b182c400030001582c3c030502c81c4210f0340c000b0104080e0364080001071300d5554407204680403031070041461082481441182d0300301441c0039003114007170304410351642d5841d580c0303c00403103200d82180c903280101e4820724198402c9560f5000c2c0c0e81882c0c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 907805062 1250 907803812 907803821
    0x2012121009050a1d0d0c02060a050c0d0816090503030315010c0507060504030213050f01060e0f031e1203012414030c1e0705070323070f0f0605040f1802040504 70
    0x200390320005401d800c40000a41300c402c00d0b060721500c1d030f08034a4510000307541280a04154903016075140b030326680c6030407081c0e0306803141000c403c28500c2080780b2403440035448452113200f19201090000035500e20032007552085840d000704c1d541a041400040c0c0d4040400c0200400007005160100041405441e0b207400d0203003179001100001c90001c1d00b4010f40c10300e40501c0030900b85400e400c102d079240440c10b84051845c10b0144004000100710034016941e40d02c00500700300b4800909a0304000c0c1e0020413200141c00000e10880710b4029588402882442c403070943c1c0c100c031303502480e0544000d01501005214519541c0c114180321040101d00040b81100d40950310a202c0c41d00f5243e51001040401070b44000d0000c82140d5007401081a00d00181005c200e15040742d5100c40311409155880320190b00265024a05020900c500c02c0d00241c1000e11411803412200310b40301c84403d8a444042c00c803960301c1103003e03420301c18026400800c401d4a100c4000f861804c4003400c01420039440304c0020b07003503d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 907806312 1250 907805062 907805071
    0x71209080d061a0c0a0b07120203240d05071e0803071401052805060f100e040b0307150f022107021002060907030b130b0403201212100905 61
    0xc03580c071031080c4082035801041ca0340c2d98483c000c0003420550031221840e81c1d070344060401000b2101c501c01090209001e55003044114030343c41c0d03080d5202d1811201e500000381d03c0424001c141c41181000342194242502c409002c103070004043c103611030a0446000c90351490f481d8549000034011000507101005201130802c580c4615007245021099550f49400c0d608047e2520300b52000882220486a264013080b05066030496000300b0706554140004000d8100c4064258000415100001d0700f0303503021650050340c00d02121b04010041c1404189580c446090041074051200641444003040c00f400440d03100710b12620448010203e0640c00d08000110134282001801c00800c5c91000c505e880b000a000700350880c0b006004516015005070340d201d5181c840035010030845e07404104040b588500c031040c01130304052010503905052800600d0001d034030748040d02003c412201080081e901155070080788244100c035500349203152079243d00040002c0c140003146495810001164174a071300804e80718 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 907807562 1250 907806312 907806337
    0x2070507061d0622081b040f020909040f15020d050103141203071206030204020f46030b040504080306040c02030301120f0309030c032009060907120908 67
    0x16245816000341151694028801000e0101d100409240c0c031484291003d0f00d40c56a444c8136802d2040e190090300c4005a086031410380140e5126041020300790300081004070042e101007005400502d8120220700640d2003042d8000403600110303000c1052181240180d6000301102500041c1c0c000b524000c0341d000d945000b0000362200010418007800450003405030251001a01c1c11443c1d481c4445200e21006200310181300d8000c0704d010003641558050b0000e0360380070304115035800421407812950b40040c0790141d1080c4101d41e02071152071560481d9000c903914000270015000b00e05044028440e450f102000030181c0e40d050b05902aa0765000b41030040d40244c07041ca82c0e03410800148400e0351708130704481040d03600800040000c405115164030b48075802040d070078080c00c1c103841c3c100d50804680c0d2029020300e840407004000d001c501c05500d242c1e00c0441600c641c10741040c00034410035000c00c85403140e00030038000009a4103070048101c0904130030541000120300001d0340d2030702c540b504044419801c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 907808812 1250 907807562 907807573
    0x203012405041206090b0f040c0e100512012408120307031b08150406051507021f09050316050d060f020903010207031110063213020c0d030c050f1606020705 69
    0x1b813011549019070070021100b82d941c1140740c661213056800c40c0a21445200207107400001e015000050403000103004001c20f0030b91108546da103401d0181401c090640e100300701c02c4868000f484c03c05004002151401c00240c00c0014101452784040d40000f0a50700c05d0603281c04110178a4098804c0d107441014503511010701500b040711450401c2d042d51200e07075004524140307040c041aa0740001c2c0858940402200c02c1d40c0e481d161010401102080240380a8200d289d01d01c0d030509608030107903106940d004e40845a01c0541c00c113111044040c43c0c440c40d0f4105806e03d43c1a0007240554002514800003c0b00244c038000716a80400c3c2207a1044005400041d1407417220b00d00c0c03017070a102c0b160001c110700000b4485a800c280304000c03803000440c07007500600e02038079801500c0070004041c000c1071807004160380300302c440d813500f020301942c4052441d1300366020300e03910200b54502034810030b00241d0300c1d9500d550602100707220014195122141201520381005d0b92140001c200703000030508075108802505 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 907810062 1250 907808812 907808831
    0xb060f070f030e0a180e190b09190c0b0702010908100c1106091c090509040b01090c08092a03060106030902090a02040b2a0f07080f010203012405041206 67
    0x3000380003502d0f5202d11400200c1010070007194885c0c0f1000008080302800035514550140951601e0f0800b00c454082075918080502031000d4030405c0c611a154050980721002070f0f80c0708405446c801060001d081d0750b001c507810b0002040390400790541c1803040c10706081040e15464110714148070304146040d60f9484d5600c2d00400c036030104e56080000c50780301c01802241003a0040d1502d405032000d81c0b2050249200002e400d99200b500392000801000d80505418240f509062264001c24080c02460f141080103031005981b141c0b0b0803604c99261000070303204000b031103100015040c10a41d8200011810344001010940d02801a04c1c006d2116440000c1c280d032291040c0311004200a08161703a00e4030606c401c02001410b88115100d81c111896072401060070112212410000704481c841d040c424014690030700d100025644c402d42d9400800c07282c4200c9009480c0b03003030384024050070a0313001001c00c0548940c003500b46101560040350400a00303141c1c98078407101240301038240560306181c4507000030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 907811312 1250 907810062 907810067
    0xf0c030d030213290711010f050a0e15040905090609010c11030a0804240c03150b07151e1505011d0910120303060512030705100b060f070f03 62
    0x20104400c5414107504080c588018a00c070254107101d0321904a6003904462505074039016400c0790850342c4140c039a121078440c100b06010f0500501030b00d0100300c84e660680c0c0580d000d50150b4001004d1903546d145440c070794105100913203031144c8070041038280901c40440d205c1c1c0f503401198030400d20100149400d240c0103a0381c1f800e5810b41c00c0c0d64010f0114491a91020508c080b0850380907131003605008074282c1310352516500100c0e100e016030f00c24007030710504241307d1a180d4000d8150f81540da034003807001c8400001c1200491010b44240c105503402002000005809030304860301280c5401030009500b107500e040c41106205024044070b80f181e440280b070082454240c40b8101501e003e203000c0c030707900342c0e81d1280c20850721403654039902c2280721100080281c4010000c000c040c00c4500f510500c2c0c0016898003030050712887c010350f8401c10080014400c0020004280c0f035445410000a0200c01002000000242030100400750001009c2100401c100800c10051200b01d1003410b03420701146060800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 907812562 1250 907811312 907811323
    0x1d06061305010e0f070c1202150c0c030714070f17010608030a090b0c1204090e06090109020117220305190c02031b061201090501060801090c08040f050f0f0c03 70
    0xd50228a00c0d003030050204000d424941944440c03190710842e810b444100081c3e4403040c6440c0d0090106444019410b61039074042000103241e4510020004035031100c481c03640050050648640f0654028401e1401250011400380c41c02c1c0c0068003610030068a40303c01c0b403001e0456070404940d00c40c201e807002065440c01d128001c02443c8000145040245140004040001500c1294942c0360082064000b1050500c100203041c0303410304c20982e95907130303505a1794040c280c2105104000d0290400198540c1c4040c00740f803188590580d42d907450980304500044030141e001d000758213500c800020f08403c0800c075604085005010341c56903903c0e50300c00303009000c10700e511801c0f0000f000040d40301c04006840000e6000039000c40214803a182003008000b2a002d4000c40c4500b40086510b0310002852803c07e62040b4180c8041380c2d6068600e80e00c40c0803030b06c00d4442000e14140090a01d400080200d0060700c0ca06c01c82a01c501d00b503884500385940094900442510885045e40011442d51410320f0304014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 907813812 1250 907812562 907812589
    0x10c0807020105091b03162301021f05101502010f0609091a0a020c12040801050c0f04030b10082b0c0f060203090a050f0714090f0a0902041d0606 64
    0x3c2c466132502058a40d200c075540344461130500240c1c014181960741c00d12410107010f406900800002d80d40d003403010079110321900514111503004001541651002c00d02d00301580408600031000415440d52038002d04005141402c184255200812141b060b07090080013000c66a0000ca249101055403070704880c02c50b40408403007894030300d0b0440011070303180c2e007140001c0d04280d01c0501c039503940ba0158040d108803540140d1501551f0804042000040c028000741d6130448000c00050780e9600c4480c46d24400c0340601d4001007002e01080001410180d201c40e400b41034100301158055032000c4140c0340660301d402c1000110322280300700c4a4142c0480352040c03101828980b032003a1030b4482d29038401181130700703002401c9260000300282054030200000c59943d03600c0012100d0000340040419140c12031402081c40c0c2010313a281401e11407170610a110f01600c1501002000c6480301e81050004100841d0126006901c0d00a03004401e002044030050355400d04000e440c0c1440e00d0401c02a20904001c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 907815062 1250 907813812 907813817
    0x3041e030308040b0907091e2d0b0a18050a0b0a1505132103080114060a0819020301090603020a0b030f01030f030e06040f1514090112060e0702010c0807 67
    0x41003080801d5020521642040d0400c022141d551140c20200c0e007043c140340c00690016040000d40641029034072040c1c440a014240d00b0820200884180010b0340416508841007501c00d00989460b0b222035405445540c070018139401d1803031b03074509a00c510524071840605074680d03540c0c1009488a65805064054081110a15180c0c0d0030805642d140c0c007200c956101c104500070442c0d0300211554908840a410301c40e0011000900c00419040c00103d2380004a0001d401e034000010a4042520f040301d45940043c812070402006990072a18294024900344002c40ca0080000051119200941c080c050401004c21283e04500510a09450644c07040f24200804c0003040741407020b40d40c03d507044d20360100c045c4282d0503150500b00d540c0101004130603408440000c0000c0c241950300c81580c100c511044512000032200c039800d8a1502400c540c00d484440700304408045584540c135101d0340d01d12040e200003803982d142d401c0686900306c00c444000150799550358240c40c4640101340c4540c00301c02407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 907816312 1250 907815062 907815119
    0x30e010f0908030c070510360b04120203090411190801050f0d0f06020a180506090907050a090b0c070f17030a050702120a030806100c0317180303090304 67
    0x25964200940310081031030309043c4c0082010004c00005225130081d2803584c41d0284410403000c1280618181e1394091743e01401d24143c21120541c1c1790b00300c01c805e06a0400e20200c526070f5152a800102c00b1121300100850004102e003a020783e44074450314443d6031015a469458941c008a00120b182c6034004010600c0084001000243d0360303003210705140380d01a40e091404c0c0c130a91402240c403800e041c4006141d980081240e58040398040600740c80c00362100c00710000e05030744105010080c45400d101075040080540014403040c000e0005081c1441145040301c10980e880700d00d254140c201103090301c0d054000360403c110042c120780b00c44c006040100301c0741380c14010103070f0b20596030700c120b03e00c01c010f224020030701c03a05541d942d00118022582040540d038120241c0d142c01402e080e01181d0040c8100101d01e10381009074442c1025900c0180e160700c5410117041000c0c00011103001c02040034140000c0f03c450108134110070300107103011780d0410008603119030400b0302d920f08095541e524001c445109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 907817562 1250 907816312 907816331
    0x105091501031503050d0c2f150f0708120105060f03060d1e050a0b061f08070302040b0c2a030c01030e1213060305070f1b060b0a0b0a020f030301083a030e010f 70
    0x740750100c4403040d400c540401e900200c0c0f20410b04d8034040c03034541c600700ac180403c005090100650003000c802410b544a011240e07200c00c2049010301440c01c103c06201001c0c0000740703541c1850720810b0941c40c001d20074000c00038a00ca0700d46030400031902d030458080c6c00522a000405c1514181c55400ca81c04695032403039480070641840c0c151030154210350800c10014042640940203a04685c06000002c011030350750034030407012507651045504407a03802d001109131540301c104000c02080e28010b00501800540840c5001103000d410b000303144111a00a150900402c03080800003410410303e00102039507040e2030000c0180031584000c281e0018088090b80c2054125031003555000c0700e00c908128074810070340c181007180027001100b13281034000c01d007030b20041510a410405000d084240c0e030300300c03042e200144080c04c0d285c0c0000c1c0b04a88030359001c0c090000f003003045032228000c2a0300149507070031110460800441901040c06400c1c02080d628030f2038005254080c095103003407081601c0c041c80258cd5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 907818812 1250 907817562 907817633
    0x21602030f0c0f0a0806070c081c14072f1c03091b1802030c072003010f2a1101020301060e011419050c070803030901140105091501031503050d0c 64
    0x500030410408c002180e5048420003080b1020780718038480c05002c3d90407800c41441e143c0018500303940059036160000700098200362007528184c800c80302a64400941c044a00001c064451042e0419066801a407404540070103a2000c00d6014640d95030740883e0501d0142410808440c641d4000b204454219070180000e0380c042e580a800d608400304016581e60340ca4041c09500d00039102d006040c650b0300300d095614206010815010080224020400900b80000c1c8000b210b281e850010100710803030b10152108190007040c1c40035038019003820a16201c07240401400c9900c2600700c4c0000c00c265803080002940c0c0500d80ca110100304583d0107140254951404d03c42d1045900e4003401c001000650481c1e002c018062880103025400440c0d07240d0401700e4000340070f0203e00102658450f041400003034245410aa4a8021403000e0641202d072801400110050311b0866031a1142c0082c00e000000026010400207506100c941e841c00118440c034a0500101d14a05180c442c40b0305480f5043c03000c203030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 907820062 1250 907818812 907818823
    0x1201020d1a1203042102041d07240c0b04020103020708160312090305120903040f030501060e1f180b0a030503030703050606091806120115080d21021602030f0c0f0a08 73
    0x17000c5412100f402c1841d0b10008003e400c20184015a818460800130895600000c186d4241c1b0081100b0591680d5000780c4059001c0c400c0810400080c011110b07000451842000950407a00601d0050702d0800307545c40d4800c0c140d0000d1083d600c01d82c106016070301852384c403241e40c40a030340c040350003409032002649008005004441e0291440b009801c08501e04100030411500101030320b000400e0369654a041040c028046446008446011f070000a250071075502000800310142d0501003821a00b420080301c010014041104807907541e464402d050740d40c0d10201940210b2180000b1590b0385003499006003543d00c054446d9003e20401d102c0b072201540c8241291308c61580c2680201d9095039440001210307158203103600c909551078000c4041154140001410598460b04116482d80380914000c564000902c0d9180a040820880b102c030015056002040e101a43c10f111194500341900006d00307062001054403000c0d8012107500401e410800343c81e10031040300b12901e0014600c5e00106035100d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 907821312 1250 907820062 907820099
    0xc040311030312061207090c18050a061e0212130303021027031701030501090b090f10020304030c12021605030c0a060302091f05030a1a030a021201020d1a120304 71
    0x117185030003e40c03200c001c003081102c004041c241c06c1482042e01008016041244403c07005044000724400890f0340e04207004080c045903020380c0c1e80d84107070320f142c1030221806928240690441c006c0c0707000c44800c6041400949041c0e8100c80720a24503501d50703d4007a141078410a1503107001400d00c0c2d8903919110500c0389225188440c2e070340e0509031a00b640380c12104121040c20342950020454004000d201c015800b48041e0341c4164088845c0e03441d40c64140340d80d29040d0759914030071b0748946221305880060b500955009882806c02e036030003200d40d40e03ca12804c0501ca4031080141d1282e8480c0a6058015100302300529090300034001500594001c5490031215004100516400042d80380c500e4071481e400810402101e091982100080d42c001043c0b81d00030340740b4ae00c8a9003024942d2003401b451030101ca41c5144003d0040445d00115400d01c407901c041000c00015955003840070150301c04440c042c04401c00032411580320042418001c000f6040d2980f074040700c07294410b00081c000756051005d100c002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 907822562 1250 907821312 907821319
    0xc0a0815130b040204180203060319052a0909150c090a050f0d0c060e090c09090417190504090c051e0f0405060a020d08010510020a0b09150c04031103031206 69
    0x110302c06010030040d104503880703140024400544c4240c041c0380c030340c09103000d101d080301038411402da4420343d100492800c900c064a5a044555444c0c800d62010340020389860000301350781203000315030002800b603450440700c0d80d2540c5c00034001004010001e40c4901c1d40b00c2c1030b81c8081c071700b04215000460140c0c41c00c0d02429001e036003d44280b07403496a42c1001d581455a201e0285102c103034580c20b000f80f11b103496002541c028a010342c042075039002c4541c10f443c1e00c00030151030f003100c030350703544d1507051051510380b503d06611042001007070f00d0000e400d1041b2500403400c1d124155901c3c50400c0c040103c07408002c0003410040c0034000c0c07003a458040320b0b8104166806d00342c055142e444541c1016524800c5e07a00642d8000302c0006d41b03191182d000f1810070f001c020f050300c1e02c02081e80e90b40d06200400c80c111004030700581048441c0d50001d0003d0014541240c8070b40d0803034011080b00707460300b21101815100b4951112010404000f08900e22441c0c034140c5105a01550429040e20b200b1400700314080c0000e4030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 907823812 1250 907822562 907822571
    0x21b0303010f06270f0905010b160f03270812030f011211040204060c0b1b160c03050a0302070e1b0313080909010306020d0e010605130506030f060c0a081513 69
    0x61801c095070460a002001208210113030f80c2d40e404840d500c0041d21501080500709000059411900020340e042c0202c40c07444402e21805035598a8038450107801d044080c4151340300c02003140039012920210b1101100310819140b800c0c02445850007019000c80000e4103020400c01c001f071016400b400d0304440c0324002c03060b441c06e45840c080002140c916419600244041800aa1245d024280100d00c81c080c1d004450a9224000310042c0c91a070801d2022040c0d07000c108084003c2614115070700704e031b1b01409018501c01d80703d5980b582000070210003640168080f107010700c92000c41d10391141d001021a5612032003840100350203006800010b00c0c802030121882429002e02010204591142d81c0c010300b00d840d20f603101d152050094000080940c8440d1400c0000044200148035003170a40328000d0051660a03110701d1214003801009140903054002c0175580400704c80c08002c00c030f0103601c2021106440f8402d10740000c1c01e07030300000c00b401c0496105c0308105503a42c45101c1d04c4280c02d10030034070116 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 907825062 1250 907823812 907823837
    0x2406030709020316110a0b160e0f030a080d020c0102030109091e1a070c06051f0611120c0f0d03090201080a0c0f03050a020f0406021b01022404020109030204020d021b0303010f06 78
    0x9081445e038000203003400c00700004102c1c20800300c49035503503d130059440e400c4e00407110200340320b41000d0302ba03011174042c2d01c8203070315002144c40e05028081200c2080800b43c5030540c0520100e0a9800c01c0e481442040d80f17428240040100009a00101c2080c902045101110700c1e2110f00725404000c6035400b99180c00d00110741d400740324001c4c0442590304020103001c1c40c104030140714904138541e480340c600c005402c0d4000c01c0c2c5500ca0000880c0d0038440c0300091003507034501c0d8888482030b44004420301c018030034040d80b240d51620600402c0d14908079614005512101800054409180180384c84102403411080c0c80027107411000220081b20240b40c009120781c0c4e42c0c0003080c020310a0381c1c511102c01201040c00543d540d1b000441c071038103816024000b40f0b0f4031440385c016665943e900a0304a45600402001d07a07214242c400c20a5100380149400c540300d40e6a074021404980c032a501840f81030b6000a040f010581d50b9030741035001952203000840c60f540c581800702068141354020681040620401c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 907826312 1250 907825062 907825097
    0x90306070806060f0703020c03060702070602070501080603010209030706120f02031e091e1e0f0703080705010f0507050318070302060d0902181612060803040e092406030709020316 79
    0x1038481841813005a555840b1608020350780d0481d19990390b100b8424200014a000d20105055040340c02a80040404500708401551254001407055030150341c00c1c05041d0140d40c0400070700c40200890b03124000b00561141c0da800513683c00c04040207210780104103002c090007038200321508a0070703061a6510140c81b9041e80d2418945818005801000540c868151141d40440c0c0028550b0880101c601c9503250700543c0c81d01d9042c800c80c020314a80084400700007040d090001020b520f8420800010300b0710341541c0300c00c215141912080000342010081040106042e03070f1142034445500010310109103542c3c0090054499030000d02e00b525100c010000441d21074260140c0100b204035114009031800d1000d1461040c903000c2d03880006805240400e44842a5200740015141440c002d03500d00f40c240b00c01c005000b10050320b01e0413140701c1c026480c100d0b490500d40700140701104810140746400c0c800201407410101d5005100070b14810418420303003145c001071340c43c1d000e549410b042010410390f0a01c0d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 907827562 1250 907826312 907826317
    0x606070c0303050a0e0f1c03120e0a11060313021c06020301080a0507210f030504050d060911010215160905031906150608070e040b1003060e0c09030607080606 70
    0x106800100c51000c41050340040281c200c0c0300507917840740c12081d4400c040090000313680c454160000340015031210001801d0760404403480c060304046030111208440350040342d00707400c40c158040d04480c809004000c0515031048041500716142821800d000c220b0144050704048020b104246545080c0e121040e20440748102540000e41191250ba41c0c0880d252038144184080340c95014816010800100702d0440010172118402c41d00d8a0220070f40d590310f28080058400c0c0c080c82428000014680d80d0f9000130040c0d00c0c0f08640100ea0700c0001e140024104100d1415581550002c1c2450000b8800003820b16074006004221114110350420781643c104080d600801d03010b0190550355114500d24450f5415114456a070800c600311003011051110000c03405400c0015001d403000c1240e061103844034400000c0e0007840007642015100000307154550540141010030345403403080040822808401e644030070300300b00380d6241100443c0041c0d2240d0004040a003402810b001003006a2a000c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 907828812 1250 907827562 907827577
    0xa0e04050a0b06040602031206090106170a06051e101110180803070801080c0f011707110f151005030c0d06060f03140d020f060a0e1c03050603120f120606 68
    0xe0707140c0e1a500d80c05c000351294403d924010a040882010584c1e5080255116040310701e6540d96030b58030951a001601040800360400d6840c07138039100042166075074014007140111080000b1400d03001d00d4001e212880c5002c402c0042441351241c0d031000c040001123203641082c1003415002070014404840c81e40300954064000d48400008400c02900319003000090341600c468008550061071700004001315441d2186000340020111304407603110007044082c0580110050510703495542075154502d213000046030004141d540990b210f40d41ca00d11403024541c11400744000e41c600d46052401082d43c4141d1040d865005518688450003031150590080c0c001c0c0441d41c9a40e6006c555030300b04261600c004c0e0160f0036140c090000aa01880d000084041000d4660005440e03c2e5468143d00001040c46400403907550080544451800da21041a10300124094400280b103081a0041c0340c501200703000d0000440d8003c0011420351075003c1d003035480b1080101c0350300030a55500f1011a5240c0544203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 907830062 1250 907828812 907828819
    0x1080105011b12200115030b1e25020106030b1b270406050420030601021905011b020f25080307110306132d0c090b010e060a0e04050a0b 60
    0x1c0368414244c0d407003040080910900e8407075102c601a5546003900b210211103081042d500c0d031a03010070005405504a50340810b00c0b0b80c28030202c007070101e00e54101070030464840f006100345c03055401260148d800c20304000c100358030081162a04580c0c3c1c00310056405403040612134051003a12103c0300f65003040f00c41c28010100031203410140e402006502c0d034103100c0102d01c91030030900003185030b091500c036107548070b10100c0d01100c1c1280c0900801e44075610240000341140079418211070045405156004400d1154000160641e400d10600100b04040c1c541c4508640024018031115000010442c5480f0b21100f01120481c80c0076400980807800303940209000c0c000030541c2d00901003900b110442c0280c084c0c0a817640c40da526a01117001d003a80c07480052488540b8641d07035200c2c0380c01d016503101e0f50041d41c1361711000300101e4030783c2d20160095500c44903820380ca426030769905580c0402404c00c403480c240c03413a03400c00c610381030080c050454595005028035034400024000000c0380d0440d60341001d014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 907831312 1250 907830062 907830083
    0x81b070305210313020409140a0c0510020727180f060b0a060f0c0219080303040302010e0109110d05070510050c0f070305030a080c0d110910020c01080105011b 70
    0x81c074000e52030341c0b10440d040076844900c010b21905036039010100c0e44194500d000b125091034a40d0b0030000181544002900d24298901d440c0ea2034080400208034610300604070070200901d8032040140b00400300d440d003011900080c00030001c00000b40e850000310400340c3d010b00d03441c64541e03001c18020194072020450840c0091514000d005040030540790a50050388107006007510b600912258250790301c030300400200551031451480741b0680442e68281e2004007110356826003400c1174002201300e5004403266400010a020070950248600241032080c13070024058600d480c1c607103403000c3e07411a40d00c1f03001d0400b00c40e03140108081408203002800c001082006810720342480140b447d000702d05590407a2040401c4000f03c0940001e9810840340e00000461a018501c8411a0b910f00d000e06010181c46d0144081c0c1c402c80403c2c0907815207001c910480e50340303d402e2082042001c506103400d02e011b40d04440c0c00801142d130b001480d541954820708103084154242c42c0341e800452042070014083d0b0303904 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 907832562 1250 907831312 907831319
    0x803131406070507051b03030406050a120c050c070f0311040513050f061f05031b1306060f03270b0601020c18060906090c0a0c0215130906090209010c081b07 69
    0x24000d0080e45010700300312030100046d00c03e0910000c180200702545a070017844100b010341c1c03143d070040032846882d2400340b00c0d5081c04004042500e55094000780400da001c1440041d038a07081040d50700610001c080c40a1591442e283c08841c0c0000402441c0620780380c400003040c0060700c2c0603144c032541e4040211a40841c51046298503102c0a507034886000d2003c441c00c29103403482023150001d803600100500028203000340038070100428490700c0d54000310300e807110105040780d41c41610014030454403450800e900480000f001c484104052100b000a1201d500011340c01c032040e41500701e0ba01403d0f402e45915060f0060380f80070a40c4211a901648155500c040b010b1207560650140d50140c60709560b5803180c4040182402003104c0d4500e219605000380050230340314002d910758082c005050a00d10203000d51340f294a650100502081010301ca1000f00843c00c810b105503401411010000c504119144000a00c55130214002a0141102044003d01807130091101e4001383e104200701c401c0c480c0e5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 907833812 1250 907832562 907832567
    0x702040213150903110a030519020409080409061e15140d020c0f0613080307080601090b0d02031f06090302060d1d21070b01050105071407230a03080313140607 70
    0xf50004035402c225180b50700c00d0f5070911000200559901030040d04d0813400444600050341042c02c01079a00c40d172502d4005000c00e03085402400074250156020031403500304144981e65a0311071605000c940c000300b034100101e40c07035000404601216172404400c0b61408500340003050281049080b0703001e01c005103040281100040340140002c6810a40e142c6955005d41410080088032001e031a54900300f00103098036100e104410342c090b4050410003034250311510a44401c2c1c00103820254a564004284400c20300c034001e58030058610598100d480300d042c864000c007205100e00c0b000b07000d000042030841304440a9082910b03c05885401d9a05040c4c503504041d42e00d1f031211040020383d00700881c440288074044000c56000f19004a900d1919900e80401128243c3c8410402d5410483c06001e1800900c2d0078055100108088908840c0c0603007a09c3e008400780380d2400303045204004172282040041c128005a81d80540500050030044c0c485041a000030782200500750118000c100c100550184c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 907835062 1250 907833812 907833827
    0x1030c20030706050f0c12130b0f0906160941011d0a050f040e0f010614010c050d050702030a0b0c0418150302100c0c03080a140f070204021315 63
    0x34043c00050099484139107000040703110a64000151400411810700e00801c940b00c6681c1041c030301c41c102079010886445030320480c14203849400d000d41004003403180321030040041c0c5400c10070003129403e41174840100540851028410251610105034900c15503900801040100184483c2c40c140900d1f01d050103e0140404203c3c4a80414001e002e22009407583e00d41c04c500300325018011803401d40c1400100080406000b14071580262511204003140f20148480900900b40a0000c15914148074115070500e00080586041080c14086480403510001d60170712250b00c01d00300710707980d0011170000c00d00f1303e202c5440151079408290240724030500010000c200b1150110386844000760f00c4403030fa40a403071101703501150036411000c00340090b00c0d040619146140d40b17801d24000c401995520007070f400c03842ea4416122800b0100c5c049a00f6500035654003003d60000600c1d03854000b500315021842e00804001034041d650114036480041c07200a220005045c40c80e0b0452417040405c01b0045c200d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 907836312 1250 907835062 907835077
    0x1091226070809060706090f0c090c020a0803390a181404050601030e01230c130b07030c0b0a09060b031b13060b030c07030207060212040501030c2003 66
    0xa1901403400c24045420300c0548003000d911100380303483e000b1080104120394020030000d542c01a5a0004000050000003200348030381c0c03191b419009031a2416290a0407618101c00840070f540154107580002000d203000c41e80c0c081180a8035204100859180343c140c903001a1115861400081094411610810141504048542d03d814024080740c00c5c0c00c110010a1140710203084142c07500c521645402c0d0400e90f4004810b2500180d04502400c42d1030941d0710400c07000e039640002c20000100c48480d811801da118011290b0b070f134945000b941d0f580000d9207141c464031541c042c004c06d00708101032259403c1c100350f9800c001a0304060814890400003482ca40c00c044407100d1400a100c5401e00700811040100344078030704120b03c2c20308001d051021030440341031540d0700c45554180105d44060188082d60040d80c001d500700307440d44414034000e850060103400a1081d54004400900d40b422002c0458040c7e940070729000c50044034505c02910f0400403500c2100740502241c8100910b90000030140811 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 907837562 1250 907836312 907836353
    0x20a02070e011208033403061805040f02010815130e0d030603081909090203010303080609150f1020100c080907060309030c0503030403050d1a010f0806010912 70
    0x1c0741d81c0c510110024071580071004081d800240009440800e40300c1c1c1c2c0e07a1504864068850350142043c0c1c2103600c4200e0340c5840d50109070760b01c00502c4450301c0e50240303502e51059000200080d0405403500440c4100a0b07070001e040110100004415405140e00107404c0a000390038040c00400382000500604142e584400840c842c1140d5816130350b00c0f0780107001c1200c2c0c011010328500b00803281810016510300100c541400540710001901d00c240b4070041d0f000314069603038100b41e400c00500704400c400001d0803004c55108000c481c03049940d540c0d41c500ca20410102c8151301a24421201581d11031a00010342c220030454064200262601040d103000e03102412070200605100ea05098030016801d66400c08558880038003488214025402003d159000e828014441c0b981503884a1a50344200d40c12400141c2c0411440710707447c11405400380c18404086c030400101980b400003840305103030300c9182d001c0024000c00300d0682c0c1d00528400002d0035200b280aa2809003608040301804d40c2e00400199 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 907838812 1250 907837562 907837589
    0x100b031f0b0f061c0b031906021308030f0d0902012705031207031704021207060509040f02040b0d0504060e121306020f0604121701080c010311180402070f06020a0207 73
    0x222440c0030404c480c0038030440d070001c0524100c0c0c4810700c0d00a182e40944280c2504c6034180b034248650226221014051041c0400f507501d2030404003950300100c0030341c0418620340c01440b603c00c160b9820400d0701d0f103801c91041c0010b183d0041d400100c5801e1401400002c800d100da4000e0981c0011081d00c05050b1042501110004600c034607112000c0d100303107000580003a400d134a40480306445140020740083c0020306042c1030000d002100c90615949034041d00100c0c4000400b182c141c00c3c00e004280190b0018002103080c01c2c6481c4840110f8410306100c3c9940c1c9982e10001001c00429921441130003024000300d81800e201c0d0a0366040c0c1d0381c0003800380310380030804000010b5070f0b0388005076411b01c004041d40a8501900d03183c0e180f070450003448a400041c40810814020480d4004880c14000c2142038010400c011189002408491ba0012071140d81c51040007150b04000d140039444840d180309070382c0141d4030700882c00c00c5a08103076210002080c0c05d0001070054100380d800901041650000311035103c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 907840062 1250 907838812 907838839
    0x5071502210c120301050a0311040e0312070801050105041a071502030a060611071d25050424140d020913021201120302101a0307080f100e100b031f0b 66
    0x15484c00300f44a85a40141450030078030000351001003a60b02e13040041e10200f200e2411404075800c5030000c1d18240d0081207000d0800103a654803512481c010a404e080052505042420010b11000700d028081c0d0a05000901c9400300105040003540c0890b04c40011900c0b400c20b1355031302c00942060f11407500080c0c98000c46015035580490103c00320740719488070304040c1800c8640401c0c0140c0003800b00f03614450100903002490038400f400950412150b854540c0c803400c101c840c03880d490f280c9031b0aa2243d0304000011301a01e40201c0c6050311000313000c10858aa010600d1448040d100d41c402c0e0303542003980840300f040d03800c034180c016181c40714007200742d1552071ba02c50002c030300d9006112002500680c45950304c80c141444546c0420001c860042d022480d451050002c01e14ac82181d074408002640300000d8a058580706000249000084120500c04015174548541e683c02120110481c1030390784080d0103c4544d4100602d200d005502e0000c1040c00c105141043c00801e0282c45082c0608004000705 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 907841312 1250 907840062 907840093
    0x9100e0a02130f0b0a1226040801020403060f18081b0f0105010302030c0d0323040902030f07030501171c18080c0109050f01081305100e0601030215040305071502210c 73
    0x2030301a6010b0f034424903030b90072087d05d4803900005c1c00001c0c40381c2c0054041c0d0301082c140d181c1c8000e04c0030b002c000001581c1c552a5140160859517903e034819280ca00e0034034002d800130038480c190540540c02c402019201d0182418904180c6034900e4000b481d441074101801c0c000d2010f40047e4101c030700032010382da02c140f03441e001d02c8001060400000d0004194000d07008542d100c105a40300082c80e089040d41c28980c0704c00722030003280e1054556a410000400401904c2c0380d06000b805d0240c0070b800d034030302c0c08241454a4280e4440b05841041a040207400420301614450a5941001d403000a01ca480c403c1e0b843c50216180c401041c007041c0021500c041c0030440c2e040241c408440c0b00410f03902c00c0e00c030317968440d1828480500503400b01ca00c0d014210060b400c2400d030b4012500542603860140001d5403451040014040000142c1d04640505000400c0840e41c0801c011007140c00300d00643e108840300d42000c03428150114010104a1058000c1c034000c21401c2016021880d41c00c2c3c2191484200d00012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 907842562 1250 907841312 907841329
    0x6070305010609180204150203070b09120405060c0c030a0f051c05032205060a15050d03050912070b070f03030b0307050f01210218011709100e0a02130f0b 68
    0x22040410003c12040014030080300c100c80024428213030060900b9200d03c8005503450380c0d244c201006078008a4402c040c415810b2445812020040042920304942d2039104002d000d14810301c1e114800108480c002002d05010f0061210001000d480d01140c6516212030702010960065806125a290000c0580901c1c58441b42180d415203c65043d80d981100070000d0300d43d22041401007007e0010100c00060382044000e010342c03614200170400f400301c00141c110525050348400d00c60a81c50001e900440e0b000000c8511080c800c0d01c503e2140c40305901036602d03202c16076001c07807426100080c2a4041c011603040008035a0b101e40d5050049003400010156210b08034011150320141c003904a06196014049107008007428512446500c81c4484020f0200e130010b41420031301000701c0500402647c2d11907081c006401c0d40e000d900c2c0d00c0781023072444940d403100d0254201c803c42e41d48000600103081d08014960400d82d0091001030130302c042303c4100c00500415405110b04a0070250004082e203407000c0b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 907843812 1250 907842562 907842569
    0x905160c030c0807020d050106062c2b0507060810080d02070b0a0e09040609120f090b0310030506070c02041b1d040209060d0923030a030f0b210607030501 68
    0xb24041031428036110395a00d51310009040b42d0004910071900d000410138014000106500d0301c52445510b1950421101c900e00040e4240b0580740710b2203101036075a5000031071301c043c0800304c1070307501c80c0d200403840171881038030841014125100b000800510315501c20210340c031441d01c0b40a5181c0c0d41381c1e50801c040d5202c11211a40016800140e818004405000701900c0303100010302d0603818038021b01c400314100200c140c60039510541c84514036414000c42c18071100c0078900074074105034801c42c0500c004000107031600800c48150070020109030100c01c1081004051500981940c4460415082c041c09860329414224000d505000c03000f0005a8045403501c010740b011b03103402e42041107003110842c1458000b5083c5610a40c00c1c4200d0f04291588400b403e41240b80344d0340011340c0d8031941880d03a160103080c110100f40c01600c0c490704401ca031022098850b0f0080303d0402080c40742d030705824900a40203240b2107a400c1044504004600f0a56103229440c0d9030115059074000d0300c620f1000c0303041c2c0d41e0900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 907845062 1250 907843812 907843817
    0x207171602041a04060e0405010e03030106051621050c01050f0114120f060f1b0a0e061617070308150d1e170a08060a1404090c09060905160c03 63
    0x403108809401c2c01d0300080840142000204960402940010120782c01380c0c1010301c0720580e20f0100b004008007440750358003d0007142c00950940d0300d000c0000307010344102300c01c2040b15802103a54608003c801e81042142d1120403c1000c0c96a15002009210307400c43d0744807540b590b003010003198186401c80c101c54141c9181c1c0790908592034206080c0090b582c401440d00c040d51061140304a0441030602c2403030b001d185000c102080342d003031000b41e011007921518224800c04508109101d00680c00c0031051621600c2030312800d0300c13443d07001d501e00140701402c00064528080d51807020364404e940001004064440d4680d0310303240d00c0b44110703401c02c1310403540c1480c0c204841d00c04c0386022400a81004004403c080800f414602890b40c4a251500e003000095083c62000700d28480c000d90481e00c02030f484541a1400f1407058a4078000304030074032a03118154020380d0303074036001401d0041c1080024082e1640751401c2c442265100200c0e4000c0c0400c070b800300b85020210f04404405441000c02c08580da8265 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 907846312 1250 907845062 907845097
    0x1612060305190c0503030c031b0601060e04050a1b02010b011701050d080313080a020c12150403080705070219141c06230411190303230f030109020717 66
    0x2c09a200000d141850295070f074408207500055183e604100401c061040c441c0919100c548500204590b00d1403140c01440d6a00000010700000b50f100c801840041c008031008612920380c007110300300802c4072844170340041d48804144881c2e150150400e107a144001c1c0c4e20418560702e01c0100c801496000e0040f694402c1c00c40d140107010900040107035400084000070300700003c625a59100d80390b4070516041006d41c001e0b080704102450200951a0042d1260001d8800b8100403c0321042140005000038207110000002c80c901c00d00c108141e0355035079805400742071383e147c0190034103101c107070300340b007029100c0c45920300c40c2c001d50030400300d01ea0b21500c1c481d04107102c2c12155a60304019200007a06603d501782038114020703951401402840c003550040c0c20a10a194000741400110181c4020310255003485803c1000000e5000303800412a20000110224420741a03001039103920905881010412020001042c0920280d004064003485143c80040c40742400f0144604d5025005500f140d86401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 907847562 1250 907846312 907846333
    0x903030f0f051e09130b1e030307030f0e1017090309010f1b0f1202010e011e0b0a05040203090f0c012a14073002090403050c0a0501051612060305 64
    0xf00a0219050a96084142c01d2403010408540240155860081465155a0500e219082408070340b110f41c14000d00c2c0e00c06541c1d440b00802e54070301c83c081c002000c2000a12400b0940d5208680380343c0c0403000103011150320000c94000805d00f6008035800d480728460b40001c40d902c03100000c03c5400300f030010307100c4210641d1041004e0f2491029201d43d91f20020703030800000b000984140081c08120b1090113800c18540a59038003d08481441420f00ca40d42e00d000c031005507844070b17440422080401002c011a2080301d003c003140301c01040d540501d40250003c014041c50000c0810034081e500305200c104c43c2c10766039540044801003203000064000c0980358072800703807094034015602c0303886024080c0d003078016120b00311207031410310254030486058841a10003008901d0201c0310800241440000c1414440c03250005140c50601034001824008001500581c030402801501d00340780d001002000320b0315204111940720b016414201c0000f4079680329003228181140700f02c00c10303070360844010304004d0382 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 907848812 1250 907847562 907847587
    0x501050a02011404060c0e090402130e010e060a0e0f070f0303030c0201091a15010c0b0f070c05150613150b09131b140a080a110d0c0903030f0f05 64
    0x8015044000c40d521010b5202003041000b0303003079000f10f11825001031b504405030001881a800c940216100341000c8040c84056504c5180c40031404140f1080080c010f409221307010b00400000e982a40140610310401c1305414540d413014000e89038100568421302610404581c807400140284003920340c1c0c400041c804244a9482b5414000142c00001051401d50f00e0b0394a030284d10724400c0c1802a038a03020480844584000c0845c0305600307003020b090701d001c0c541d140c1e011540018640c008007240200001c4030544244c0c02c1c0c0d1501070300001507030486044040700003000801282e805024002c0709032001d200d41140d1050504c403602010076100628207200b1241040c3e403082182640c0200e4084050000184602c1480c620b0348221140ca5051a40c105025105e0f0300100b414000e80c1c0c00074400c8600b55a048000c49502c82034160001807080a800c140314010301604014a40b107500e420b40c0d0008003a01711a01344107a0303000e6100c202e60a4071158040740c4040ca00d4540070001031081c0714400c111034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 907850062 1250 907848812 907848817
    0x916030b010c0b0f0a0b100207150504030b0c25210509300a02090a050a09060905100b0a0f030f02040222140405160815040c0c1e020307050105 63
    0x505242c458519a06500e41009954043d07640000c1c4281c40c0e03045c4101000c580c4241003105500b550080705030000c01102a4445070a845030104000c0e40c10802d4070302a100e2030468004e180d0100d01e25543d400c3c698a0301c48160080342191100440703c60183d441d0b80e980d2866241c911b40e00c480e804141c166100d14003420100d03241c501d2400d221081c00b041c0101e698030301401c03039040b68006403400c042d0354038500b40c51180400500850316400c00740701500541c44170b0140ca82d001060040108498940c40b450100406803040003401c12440e0100c3d03003040110100d02c070320003540345403c140b0041c0b44400810010185510886100c62a803020400c0040c035410250034400307000420040c10400340c640f11022542a21081468440b031805081c031030b4000c0b40071003072000f290540d002c12140c0b40015404002e681c07a6100e40061043c03078800111400c5081c9502d0947c414040e00a0000c1e0380c000742c000e0b00400d18a40220384001821440340740440440512260441e0000c0040801c14070b04401500d50340e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 907851312 1250 907850062 907850081
    0xa06060812031929090114030a031b02060f04090510230f09041406180712060f1a0a0e130209130606060c1406090d031a0d0c080c091603 60
    0xa88130301007400b604010300070004410740350840d140c01d0640f000b01004400b6505810628048817095420002500c0028512255070f6050400041c180080c240c05c000344103520078029070000703000480c3c5411300f00403005070003180c4089809200946070b04011186245850143c442d41c000340601e17000e14100c400142555050000d03018030440040c0501160020308112426140e400d02c05403800780305901045075a41c17007001c45207400080607411004913154400f52040c848038a2440d10613a007030184a130b1141d800389100200030440c511790b00d0740c601c0c80c0d2101c007425284200031100c40020503100407c2d40c02d104540d074100f5041004d010b42c0c20030090b1840074129a48590400d0380050005030141300e100050041c1e6241c0b01021a02480c02c8141d024103028036075410703084081030140c001c0780000c1481d41c0003100d04000c280c8107803e604802d1801001c0e010282e110794010b80b400180400c00e0b145100350b07180d40044d501c182803d0401d000680e081682d01c5d816030b040c0b0728091501c8030b20a50000585c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 907852562 1250 907851312 907851361
    0xc0806010c17160605040b01030339020a0b030a0606090b09030601090f02070f0305090f0628030f061806060203031003030305060612040305030f0601081306091505090a0606081203 79
    0x1283e0652111801c603882240c0481d03450b8a0309005009040e00b2080c1d2504448542c1181d0507001c00e0500160340300341c1c5004040394a0b0158140d4007086550780d48008018052240d20b09807a481e114403020007604182c8130f200086001510040742e04d00c4801704480c401c0c4001350041410346d1130119000002d102d10a40c803688a9401d1010b0320000b41d00f03035a8400c003507000307039903950f100d070503090410200e1500419450300c600310800c035407040c005c84002101d1250b0040f00300c1c0c0401d007000640c20703800f078544078542000c0c251414001041070f101d051520f4403a0b445500c0200642e03912448103aa580c031040d44c140041c499404c0c0104000f9100790012507100d82e000e000c09091950b0042d00350b89480050b0790880c08900048100203c181e06910644d41c000c000f446c0074569030a01a201d941c403143c8041025228540b0343c54102c0900c036030354003070403c141c42d140c404000c64540310035801c2d2905a0000b08880040c1480c5000414210008070700c0d04984c0106200c0e4610b458402030100460095503500300f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 907853812 1250 907852562 907852597
    0x312121302030d02030a1416080a030905030301090c08060411030c0d0b2d0d030e0d020315040c030b011a090609010215251103070f051e010c0806010c17 67
    0x141c070180000401183d03d40c00442e1103d207044409401441c001200c0d0030303006028445c070b20404036000b0b00003401e40e8001f86065500d040c118130031000303880300700806025031000000004048901d5480b81d00c1e91300d255580c4c444c258440c001040144d40409010104064040c400305071003200e508000e0400020749980041c44204090126032014076441821280004240030042c2021415182c54007160040f14040701c0c4419030381c6c01501100e6020450346c01303280c0d907680000031500c08012154518110401000d210702d058508011000c496000440d03c07804d10310700020340425901082c03003010f0101c1d16120700b40840c110034844d45400c4a003c1038114030616004003510b0b404a08441d0094204082014800c030300503c19224401080c0040740412007456400040e1b614080180d5101035880030b58071100b00e030705003055494210201440c040320110401c1c0880300d01015032001a80b42501c0c4c82c0c1d4035240d501c034401501c11280c6003a01030b120051158248810501e0780006200c1c07852803035034084 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 907855062 1250 907853812 907853851
    0x4060e19030317091c080c0c030d050403110d0e0d060204090c08041b0509010b0706060806090d080109060b0909040507080d03021201090504031b06110703030b040b031212 75
    0x100250303005801194080c1e6905000e408075284444c0d000d030101005202504403480c0a81070605119456010417a04001003080c0d01540401c448070003010b5800c898076106000507040082c50103130b80440200700f88042040000c00d02054150010f400358031a00340c40c1210005100340244144000c46a165080101088007440742c402c11118896966843c426442c00745401d0038212080700d20700030b1059800700e04008594806480302e046d503040c00c240c0c903120072151512002411046c2c0101d4800c4c01144c0420080e03803000112070701188074a03540c038101641d03074005d40c00403540b49000e90284994100000c24082c10301008003030300035200303500f2075120564900103542400e0010418100194001909814181083c20090b02420040c0d504210500f0181d4014010790400c130250050b459107001c0d0081404002d510070400d000b4003440c42d036580d1406180060041c48480d925900c200c1c45d140d4189000e040010b103010030402105d030102e10300000651700050024004107c0120188a060b140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 907856312 1250 907855062 907855099
    0xa0504050108191e050a020a0b190302160f0f0308010510091509080f03090108100501020a140a0503040b0d1812051305060a0201090c0819060c121b0e01050c0304060e 73
    0x2507a0a005d20301034250021170b441006200302c4554041c600280c4140000040f080c13100185511102050800503650108400c0850202d40320200c0a00071650059a01c0d00784a410140c125040384207640d00e202c1c0b6a20f460410000c05501c6807a40d000440144051003942a80c031445d24180c105030414002d030681d036181161810302c0800c0640d0311500049107400389940c01840054012804c074480b15203440c1404d00003541e46080c118090822180c92900c2c140c0c0180c280420000780c2d40004c03d4a50702e980f104c0c00c0c07103801c2d4040440c490080c1d103405261889140d42007041d008540d4425100b8041030342d080d0040b11583c0141c04044840252080e0000300740c0e031900000c01d04600c40d9000400d0076619402c0c00ca11104255002036060b402580c0034800c43c14134a083d95143c00e501c0400020b00c840041d2003195650311480482400c549803401d00082191560713456084030040e6074070702c1c04603141c034001154540103500d10260f09a20078071052068900804602d00780031000f6040b5042005c00780c911 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 907857562 1250 907856312 907856363
    0x31104021c0b031902150307050d1103190905210408010207050a020405010503070b0d0c0e060a0c140304061d22020c011103010e04060506150c010b0a050405010819 72
    0x1108079040da01c4208560714181030109096103251300d403501c030040030150003040c8095540020030019003400400a100640102c007910040000d402c02001015505803003400b01b0351040d9502640c0d44c404002031400888107000c1c0301e90556009003d4000c2030180142005015840b035419081c0e2402403201040c41c0100740301038001903004c1e000400b422402070050000b2244c040c3c0240f80282c1004c0000d210445540003110003112400c2000500744107542804c480c90003502030f01d50f03400000050f06042803940800c3c01c0f4102409610040414041c0c0c4078000c0d035030f00c01c40c03080101007041040220301c41000c103c1004500d55010744030030340c1e0902d0b610708000e40c070701840189295030f43c1c0805c00c270740c0038502485040994908a03503811315550420b80c00200926000307100910440d25800010501d4590102240400044200c110f80743c038a070a080a010b48003000985001d030035500310004041c42c250042604a540c5d8102921a8068803207144082c0c142226003600c90704030030303c255017500614041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 907858812 1250 907857562 907857607
    0x2060c0d030e3c031c06230307060804060204090501061106010b13050103020d0905010207081201060206011a03090a0506070903050105060a0b091507020607110108090a031b110a142803110402 84
    0x1c00500c0900306030b0003c180c40987c040d020581c1603a5404002d840c0c0740000c01e981070328454108810140d54074030707042019100d1a0007d8070740703504003000050380f02c0d040000c10707114800800039180c2c180e8a0350340904450003490740d1225040d04c200420403803940a68020141500e281201141e140542d850741402d903400301500315005440003c104520f42c408a00f92405011305101501c51549010890008002141100c03842e01c2c2c4000041501501c003000140741503a0310405071030440c50050809042801c081c4070070b03070703a650801c0002041443c0040d00c06003a04c14402c41c182c00e080c900c1d01031181c3c01685a118240702d8404101010141ea1030380064500103106a05603a4030947c03075000103040c240003a001c044e06a100800103000250000201848130350003004521858005040014808035442643ca8021036002c402013813882110072003140e02203040d04c985074000110401510354420313030a038107508080c8480d001e1000541204681c00440ea00030705c00360400340030030208240d5010105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 907860062 1250 907858812 907858867
    0xb070507020a0e0712020c012901020d0206060a120c0803040902090f190b0a02070e0a06091407080103112706271302060c0d030e3c03 59
    0x40d080c08514140e40000007416a254010001d42080e41d4050b140610a921142899402103072105200e0406d500c0601480b00c0c50742da10b08050000c40c1d0f80e00441808071500c50050081d000743c00801c600000303485000b6640602403d8096140003c00000e035a141541100c14024101d800615204108050000f8020710400145e884490034208440003810b084058000d00b2118111098243c41214034412241c41600066852103006404c0b810602141c000070040c14a0105205846e0b25680c003207001d9840b14034003009410f0300c9500d0526000411100f507000610075200510000c0c8000c161948089405010404070070b4131a211821000001119540e41e10104002c11005242491907940000300ca03001d1124074046501c0c4418007158010401742c1e0010b2007205c0765086494a004659408050000b620318280204400901520600d0341c680d0f03076846580890220850303070200755050949401c1c4c0e161104455440c010808180c10a440403490005000d60310078044c0d0120b20682114014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 907861312 1250 907860062 907860067
    0x6031a090a0b01031209090e1c05040b0f1308010902060f0c0a020a0602060a0c09050f150d090503120105100507020d020f04020a02010f0e0d02032203060c0305010612141308070b0705 80
    0xc0004140d0a9580d10400d50030f410556891011301022032609c03410050100751002c00141c40e9002d813818400c55100c016020301c0001c13a10b90345003402e0081c004403454400c10010751a600c0d444a400d807117031240083d600410421021a4148540004103210300900b019a00c1207070702c13500003a084007807551041015801000803c10a501c8a102e108003114107414618240380c10140402c110070700070441d0900861202d5468840f2410b0301041e566509203640f020301c0100c2140c03a01c0c50f100e80004109203210100d0794004101c500e0320102410b80b070701c1d250f52014200405a003c101000e4030024003030f41c1240c0e5a840b104000d450798001494000c11680000c140c0025040f50303401150b03003049000400b07801c08c44841003101d03030201c101e5071810180000c42011148581d0103008664856000408051800350000c50031741d0140c004030f04840e100d442c0d4408900000003503c060b41d00e180c560056022910001440000c0845002d01c04540510038290900e46503035600302d04090241c1303984011501c00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 907862562 1250 907861312 907861343
    0x10e0a09022d0414240a0306090506070504060c240c020c030706022a0613030f0c050405040b180307022d150301050402030414060708071206031a090a0b0103 69
    0xd0300840040042c2c252020885030b021300041e411058000303042d0205254002200745900030341209428000304c0006c1c40ca0456550b24a0044020400c03021708807118042e2500190901e8001c1060390704540640e140c101e4409003075a42e2080f40404840f070341c0e2b000200303149404030088180c0304440b45694a03800a00707a00c031507103080500d46a22644101c04650240300380c00340300c050010b90a8002080c8620043c4100c0001000840b180207100650307080241000001081c44203c000e040c9105000d890080d58443d06c600a00099a60448000c3c0841751100c02003020401e403110f40b1510340b08000c0c00c2d81c0c00c1560a070b0000380c0d140e800032034405142c800c0c3d4882c1c0805d0510340394074500444084911040035188500804034038001486800c1c03280f40e02000240500c99a4000c2940400c02602a10343c50300d0030004c0603250490a844441c0080c44903c41074900e040d0500c240020380750030105100e0b0004415a680c40e4000c40100300c036070a070003a180c3c40000522080e600c14065031103a001101e48104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 907863812 1250 907862562 907862629
    0x70311060c011d33071b21050306010522051e0a08060403090303210219020c04020c1b0a0f06080901050f040b07201006080f0a0b010e0a0902 62
    0x4c400c442401d804851200c51080241208000031603007808050704050342e44000c41940c1d016807403441d9180b02005403019404120942911420100e0890750301c120740e2240c50703802c840500003156a41d01042041103000c844178414144008104504203904100f5510b50000c503102c2c80498044500d01c045030130401200d840d000c0e803c0c07006412146c00425152034141c400425908081c48060148000750704030000300c01140265034100c00b1000401d40d61080d8001004242d4013596690b8401801031641083c09031409000300d03406504104000d1901700d00455503400344001611015a000904e841c0004072180c1c104290801000d254491140d42d00c0c00c0800c982c29074030028208940789030060200800500210440e076000180e40c0303030440e682000401496101c080d80d0401c84c0e0380d40300b040c14414925800f0f81000f0140da0391501501c1c00f1500d406045070707598241c548020701c000c1c541c5c00140401b4250b4514258010840a0b02058080071a004103843c51072850900d501c40d000c84e08030003041003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 907865062 1250 907863812 907863823
    0x3020903011b140c07030b15040e161413062d0e131b030b10050a14011b080c070905060919020d09061103010e18070311060c011d 57
    0x1e070400c01600039450b01d01c0040101d82c0c080301c2280d20082c04946018545820840200a51ba2282ea11501e504050320441039152444002d98419070030030b16108842d540100e4520352400795204480c1015041400300300d4084010b00095402c1032600007040b100c5840c0380201001000b00303040200d851012451072001c5000b194402c09001803005c0410440c040180e00096030059482d019001100007500e031254200d880c20701e562090341960000401844040c0b0720a50088a50302c14441c45907507910103004c584003451050405c188800c92020a455014010030004148002102103c8104951b5060220b800480b0080900c2c0d205060903c482c0d43c0078400d01d134000004440d00f48003840c0240191410034a03c7c00f07070300003140d000f14041407500a150001ca0000790310034400c0c0700820714a80d20104c16002440380001e080e240102140c00c07141c1403800c9042c4207a120004e084400d0843c0c640364104000c44080300d030801c004000803140e1040c20720a644910f0020404200121a40d020305490f10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 907866312 1250 907865062 907865081
    0xc080603061302220207060f06050102150604090816030504060e010311340b0910090b15190b371404030206040305150a11041e09020a0302090301 64
    0x1d900000910400310302d0100302405071581110a5813248120f2103800000d48100241c06402d140042081000c00c2502c1c0c02420007680380b0002044480c2d902c7c0012a500e40420400c4114856410b0200320a1301341600460080da02a1403158035209180642d485202080d801c280e00103000454203000ca0741e4080740032240441c0c04d00c5c05210314414155041035500c2140d9104a43d100820381d4174200c10060b192540091200784a204803a921a050040d084842203c82003420b001d04e079282c0100b11124800c013403120380c200720903850780e6841490100e0101c0444600301c1c0c0c000c072a8590312815648000d07000002d0020344246a49914900d9000010305010001551aa0300c250010410345207540c1c140c04200342e010b1901108103110b450001d07050f40311f190000ba402080005020040c49000a4000c1d0f1030000c071900315200b1f603500c4088004540c001e0710b45440040c000c00c000c2000c2c651940842c4002106504110440c41e40ea40d000c1c4201e0380101c0a0a010035008200340407285800c5c800d0003041c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 907867562 1250 907866312 907866319
    0xc061308010c0905060d0b210c040f02040311010c080f03070c02030606150d0c03060e010303030510140105070305031909110114040510050c0316061a1807030507020c06030103060c0806 81
    0x8075041c880000c1305c40c000c100c0030814042da03690340700d100d80d81c81040c1c81001c00b211084454440c1600c0310110b4840010544c240d0155041c0702e50140c46031441c0c400c4804813034012007024840321428004480210201000380d03000c0800380001c0c0941c0340f44000845c0180010b85031203050740c545106042c1860002440c1900c0340c1c43c110307804a00508034a0480ea0a000392400002d1308018000c0154010a503070b03000003884000d07460011007015090381c40540038503428400a4281503480107985403560950882500290703060200c0b00002c0c0c00350014681245c80320710032088605440d159541199596081602d06003000e00c420a0f041d40c114400f003416103c2e03400503074607280c10100419520803604801c01e04221000402490410060040d60444100182c001002910608041000c4c00c2113482140c41c1d00b1040c40e440010780307001c0441d25440d0b10344244280c890b9035104406c0d00140002001c0006500840303062082c0741d50748100860207144a0400082c0382c9200950007040000d004002600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 907868812 1250 907867562 907867577
    0x192a030e0601060e03030417010c030e07030305040b070f0605042003030412080d0e060a06090b0607050607031119020303041b0503060414031e1903051012050c061308010c 75
    0x91111001c1421815104181400e0b90410141400702c1d24610941c0d008103000098140a1001e0b64010b400c1000300520640e4213000101c0c10029042d114a01c5100050100d40200401c2000c3e0421101500c080c9003e0186a6044c01042d101c0784261002280d0841d14046840303043c0b2265031203d0119204180141c00550900b03040c40140d003441408090b003e4542200032541c2051250142c0164004c0c401d01025a1240d0502c17480c40e50103806a070182040a07804c207100341006081402c10313200e411790043c0c014940c540381e60074141c0040411051006030840c04100860f1906c400d113548940801c00c2ea802940c1c0c0389003d007825000c44101d2080101c01c0148000104103903a000540d490b009070b0007240c00e107122404040d1451452103149031006801050152500c42e010202c4007600703403200c0601640c92841401d5201b1404c4600460389810300821140c400e00100c2605a0341e0728a5611400c101c520300103540e00050a59000112414104107400c24248043d050a02400803110001d0510b201c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 907870062 1250 907868812 907868831
    0xc090b040819050a082109010c0f0f0c052d06040807030f05040e010b0309101e1503060207080702100201020f0304021c0f060203161e0305192a03 64
    0x19101c0c0c0c00a2007540b0750303a00303140c05a414024207010390207910781d2001d14a0f9131001c42c0b807080d6032000c40c502048024502e07207070005103580c01d0600982182400307c2e616000c1c0682064829965202c06120440402282c40042000140104032543e40b071000c0070342285140403d524046d030541c0e80340700c60702495000a0b041c00002511581500d1120b41d160801440d2400911070032201801254041000304441200001c0c5060f00c0c000158000c0c1241010344002d00110401c00c5c2c1665900c111500182c1e4014424142c1085183e100800ca66a030020710a0b4169a0707403609002d0f40c01502e416150314800081400c11440c0208591800200600081d42044592086a012800000d00c060b004120b400620740c241c056643c40030003010303030009881ca890443d60401400a400031154200400d404284200380316009100b41104a201c50722444000d0341c0f03c80c0110050500a0081840000840ca1718041c03a0b05a00981035000b00c040c096484403076040404070301c00d03844000290180f624110055 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 907871312 1250 907870062 907870079
    0x50f04090c050105070213020f12070813020f0406030506100602071d0a09170c0c1908070b0705012c01060b030601120b03070812041502030406020a15020417010c090b04 74
    0x308980b82401c00c3c3d61150241c0c000700d03c0c2c03110491400361007184001403d0800c0400c02c80607050b135203440e0a1211007550b40480c242c544400035500d4130b903920003042641005240180c155031400e403000d8004074840e0780c0d0b5610545042d4094030b90614800324850b0070300070a581007041c10300034100400103a00f01141000c5032207007000064512454103496078403070001d0101c01c00c3c40243c151212041c07651344074400454907845400b4102507610400040303801031040700c0b040c1144016103501070050700c8540d162000b09519984115400c55042d522100c040e046d034400b6403610200c2d034000441500240e14180e541d0350031590b2503003086444020a0042c0401d0342d034040c1d0302e00445c7c140074200250100104001070305d492072130342c0700041c0351180a00d001c5c00702242c04041c0080b10214600110903682d038040a0742c6034010ba0003141d00503807007030b00900c01040004160301e41105d8880001407903e621110301a0500228520f07200c8580e4588048030203641d44050004020000c072800c0c1410141040c411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 907872562 1250 907871312 907871333
    0xf0815010f061d090a050a0609150b070213110309100507050a0c170a0c110a1a030a06081218030c03120a02010b062a0c09180c030105040804050f0409 66
    0x5250401030f02202460725814554400c07032284100400c601c1462401c4140070020b0002110102c178540d0a0140026200d4440d01513001515880030078503403010b003043c0b0a840140c00100042e03a0291903500307900d91a0b1420320644400a400d004001e56900d401c3d8095458100500940c0004502c1d0004003c1411381c48810380d0ba005005e440d00454507801800c002000c144030340300700000004e000482c0b421a5030044d2407440410712903c0d81915007540d140412441600320304c0342c00c0321441e0000d80c501074020110015513105005000010b90240c5848140b440c00718a0061040600d030001100040901c1003262400c507010118018125080c102000ca0b1721100c85104a441810303005c91055070050003904a039041c50340140c43d960710f40d010003040d09104c1d10b21054000080c1e40c1040420441384020640355000c86024203400a42d441f8a6403c00048004001d00300b510f02072002404c6640d0380038010540a90b0282c0d110741d0f01c460500c0e0401c07151300e20121010f0700c1a0724111901002400503c4c0d1b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 907873812 1250 907872562 907872569
    0x3031005010c0317090102030a0b0a03020d030c0812013002010e01050a090909050d030509060c03040206071406130b0c130902030c0f040602060412110618010e03040f0815010f 77
    0xa1908150450b454291030655803809500c1d132225984081142401c0e0541c0a18400e400e079201c10301104a551040c008521020b00001e07400152501c1030340c010a0149440049403403252006614001000b4102c04140e8800c0e00050483c100750b5407118040c0c00100d102d00300300302c2c10f541030300c0c4036a40e20ba00191010526003601c6050140200301480d4140c0141081030081100140c284444001403624503140c041000c180c03030109152002003082034800040c4140314018a940240c607540ba55003c200864110f02c1003141c1c00c8801031008101050b040c8501c5010318400c0004c001c0350100380c40c011414010003000000e40a5007400142c1e4440a01d1070800e0842d02e01d068010b0b90303038070741d60800303a11031203208804484190300040005005e40c1c005201d074450b43c0511070011300d0041080b0101d5042c1d82e2480008150307030081e004202012a4042d90f80d02d4010117a000080d0f80c00c3c40307480c0b00d003075400507408046001e0b00910204107110003400540347c0c800130240341480759810000c8640030400d0900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 907875062 1250 907873812 907873817
    0x30c0a0908030c0c2d0d02011211071713090b0a03060f090507060e01050909090c030d0f0306120c0501120f0e0a0209150901360c120c0f1407020d030f110303100501 72
    0x441b03040d64020440404028449103050001c08420f20000b101c0340e0084004441c1101c40d00b0304c0b000a40404401d5a11107440c05800c4c4082c223107002003e0016005008030503074010300501c40080080c0507441a010900400c101c007244c803801d103040113400e088955000d0030a100c1c0c0b404802d10640e910000712120740030111091244c50310b44903141c0b850121124401c0790140312740714003210516044403080300d00e91820b980911025498081c50b001c0c0c0a040c0030020300b003242021052100d5070084540c82c2807140001e030700144007003207495401d0989420b44044070a580180d83c1d08000d43c101049020b500c0840a0a25150151284081124000e0520071400b400b480d165030f0122852230200741026100300b0221844c0003100b20f9003160300501d885000200404c10440a009495034580221420b4140c40d4484030500e1500b80c00076210504200034480d202c00041040100696034007040c200301c1ca000390b8540e60b107112040800381507000b0704449914958014000c02017100c88858980782078900a1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 907876312 1250 907875062 907875079
    0x8040303200307120929180a152415090308121009110306010305180604033b030705011b0807030e04020a0e0f0a0605030c0a0908030c0c2d 61
    0x83c840700f03004000340c5d20020700e0030903908070001410180a00d280c0d84146914414481500d492450101c212448000d140d159000a50000d001c2a90781060740c22a41d803040010907141c809400040400f50720b080c101200400414061020501c2da411380342400c3e62034240a10803074115220201240186a04c0001440c01300c00001d02c2041c0e03040b603d4006003004081440000f103041c000300c00c3c6400c11150b9500003450140010401d501c0111002e40541320400038040399215034a088030200704448410389025160f0280c41d07035140302e0400c072100d1000f40020031100040101c007018185025a48014100050146020340200d60919002d82d00f5600000865494800d858151584820520030036401840801e07008400f80e046007041031244011640900425080d50421030244041d020714000191700f800091042c1010340020943c0a4080c10900d411540c0c0c1c080c9649107512060a201d400d40108c1d0002707180781040c101002080035200c0d80115203112210309010419808195a8801c0122 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 907877562 1250 907876312 907876337
    0x2042d14060d09020604211109041203090203070b0f07061b2c1509090a150303081008070f0801180f12090f09060608060d0b0402011103040e0708040303200307 70
    0x5c000c03c560013020078000b08000750400e085a542d2107201c3c1b61042d1240c0002e151a01e1030381c40c03d40901e500c92035210a0510700212040011802015544d400300e0301441146000b02d07200c80b490000e000301702c1c2100d803116609d4449141c00f09c00d807400e01d0b20b554054010005182001c0b5000b4603e03218024001c12008003109404e90b087c12402c03500e004440e00f20780b840038110020090040104600c440a5500c9900343e110540100200c0d08608016903141000071428170000c1d1203140032a42040b18001c2070f002c26601c40c0e941c241000385135444824014920030003006054400e005469854a812fa1030440c6c90b06641c032210b060076000d000003030421030426680903180340207000c600c01405800d0000e007032803038032510945c0042041d8041d510100300c1000c0041c0c454900011011100795000320f4061064680f9401554030b034400d4001d1381c515002c10b10003c10288503c00c5801d00c5910240c0d90307203805060600300542201c00045d00409004108994604101440801c0326002045482c00b082038849 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 907878812 1250 907877562 907877569
    0x3060f050a05060703090b210601140d09050a1709180402013c2610032d111809071404020c0a1a01051009030f0602042d14060d0902 58
    0x29030011481f54001180007200c188401c50525104484a18071203500e88a0600540d102502e42c0b2822009803010400e10005804607044030b5410f5108808480200340180e882052220500c00c50007030740000400c60f0205460305209250328009900d81c070704080d0425030002001600b040c2500086240014a0104182404510900341c0045011040d15160a070407009000c01e005210300c01d0700f620341122009504941001070f0b40102c4680036a40356aa1656a41610720140710005040810054040503200032295a40401ca6481409203ca0b035820010400001c10641d0301101c062800c4c502c100070399140c002501000380d0704903d00e82d0000295140000740a40705c0c40350314050a00030100d8032010421026110803c078800700030604a260b0301c940c2800165054000900d0002d40b0186081010500e034116200c4400d001e188098a401d40b26101d10035000400300008260780861500501481000511000900303001c540400c2401203041c0051710b87d00032a1000c120305c039510b8400c40c08565 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 907880062 1250 907878812 907878827
    0x4110316080d0c1a04210f0e150f07062909070c14010f0b090604020c0a030f0509060c060702100506030a081c06060807020c061c182103060f050a05060703 68
    0xb0102c50003650149024544050301c4041d100d41b0140c0c652107040b02444150145030250303d41c007040d135260b045000e2a10200554400100e0f04010941c2c0104076500f1a18140340090010710300400010980d44001101842c0e4004040c00d00003984c40e25543e83c840135581c2402080d0031208528045040c0011800e01011740c0f40404a5200307203618001c02c60124030b09030340040f2250307007040fa001200355540300148801d074440c0b42c0240486030000303484000000d004088440c105045850700d03030304000f02ca5000c20f010740d0040000c0e02840e406101000a0240c2c1000b0a40300e8501256003480603040140120340e690100110042c5400700225800e42641c0c5148444600303512403500621a655458102400ac0b00302074550800500514602c0b60140c2000380441c2d00c00c1e0780b000f4107078081110102c0f03c18018069403200c103658941d407050300d2011500c40ba510030011441e400751071010311820344000e0100d4006500142c0d4651800004114a950300c04820007215030507101c256445844e4a811503008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 907881312 1250 907880062 907880093
    0x90406050910050301051e0115020703020a060509040c300e100903080717180a020411040611070506030c090d050f0303070306081902040c0c0b04110316080d0c 70
    0x21408200304591084604540c0b01110b00c15002081640c4070f242c3d400c40342a0301c100142c009684c3d01070042100107031480044004a00c0c0c3c0c8103545019803680d0004514000990112000440102d414100b500e030901c201100d04049003400140025481c500007070701d8540749464161119a1000b62402041c80c2d00034800600e00c400c19101c0d072408488881c001401d0540c3d060300000d40c03070400a40d080e40960807604080c2e084185900e003c0da501110000d000c8000b544420280c06140070b0a401610707903000e540580f464112202c2d0301c850070044010400c0d20072000c080c2a540c01a84100b044d0348481e4101c1ea0810842507103243e0710f40301c5401040030311801750b40003000c900c40c4030010100b0843c04030203075000d0300a03a5000d000d8640e80d60b802542e51444040d100344681c0c8040662030040c50a0340c043e821000305402c154402440310f031103d102780c06003101e06483c10008010509018a01401860526141840135030030050911100b03541c0d0301c40007082603082c0301711041402c6c14800c22a003c400308 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 907882562 1250 907881312 907881319
    0x702150d140109020c120f031b040e04050601050f0114030406090f050a1109060906300718110a05071506170d02010b040506060f1305040c0203121b0f09040605 70
    0xa6503500c4120100a50203c0c2c0800f5885c054a01d039488064006c85c1107904c0d4a20314074085096803a45842c29070f100070b030b5405c8080404004c010004080c88074040c001c1c8150701071000361003250b00d003200f403000d44c0281c40140d60410980e2001c12884900010550f50070980160000039a0340d114038000c0c441d89541c140103440c622598071554100301500c8681449114192000b20854650034148001e21070152020f42e801040d4210085000c0c01702817800241d00300c030348020980461001c00e0301c1d061114940080201e641c0d49104031648036424051566560a01d604003842d2110300c0a0003000c0d801070150041070104843c407026848000d40c6c201101070940072000c136441040b005481030396000801c8061015500303084544850b4a000d1082034410b0310003626051030600508441d50b47d5030f010706442e0101c401070420110f004d440754418199950b40f1600151396400d1002080c11300f00340c0040139952408041052148040310410a81d1401240060361a481f0b41190380040d010f000c0300e4109641 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 907883812 1250 907882562 907882601
    0xf030605090f0a0c15030912050706090206030112020f03120301060f260105211209030102040906030c030c0b1e07020103020904051f0f03170307201b060702150d 71
    0xa00c40306601300421500070702c2620301d000403180303c00d0703040c1c40244402070a8a04540703211294140220000d140252103000005440c8140354001900e5400030303004040e95990402544085046c440500000c482086006120740d400d80c1180710798902c0140034440402540d144621142401050310400c040352050b0020005040609609545402449164440c000280d01c415105910368024070342c40e000d06020f00f00c4030040b14000241b5a2240c00042c1c0c040d036003003000040700c140d0752090700d005d503108424a592151650801002c90482d0340c1105104c09070400103260522b0141e44c0982030704e0b5000007116181c0e00c490005900a00591031042c1e006070401c42013044041c5101504880d8406110001032500c0c1c445080d0601d200790781c08010300406000c0d07808900000c1c11400f03968041658039004003100717561111b07600c00d0480d01da40008a54040b5440c080e45d5844054442c1c0c5551080d5001c03410700010350006180074100c0c0500440000300010034111a400c6a0020b003030a0044950084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 907885062 1250 907883812 907883833
    0xb130c0f06021b0103022701140409060503060c0307020601060c030507050613051b030c04020d02040807230f0d1212021303060506061e0a031b08040209100f030605090f 74
    0x94a0b021060301c00709450f4450705a0f207001d503020384280d030309108511490108906001d150304022007451248681440a10000c10380710209000007480a0119564003082031494681450300d081c001511a201c540030a000b0807842c40d43c006001030440e809450100c844d0480c0d81415581031041c0381001e85240580d008005450703402c901e00141981c4540100c82440c1d00401c1c8840048a000a41a0303140e00540205406440c1940242c4140860301d0801403a10b5079034400289000029881041084400400b00240801c9a40e010130b6141c02511060300480012000403602d00100382d0041c41541254002a40e0300e215455000b000d0f402c0260456445403413000084640c6400e100881e1a2401c1000260032030400d034060302d0707074000d40c0702d650140c0c4510328840c041d042e000000c0040806640d01460761548041a0b5011035951481d2207544545c1000e0050245040e0001c00301c01070040000010000002c0143c1e15100f26a001440011551140d4150b942800c0754071b040300b60103100d181740c1c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 907886312 1250 907885062 907885067
    0x3241305060306060909121806040609060306080a0308181005090307020a09060b0a05071403040f090b120c0609010201091505090708010504020f040903051c0b0f0405040b130c0f06 79
    0x350080d1001c0701190321981e1100100136615100f104c0d9a6400c1d042002e0400702c82d00e220006d005403011682100441070510400300e085604030303a1060001071000c1d00c00b0400280c00d44100002b1b42a1240070340b0302c84416441c00b42c107114000d042d0080c4d8070002c2001a840c082c060040c012584143c80050059081512080342d2340d402010040c2d2196450322000218800c041c8550030444082440e440e0070a41002420345564010360425131751041ca45900c40655a010700080001d0030444000d21003142c00c01c26411f00b11904511074500500c112a40480245000588884114011500c49070369801c030b100100e000d4810403c0080000b00d807185000e450f01702c0d82e00f00e14820721720b400440304010f6903034a000d4240d510a54010b5006450340740b81004504042e0043c030341c1240a42403407440e111b00700c40944a4010408071030800350381e6a001c12896071908201030700d681002210305100e6410292150310b00208050719400e00d0312420340d1400108020262004000d1482c010f030000c41c0c95603820003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 907887562 1250 907886312 907886321
    0x702130501060f0203070c0303110a12020607031109010c1103121b0d0c030c0611040e13152c0c030a110a0609030503120a020d0c0e1311032413 63
    0x102c030045807014109001091000043c0c49070310b50440c4420545c0d03491911700795402c18140d541c500040c04ac240550020504040881001540c55801020240f80c62007000f400c50f044442000c0981508014400045c3c0e404400209416040340c5103101661881001a241614540c0000b403215000316800c17130404100c00d03038a241c0c0d00b481c2040d00d0071b0184504040310200315402009020911109003540070400e03a6110030a412519905107140035119041c0782e501c00812901d000203600401e04100c2000310000044100a51441c030030302050300305054140540a44c140c40c400e04c624520007030803043c4010007640c2c5e100c08002c0e0130b642c4010010700700b001135400380e1100700307010b0754000d0700000303030503100d002854204d07034014020b181003003030711480d8a41c14038000d805007221540a018102a000c0103100345061849541c13650313440034046809001803200d0202c45441e1140c030b40f50304040031355007800489071f01941114400d00c48151100903a103400030065a8207800000d100c51020304801d16600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 907888812 1250 907887562 907887569
    0x309010f020c1305041b0308030708060406030b0405160b0306010c0602070206160b01080f1902040e0a0b1807240c0302010f091202151015140a0306050909071d06060702130501 77
    0xa500c80da4060680b00341c486c100c5075210080c0550070420008848070f20a001d0f09803c010000c002180060743ca44400d055400243e03070a4445800c501c05110789040c0e111010802083d0b0f2032085821481c0040c00a00071800c1401c010300032139000210042155281c508aa0801e60211074488440041d03080080d6296001d00480517244113503500e42c07000c00800500400d2002c21a03212074040d04456090002411802060318036621510b0791540004146015051180c4042d2003a081407c46580c00c440c68503031079501010359006c90502e42804141c0c44a01605900ba150401d6000d41c1c2081c6002c81c018203003441d90001e007131300c1c01d180c4400b002407505500024280d03036821540340c50703e07228544c0b000c000d0a403803032440d5800c01002004950701f003002e010003068241c240400b425421545002c481d40c81014002c00080d500c0300107001d60701d0190400d51300314034000000c00160341070034422080c510380161094040c1d16048000344041d80c4002c1214203966024041c1c0c0020160001ca031000351a0030701 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 907890062 1250 907888812 907888823
    0x90b0c090109080601350a030206060418020a031b120303020715021309050a060b0c0f0628150b160b070309050c0d1b08070e0115020309010f020c130504 67
    0x540c00a107450700010705505841c031107034900a20308088581c0d50a000d006c403611030545582c142034042281c9007401403040140c0290090304040c0380c4401000300716410064182d030115556444040940c56018242c011f6a0703001440040c044826040070070014000c0e441a00402c20560000d420140d0540140041c0c1b03201d07022100102c5091211442a8040e150688080c0c2c0c0707021004014034005900541c0e040307001b0110010313001d42c4480a00d8415404590443c445a1201c0351010b2140c00410140c1d0340034035040701c0a4640000d0380d0302b4150709010403003030340a52600e5400b5001c038000702d403095000600001ca0300c01e503545004507071441c00c070913010400d413603403d41c420000e010355009005291300366034004003911040b90300100700112000d04c0310043e42c08001020713854140c141c40003603c40c040c102c80070041c1451803800b2400784132440143c002010701d0b03080c158075040c000d4002055030351172030090810401c0b4602c948000c900e88641507404550024118002c2901c500017a80b000b80038a0140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 907891312 1250 907890062 907890077
    0x9030a05030705070f060c0609030e0a061806020102071502210711011a0d080f040f240e0609041805010c0e09011d04020d150606091401081b0c01090b0c0901 69
    0x790710b03017403d10682d4852040030400800301b100025455030b008824203440b900340002071140c1ca00200350141142c6c1c03c044080f41d0b03100c0f90001e010b140040e01c0402042d01d41700a500c2c140003983d03051110124212050000340d0003050303002c5101c0360103802d922803040004100c5001d1820000040c44c4440c1c4aa8602c401c2d40b9158404190032016030121101810241c010700640542d40d45140681d848159650802c040074070000c68100181e486880041041207a004032401d0400d100c080007400c0306210205011200400601c951a002e0568000f10300469002034050003140200504150402c402007082d441d0800c1c10a4190300000841c501c0c1034160b500c0d00c1d590782c0f40c0307140323880221000c211030490385680c600003001031515140c1c4503001440703030340040440c01070302004109a411541001010425801c1c0c107110b4000002a44446c0501c05d1034107a025080906103010784814107010300c0b4444400140c0f02a0131082500480c0009134060a890340070301d000300100e40c00d900045001c03800181c12 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 907892562 1250 907891312 907891319
    0xb070314090a03093012090807050d0b070c0f030201020d0606050405060301260a0c050f060306090c03090c0d0606081509070b210a050103060b0a0e0c03090309030a0503070507 77
    0x14000012a81a1207070b084132030802881e049440e02c840700810305096900d10715038000ca030401010005621500412180d010100c1019103032032002e4010179055844400c04100ca0303070342c3c1d18410641640040340d1000710b4503202400c5480b20f0b0000c0d005009002c080400394201030341507004008416408004120705c50300c4403021610f902c1a4421160310080070300040c014a0703220f801c1c4007603289000c903d0040154100c04103a042929040c1c040c4d42010800d0010007e908102c0b156200c0d45400700c40d111700d50700e402000a0001e1030040c24510054002200003140401c040026500105004010000c03041d014900300c3c0242c1404d01410a0f2030143e40842d00761007980051103405a030741c0f10098290b01c1e05041440c08aa040400354101484a00781404181a0540c4059009043c0d2990120307449d070541c104402655000140c85010382801d2104101d41051700031050b402452540d50f00344c0e80c2d1694010107145000d9408025498021038404901b00440000140f2041c9e114800f0748008a94 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 907893812 1250 907892562 907892581
    0x3080a1112061207080f061f05030312100504020d05101406070b04020d0c06030e010c020706051611040c0914032a030a06020310090f06061b0501090b070314 69
    0x203405200008902990206042c3c0c6040c0480e030075407404160845441a60320480d080c0b5017045200200c140d030b001a0709000030442d103120f03443d0080300c8130310f8024011481d000100365641300381031256050300025404501c1c0da040b80d207482d10080400510564480301d80003e030b40000c15040d40c0b80202c003160324038009102d03050810803288420006003030a0400071607484a0b140d03414014000c0341d018650b1018880010880d2000344054100c40e40c0000fa0403d0302c401c600d0844400081d444159400041c0400000390302c0002c5603148142101d5214410b145450010748030b09400e594183c0c4282030924030108c42c0c2d0700c0031115040f614001401155007001c80c01b07240c3c45007a01074041c9401c1c089085088150301e0070541d0207460395003750454440a456440d030004076041564182c5011880840400403503445000b14400740c0d44142c0200422854054040d01c09048100300790468034441100d0020300c00294030540e2801d4218504442138900040010000c001c2914000100003034078011401c01e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 907895062 1250 907893812 907893817
    0x24091e141c02150702091611070f090213050604090b101409040507020c09040b07020d0201060e010e1b1201050901140a032d1101170709030312020c0a03080a11 70
    0x10801e101008030040e903001d0240042c4200d6441e44242c004200ca900142c03503c03c50f0611646140071044605501204001c180500c0c021418500d070340105000e0000c100f003100790704115540000c0042e81e0750041028886e02d40d42640c05075070f003c040403c0c0094000100d4002800565048450640c2d03003091400503200c40c03410001409c0180c3e428041c022440c1031582c0082c0e0424503030300444000c0300e201e10004100305d404440c02c998075042201842140b980410400407419458002400351a0503c40300e500e6400051180005030455400400c0c1c0583c20b10303800d0407448154000301e507610001c00100000e1b15000b03108090068941000018400c1a0103400c8801140020030315180c092031070319520041481c0c1d54407100025900841c3d000c84540039181c21200c0d81c4556100640c0c003400f41c0c0090821000e141440d00764800e40002c1101895116503200103496040c10440750003136220400100030702911021104920640d50844e0506401c655560300c02c560300c242c10702c6003e1609440e1007560 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 907896312 1250 907895062 907895089
    0x6080601082413020d03090902030907030b01090e0a0b1b0a0216060c0b04110609030703051b0402090117090102040b0a0e030705120d0c08072f0a24091e14 68
    0x1415440703030180c014680300c4502c20005c1d01034a0036514803074603208018100c0c1c1c4141c480c1044ca5120850030003c10005090306801001099420051506680180c503100c112814005251a2001d0f00046401c406196210b00504401e01100d8445021076406561903001056005080d40f4482000034024820341c40c6c00c11444d402141d12529480355980c1c60038280001c0764040d841803051100e8000b541702004600c0045014000812000199280d440d52943c0c14111007802180104480f43c11070340c10900810318003840105914007070782c40a2a10f80240a6a04034500e48600015203007a400e81c06041c031884500d0480582e9100c0ba61001040404c000c0042100019000326161111040c00f030041000258004e450b905d2820390256181c45d21144503a9605003250910380720303020345403803804041c2106507054860304280c40c00e10300e1006440c464841e010414000300074101940c64403c40d144001048500c82140f0844141c092403030405141c3d02407107800380b0100c2046111840e01100c1080364 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 907897562 1250 907896312 907896331
    0x7030c051c080d0b060a030605040f090812360f1c050a030b03010c0512100302010903110f090f06030d02030301050604090e0a0803010e1014010e1003060806010824 72
    0x10980740d40d44616050700f003108091001a0b40d00203d51450b200da00090100003803079900016114105400c1200f11104113404e440501d02d003502500010700070720b00b15800300501141c42441580d030086070310044500e54824114402001c40503440307030302c190b0306038805003980c0b07409565491007801c1d0540d56441e990600d03007004020200300c1c00c2440e409100141582d040034a8085106581100800c0c00e41d09504001e00024100094010501e10407800c0542c02825002c0d07010b40d56441c54000929a00c048c0c00050448103060604c01c20301e40c0d130403044411100c80a400d001d007902e0800030001c1141011200344e4000d018038803040010520210440e03040e0f84006100504144c02c0a800030300502e00b603d030501c014820390410402280583e4003940c000c1003241200d02036032801e000f01c01c881500a900144284481540e01240c5a801c8004840800001e89050886648254044001e81401d601ca83c0c01409400004118600e0214000340410703010311000311591101c0100c0c4603504022150212b2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 907898812 1250 907897562 907897609
    0xb15160b06010207050a0b0a0e0102030703020d0509010c02100e01020c06090a1404020c070b030108070918030e2d100801080304360b010e03071a0d090f030207030c05 73
    0x45500304401c0d081001881111601c544500108074104a20340003010340103c080740c00c3c0300c0b00e81d00105a00342c0c50b40a101950a044075568040d50705c0c000398040406100012500c00c030107034070600001080d150020030704000c2c4800030038040c106201400009005010b0f407421035219040000485413261809031030401d60514107800c23102c04113040e82c01c0b1503000d03408000b52046207808100ca14040d051404040303907030b5407601c4040d52410301240d00c0400407a0a0818110f00341e00407480c00ca2a094041c1440850040c00500241300c1009148101c1c203d4001d0304000070001c1907065003402420000e0312450354108020f00151a0242c091050912030f40c001c200074401318ce015525207401c00040003105e1840e8107c030040c00450100d0180d00850316070303501416900d56a2010340c144981c00164094440035040240b07a01126030100000012420001103082805100d030b400940f000f500319128400c100c11361300e00203480701140e203c260707209104400d0209080c907090305100701e0704005401002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907900062 1250 907898812 907898857
    0x14030307030e1503041b05010f09150c15060f050301090c03120e040504080334200703030507051011030a0b12070816080109110906220b15 61
    0x2145806040800d640011900580f281407104100203140618031400342c1d0040b02c9200d01c14001840071580c0624100510130480184254004000b0403e4070701c041000d40c61f030000b415003a01e41c1030031440c00401619088121642c010f040e42d1111064078811059060700598501c10507007a00c0446c0d1014000c0452014100002521644c0c1c8206807030303041c01c4c07904403541c048000408856007210140c1e80b401000040202c5a15010700700302d11170704070641d540840341152203000301810802d203a600c1400701c070121508009611b80c1906034150300b0401210081e80e100e24000740150001e440440d101d1140c0c0c0d80003960035085002e10b06441500800140c00c43d0764151204000d0140d030780741203800840c2c041c2e01400000e4180450009083d0150080500b2a00d0803804003407104658040441c0d80d1409850030009051140c44501010302290715030101e440f804c00246250071070310200c0c108594001d407810001c3c0c680c3d4000208416044818648402c110903001d4240d200c1c41c500c40203444802c80e1188c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907901312 1250 907900062 907900067
    0x240b25021305060d0602070f0308060907081611010203010f0807170a032109060b011e080c0c0c0901180b060405010c0b0c0903030706091412190c1a0708011403030703 73
    0x100e03072041004113041c9140c00341d03071150b800b01c7c0e01c0070030181c540c14001004842416000700b144c6c0d41001e0f00b560209240d03e4100b20083c403c00001d04400741c020301800e400765055110309044502540c1c0765000b1581d81d6510b00d9a5010380010344035942260007500400684054881c0d05090741c100314a0242c0303000c0300195001c491031404032002c40850480084840b00d42c5403644074110200e417084200007519000080054030900c2c2c5d40c0310302106c07080114441030042e50f102c440f854110301440750305600c50800f03022143c20041e01101035508081b0300303c00001c1c2034203520041015100d9044d820082004540c0c280f01c110303c04ca010f01d60114031524504000180e01c80400d9a02c01c00c66498141840809030002e030071980b100c1300c2920440d13100c0000809000b807040c07000c0c2461801c0f10003055051340d42c41e1000130320f018200d88992a08110007000c884180075509149046500076045503102501e12600000b404050726403000003100c1200200395905019060071051000400550910301580d904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907902562 1250 907901312 907901321
    0xf0c0a140111040608071206090506090f0105010f03020c01061203020d1d0a03110301140a2313020904050c061207180b0435030702030f0a0213240b250213 68
    0x25904002d410b10041d0001c00c1c47d440b501c40038000c6500085180d0401008009803d040030b003031240c030740c024040100312584c0c204e401c6060710165402c0142e107590201810300d00405007a40600605020b01100900309a40030550000340300103501d646003001482940b421845900c0550b03d6000b400204050002c51010800054040001070000c54030982c0754028102d00c1500366140725005440c0c0e10900d24005030089144080d0414030b008036410f00e0180192100400704840281c09112844081014000180f111522668000d0300310750303503108815a0380c10340150460302c40000580710f00044000d828111940700845040980c41410903060440c05e00c01c4040000008401d8005254644000041c800c011044948450044c0d604c480140c014141442284103035101941c1002e06603500690340c020030700420140d207080015403407003000e0010ba210340860000046110b51200c0000f41c01c00c1d64002008851000c1c110f86011075903000341da6180380c40031240203501500b200002d00380300d40700b80e00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907903812 1250 907902562 907902571
    0x61609360606120e0a050613080f030c070b01120c0303110c150a0801050604030f0f02060f030f09190c03060b01090312030e0111091f03020f0c0a140111040608 70
    0x65800420811051010450781c06520041c08103004003540c8503690ba03076105400d0b4200c081c0000c0c086039011552000d443c2c07040104405001004442d0110030300814a058031200c4003510302d8140d0382e0800c492084a15049040200da0b071025110001c6810519060741d02c80495021100140c0d4070f080d5a41920b040504c0d02080140e4861800d01c0042585c2e104000d0003203c0b40303075180319a1398003196001032070010146c00450140404100400001d407410098001c155004200f84a1041c1c036440011503030300c136030610f2501804021042c001c150b040c445031790f1300406800c401c0303030014401d0800c014401c0c404150060028182411308002140d2030ba000701c1c1e100c510524040200c0c680381e030748061808a420300c818001990380c40b10030501540c248100c208510751812140d050500200014400b10382c1e40d62540c54500010b8010b1800301c1c0250145e581040c3c08014003074030341703032480d03d016601c1081c0304081d00c0c0400704a803080e076800b2041c46000b42442d4200b40c80d03460541041416181c40f0000f42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907905062 1250 907903812 907903889
    0xd0308040f05100911030f0c0619021005040b0910050c0702060d06030209010b030406050112021f020a08031503070b09091303140316020c1206060d031709061609 71
    0xc3d901e20b0076285a116080c00f5038404c80c6514003400c444000e1500d44050706a110040b9440b81080c0021983c54a040e201d0480d902401702c1409542c69000700d00381115101011b0595051400703000400c00e041d424140b1441d002001c85101001c02041c5105559040d9110800340908000600260800d100103201c04441c4c3d000100300103580354085418450240e0148080d01c00c04801d1104200103400780c0c60040c0321020000c084200b480d00010005000c07203080d0034007150750086070442c09000740701511485800002e0f80da1280350250408960080814405120b4000c41102007035002910742502c25040029120802c156200c04050f040320f0782c50103084e014022250303524a06a95010000e5119241d1504610301d81c04401070085e10744a400280d5500c41c0126102d5202c41d0340c80001c0c500e500240864000e05903e8542c1001d481c1d05810b05208045030461300c08100c0031b4070340061007074002c0e80794020350049a0050364048451170002d029400c0800c0c9098000750301c14a00031840544001c040c1c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907906312 1250 907905062 907905073
    0x50d0b0f030a050d090905190509010b090711070608010b0904090312020a0201150803090d030f1115070e06031012080f0a020a140f0606091510030207020405060d0308040f05 76
    0x140024500340160b00c0480710b55209188004c500c640c403420050080983c004240103605043c100821451402d050b001b00381036841c000114280c20941040203a00c1c40a80031540c0b90401400080c01c0ca801141010320b588903841c40002ca85214104480c125085c40d10030303904001c020030802c03016002c1000e05038104110103140c050b900340780d480107100011013600001004c1107090002003004c041c9a01c042615003080c08441020707100e588144901a90510380004082e82d803080c01e4172450010b0040c0c3c03044e403003284908062070924045150051a440c1c0701c2410048400c42044076912046910001e030302d0180d081004119000002036007844c1c412098035040440d00d10080d882034201068900044e4003c41c04202489206060b8550500218001d440620348111101e81d0f210030241c0001e016022100c00a181e182c5825100750560b5801014460421801040280a5042100c05912403407502000c202e880c80c05064551150707a160316030201c282c6e00c40d160600740300e00400099a050155 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907907562 1250 907906312 907906339
    0x109090b121203191407270e150603091902010201020d09050a0605071b0314042c070302072a08010e0a0b090c031509010e070b071b06050d0b 62
    0x20b00c07081c699030800d50b03507040e01e0f071400c40c1c05500c500205054480f40146850704001c91001040511680b040c0641840c4141005540c0c1034040e404028024100c80d110508010482580400f8614080d818201c140070b00d90340b120040054602c0305a0309042c0382c0d0300050000d16049031321103a00002d0380c0140001070a103070b1040d11450659444590446194004820400400c0418402c2e16080030840c504001240e003107211a81031400700050280621030303003291100c06031240c08200d4010342080c0e4050078024103903002c5150318000700c4c84068082c001c0040028001c034440c1c03007901c2080341c02403074400c03d141c0d82c1a400b914003004401207d03091489500041408a800d01580310315500c1c40c001030143c0505820212203030340024040c0380554010710301009640c0d9000419415900c1400566501c1e600c2d00302050380100b030000c2c5048000c2c004c1c160000740094100c40038121440c000d0402000080d1781d0070ba140c903007800c24012200420303018058030102c138801d50b0084000d100040d089000a081 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907908812 1250 907907562 907907599
    0x14010b12100f0f08010e071412070504090b3103110f011b0f080105090a0513050a030c0b0c0a080a050606040f0806010521030306132d06140109090b 65
    0x6a412107483c00c4009001003004450910810b000040020090003080b400c1c5601944040c0c0c07840240c40c0b01d407141074503004105005116140050900502c03c000500c0507150500c1d400c1411140024000c0c2d8200c2410030190604a040783d242c0d4654603108264500d581d400d40342d01d801815150f403548603030340c000c46500e81c0901c41c00c160201020004406040041c800900385061292103c042200c420010441a01c070903441a07040600c400c1c002c10039541d94030040002000b012409130592003140030304814103030001d02e10700c105405080510803640e220940300400344980f00c840000182044001503130000d60f83e003c0c517008200105100d02c4d06684680c0c0e0001d0445580102c0c803a500a500100114a403040c4101e264030305200c0307404012007503840380390380b01e0000520b2039000c0c04021041001c0301c0700d154030000d0452460008a08951b001842158484210301520322503649800030209880001681010301000140e481010f0346041594071406410008082c0d40c0010819a400301881c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907910062 1250 907908812 907908839
    0x1903091e031e0e0303071e1b06090b030903161e080d05070309080f030c040512030702031b030c0d0f080a0f14040e0c070507150c020414010b1210 64
    0x303020b580c2c1c1c81c2c54516000b041c4200e01c108502c2901c148030409402c101d0644000c4295680e1580004008407128034106070064015400ca900401801da02800140c99201040d40c4a0907510356a642c280182e4940d00980b5452105030345009440d4000c0c8506d14600801d6180b91440d9445030074030a000701a582d010a5018a410f60300310b50101003c1120741c3c070701559201c0c89500880d01c0c40c061281c0c0445442d0018544103a1034400500380002002030703004c0000000700c0c3c005000c0500207441d562985801107440b2341084d02e00703e1007802603c103ea5003580d2840c1c00f0b038030b82790f03001400352403042045000c0200403041d42400303c42d0b100a05100d0004200003130058a04000980c543c1903102c0a0000020f091034807107045180d5040341844180283c0c001030001c01d500100140549a0b940b0090821034640111584540c5508541902521000d94080d403002482c5100b55014072240c201d85030f80d020060400d00901c020018140040850560401c031220740005075210302654a03601c0324540440031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907911312 1250 907910062 907910123
    0x90b1b0f03180a030f300c030f18121a01080604020a0602010608060f0c0c0a080d0e010b031b0105210f0a1505040e01020c060a0504110105190309 64
    0x241c1000c2030b0100c071200c0c41e4010045000c030031283c0c20b02d410b081d9501c0c01c840d40d03030044001d0480c00d0450704405000707582004040c400c9480040d0b0860590f102e2100810860054108800080c0c0810013401d02c10b00500c0c840c0407a642035443d401955041c05101a60050b501c03006840c031618084201582444200700140070b84a204040e05044c034042c018440c4610f963b61140045a1400300304020100d00444c5964004010030098100d0740c44404180300c40c1e01442c0c4c10125140208910b0314200080c800c0204083c2c0c003040e0080c0710300010070070428200c0d050b018040f07070940c10401180108005005100300c50382d03014180b060409181b260248480320b0b0382040c1c40c4204003880140300c028407104807103076842800000e0501000ca02c000315100001002d00c52a8059600e40d01d20600904007901a00c50f07100c200d000b143c1d010300d021983c800c05020180c4090342c1c4c920020300801441d500c603a007201c03404030441c992041c43d00d40440d401c900502e0035000c269110100300704a41c4400a4992000484 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907912562 1250 907911312 907911343
    0x20304051906020f03071e0305071a090d050f0405240304030207080c0409050a0b0606040914060a0e0103030c0f06090807110301050619030f05010b03010203041a0a020307090b1b 78
    0x16a0300b414400392a0a03012800061158001c1c0301072130000d41c503403c145032501c1141e4003081400c1e00174a000d030340d5801a00b2000348582201740f040c20810301c00000c001d02c03500d1560111030002e503000e981680c2c04d104400c400380b468902080107001d0741c145180c9005007205100a0043c41e03d400140c41e91860b0401c0e10200c0040e04800c2081221241c100f01b50102e20b6405c680801c2500c1c0540d58880e60341d03c00510042512000000040e450364500c4240c40007400710740d1050024040c058000c50400340304441d014481c603600d410100780401c0c81c00c0441d050320b6058030790008013a6640ca039110b4030050302c941285c82035220255400081c580c003001d080d21512505208040807402c00c01c00d0b0950710004c0c4440c0c01503a04501d031000c2d60080d02c01040480340c220403c080843c602e41460341c0544007201c1c10a4046d1b0001003800b0401142e900400f45450480c03c2c51941c50725540034003002c4c0d1009460a0300003880910090001070036541c020111812260210498010441c00c0c40c0c0c02c011450750f49444 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907913669 1107 907912562 907912609
    0xb030f041401090c0603091505010f0b0c0f2406040b090a020903010f0606050a230403031d0901030605061e0d1112030c0106090b040b100f02030405 65
    0x10004d42050071114603503142c84004d00a800d01c42c03012113050714001111443d070200e5210f100e06a4031400244142c040c60444856100c0c0c0002108280714054400205a844020401c501c2c1030381c2032400315140030401001140000800418042c05581001101d0702c82d503490b40035555000060440041c0c5495520000c80e005081e40c260050149140000c041401d41e00440a00228a1103644800741c1c2560314007050600c0d402081c021304120024081030001034040e00350000c8110404140090395010300300003902407207081c1d0058550320b50754401e01c281401c2185200100403c03900d0700c1260f2006c00c801050b4200c211072005811407141c080c0c40706440c2d484040d034110220703415040f01d03280d400099145000300b2480c81075414076403600c0b01d5105a800d2a0107111003c03100100084424490b015099032260071284000c0d0850004000119907507544c040c2441c0305031581920f490 = true := by decide +kernel

theorem cover : BRFrame.Cov 907733812 907913669 := by
  have h0 := BRFrame.cov_init 907733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 907733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 907733812 ≤ n) (h2 : n < 907913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
