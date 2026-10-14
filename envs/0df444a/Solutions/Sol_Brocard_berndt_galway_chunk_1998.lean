-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1998
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:24:54.576762+00:00
-- url     : https://prove2.me/submissions/ba5e1682-f7d4-4856-95d3-9a63db0b8874

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359172661 ≤ n < 359352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 359173911 1250 359172661 359172673
    0xc0703050706030f02040503060601120e1009050708160306050615040303050a09090b15030a0204090c180509010b0d0b030f0f21070803071206031a1608010503070501030902120f010608 81
    0x81c0c41d01e403d910881c047e16030141d10600104802e54440d40c3c2007010280314400010f550f9009a04080c1030a2001848208403600ca03200042417000a111b0b0030014040c5000138030b11001456030003442501c00e07100c05000665039800080c036980340d40000c1c103000c2c0101020165169140d103406001a084001c05000080b8400d0021a0640c40744c8103030a00f0700380080240c1e0004a0707103121620598001070030450391940a000003d2100d0079405000f001c03802640f20600c0400348045954449881a84691300ca0804500100310505400007102e40026541c00d0228000c20700c40c011924103000504081001e1050140f80c0e407500d400400c0301240350302c408001030b40c50800075050004901916202400c1e154040002c03600c0d1600070318040380c801d65100740c0400c4440e500d840b80d54070050804040340010145c1800c000f88102d80d0001c3d0585841d4a04240c2c0f15035040c00c0c0402d5841149003d0382d8107140c0d40d00284410b5555513010b429514980340110b070905034a4100705400390980e4401c03441c0341d01ca80303 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 359175161 1250 359173911 359173931
    0x12060509060c04090f0605040c0e0306090105010f230d030905100804080a0503090a0f0f060501080a11060c210c06070f0c030c0f06020309160b0406080a09080c070305070603 76
    0x8074030240078003040034a1504084c00c10301081e00130071141904000c0d1640e208030000c1c05498502640d410800141c844210201c2c21000385800c2074001066403030b040c0d00d41401800b03c00b40003a07e0340280c80800d101480076541605181d16038106070741031541c2c010304c1d1a0341c00c4101544a040c81090740c0d800d44608042080d05101030341d4045040e0b800401e405018007002004c1441403003d1039014004c502100e001030320320b41b92002c1c00e402e8441c0982d000407003c5400c906000080c000d050061411600404902c0c8a50702d96060586a40981c50f2003580006441452200c0410104690030803113400c030095200440320f01556503014494074050707401208000b800150085184810070700c0147c0701d203c00c0c41c0c1256800c4600812420044070f42c1da20b603c6424000c40d0f0b50b403000e94428203509000340207801d420311108008207205e61110507840d4040205001255008030800c0d08440345c1000441c2c454028540802d20340100303001ca03015885441000005d04c40c2c005142e404036011920204442c07502 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 359176411 1250 359175161 359175163
    0x6090504060f1a09060c030c01140610030e01020f0a0c020f04020405090a09050111031801061703070816020301021303030f1409101e09031703071707030f02030112060509 75
    0x303115140e0004840d40b03040084207000055020049002c64041d4a0702c41000000382050300001c25080d5185e201082d10f039140d95092080158913408005d5441d028900b07280012001580c00001c8001c154071142c0d030a03040c1609405560000303c040d0b000c280c45503c1c4103c0180190440704007684074036221420b600035810140f00715025142c002d081e04d4125070300c40e407498002c2d0005030703012a400c0d96101001d004070381e01ca502175801458020700703425150100501290035036400e50480101c0741c0e041c58001010102c004100c88005911043d05c9407284050000796001c032411080103505540001899040b06001c18041029170340701791110070a075a410381c41210f0155502202c0d0309a040304210308419481d0144560380c0c501504e151100301046600308440041161450450101e00480d2040c41006050f035010141c41c1c1c2d03410003041c214a00506c0080421030b03000d190a0070f120107600850105031098000030b4603084120020b6503296502c1842152072188800d00746d40141ca4100480c054601c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 359177661 1250 359176411 359176421
    0xd020a02090a0b060a050f0403060603061b030501080d120603020303030112030206090304080325060e030d0b040b030606010305100b032403150a320609060d0b19230106090504 77
    0x4d080356040158100040d1429800980e4083c21140b0508c000070025007980075040185119000c0400d00900d0402e83c5e03001c4040701c0e0064014503040500502224000181400d881196441c14045c3c0c6c0207a60400701c01020503420194150100000124078041c40c18080c040c0c1078426402c4400700d42c0d88544044d00ca015501421035145c000f08169034030303a000000108260700f210324a40c208608566076000c00c0b00d06212091103a9080401c26907040c00ca548601c1317a210308162000c0c480400c0302800240c07034070002002581419920380100e124141150811005800328424855480c00c04106594510320b100c1c40c242180d8040628400250401091100c2000e08108c400b41064940c422040007502c801c1c3e4a011080048081d80441c0480220981c110300840003154066400c2500c107014901034002e200d40e0080c2140103c04000940c41d144050b440000030181d04494191000c8c4880940112400c01e542800300006144000c0c28004945040b04c0450302ca071102c00c0e98860902060324 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 359178911 1250 359177661 359177681
    0x121103070611070501050a0e0303160201020c0d0201090308030c07020d0c0e01120f030e011b0804030b0f090d050702041401061e020d02030901030209030a1406070908070b030a021b0d020a02090a 85
    0x1030400f900030030655010f20050a004180c074100f0710074184c20780000c6403560300181903900802240d0200d030029540c0501c2115081c071404e030342211007412240c001901030034041c4001054108008006485400007209032027003180d00030100581d01070141803468050405020f0010044000800000c00e054400b05c0c5e80505540104002c10100003504c00307483c00f22800da03945060060b00892525a21907444080c8412481404500d48560642c204500216802002000c2c45050385091008100d40010401041032240c0744c041d87d254514404240544076143c00001c0c4200840e0021801e0303600b28a403005181c0607401031407001004214105d80d142c650404205c013507001000100170b20b51084d0000c1a403a1380c094201c40300c1048170754400b180000e8010f14600c442c0c00041c180140c4036440108a0010b200250081200c54103184641d5010711001c2d2064841d1540019440500015854030150f04c2071014162141940c19a0703000e03440700b40302d0208030b1150503000c000400c024003e22615000d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359180161 1250 359178911 359178913
    0x801030f080c1204120303050604270305070609140114390d02040f0602030f030f060f0915010f0c051c091a090f0409030c080f04121103070611 63
    0x544229120105550311041804286014a440303c0e0110703828500200010714014560850861107428010111400501043e1060707044c2188000b08a902145004481036426004031050880c1d18007035503c2e00c68200300030011030a010080c4281300c000d446184003008402c00a01c039844160048200700f8130120f4106040381307810f0100204c0c10204020100445001140c1a0403e00303070010a41043c0c0c002c10000c851441d000141400b4034600c0310081c7c0d0040c807003400207509000c01c0d1100030030140001440b0346449a09000042c44959031a20510450303c4094511819805c10596001d00c01c02d46c038092a02285001942c0c4440500c150100705520350080f0142590440d02d2681c181e41c1c0000d030803110108034054001007081c000305c01020140301043d01c8071682c3c5e0031845003404403110500c1d0f0020b120340e19141c912000b098200348040041544070282d640c0c1d0780d442c42082611402642c010700b404a0941d0b00940070000d074902c020380e02d84000c0301211400e942e40c00b003c403070003140b5600349549 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359181411 1250 359180161 359180183
    0x11040906080304052b140a0609050307061104081b01210b01081003080412030c021017060604031e081b071d0105131a09150a091a01110a02030303010f030c0501080103 73
    0x106d000c844c5418400710500382a01d00e11690380e180d02084d40c1c00d030b440030788040c0c00000c0c4131000c0041e144600e82001085017030080c00c11b85030981698880c030140c90001d540d00d440d248004510380c842d0340000075505405c080000301d5110b0021724001000720004090100e01401c01080015005104400c00c4a0344108075501d0303d07040c034120091090045408406111450352080016034a800d011021940a80d641900e001d20300800105032020140466006210410051010070400181c99000d04200e411141c4041d1140c60070741c0551240c0c42c0e130103c000505030b0600030514000f064107411a100d41184003d6a500400004c01181080c400d040c2c4c0020001c4031207010b422640c009642510118801044034002200032900d065800c542811000004002c0005686002100080039020391a010009144940300740d0030241c0407c0d4100d03040c007081310312480100004000b903a00701c82e8003606480c0c90f07580d140a004110081d90000312080c03064040c01080d04e512900400b412a030b004014042 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359182661 1250 359181411 359181413
    0x602010509120c0c0a18181509050f0609030d0f0c0801030f080702030712231b032b0f020c011418040504150b180a11040906080304052b 60
    0x2e12035024500d0550240940414040541c0d1190204001000b05041406407a5610301001c000c66440400c044005a040040440442c00d229005a40b1003203600c1c0c001807099950601c0d6240501c4031300c03a559503100340402c0020280010010305400e06070070405125140e8010481410f880c00c0c5080400018a0f0900420115909100c1d607481580504000c0c0e251001039004207043c400650030001500180f281507000f000000c11000000e000c0002c1100300a581000300c1c1501da24034001c0002c180f4605546150345684d051003140300115181c0003005090341c051900c4200c010400c180d00300810600ea001d5424540080352400c5420350503034482c0387c003645100020f07510b42c0110040030504c1881303440c103d005071140c0c412540640d01448454446030200ca101a0940b600103e100e802209081115040c40190761415a0005040c103c0810700780200e42e240051405241e015041090074000c000901003004401801541d0043c2c031012410190040c1920030319600080d20b03101460303003050f010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359183911 1250 359182661 359182693
    0x180c010c050a12120f0606090617180c0301050901050103050c0907050301050d031707090311220f140103030509010f0f020a0f11060a110f0f0607180b04060c0c0602010509 75
    0x1c002582c00d42008030303034852007084500448803c0c44051074400d90300c15087c4400c41e0440d8501009141c40d01d081da030700e4106129000e5840c240500200d14400c0149942c47c1c05000500100041c840064000c2150b072030b0049905003e0300080c8003e1312113008650000005040c52283c06204008a0319040d01c1c6034a404240700d0071214150040d41044013081b4803440b03000d50b001b0001d01420040d512404101e0650814908042c444100310f886180741c0041c4401d00e00044c80302d581c02c10629007000a4000703514001c075002d04007104205951040344400030081640100117807903c25030a07a290081820300740c6060b0790103003c00080d031015a0003d022100090000302440044138070400d1848100b58540d0007180035500000000d01c04a14421002280d1400410400d1031711040c1d2001000c3d2010321004094890300094140700c100825003410b940c03010006031000340240003240055907a41d5039000014403a20010008070340580c81103000103101841402403074041c0501001401c084c51804a10b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359185161 1250 359183911 359183933
    0xa06020c06120c0f040b1308010b0a0e1f08030c0d0c0221010e01020c0705030f010612030804051c0f0201050f0f06060d0f02040b04080f0141180c010c050a 68
    0x1868660f808010300312101d15940041c00040c5003403403c50352507030040d000c00070001e0a030750000c2605078074019000c0722640e41d02c1d84440841e50400a0341e003458032081d64540500e00a113141140410840c280029440d00000081440881c41c00680c0d2801c0c508442c21500c03010407900c0690321510140c01c108090790000014202203800000009a44480454483c266005410108455045074200300400d080c10301121100003144030080081c1410122240807542d00544040c0070802000c002808012040000010b00a000d6507008204401d41c00018244501c5521500055013018085146182c48000b4140240304004641d48560f64141c04d02a00381c0014450003600381d20b07091707030244ea114544020406000301090a990302c3d81895901854a5101c1e00b41c1112a03243c07403150f0540c0711003e43d88900040c1c3c9000014401149400d4044140d0b18104d41180c02090400c24060501010035000302d11140e42c0054549519070380005407020142054081e0041c0c00ca1500f440c0000c14402c3d00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359186411 1250 359185161 359185171
    0x90b0903060606091207140a050118060c080f0c03031b03060a090203060402090a0b03040327060f0c021809060105040c050d090c0e2a03160c020f1309020a06020c0612 73
    0x24001410017580e0380240b17070442c00e0f0300000c00744443c01d0307001c00e0030704007040c494001e44000c0c00c04004041384501d414840b488280700d408100719403604070381d0800000d17000721000314541d001403940360360001d42c3c801e0301ca80c800d40340c002141c0d031140c118045942e22503090303d204210041c031710403119140640d080060361008041552240d401c000d40015a909d41102c400500a070380e8a041e180d10741803401070410f0900d45002c940070010b04002140710107011200105076980313843c080345a80c015040c2074031000c02e0035100039800600c20040c8800200085c071410320400b03072901256010b99945040c0802c5420310390b140000540c04125541c80203e094014004c0740317104100206240e0740d1440c850088020545031200306002c4001c5150317140304859288107082008402c81441c41c1801c0c000c1106001040c003428041c8078520702c0c00f000b95501e00c1c0e600981220b001c0c00404120001c022400010040c0c04400c03403150800041c04209640300040c079800c5c104019050307614000b03901000c81d10200c40104 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359187661 1250 359186411 359186419
    0x307050a0f140937051203031b0703030f020c010507030f0c020d0318051510050f13090309080f03040f0902030f0c130b0d09030201241505090d0b07090b090306060609 73
    0x11390f1182c40e03034072200b120b040204d40401034003119041501b0807000a2100c80d0311402c641c414400d0116002d00000c4846007030005401c11990b071403203440d0660281c0704611603000141e2021031407403042c1506410042c0f00f4100e540c1e04221003c012010141100d000e207002c80010ba0040e500201e5150280e400628901200c541d29508900690780c0e040ca008010140081185600024041c3c01132200380303d5030245c102140e0f901040507100e40806c42e00a205440401200d8071104a1300c14076024404d140c4c0a080d10200381e5814601000c451a92a4001e21507900703200008040003964803694400d42340070b030b01101c2000806480303804002c1107a07041003110300000c50351030380c0014680307004200400320315000500c0403610040b00d0030f019007160071042240144860001c0c05030b09080c044801c3c1016125141340d028441000010110707968082c100076281c010300b0722021002803002e48050548180038030b0f40c603110140e8854241060030f004240d80f01d600b41e4007000c0452002c0c41d00d10050200b002005e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359188911 1250 359187661 359187709
    0x105070909020d180f1401020405030c011b141609050c1b0709020a031505040e0a020111011d030309070b0a020a0206031e0a05040b070203090904020415030203030307050a0f1409 78
    0x303000e40041c03060315602103600d2800d0300c940c0001c014460303060100c21b4550303600840c2004c0c03404000c03944620ba00d0f401d640c10080c03110411046d801d82e401c03480ca800d942040b014005040c1440301584d4489882d5080d01e1070703021140001030b13040300500945204600a840103400e00410b0000211500d00c100000b041f1070143c05000b148608003031003c1e01e0440e0b00d641d8080b1b040d580b5800781c0141060544c01c818040c03410001515a00480000c109000950a00c2d240100e407030280040c6004291503081c542e240348440c0305013100c02d000040a1802a0020b009403000241d440350500340c58441c0d194608056007110301c0c480e02601d40000619480b00c800000c007a0507011089075491014000c64140907160b69030010f002c02e01843e00d6169902180c9400203502d4100c0c00d070700040180300d0080000340710b03548440204865520501c6840700640d40078044984038104440084d1698111a08150006179a421043d9009108203620f1311010364400000c0c1c0380140703240030301581615031400c61600c66845 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359190161 1250 359188911 359188931
    0xa0f03090314010f060605030f0402220204170f0109150e030d06080f070509060a03081e0c061b070c0303110a02061305040f11091239030105070909020d 67
    0x3012280316003184074030000805076005031070013044602d20b0300710b80c0401000303108010b07110b00c0b030000541c3c2140d01204c0d00f1062101100c001c070710700c004070030800404900119000809202d1482204d0211030694141c40c41f14403281e145a088989902c1c000d446034151803488400c000c082d0f406180514519010750b80381c01c0d80c40308080700782c480aa010118503808080e9440c100c00040c01f50001600b070445e6540601e090082c001000c51038a808080d2021174006021152030900007150b030100315540c444030783c5501c1a00d5216403510000c41d410054400d8152001100e00c49100446000c254400890011241191022113000e9502000d000300c0e445000c50b05005030ba11000603100d0040050b04480a441c01d0205100a542410103891695030030424100d421103880300959640c50b07410385407506040444c62440e03241140090004084144070f500300d400c000b0554641d511513120282da083e8041c0401000d05017290b204071040c03400201000c00a102c51040c5400038001440003400c0032a0032046 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359191411 1250 359190161 359190173
    0x80d0503040b190c2105070e010f020f01060329011d0402040b03070e07030e030421050307080f0406081602100c020709150e090a24061203020703051e0a0f030903 71
    0x8401c1038040810700440446110100d41c040d41c00d017003903040380180003034245003c1c090111981d2980c0c1c1d6041c0a0f0f1041807011161003041485074550600c0028030525039079040005101c0d2104000d215200381d9003030008080020340729564102c3d02e107010401002c00132207201581c02100a40100d0b03000b03464000c0043c0039038003001110050521001180c2c51400c00c40d001504035600e10940f500d0540090100f04542288103001c0075505000d181c801480090520b003490851103030030781c01001d154000c65290a1440030327070090001d8442c2c41d2566145a150030b0101c10004800c4502840142d00040c400d820701d40c00c1ea00440354000d1f540c0110f030441500c0f490580c00361001c483d903201182d41c2c200c01c00c0200c201d980f42141d03005801c1074060800d0355800d40720201d180611100e01e10700a80f400c0fa04103c4421290b01c040d004104409100178500140d00c7c00a4680c4074600c026143da2240750488600686400a100c107888a21001490303c540c25640f5184044a0b041c016010310a84c03150020105103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359192661 1250 359191411 359191421
    0x503060d060c030507020c030111031b04120309030b34031805060f130c03110d0606081b0613180b19170303010e070c050f19020109080d0503040b19 65
    0x907483d10040368601c0c4c0540024a08503846060750320981c101481542ea05950340e0403203030000d41c41c4c010f00c2e8070360b2040891150184940d9002d1806141002030b5881816804070204040c0c901c541c03441d9006840f4a00c1041103000c600c03404000440fa41030700c00200408658900041200c0740c200450028615140c40a502001e54000d03103641e0448030821100702c1c440004564094120a11440940441e8840301110641800b00800c0010450b14505a9a6580b0403c61803e5484001481841c0d100e00c041512006000ea6404919014841d0345445151a10035500c401d01c1d10700c13220b152036181642c0d40745c440d80d05109260f030980c0c0e650079142241d282c540000141118030300e801441140380041c841381307045043c044044d075604240018441d100c02a81042e030041201d1401d012460101d04100b800c0610522111042e0700c1100182c500c5071109040c1d84440034000d0b03c1701c0c03c800d5918080103440308503c0f10b90800180c0e04000003000034038000b400ca50411000398003010201e400340c031114204c078 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359193911 1250 359192661 359192681
    0xc02060d09210206180f100f0c030c1209030c0b040b060108090607020a141507030e0d18090908070b0123040b09013b01050117160503060d06 62
    0xd80c076540d00c48280003a900020350207000361042c1c51a110241c0100a484d40006009620304142c003401c035407980d4000f0002e03680030040d60002d40301c0808071000d00c0c900814125203060308850a01c21043d1119000b40700740118010b060b103d010400b01107040541c01041126400c6081c1701020302d02d480230801154000348550720681c016020340c1003100025020010041610040380e120008100d4013642c0031518803c00ca40c0884040300c0445c101c000b4600301049a00e014820300c0c50602001519a49604110b4450f001482a42c1e540c0701c603544101d80c0e40d0303800405c44290f10f94a0710100514042684001030040c0596002410310b00c4642d16034800d90310a074000880042d918240c0d0070030000c40b4043c0c8005031422141000700c070b07260801250085005200b4404500c5403041c172403488250410b503180068005801e004002e00101c0700e141c101c0b482c00c2c0174680c00540d44600e0202603206000d80980a007140020102c0f0007401c2100448199100508903500080d41d55a04070010b5130038007032200c0341 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359195161 1250 359193911 359193937
    0x210121b2304050f0609030313170c2101110703080105090601030902030604120e03070306051e01060203030117030d020d020a110d0c0609060b090403080f01060810150c0206 76
    0x44038035a100034801031550300c81d14042080e0600861035601400c003128211001074880b04490912500040c200380120390500e50503005c0041c00048600003c080c0c81c040c1c0ba508600c14040b041a62030169860200c108040c1e0080c42e100780f0020040b2f02c29030340c0e01105c1e94040002c51400f101c040d402074940c2106c803045010410070f40c01440b1918017003141c1684010300b840d003003040b81032a0300040c0d500d01e0080c001402d01c840e042c0d03055902911580400b040f0000141c102c401840e56803170150001e0200b16441c4411102d0100c0032122001a5135804c0d040b22111703801141140d00704905000c007015400c6510720039105c10440800b010309540007030280d01c080c40c100141c84008012000c0c2150244e280408401d80000d01c075a03022541040e03032a0600da41000780007843c140700389805002041c400510329804140b80c1d0030401015408481e142c4108085244401240da0b100e106503050841070740d4003101031210500074456043d008032500d2003e00b280c40d16121401c03958001c60002da2111600070b4407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359196411 1250 359195161 359195201
    0x60504210804050c04230405070e010b0c060a110901110309090a1413020307090c091a0c1b03150402041401140301060b1303030507020d060c03020d1404050604021012 73
    0x502c401444680109030003503a091200302c00c02c000c403d046c011700d05400003104107208007081c01d10008214420151034000740b10199541c540c200c0c180035400521031000d0768441e680005881211501a220311640d906290500b010301003001551803101e4840b242001e8402409080741c99a07480b0000f40c01205460070005002030040c01c04150008001c114011818100682038016100051440c048502520000520f10109a0100d5403202c9a5000c44c58000700070014403c01c0c1c02a13002010210000e204960103c00c603a0180d039030001c202c203035040d4075801c050f022000301785814400662062000304002000d02940d0700d0030f04c0081c0d0a800c6100082d900780000c0019007000d104400140c400f600c60035040012000345035a100c440390000134200280482d1030811529400ba4205105920144c1032103014a5010007c4c0250072029861090034188070703980d1401440400300c2c500560300140600b043e583d5035000d100021480034040003c0200b64001d000c412081803081141183e43c40311800d00c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359197661 1250 359196411 359196413
    0xd0b1c0602070c0501020a15110c0a0602040501180f03030c020d0b1005030601090218040b0f06030705070309050405060f12250e070503060901060c020d1502070c080606010507060504210804 83
    0x4600c40f803a42003a41554013009240c4c01040164625012075020300001050401600281c0c016600400d010740c100d5210b18205030741001079640181c41a07030400ea8603039011b20645200070f0541c24050bc6010241c0446c0c0b1303418000309105500e40c2541c0c42c0050f10070480302c130304c075610511a50700456840b5803100c5100400c0c4418030f0280201d6004001c000c800358145540b4103114140503042c0d02c406441190355021002068551603038481114400414094032480c0c00e00c0080c1241e480000c0440c001029004041094a801d100b100e000d1000038000c4030800085030248444030b280e0403440d06691048292044110102040b00351112608001000c0202d00e0864144817408010f488501031050900800030251610906541140c5080c9003a00400c0c1042c00402d041154144024090614601c4102a000f800350014580280704024000c0340300e60390002e00ba29020141c40701070000c0d40401000c0d000c41c42039001103802602801c10a41c58814841036405000074402d400710120b0503150800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359198911 1250 359197661 359197673
    0x803060405070822020a0323014703060a0b03010e030405150d02130f080c01030912200a050a03170f010302150c0f01060801200d0b1c060207 62
    0x1070b04400b079428200000d0070000c600e8500380c4440c00b44c500e42034807105040419595084241801550003850498100d842800e140c043d440c240d840303910266013440c3c01e508025002050314805204900c0d15020302d04800b40c04410310700f1a190782c4186c3c0c50403100783c0181c02d42e4280700c0a801009000702c0040c2503030700c06040c9425611900500005500140b104210507200c411260302c54071884e080c000d80e110b00032001c2000138050a880313074058541e07040c00840c44d000491403000560303802008850305844448011015901c0800c4020060101e0003103082e4100c0c0503039420501d620399a075004202840402e05145068180d00c410366040d401070702c3c0b46040c035800400004000c5070031242400507141c04440441d400b001884003e014408102d80710a04e107810005581091940506981199892102c018068603107400781c04065407070b041110804465030001907081205080005091940380d60704d0390024001406c4144c0c2140040008280380351000c40c250008610410300140c4484250400b8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359200161 1250 359198911 359198921
    0x10030b030721020103050702160f0302151c0e070314010204092306060f070209040506040210020c2101091a0f070305010501050d050901110c030301031106070c120c0506040308030604 80
    0x20501090082c1080e11082d400d0074041100c007034082c01e02040304d40b202c41c022803a14454000c0819081aa01e00c041501c64007000c0780310407030340200c90184180812071280b501d02d03c0741b500403c41407110311900380600001c0343c02440329661081d0907601240c3e5030b5115014100243d2846241d640d60005041c00100e00301d100700f5000b00403813030b0702682c048cc9403855a03d2015000d801103114420100d1041498103100080341e982660141c0345420704c0c2061318106503030321000d0f10120f1284d80a050b40320500c510015004019910050081d8804442d030b00d800014991905201f1801d9500d07108040c011035840c10018400048461200009142c41140004d4407031002c3c0802c0101400d00c0e004000503a403060075505000c1500c07900054a486200c0185c0c01403980c40742058040c0008504520ac03107901001850480380103154940a1001d004104410340c49003081c010800100400309001100038a95108100d5104030700d2003c1c02c0c1d44030b4002954030303045580120f820100001c07c00025082034090703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359201411 1250 359200161 359200169
    0x3020415050702060a030924020702010e030606030a0b090a12020715020c090103151e09030905040e120f040b1801121a060c0111070501020a02060903070308040b0705070210030b0307 80
    0x249080030b4103a40024214410700e1003c03c1019121441c41c014040c641c85030454041198810b20b102120410f1848065000610140d01140e8500d61048142c100800c04510030007000700a062003d036281d441d01219500a803880009104440801001503c2444040c890450307580040c030031a440e00c003082113010100c40d82c1c4421034100600740030303440c0c4616000702e06480d8004010402140c224000703400a04d0500b55848545480c0b00174400c0d010203541c84258030b68060f54440450984a03024003040d5141e4418040040d400780c18003441403030b00d010280085d40f4110038800c0c5040e03655891500305401040150285e0640704201e4a40ca6800210074101500002810722442100200a000c040040c0d41100d0140c00d0005480141c00c40a500100040f0b10600303c154035117607a420024000c0d0050400300026104010100300030070750010a8401a561660725001155070351340e95010109405841003090003014855100181e0b03030044800034011031a50009444c541c82020586445a5580 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359202661 1250 359201411 359201417
    0xb010e0c040303050a0e060c0105010311040e0105011a0703022109040f0506010c02040209010e0303072303040305060601180e040f050d140d0b0604120b150f092a0a03020415 76
    0xc000c000213500070044d9103044010b81006941060b2201c0414050700c14200510080d5282000110411000101c01180d4400507a010864002d14205c01d6007200c0085c01550355070411000703040c040f9111280104003851203031050b1003140ca008a0001c0040b07600c21107201c45c00801040c04405810a840784100d50b0f038a5a0040c4140e0400700c00180490000d004084e015a0300001e25183c1640129040c0d03065440182c01c0301d50f541f2180c1000803900e460801c5c00c00d070b1180e90180907480042e0010645080d260010f0141c4102e886010040d80c1c0a030a81d820000c0b030388041c1c000011000c140950a910540c003409103400c04054619101d414060303c040645c00340088400103074000ca9030b000c20b0701d680c009040c00c0001c040103d2400242b13203000307541c003152441030300929460401928241d620300036000e501d00b540d96219620104801040c001300c000303821441c0d50001841c06040e00e0380b00765051102440703100c5800c41101a0710159403180d0781001c0030a4000400f040316080250104d050600245 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359203911 1250 359202661 359202667
    0x1a030601170403110d03020705070e010e070809070314030307020c150702060715090c1a030708060402071a090a0b010b070c26010c03231506160f0b010e0c 68
    0x80081d029a540c22000100190018001000c0601441950760503400c2407007154004250524014040c1d80003a4044515008144c07000960a9038070b0980c5060b20f018030b5607400241e44000341201c00d604001c2c1050240d105034500000401e031119136104294105c040510341e81e2410b1200130b4a400c040040160144008105080f011800242681c0300c0381d07412200150344015500740f9011f04102301d042c4840c100d181001d03080030003000070207040c11a00080032500303103007550100c5003170940000c68640010444600003e00d0900c0e065006200b00da204600b200e0f00c21980083d5148948021164088568040d1006a084c003c01c1d030440b900511200e070307405107000029620503501014920030a004034001c4803000305101900011207000907006c44c02000107100440303005024150112400c002c1000c82584001001c0501e1103182c071400e065150300302009060780034003a2581c40101d003010b20324004902d07540040d00d040303400e2902900400034003c4950502c40024507245c0f001d40000380000d010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359205161 1250 359203911 359203921
    0x803150d0804060c063312081e0421031106040b13050307050105250e0603070f0302070b07030614040905030d021b0d051b0d14300405010b120705010e0604080d03050115050f0f031806101a03 83
    0x435a421680c41061201741c2405003400f8034106246015110b001420380d4200420000005000c04845265410700c6003040b000084020041e41c020726614001500280200005078150b40200360000ca4121140f800501d082400d0300c442943c0079094134018000b0342c42e048100700b4803c3c02c900030f081c800c60844003000500c48640d5030696a100da400076815468002ca140300600d41c0d40742486038030071101c000382c900010240000400c80d60044500c080c900c0d00a10988504090000d90600b510710b0355241c01d225010550224011500040c041070305130820300f846c035a5070200b10500710f03400c1c00c00c44a0340241801c051900b0303070940d1503050303441c0e0040c0151000e00d0000400018550304840c001e007000b1090380034410104955205d144c0241e031051041010424100d40d255000c90b04032840031070782c940c001070b004000725054459241440c00c410070600503581625224401150480000318001070400003120016040420840d05c00444842c4601c3c104100803503030301d6600740c8010002a651551500c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359206411 1250 359205161 359205173
    0xf0f16050109120602040803070803040507120b07032703031d0109021e0312031302040b06041811090406030803150d0804060c063312081e042103110604 67
    0xf44903240501c1d024507049814019142d04032809840082c060b0384d920041c80c10094100d91040d141140c040c403500c00005900752402022a1a06602c10005040c036102c1e03100c110042d245240000001810100c02248118100005101d9080c442d8402003081e0121004041d82e180305056400313001c0c0d05110350ba10059a03003400700c0000c0324480090003500d44001000c6450b003100c4910b0380e0080e0000200b800842414200c004070028400c0f42d0910840c0300c5541400164082c0d84210040300c0510a42c11b080d9001e0368004105060380d9806039070600c1100d07030000c3c060785d80701d44c0169a640c0c000418840400c1007141201400001650030458401c80c2d40c0d903d075130520551007804208903014034070404004c01c81e00300400c0b070110b00200c3c000d450101d4240014100c0c8118034061555840c0340b0004a01e081c0c00d00100c0c006d50003911150820680064100386180c09a0310030f60b03050010003004c921603003080340485404d00c14294400034001c2515001e00740b4640360350402d84940c0000304000001d81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359207661 1250 359206411 359206427
    0xf1009091b0c1407080a030827060a0b031903211803080c161101030c020105151507060e011d0102131a040308070602030f1312080c0403050f0f160501 66
    0x42d1180c00c104070f620010f203e40b820b1801c16080304583d03004441c104400c1c140d103c5481c038064003d400980d14014641002d4100c441c0e55400101d10700d411100c00107528588652280d0031010001e01545e0303000c4110301c89102c02c0c3c01c40c6034044000c940141c610341a50341030800c100c85241c4600707000700810720725415007401c0c2011041c00101003200d00c40000d00c810141e00152481249060b04507402c1001d1486d0202d410700e02038a4140c0064039110020580c2071050250710302076158699020051054601404002c00e14003c8801c5010000c00c11400000c1e5280f0035010a4581d0070000105105000c03010819503003590240d0718168010701200560b0310724225807500700c1d0310303811031000811205024203485000d55440a000d000010424a081c40403540040d07208020100380d900d000d0b502e03121402124a0700e000060003858809941007603550280300d4068001000f66641c9042541d00e6480d14a004256039072078440b600300c8120340c1c0390342400300302180154550424904480d818030300002d20790300c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359208911 1250 359207661 359207663
    0x108060415020304030e06070f03030b01051c09020f090f04050601050d080d050907090e03030a0b010306031208060f0a03260408031e0405030601062001051e04020f1009091b0c 77
    0x703640000854105030003043c8070125014080c08494950100d400c0039409000344140a070040303814803c1000482d8440d1046545450400138013200180601c0038442c01001c54083c12608198101602001580c030082541c6c03241549604075a11443d061428504051060380000e0007a126034166800050100c02692a03010009000007055600c04001510344540c592000d5401881d181ca048441d42000c4021442902c88820910004020400450031141b03588409080411581085843d07544146100c03600138000520342d602e58002640014034400e81e50340116042a65106c02e0002c54282070f4105580070f00c903035000e40c102444d010400c0c2e103d00c5454402407810b00064448603860310704000340d4016100140484501d50f03140c000160040003001045503006a4428451103009014041c031032190310b60060507400140070f900c0300a452030018004907030040846211440036211080250442481d65503500802490000d00714101c5e200c0c649500042c5c910000148021a00320401280203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359210161 1250 359208911 359208953
    0x30f011a0708070809191502060f01140d050c091503010f0902090a0e0304030b0c090102100204060e0603070e040504050d14030f0f1801020307020307060612120818150403030501080604 81
    0x40d01a03076001810540c1b0420310741c01c1b110b009801c003180f041840016031102000c02c0e002c403400c5e9245c1280d41e44d1404024820400035698094044030b0500300f4071000d003141c0b0b20800450f0105d018010004824240888001040b4000140a45060300e400d014800c06a04c0108082007480c030f50340c010603a00a001441103c0c0c0507210005410001c108008660055400104c082c2c91801c001d4882ea03040e501c541c5416005224141841c0c0c0040750500c215400c6039030607154600404290014852540c000808000030700c106640c000e203098480d40603a07442281b044014100c460488200035100c030a50b020316006510041c010450302c1b44484404680141c40c140324040c0d01d40c2c64803510000c6003500581462a0350000c01405100c41e0000060580c90748905002e0040302c0c1c039064202900b0b91840c070043c2480b00c00203000c030402c03801140c4240e0408140041440303460900408249001842458161200f441400b0842815030511442e4050403282000d043e013400c0ca0384420350510030b01c000540a03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359211411 1250 359210161 359210167
    0x50d170c1c0f0e0f4b010912230a150c0e0a050d080903030d0b010207091b0c330e0f0a03030c0e040c020c03100501050a060507020a0b030f011a07080708 67
    0x20364030300030000c0c610b1a4104010640302065882180952900030030307801c17840c3c0790110043e4040f50f018201035402c0e14620500e0f04103c11a649802840f03c084a8030703240307140421501d5007582c02083c001410064083d1080d9a1014043c00241c0111005510074a0400ca44640c04503150b994910b070f90720072100d00f01d88040200a15040140d403600c121601c90342d01d4440019402800103c0e03820800764a4000d03000e4480b450b540d140c00c441560303222032011100002d40c800c1c404841303004164506003103028503101204c081351000d400c2001000300710044403048200400c000620401e00031240e0010740803000c0c0c140e001c005034141384d490300504801818142c0300e014158000c1d02ca07104455603001c0081050200d034410a4000e5140c264200c0c0081c02809035a100002182d50303801980c2c12500040c0c6000c0e4200d00d09541190340d9044084201e900135003445000a0109071040510702980c41e4114400040d45012226008021940c2a12103060b4050080f100450b201ca070035288410b4001d0400c0307035 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359212661 1250 359211411 359211439
    0x6050c0c0103061404090515011502010501080d050d0e12040f05090a06081c0c050303010b030a0b011805120304030503121e06090a0504020616051c020601050d170c1c0f0e0f 76
    0x10230708441580401503400764000028055541c4100c02100303880130f8008100c26600d45034426100d50090140002045c0f0420940468103065440780c0012207500b400d40c2e1012510046014a50b44168800c000d00324040b10148400d28141f00f641c3e81218440008000042c6403481083d2a00c400100320007040840700b00070329503280074161241c4455405800d5990380d60b100d99410590b031700103844070300c0f101d03144c0501d0310101d50091045002080244041c00c81180c6403000b00906800c1c8901840340c1804140000000200c0800260244038000fa207126401e2901907440820f05c200d54250b26244000807060081e10f1319205505908010a000040f03031681d503900114909124070a08a11850b00c0019240103110300411a407001400c02912850102e010a404a13034642c028007039164403c0700020b000300040c2e00b400d503450782100c20440d00d0b4100500e00803424204074860640d60a0f500c0207150302c4080d154402620581021681048040a0340003000301d204418000f541c0c2307014180c02e4120348 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359213911 1250 359212661 359212663
    0xc05060a11040b0d0507031d1002030603030706090b07020609070b04050d2915060f090405040f050601030507050102061605070f1104090f02040c0903050a0b040611030106050c0c01030614040905 85
    0x1d400340a0412125982e58210f213800b03001050b0844224001910b402c008040c50344060807010345c2003c0c0c070710040c81c0380803501010800030b41c00542034981c1488104428030010b034440c0a580c9803e4000c034144803803882e0181c03010341440d10090074007000b03410440302840700303000501c2550103803541078542000c8801c2600c2e10710401068001d41d170703c01070380002c1040c0b5103840103d60075206001401c102041c50a4020510810340a80001101100410300045849051550089a0107402031507054442580364590038180b440a800c1503480b504101c106028a580422aa07078001c921548110540d0f240e4520050603402140d070000d180080c0101e441e41441411000d00d0481c150043c8100120078152401c50010398562500300d000e181801c0c50703105c5544c0506481000c6a82060191000c0207495645000e001d0004200300ca615550f0380d58520340c001c4010245020f0002a00d0303281e512080619018074111805500604242c1010000c0c00b06240b011310308160203c06940116403d03041d86001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359215161 1250 359213911 359213917
    0x1f030509070b04080607030c031a060702190303170601050a09062303010f0512032a0a05010c05030f09070b1c1b031d01050403090e06130905010606030c0c05060a11 72
    0x1e00999000407401113900a0089080e0b0300031801a10204100340070082c0640a5440c0381c481400d1000380c8800012260615500500e9030b107200410a40309450000711600407409940c00c1540000d15850346100c0140700008210741117402401c01c10300b440d0b800e200091031460913010309070400440648054042520000b903521410b014441079480390303100c0445070304010440c401c292050402c00c001607140c102c0070080710100c050f0806010f43c2d940c0c18901024801405103032006192203014403881c0031a1007032050a01c80545565601e079281442c8801c00c2c0b603020301825034403554110300002c0001e800303200d0441d00b180850500702c80205e440405a0303001000d0b441c991910003240b580840842660680c82560307940c0c40840080c00c501b011035682801c0310000c0b100200071030f460f0b0b0f42c18455007084446541e0b116000a004000b04002d9207104019034500e88411070704d507915040148251909800340840c4001e0390301d0702c50718614141e110f280c0d580b074025040c155880d80e10161070342411906021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359216411 1250 359215161 359215169
    0xf0c020607021c14011e1b050c070b0a0c1406070c030e040b0307030b0f090f060106120912090305060705180d05012003070314060315090c2206051f03050907 69
    0x20609140c41c0544e800c44c060500180d11980b1080458070189480e01540700d44040009803060081c1068900102510340b580700c4501003925120b05100000d50214401c001c0c85156100d81e01c030401c01e4014030b07094071580c2d81f00c2c0e8043d00c5500000c2c200235542e41e0110b24000081d8043c41c0041101160300041801440d80030452030301405001404401c1c0403aaa040500a0a0040680d181035407124440380c0c503041041c0100005412120040104500c03c10181c01084088040000e50a4141c2d2700c503034070454003002d00700105640b080c041041c0102444603079408841400e08500d400b01d038807061540100603400c074078030907440d0000c40028031a003544100200010700740c905800100c009480c040ca600200e030b51500007030510750b042c00c1d4002d034150a1401003801400409080c001d08100c00070051004003041554818210003641c81c0e41d40342416081404003854036a0184240c034054015075455412039402074142d01134800000c010b00707a56036884103a9150000c1c517170f116542c2083c01c00c0c501c2d0380 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359217661 1250 359216411 359216423
    0x31b1e030302120a090209010627060305070f030c022508010203090a0c081c08070e03031c0506150412050a0b040605010602010e21090a0312020604030f0c020607021c 73
    0x40988205a05039005005102008401d0f01490355801402400c0c3d50303072140e000307401a20701001046400d0081d00350062000d40c402c030300c51102104072420004500781c1d602c032100094541082c01029038000450b074908202910b4180b1522100e0700f00695148281c1c004505a0342401203190081a0f501881001900400b070003990780f81042000d107543c035114411306503180c5102100009482d0400246c6400341d014400c60403001d9114240c00b900c5400000b0010018088100d0300800c466030140010202503402001c6846200e5140d10510201c550040103035004100401c03a0740e0009251409441c01c44e48034a1802e0301c20ba01c14030b80340f030074100c0e0090008c207c0d55080c03040c401003200315007081d41030b561294000c00c2400c103642e8001383d540403194a820700300c42e6605000c65a402c2100000c0c201c0314009081030700c6281d80d80ea034048000c92a25840310040c0c210070103200c101680680c0ca0880c80c00145401348815107590000340581c403419074020320072803442c00803a4400b20307414802a120f6400c64 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359218911 1250 359217661 359217713
    0x303020702031c110c0109060302070f0c031b1d0406021303050a0303060e13150b03071a07210e0f01120f050403020f030f030f0403111c030506010309031b 68
    0x1101c83c24603125046081001c19164590428000000110803102c008143c1d9001d0178680b03031803410b0300250302040003030701c0e608102a81030002c11800305054004510408584c9601d20882c0703030322400d900781d6030001100041e28040d6100d0140480001d207800c41d0300840010391340c541d0903040d0f0f0b0310052141e100400034018000544149601940024205d400f11841f0a850b5907820556440c0c203000703110000c1034100c0e241200300b0172040552080880d440c0c060200c401c41c9d40c4034074200c9070010000e80720342241c64000a9100411964186182070428039000d40340070f509901d20b026021603440381003240141010310408605030b00c10400d40032200c01d00c4100304081c01100060b0009020111030503409441001103511900c40000100d4142d00300c8000c503242140c40721504c403d42440060802d81c100240102044541801441040d0320442c0c64807000415144810001d005d40f1070041140741418503100c02e0602190308403502c0006140744089001c0c40303c0345450902002c0c0e00302c6500d155105040303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359220161 1250 359218911 359218933
    0x315090b190f06030f060f020d0212060316050102060c390c010f05070f05071d100b0a080c09120f010905060c07110108070210022a070b0f07030302070203 68
    0x84100d001001c081c0500100c801000c2040070380300d051100408540c40104d400300855030940c80103000b98900e010142c500503203207078290217a804c1000b14a4458050905220861034100b0014030301d082031000d80c0307068918260000c2c0d02d880c3c0c000c1440245c1200022000c1c480703100b155000d44410300b08680740500c4410260548000304048803410000d100d03040c05004958000d107864180318542d503564a203040c00d107681d050150400d0300011509072084103804102c25407003603140249941c451611090701d1a1a000741604805240d210084500c41041036081c0554811303240f50b405042204501d584000703030070202d080c980444402d02c8160043d0b0101d0552a02c0c19084030f54901c0c051801c0300d03119124656407000780d202d030f00d100600403541c503a00314030a035002e084c0380c982c0610940161905040f40020501c281e030f108403c2003d02c4402c01c0001940d041e2003d8410680201850040424500300804104c01d440b554080c42180b03c0046220002c00d40b00e501140c04550303002c0d041e01d290b03560b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359221411 1250 359220161 359220181
    0x40c030b071b0c051008010b090105070c08070b09090705070206090405040f0218011401140712050f030901090b0a0e0601060e0a080708102909070c060e0c09070512010315090b 77
    0x3d40d006440c46a500c1004813107419103c2c00d4114165942c201000340382032070b0580195032540c0320407000c0b12083c01082001500c22002d003c290300405601412603921081f081c00c020440c0da0060082051000601160f0056215442a03078145070055800090750784807030405c4e06003c1940d9070700a62100801ca881c0c511480c40012041c104c801410307111a00b410207100640728518203e610b08100c034021f000340c40c0423030159a18001c401030f07203081481c500848590035000310780c802c13540e004250f9101c1310032404005090012581c0700e04000c0c0100001068a05c406403140010f108482c200302100c0c100c07000690b219800ca80041c01c400c400c030f40e0a90750f290402c5490f07522000c00040c01074900740c3c642d0103003020540c140703507068001407141c2400701500d0108510558041e2182c010090a501c2500c001030b03c40c82126005030080d8003c11215001b1410031114540061449040080034048000b07442e43c0c038034003070741500d40c4030541d503d1620940d12030000a1002d40c1001e486035026000380405115 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359222661 1250 359221411 359221433
    0x9032d0f02030d17042a06050406080604062603160c090c080402090718030206071103010c03060f0504050c0f070f051207110103020711130b120105040c030b071b 71
    0x842641a10035419071090f080e00c1894240c0e06071904e00c851000000c00060106e40c9440241c119078030f1840f04d0350407003d201d0b0090003c0d600084045400040c09100241d0894100c541c4031104403800e005171810a140859202080e28021401c030f81e03460200300c1e4691091041d41e450240c42c1031581c4000304281003481004a580c0700382140d80d072400c8480702825200ba01d040b442140c024020380819110003c040784c896002c4c2050304100204541c0200c010381e141d4000384540b03401a084034078408161010142141d4003188100241490800200884c004040300c42c0203c40e0111000940c55036001e10000703040c030a0381d070320858480001800b802042003c40c00c0c4200300b070080e000c43d201003500e028016203e201f001c8000c0d14010005080c800c507984260014607034148515035043c45081e02d0004104203280083d18484202d480c1e04084405041c2082c1c41c204189601c0000c0c00542000d8881c401c201c8564080134200c00810800030b58010300962400c01c00c221500c0242c901d03003810307080503e5091 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359223911 1250 359222661 359222663
    0xd0609050a05070e06070501110415170114040207031701030b190b030606091e07050a02010f060311010c020d140c010e0904020915041d010615050a09032d0f 69
    0x5142030081520080c46202c0daa10444080c0c40b80100c1200765000c014a541001c5002c907003a6494402002d540921200a40300402c0000b821a110074094040940380c62004540e00681405070401003061905255030814004c20940300180e13920100d0038201c1785a91402c000706240c04040d00000100809150401d109001280c070f0a000d00c10302103402400c0c0c40c00906401d41c07650000c0e01280962a191900c01d030000f44680c107914074480d0710300498048120850707141c1c02280b008074803090b101c1e4080c044e04402000c155404c1124900719603e0039100c1341c0700c1200c541009000f580701004c40d1102030644415a8020340400003441e495a103060fa60020705103102c0c000390401c44013000d9800d0108450740107075402404056240c1ea8054044030003020701b800c140c1c4c841c0e182d00c68140103181b0541102c40154002e03001142c42820550403c81905080150700b0400c4800c01c03844c042d4a034008045002c4d65031242d00302618a440501d8918484080c0d80c0c54040e400440c01072000700907064002a20007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359225161 1250 359223911 359223929
    0x305030a020105010f0e0a0c031e06030b06030706080c030705090d050307020f1503041401150e040c05010f0807050307050f0a0507110a2114070b03040501050c030c0403260d06 77
    0x41ea0705e540c078401c600225485003246101100010480da00c0140c1c00100301c00701c09240000f42c9001c000c60003108541840309444516580c0c02041c0300703011442550f250312140541c005c104442c5001402043c00300300034031042d030a80011001c2843e052240e000c443c800000100760203072120443c280280c6035803000d04128480c4085403081040d074101415007084e81c0542d000c0c482d00355a80c5446031031040300071350b080b0b1020303558070540d503e51102c11841500c003a212114211085180a141c00420034807a40c1110741800f829460380c00e05503074404c0e00030764096070318640301e500d0361101d03a01910a0b0103840c59512401c1c82c082242c1c00c0155011000d01075060086c0d01c250304400554040c41a090002c2c0110031000e104070518001410b0081440d060303a45c424510500e8000b100700400307040c001142c010801c602c200206010912000b4081da42c1c12401c1c1e03500c07491550a1448010000d07110b10f200c0204044d82c800007d03031b2441c844c1c4241c00710b0a030303049400c183e0ba91300c0d2850a100500300c1d40544408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359226411 1250 359225161 359225171
    0xb01060e0102030a200304152319020705041104081207020604060f09080318031014010b0714101e1401181e0f06060c021302090a08030a021e0c0f01050d0b06040305030a0201 76
    0x201e040b450075074001c4c4604500b9480c16800040c16031000205600d039508bd40f090b514005000e03210b601c01c200d1b012444103441a1524140f04049051103030020300d41480c51800e10911015079500000c8a08071545c5050041c86600740300f1003921915400c3e8448c0900d0700000c42d80305105018006540301c142d1b030032400d0b078640b070740750031020b200312001da0b04900c0307014020030b0052201c224500c006200c2c26020740035000d000200d549100d85800300201d00c014100b601c510440040c5800e51484071440c40c280c0300c0a210407501d0102016110005104100201c009024108543c621a51010340b8401c40148140f0f070300c0c02494a150051704000e414910360134500100090010b11488506000f15402402c0e5070b6181c40441080c40079400901c8496404079055400081d010410001804480744070303009801103418107003410080c503070350020f40c84140d0404a9015116a1010300fa007a1800003400c0c1151074118450261008110040881b50468000079000c024024000b0182c50443d141d40c3c02800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359227661 1250 359226411 359226437
    0xc0b07260307080403080604020417010e070b0309030a0e01120905010b0f12060606030a06080604030c0215040b0909090c030f030d060807150f02120409090b01060e0102030a20030415 80
    0x9103220881c2c0303000002d01c142c00403500180c40b0720056904000300400c05400c1070384a0842c62955440440d42d01e805a54540814910305014042103004002400c1058214601901c003070b51a40b0401526100b000315038041394402d0384c00340d041c400304015101800c101564851510340c5c004d11220942a1003400b042819440130b00c0c03c0780ca00150703a410400a003401d5200e0f5018010683c00280450078516252980852031503002c1100e6403003140030340c0d120b549070409401407240e109c1c030b14120080002c0040000f03220402c049411100000d1303050780d50481c20b0740e4501450f800d0401c940d01d020f070325000e18003006c0c01c2d106002010380a55012000204640703940c4489240e601c1401c0d11581510303080a080500819000340014a58604140182c07000c3c180020100f00050348650020050143e44054400502010b0b60720140905401d06158030300c0c07030344a80044e603a4007401c0030940c2000182028429404501c00c001112201c900c01101c1e102c40e11012100500d01038441408000b0382c00c290010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359228911 1250 359227661 359227733
    0xb0603130f080702060708030106092c04022202040602010f091205390f1b0d05010b040501060819111c1410080d0c0209060d0c0b07 58
    0x64056031009900d03142180e050740e509001c060790000159411001803140f140981c0701c2d640242030f114403031300c6050340e43c2d0304141003d4102c040329000422400d101040303491142843c1a02402140c22003030000740c540d03440788006100816980d8508000300811000c0840f100d14a0b0060400d650194009120311000c0405080c00c030303104404050141050341c0030002a60740140e005107044142d440e04070099404071410034000c1078035115808818800c0a02d502250a018480884c1c1c2024a4010301842c49000d03640d411021101e6945501c1004119402c10804c0002d5220994106020384280641c0d80e507840c0c042e1a44204903103c0c0c0d02c458620003000c8010b1070074800c115114178800811800c0c110211010002041200b00c03a1a41b142d6540010000c1e4421480c854070805000c1040501e403410100d4150400780103440b032100380254000a40c00581e0388141c076690014058809d5086106181007101020302594401e9501d100b0020f03101e801d0080b01c0152203d0b15580c00409032a210307a0528007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359230161 1250 359228911 359228917
    0x302030f040f08300a05160806040e01150302010e12072c04121d01050d020d14071716081503010608190c080307020631080607030b06 59
    0x404580d2900c000040020b03820a6105004a01611200b810100c104940c50038a94910103003603001c40440c1071281c1401c51400d41030390702c0041c4075820b00050610a0410401c01221a682c1060280c1c540000e403068032164401250501484000e000e19a4030f00824900d031045400140e00148540c038007141c2c0e80c00e002e6000e05114074004000c0c0501c84c40c0080ca203a0b1094a030003001249101030020701501c50030740090a020310f010300c00d08900210303404009030850508254041ea0481c4507044060170303a8100c416122401d81020001d40c1c0c614004418030020550340603001403e070020030510641d20360050b0b8003035000d0066007a00113180c803403004130a006510345044e000040c0000e000521514083c0d60314128142e009400072035807548880c00b03e03080074a6a1314204541d5800d1521405010380041321000400c8920051440c0000503004200ca510500022541c07444a48109001c07a0f6050039200d521001741200c0912070343c0d1250000d9844ad01c05035541d200090801442c1c08052802e10b0072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359231411 1250 359230161 359230171
    0x3040b0603120a08090f19080a030612060506030606040b0f090c040306020c1c05041a070c0305100b01090f0305060c030403050c030f040816051f020a06090b0105091006021209120a061b030203 84
    0x42a41c070300c101f0b555408010750050310300c07404040c0c40f03000c0015981c41042d01d020000d8032651000c680ba150402c18075150000c0140300f00d00c1a0f0410a0650f0b10391200c024030048500255400c2d54140d48a10039504284075540c80140810320000c0e860300300803400b15140390005108010591203940e0f805046030380703008901450400c450b60701d40f481f207008078503c014944548200c0f800e0790055681c0e00ea10381044608400700122644030450450a5a4031202d624050f003801c0e0114a02141580c0720a031740c442c80103010400c200000800701d410315000350155000a000c907411a0741d0351110305010071240e085449100c02c640300c0c00c1106540c5407150b012210942d0b401030721b00b146a0520841c1054583d010b04001c60642c09540c6150010078480d00884040310300a0582908551400b4248a51414001c04950000000c01014080709070301081c0d1011125012000c0d544815003140054181c42c0d000ba441c0a4a07c02c40f900403081100d03d03080341d04000c90901c0c242c2d480300407140c801c2d8168402120707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359232661 1250 359231411 359231443
    0x61202180108040321020409060e130201050703021c05070b01150e150c01391202130e090f1009022b0b0f04050d05090603040b0603120a08090f 63
    0x2201480075403050100580c854003900d41040c03803403003c030805100300c08000201c40b149600040c090000703007110302800009100c000a4011a854082c080f0140c02115540080c10010001920414140308100558100480341d19803401c0031030000d4060540d520400f0300b202c013908900000140101c03c420001481d194a07200d012502e07025808100e01c20708601840c06242c1d80520441501d28000d00c0b900100c9080c080034070100f501c02d03149100f2031041002d0b41d120310b4000394810302c256070361005802d8404903880b0030260312000c45920564100840f03070880e07018003060341e003084a41180011644c403891440310a4500d00c00156440c40295400c0200103900a9621a4612052841168075181c6680311a450f4609080c0c0340d80e403402c4440b015110000301d070b1108800d00041c40020f0040070498403ea042c003030b01c0c020000b40480c08501004001400b4244103000042040c1c130103001ea500d054000048803540c0d0b580f140e03000752010406895100e101d10a041a0001000c0c3c0011001c2c0c403040054 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359233911 1250 359232661 359232697
    0x40e041a06011b24062105031b07050405090d0f08060612040809030d020318060301030b040f021807030f110a08271005042a05100203070c060801061202 67
    0x4643d10780c0384201030b008840400b65090401d241a0301d80480c1d030b807201002d00d004202c5a207000c26038101002070101e010b442404250f83c010000700e00108542031503186003185016040c04a24840c00d120700b60340025042030a140822280385000300341001403d82580b100e0100a03800501150a414100c035040c5d04141c0402c0107641d81c0c078510040d190721610810420340750509031400b00f0304044880f541c02c00580d202060740b40c04546010b081001a14055a8107403c540c07550b01c40e050f207c1d0000d00060f0150000b014140295100d607400d0061010050703003205207504114134003c00426841d10142c1c103507890f01240420300b6404070201c854040c0c0540c8c07040c5071500d45c0d201003241c00340100d0600c581502d00c803030000f41811042c00703418540c0c40444000511842c050034a003640203501c2c80342904044040c0381c42c4445d41e201640c01c6080d10400d660b02c01420b060200700341c1c514817407401d010f0010200c480c00050625800310a01f410381d4081c0e65075110240f0f5403180780c2d0682c0507804400782120a19 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359235161 1250 359233911 359233937
    0x5041b05091201020c010606020309090906090a08070f06060f08011a0306040803060109030f0b01060801060e0a030b130f080d06050d050309040b0609042c0f1020040e041a0601 77
    0x11200c041040c0038500061170010b010070301c20b003152083e510070005a000450800451f10780300c2a242c1c0e1007500c0c0006060b06107400e6a02c5034544c04852002484517401003076440602800b0019040c1c081d5120000b007048075250f560401089105115541c801e40c288a503100105258101640e02c1c2c001c050003c01040d03e0716a1401980d4000030442c904000a038540000810550309800002c680192510055941403000081041205802440900001003190181901c44002410480390400c035418003a03110403108140382051002d000d00340385001c01001c1300740b10b4450002c0ca6061103150b407c0110350f650708203001a00c1c1c660b600c0a0a140c10521405403d410241c20100d50804000d100c20310741516100010f0844100c408891a0004600d010b4240100a0003003c0c145024490007080c4070082c0900e125910222442030f46200d9403a810007045a940e80803001c050400580d9005442340e440e204008446a0b00716401d0320340183c2103013805007040101010900996040e900c400d607105031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359236411 1250 359235161 359235169
    0x60b01020d05071415010e040506011502031b03090d05010209090f060d0b060409060e0618120d0e011b0507030305011e0b0306220e0f030a0806131e050105041b0509 72
    0x5110140541c601400d180640d281740c03507042c4a8040c0c040884040c080d41000d040140ca042c4058110b0742c4800c4014641541468001090b40c00c1c3c00d00d120381c1d00c0d01d00615200c000e41540140f102084d001182400744104011043d00a40201e54060b6418103e642d6a159118139601003502d1440c0c02554a4815038042600c1001d41c81e404200a40042707003500e00355a45000701c0f000c1d0070104426811050a00a0000800784a1100c07440030200500f00000c000701c0c84145807183c240800b0400da543e00c1c440504071000e40020208480e16500311141c030540c0c10014229501402080300040d141a0000c030300000d0302c2e0401e035045020500540081420484d46a9030b0b907001400343c0742c0c000c1c8240907134994003600814181030380d0250034020030346000303940000d41b400e10241d19401e10354009019007248103901007641540110100e5001f6105002e0f580f944006200c03034a05009010400c4140e20f0b20540241c2026040364010b640030007002e48140014003c440c0078900c80301c00990104002802e51034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359237661 1250 359236411 359236433
    0x2041505070807050a030c05010b01080f0c13030c080102040e1b2506050a0608010b040b18061203030708100815070f090b0c0703031107121e1e060b01020d0507 70
    0x44a12500791030107801307031581d40c40c1c145080c0d001c4000400100c0b650013006000c0c01014684542801c0c401d105007400000e030110014000e01180c20307924041043c50385e00e44040841801540c100c00005541a160b01d0468041c0d4018025a21544082c1c000700b5140e000030540c903120301c8400e0000d1400d05a00400b100308040c41586107246103441004600c001c100c4902c24036001d05903040c000100305281c01030250940e451014414421403602c00b503100152900f2101d07d40e646208014692244d94680000d00c40d1045011007101600c00801007118141e00300d11458010405030a428071040d554100c0f660380c440012034441c040c1091503011441843c081e00ea066502c10072418000540b80d120015042e143d00050440700c042c0d1b12500d001c1041c0b68220200c1044401d01c40b0140043d1070030300c901062050b41580000b00940200c0801202d1307030300c800e4048000b555024072616000841d903c840d44804000f99000e0700c03038610300041c600382076000054040306a0703400d4070b8050502015031661012a8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359238911 1250 359237661 359237663
    0xe130b1e040206072a051903200102120a0e010801120f06050601020f010f0b1302030c030c0d18030215010801150605070f24060b041202061b011814010204150507 71
    0x1d0040d2880855411580e6054402c1c21030580c501601c07440c10302000030312040e0f022410107e0b140050705102003140d81603ca42e6010b05144084c02007007800300101d24103811a02d40c032420000106200c0c040b141c0c402980d10300e03082c00340e840c880140d032200301d481c0000700c000318002d00110054103100f0000700c0d1500400d034041c2c030500684100c0c81d00d9460203403d581004402031643c617030b1050021307900c0c5840c03540c1e509207407882841142580f070000304600d9079110281c000c40c80303241c020441c42450480740e000865400fa020300c505445040618020b03544076101c0d80d101240f481428004a00d2440511802110120001e0900340407803402505403155880705005680481c40282c203000420b080d140c112612402c9840c004034284141100403086580c590010f10329050108410006011101030b9070180c182c040b241c1550312888034801c400e0207030800701e64400035401d01d01040441405034400b03e500e54001c00502d18041c139100b410030300300d128600801e011068460b201c0c0310480e2250300502085 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359240161 1250 359238911 359238923
    0xf030c06082e0b0d0e0601090216080c190606060813030504121a011d160806060d0209030a080406110601121211010e03090f120a020402130e130b1e04020607 69
    0x41a02c9180c41d0289034000702010540507111034403200e01090030880a401088d49417421810300c2d11905400b40e45031000c92001d07100603004102036000401c24030600c035141000e1656800c1c099428034012010300750368490070b0013060610000840706e09141c0c1810264030b80c1036a95a107002d062009224201d403500a080d01c0484c0c0420040b0050400040341034044c00380004040d01d030b0b0350034605201a0340c400030242207144607000c414511454124647c10340150084031a03503114010010a00000d0258800b02039251160252150501010030020b00903103800e03523154400c0002484009030303920001e06c6004901480c602c0d042c400b040c0c43d0b03500e0310001013440c505001075800c2c03259102d00390b42828240400e03a0b000001d4161072842c00001204c04030a054900500c1c800080c002161034601142020717000302d4001a2000c030301d098110b495000307000b01501130815030503c41105400402d00f45021501c6c3d901d08130110300e0f00c440c40030b828940001c2d08155010560744960902840740c0107010100c5007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359241411 1250 359240161 359240251
    0x40302030105090a020f033921010b180a0b0411030916060c08090d0c0510120501050a030f060f020702150702040501060806030c01270f030c0608 64
    0x140e40c20b0140da40030310710036002480c280320580101b08030802204000c03813107039101d05405415103010300070b01760f210f5403107480c410401c42c1c1c045100588041c404235031542c000201c120040c803110702605c03400341080181000304030f458164020300c83c01a07000c105981d89201d011001603e8030406400c590a804406000882c1202c1d241030300d800c0b142c109541040680e00140285001c3c44110607810006209516005030421030035103c00f982c030f100300c03202c990103100759200b4841801207401c04080180b10181624624000d200c2004100c00c0307004225000d00c1d401c03c8000a01031a08550750310075240c10280c0032005104c00e0351124001d18180d6a0020081d409000c641d0169039480224600e00301601e0300c5540e2600306204000407030303605820031300a0046071300520076183ca00103400b40b1105001c2c20300c5441d6504103080e2080b00c0c01c41c0030303005400070714048000c15116625401a0220384c0320b055008991601d5042c2a2000d5a0403100c11182e9080344109055006c01c14035124540d00304c200411007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359242661 1250 359241411 359241413
    0xb04050c040501030803010608071b260309010e06090331080105040605040210360b040b07121b030c0206211f05150304051606020a02011b1502030c0403 67
    0x36030b4426030083c0c2c0c02d8070001c4010020700386c1102c04103600c49540d00e82000e9150301e5001d0440441a18800600b18060340c410114030130b0380308811125106d0385a0082c5840740761000300740c1c0c042c00191201c10780d24000c2401040e04042c001040c0c0d00f0b2003008a07407010800d20340c1d00614800141d0040d00d01c4088000407400a07600c0002c0c0304c3c182c042c6005500c041040e18180c0107204102000c02041c0c01040325140201c440d220900d8102c50551200401e107010503103403141001d940740080d030045113101e10005000180404035100401205114100e50300b00c0901069054440303414444c4036200710914264106d00007440303034110b0401a84018212810091841c0c90524a07014540c005600c3c10341c0b05007404100700308144000400c50100200350015801c0c0008518540c040c5d0070700004020011002c07404102c800d0280720545420502442c1005594080081d5250340340c1d801a03001c10341d00c0140d070303c00018485403200c2980c1c11190100403155903000010007584000d003802454201404040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359243911 1250 359242661 359242669
    0x4051005090a090c020a1a06032a1c0b07020a030e060a090b12040201091a04030209040c0e07081b09010e0d0201110d080411040c080c0304020409330203070207030b04050c 75
    0x1010350521071740104421840780c64000412160f0420000c088042c04081000b1a6000a045a4a0b984074001c0403203800a5500c1e20507071600c0c1c0d440d180c0d4403002c0051003a10010540e000000240c0c01540c102e460703038680d850281e80b24892024050002140c10b40076031050705094004101c0803546160005107269900040582038000e01140700b0b14403103800900c4203641e440070413103000d4010306140441c0c3ca100030364001200d10032848000d00607000d0340000703400d00800704413030001081540c8a40c0c4c0039141241d03004003420000c03146001c621042000c481039101d4100156800107006840e040c0404803070500300504103251100881c1041000881100c0c104001d00001c0382d151940c0d00c1c0e080b5681400e00d0000b195011a001150055161078090800964040302c0141c2000caa0058a41e4a032600e00114000d000444d202130400c1880d1003000c02180c03114514900e8802d01c8000d141c181c80340f140045401da100c141e41050041c3e004001c14400300b111500d400d42c015120354201d03124004204041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359245161 1250 359243911 359243921
    0xc0714030c04110c010e07061d0d0c080303011805070807120e12040305012a08130209010b0d0b0a05090c0a05090a0b04061b0c0e090102072f0604051005090a09 70
    0x3c888800c0458241d80344402409491000314195010b050240c0c2007440080ca03681c05024444010313103468a001e441c54840307842c04805207400184141240b604d034240039a0300d600038803880c0d40300c4004841907880207440b489070138000c0f880c55960401a0b116441e0480d100c041111030700401d02e42e00d102030350700c40d00200b01d440d00864014200030f0300c0342d00d5410300608440146200103039a0400c202c0c0c40209204100c851481e050f254100703101c0c1500c0d640158005008100c1000750413041600c00451203a501c00060400d001c40d001080c01b46181d40b40901c0043d005c1840380e29000036804000c00c81d0303091030300050903680d9120700c1e00318142648040002c07410044c50f0701c01ca00300b8100041c140006c40c1e00503c004d503a9032800ca41004ea141c800e81c0d56540312180c5108031070740b0301401030100d20005801e4044481940c2c02c61003030205030070720f1004050149042d840f018140302c8040950a014284081030b20b044440c01008500800c0b040c1c603003501c441d4800161940e0000b48c1c07850100312014148070b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359246411 1250 359245161 359245181
    0x503240d0602090f040e011e110415200105040228030204050c071a07020d020d020a020112020f030a05090d03060b03061903050f100c030902130b03120c0c030706050c0714030c04 78
    0x32885c000300d2007072007010485408d020000181840c26956410701c0042c100c07421a49282a181440500213404aa40038034911a10030031502d80c008010b4031650541141d40680c0c02140c03011030b0109010b0030503906e8000000343e80d0303404481800400140c50603500840e444080d240407103150108980d50300c00801c1104080d00c0603041c0070014400e51503410450162005845e00083c40c651160744070180d84c4050040c1d009040000304d07510030241141c40c1d0103440d8840c60719242e40f40caa08085280c039002e01403c1303511800234410600d000c1c0f803070f5201e40107400489a60303503500f61031030312100203101c0c40100115280d840c50706030410000026600700164080050648098510281c241ca03a1710180c6980c1784c001c0007050b080220382009170f5500b003e8000044144240003c208082402090a044100d0044007140d00003090422400c103010170300c03200c000421070a0701d15141d103400b4162007601443c0341d00051079000c1c1c034060000070309100c40d20081500080407514000f0600300081c094030b03c0480 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359247661 1250 359246411 359246413
    0x30f0e0f060703092303070b0f070605090c10020c011218080c100b040b010806010f0201141906090c1b15020708040e060904021003020d09120503240d0602090f040e 72
    0x400022085c0c0300e0070a0307056014a250501c00c00100c000070341d00c040074000c04000040005403446010800380448079400e0307001c24244002d1400350341403500c4501284c09180070f00c10b00090018a580702184144071030700142c440b42031001895030303044002c240c0d040d84010b141c40e400d011311001c0303041030000c0d0500300500f8000b0f008003200c2d040b0060540d0900101c20b07000e01c3c1040116880d070380c0c0110440b035111a003840c280d00001c05400c8102c4c09405010355058950205e401440503404030340500001c01c50f5403190604c0396960325440b58040310b40411190000400681c808090310a00c04162051103008001e040c84c00441080c2c01700482e4011704080b50f402100180c10821410182c6086500c000300300c41c0702c2401e00d00350b0007041c01112034101c040105a80040c10026660740303903114255154010b81c542c40d6000c11600081e04070303132068801004224100d2002d49640f580a101409911000340c043c081c41c4680fa620640079402c045181c2e644240014825406500e8070f124185842511074 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359248911 1250 359247661 359247677
    0x306020301061709070b0711090c130609050d080912030a03020702040c1d0405102103080f04031d06040504022a0d02071401050705030307031b0c030f0e0f060703 71
    0xc0e80180583c140d2020710a4400d4000c1c0801034013042c04100d282c04c8825200116139550030740d2804403082021210f503c0e44c400d4002042c0300182c0400406000c690011200380e0003003580703403c41035507141d54620800e94005080184440008c160002501c6004806401c84112016020110341190000c1400f6030000fa80814144291b1400c0c1c010410310310b00e2410400c200440c210040119810200c4065009907142e03808612020900c030101c100402446100303c0d0324400c8600f01c005103d81c00c2100b60f000500e080e0101d041c86200c09486801158980c445020740c82c0e00304a000705440d01c07480301e0342e40f000c0309010010309a155030000b0448000740a110700d0202024196218000704050345030840c0303034403c1a403070740c19540010310181070301e03544040901c940111100484080c881c82d030b4000c21a0102005200b03029030907410544103910500103400d90002d4070041158a40708004001c2c000840742600001540d0040340c006100c404081c006070010740c0c0030790201d00b180e0300c840c0302240054164 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359250161 1250 359248911 359248919
    0xa030f02151c06120206070615090c0503040210030513060905031c09031404050f09040206071211120f0304080c0106030501061d01050f0f090a0b091806060103090308011502010e06010306020301 85
    0x501c900409404115a80c40e0070b13000030740114540340107000e00140760a6840e4611900f410400c1c0c2c0080003414031303907000d1007001c2c48008020000d4005840c22809419881c0200904500034000c070751180c1d40d10300c11040100b1451b191070002e00f4003504291464001007142000e600c060740e00e074814900c261100402c0e48600ca242c0140b111900003070140055900b400180482d541c2c00149400d80403088401c2505a1141c1c00090058401d07018010501025041d4448a148c1c1081c1964044100b1005445100c801040c5040292041c29000d05082c035080001030002203050025240c00ea004400002c0c00c9602ea948481c21a001901310310b1303104403641314007240c4c02c05079880b0034050706080d920800785e58100c00200d5818002d82118600c58915000000c800c0e01295000c3d01000750000d04040c0c907400c01c286101c10aa80d8280d480380d280c0640000a510707540a4003032110b1300c0d541680d60108603868610001da44e0b003100d441580840d525400348481442003045002e001c1c5000b00c1c4016940c2d454 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359251411 1250 359250161 359250217
    0x28050114070f0206010b041403010e1509150c2a060c0d060b09030307060902061611090903070c05041e05010308220b2b0f0605040e07050a030f0215 65
    0x180b80079046500000041c4003c00e420400e50302100c0c02109a005400800000070f030142c602d80c8001c000354450b8500c42d00c2000044000640190315000603038481d400000014400c80d10704854042c0d20035005c100c007542810350901c050003a03140740002000c0150100c0b8280b401c00b50155048654100c0102d4441d2102c035031842200d0050100904151030a485180820740324042e0b004003501450382d1790340d014207646800c000c85035074600304105590b60040070b240042c00190001c0c0080d001d40c81640000d2040f140010031110702c19040410190f9241c944000c01010700810703102003212804a55046000d04120b0007000e01030f40c499840180c54605031780c40c0f801d2507111441c0101e444014070804000f05144941100e406080c0c40341d400340310403090315031008843c4591021a01040c41c1083c20034052045503c43d40903140c0460341402400110003006559030924081d50b0382c010500e80003040080c0f8100f412900d11480076115034051940745803556641d030409404030800000c02801c101803104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359252661 1250 359251411 359251427
    0xa0201080c070203340503120c011b0210050a060b091e1e090903030103080f0d1104030503070210030209221103010f0608070302120708060301110408010213050f032805011407 77
    0x8483d61700d62400d5032900000960380c03842c3c110a4101e11078005001110300c5000e40115840c2034454045003a84801044021340d80c0d01d00440080b8000d02e050041260000c003800741030304546003040c0c0741d070400300d544081084800d004445012a0107080301d441c00d440d03d503841c080880741c00e04070409003903c0c0500d041c400742d4500140034010980040005000207603210302a20402d10782550142d441c1c00c04900408018503071500010440c0d84089400810010000000c2c01410710036030380500302e99006207068050f4000c50366030aa0002820720108403410004074208104030864401241d002c40648040415500c00c0e00820040384d8800d1040c041e80d60085041d40d0090480e150451034509070710381d0100c49000161581c0100074a0002181081c0d400350040701c49004848a080c0d07035981c0c0c84100a000794400440303240d000e0003040001840d0702d021070220846100107805030403a9442940e20490a95055495034800004691640e000c03400920462200c2c09004540100307a042000b40905618 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359253911 1250 359252661 359252743
    0x603021b06010501020d08040611040f081605240d0f02031012121d030f06070f020102040e0402010e06070c0303050a1421191803090f06020a0201080c070203 69
    0x2501c0000108250390380052034180288042c684035249445034509500506004881740c0c802c40c88c00300b4040389030410310301d42c40d00b2903c450040b141103030400745503054004140d10481da8068007108007003042d8040ba00701c41c2011030041c011285840421400d28044401482c1440350040e0f010040012180701d0f080301d040540211210500700c40c16950310000348000444c8020704010300509440180440b120400440300030090a681c0390348904140282e441c003003150440f000450f412613003401d050040c401c4030240d451800403000240d640340c0064413007881e101100c58018000b00501404640d080040802851080c2c0d01d061340c4a91495005103a00190814914941d40410001c1071826143d941580c022003040c00c055801c0d07462103442184d61a802400da1592420300800500c182d2881d9681002103200740c94241070710b5180c40381181885224040d210141e400003d80c00b01541c0210202c0341d12613507081d0070516240081e030209003000c0c00040000021380800c00a600300320a250102c00c0c040c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359255161 1250 359253911 359253913
    0x60105040f09110c190501110f03010918051006060306051c240603030c050d09150513030c0303020c010e0402030907091d0106060f110606150a030608070603021b 71
    0x80c1050007192800d8000d100720220700e0354614441c007000d490715054852041ca101305403482410781c141540b40e540c2d05407400b181d10f5480d0044003c41200104141e0b9800f00e042e028a070700f144e08241d42140140b408001c0d0488510409854100040c020002e5582c1400c0080000c07880c00d1400d50040d0030f4554540107548500003040081086901c4002107440158002d10910171440309081d6090503240d01c0741c000303081d460030880007000345600040702d04c021600c6502141c0f90b08241c0780382226a140c1070302500c424a003541d90014455072080000e08250104042c602440c6550307a0348480c092103c81c0e0088015030410303a4815100d43e0018050741c08400705507420f42c69450501e403155100c01c118050703a9112580c80102e402500001e00c0c060f981c030070300840204003042d01d83e00040c040c1e0f417201480d54006600744800070f620840102e0030500900b03016080c000d0000101e440b402858104061043c100340c1d0300c07000081d0074202040b003038008102540f80141d4480480803851410b11a003000c4500f9 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359256411 1250 359255161 359255167
    0x191502060a230a0b04110c0705060a0e090c0f070b16030606020c061309050103030305040b0a0e07030b07031e15060203071208090f03030705090a0602150a0e070e09010c08060105 78
    0x6001c50207807090142c0308180c25070b8142d40d440d400c004004003072502405070050318040000e980188818010040902c3c01021138405550b90700c100025031140034401000500b210086012904081820702d07003202c0c04c0201030381030a4130705010003101d4104c00000e60300c51004c501440b208807510b02d107070845405546401e1028a00f0f25a0283d695407440320b026018043c0000c042190350041c5001d50090000c043e0309001550b524100200a400251000d0b00c90016440c0880e000b000e0511465060140380c43c09400c1541c55610382d4458540010008000d06466011052400030036101d000990055414001840b4180040c1a001c1a903942c0100080d9803007000440301103403082409101c03401c43c925113160b0b255901045107042020325800849944004401e00c004190081c01900b0703a1042551300395041175071120220b036a00e440d0402540c00001d642d0100e0345800c035a03003110010003120001c44180c2d595500348010450021170780000070703035550f82c0030238080d42d4000328007900001c09283c1641 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359257661 1250 359256411 359256431
    0x50a050105061330080703090e011203031a030a03021f091709040b060a020d1214070c05160b190201020a0801060c0c03020d1b061d010509191502060a 66
    0xc3c030305005003103c48000700540f00303610030b1641520030300489600d40c0b50b0000c0041c0c94642c0d03c6420400040f008904054000b00742c14895400441c100d41d82d503800242c819415817001e0f001411707a100e00701e42000e4000b4080c5000c0d1030800111140ca842607005000743c260340c04e46044902d1600180d0041c584c20915180c011500c4088403656012a41c80351550301c829900005c1c000382100e001482d000300c030103e04407690f0303500480d9244090b038083d180d030500841c88986c80c604581d915030f5011004120300000c01c09040c850090411601d00c52802c0b69401080350160810460480e80040d04500d000030310840c2400b2222804030404841d40000e50a10611000140107000140124410070100207c0442030180b1285204c00540d0041c11000d2000c00c0da0030a1081c040c07070400840c44820402d8800100188220000b030446a81d0b0000d5601100a180044401e43d1200e50030541c0200402080b90b01419414400c1e4018104c9410700d403000001c00401a040003c000c040f84441407911030070f54 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359258911 1250 359257661 359257687
    0x2040b030403030507110a1b0317030a0501050609090c0a09030204021614060906041e1a0103050f072102040b2707170109020f131719020a0b03091906050a05010506 72
    0x7101440e400220740d01c05046080448840080c0b0703601c00303403504008002b80041144108000d5004203007604c5d051050340c1c4c845040c0315203813050002c015088004040011a40029503000d0840d0030001d2410001c2a640e0350001800e98200e00c03100342e4100c0721301020301c2c00c120100c40700c2c01e03c450050707006d080f41e46889080c4030b4a43c0f50080000e0403c0c013488844410f4000390010600406911201d4084400540c44103c20209002d02040f40e65100e10303100810128000155481201e000d004c41c0080b1383c9408040040712009110304a800c6170310b03181c02d030802d99030317119101006600503444e1081c80c1c0011900b821109801420241c24090f00c1e591326200c540b225004241507404030000540c2e0f0741101d400c02c542501c203501d0103112a410402c00440e008035a000301c00c540700240c0048501c02c9a00c4240340c000440d00c2c8100a5001c10100c600300210b401000c043c5501c200f0110030341f201e48402c0649041810410281100c000e5610001c000081d202d91140601600d4140c40d900c0c00c1140681d401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359260161 1250 359258911 359258923
    0x1206190603050d0f02120409140106021b01031109060d09230c0108070519020601091116150902090415060906180b0f031e1b010f180902040b03040303050711 69
    0x4401080740c1a402004132a0080025251180646102d50707515030b42c44c281c1c10001c01c000440c0e2110050481e000140f500e03c000b41d00c8422204c902c2700c00b83e00d04401c0d40154024241e00c00400d48041e4140403155043e50f44501a0180c00090203003c9207d0f031003440d0140b4140741720000c804403203610103242c904e04031000580c0d8042640a007408200d9498a003425110b5004813540c45150008030303d68880007a0380415205c1c100ca1038041f0610001c407135079444030360034041c031056032880015990714140403a1960740b4010100c0784175031001903044103e80108d1107030241145d0a0300c03052000300c40007150040034030034800100074010742002103a042005184003044410404444961a540a0030044e5102d00d03040c02e1b00d21004044503003040e0b2680c41030001e11b01e8904d12540900440344400340041543c4080300051038142d40707104012861610640f5002c00d82d081c05170541c0c0f0085404101504107100620240c890ba1062644034681890010140e07003000309010100046c00c0d0400c4542440050301c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359261411 1250 359260161 359260183
    0x40c0219080f0403020d0303021e0a02120706060b0a0507211b050f07060e1206130f0302190c090f1103010510110607090806090f150a0b120619060305 66
    0x3040b9500c4a0031403000801d40520340000c0d500c03082c0c40841004140c1c140d4000c00d4280221014110038032400c6492200718065503502501503040802080c0344400765000400c0c0d240d1196500180d415110700c00e0510a400c492869400f1030070004040b02802148184180e0348501065031098820302c8880040c0311442490403c10520707049036000d02000010320903041c7e9528031000b00c03800c05030b84c1d50f0002d02200d85010001d0184401c0c0603500e400320004644541301c0d0b03001c880c02c3c0c1d041c0400c0c0c1d035411a01044001040d011030040c004000360343c42803402d940c0b0741703680540035a442c1d440c1071032036810449008a40c1e6082c003620700b140f6844003c80c00806c0d00e04640c41121010085250007070140c40e161760040b108030700d5000c4e5804000b01141c105200c0402e4a0112045460503550201c2d496038640c07071032440520340d910604684001c0c2d05000b07180b43d8401c0000d0070210f01000c40030b000c80c01403051301405482d540c00c00c004000c40380710038040011035100c0304101446807130700d5a201e0503101d05000d90 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359262661 1250 359261411 359261423
    0x3030e01032307050d0b0603090615030a05011a0a0b1206040b0102010b0402131706070503041209080a03020a150207020a1509030f08120c19110705031b040c0219 71
    0x10301000030080314202c1800a9045a0307002d0101d02e07040400524a5018000000c3e0541c5040003d94190074800182c910822600c0010075141c0c890140c58100c107441c020b0219070500c14201d42ca40099020701422902d90015000e68000ea680b80d0100300341845203030080301600200344040d012203c0c484800c030b900030000703480c0001d1120501700101c0c050b12441550a4200d400011104c405000d40d5090000707c07600b80d02402c4813140c0c04450301e6200c00317041e12204009001071002c640803e88140c0070107606000390810110256541c4000c90400e201c080082d005a00b0222482c0c0510a8100024013a176070f01040440c90140f13036030300150400c1c9980c01181e004201290b000303480f40f070203402c448000d10f0f0451000d4038a04101d10300002540c0c07000703580325040c00c20a000706845171480380980d0005110445140c11860f072404044440030200c01107050144030329030340003899441c2400106c2c0f40b840324000601c0c20901c910140300694400703c03041821540000200040c0456906104040c294014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359263911 1250 359262661 359262671
    0x30e04060f08070503010c0201060f0b030603070e01030327050102120310170a051203010e01090f1b0302040504050f0c030103083405060604090c090f0207150c0210020403030e0103 79
    0x540424010300c1150000d94640c030110703101140007080002d4200440740200c000340090140c3c420100e0a82c0d209118645030301120b24014011078981c400950b0b0f219201400b00c03542156a08810032481100f81e01c25000700d1b000c050458210300702c805826114017142822045c2a9203840e0000b9501c265103040c09403403400100c04070b02c2070011078201000a214450002c481c07205140341458448510710011690b6214200003900400c4016050724121146400c1040d90b076864406c484000d04411010001000e5840b2009181440201108280d50340d180d6401601c86050131705000807074001410660012a01c2e10812000b400341d182103906690b440b484694490004000050781d80442c4c9400403889590b81d41c06849035800000c0c0c441081e400f9004885c6203071244d0090204070b074100c100140141e4150342c010301519407160401d9490514078440145410116100e21070591480d0100f916101d807280360503208940e04000300e01281c03c0c40c50085241914554000e407a1296085030103050545030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359265161 1250 359263911 359263937
    0x7050c01150312171014120d08190e0c0402130b0309010507080106050c0d0e010212030c0306010e180601030b0d0219080105090f030f07021c031119030c03 68
    0x20341014240c50707003010312100030076200e28140750340604100a520000c1d0a01040a4098008810141c0160003141c2c405090b1410210015840a034202c800b40e00800d07c0814401020410451105001000d5813190464106055110070240105030505225401e040d05003195000100b68103080d45400c40d401031b900c1c800d2a200c560b1841d000d510090003000c0100400050100c1900080e2145225507100c6c10180e81b80c0c1810b03121400303640d9918105520000c0f9001c9030b00c0c01002660313a005014012a007411142596010113980300f1181d1003100705010043c0301465030030980304903001500700c1e118041038036500c42000d15103c008103850b040544456a20390740e03440340114914080d80142c403440c0400c0040c100f4240d082c00903c9680d60035031800000941004011450341070480e80300000e10b01c0c10741d50600401c901d410101003039a00c042c64070428050700754801e0603a00c8551098507004007030303404000964101005c00c0c14030005111000019000698480203108405605082001e441c07000c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359266411 1250 359265161 359265163
    0x1206031e02150a080a0b040911150408070f030204051b030f040f2001090605030c04060e030708010e060702210a1b050d0c1416061d03010c0e010e09090607050c 70
    0x5505410b003a404002529000040d4070a51107031040343d183d1810302041c3e0006040c04121294190060118064058180072600d0300501c0450511041c0c50382c1420113403034009982c14444594000325080312106070820441c20180034590340304082c10803841d9080e11595914030709100060049846006c500f0000d0b0130410440703107010b40c06800c00703090714070074040c034003605c0d85482c00d416818082541420002032040c440d030201d030311071801c030b00d00941400c1c0ba158042d28000e540b0216254540107290012420802c24459000041c2d05007000f4030351070800c00c6029041040040360424902d0104807841512100302041315a0a0f03140c0ca82407084200380100f4062030001c0700d20017031040c02a820b505183c181c0c4416003206050086001550707060407120100e60360100001c080101c103c1d000070030800c1d01d01441c088140511301c2e41c1101c1c00780d007078200000e08503207510b2106008541c24010b044a1b03540d00c903403100c510351816144c80802c2e003403884a041c1c0c2e408c401010306080143c0003540d1080b01c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359267661 1250 359266411 359266429
    0x9010c0302150106080103060b150904020c010902060a021e0c0a0b0904140f011511070e0402030307050607180b0901080c0a03020c011509110a080402010804060603120c02011206031e02 81
    0x42da11203060103558503881c005000701c1e405e11003510319600300111031341c80c0e243c41040e40001d50358000d8568a04040a03040c030cc047c0d000b0320b0740805295a15500356002da290200282a000d0741c03540548440c03080c01c60108050300b05010b02100581c040034042c8202d4440e1408041034402d0300c2040ca8503041c2c00000a8058000c1140100820540d01d082c4074400408244903030585e81c603a14100c0c004d0006140454000d14402401d480307a9118680c00c00c010750040c003c0a40042c0003070152403030714901c3c0e110031385044401e482501c00202001150b00c1440d50544220001c1c1c1223144c040b40c90221208002054a0700240656076609400140c0c4450a4040c3e0304894185845000034048440c0c5080741d01044182486507520a5040c6101071003500d0340c0d041110030341c0e081911040000d486580044660100082048075000c0d80c0d01d4020020855108030008406090f60700e000c890000d41c40010701003a501094007a00900f090b00c14000100009c034901c0441130007803107a02d074401c054000915420 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359268911 1250 359267661 359267683
    0x501020d270b2e06030e120f07060204051906020c06030405031c0b030106090b03060a09051902010e0612040c0e0915190e071e0303090b280e031002040b09010c0302 72
    0xc070741c00300fa1800078039022525000300c43c0d49440400c02c0388141d541d690340302c0003c0352100c04c1e001e07000c1008107030404a4801902e601405504014103041c0c680c00031890145061480c43c409200010040020b50382c100100d0b428044107803001419410941d0711244e89001d040311411a01019051228110240ba4803030340314140011b00078001150ba82d29018000c00d40e1400c4140280a0800001c40182c8240216480710798404000c140e070820f00c403491900e620f84020100c1c1008a80200011a50360304005066074540b461182e40ba2402c0034985514804515404400c008a40d101040b25185003c91047c1c490400380d0010000359071408503000300e00e0188404842c3d22407a044040044000014a00041d00d1107803105020032424110b4482100007e03101c02800a00c000400388001403420b03000e442246c03401c07400f4240f8485805406004171075a0315075840010341d102510b800c240340422050032103501840c41146400e0134407110140500ca0702445505001c0003440d410304161080046811074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359270161 1250 359268911 359268961
    0x90609010f030b211015150c0204021801030c0f09060309030903060e060609010b12070507020f03010908030a0f06030c0302010c150e1b030c01020d03110d02070501020d270b 76
    0xd00c1c01c3c5060213040808203000100d0340d21510304007010b10f220510414107525035042d0001e080c070749801c40740150041d081d2032001c10441c0700542c080040c3c0307450018213140c10100c098000220540c00004085840c103011074010001c190740010b01c5982c00c4500a011740341c1c2854081040501410290703400600c0307900003408a0310b0300300340081602001c42e5241c00f542084513502800d036079070101c0c0101030150080c02c2c1c05500820002c540c8a40c06400140075003440071700101c8a2817141d4001a007101d40d43e0030103461941c0b00004204080d40c1c1485841c4100400410400401e425500c500303074a08168040241030010303440010302480140c45600a04240038201401000b640e400343e02c0d21803288040300080c16210590a043d50302e40440d8070390b84000107900405092013001c004030040c1086403800460140200030f10b481160700c80c0000d0500034020400135940d80c0c80050498101c88506c2603070001010b5000c0d0030090b61220641c00c1850a4100c2031454964031080b43c8000d0400c2864000311403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359271411 1250 359270161 359270179
    0x10c0b0601020f031303020a0f060807030c0e10020d02010b0d080301212013090302370605011823070e0d0b0906070513120c0324060902090609010f030b 67
    0xc224805c002001540e02c2502c1c9504565a02c0c104840b90303c0e40c81c0100341c041a00b0b640061a0940300e580300710700d81d41d0f681c90107100180c3d0700c4011a020018100f400300c0160000840c81c0e0700c2940901a030030030b06101352646d000c4d6115980741c00d40346003c18040c02c50174005014000d240c0c01480c10f941e060582d04181209808050214941404030075040414000c90464510501038401d510031101840d0701900070b41820241e080007520f5101c070b100076800079503051102090009698007103e040e030700d02c55600040d03294101602d43c074155250016543d1410b08107440c051030201c00b04504a410220031268144135150244103868803513a40b55015017000c40c100140b030034004084029801440b00c43c090315019100c00c502291079201380c840014540342150000c118809038004d400711054010741328608002e0b1030341d0303e0300606460080c00c150340702c82c040803100d85401240718900003410114811032a114901e0042211030241105075818007013181c40c0c0702405030081c1c03c0200014002020814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359272661 1250 359271411 359271427
    0x504050108131a01080f0303190914030316030b0f0105300709090c0c110f030703060c03020408120405130f0b0d0605071b231204151103030402010c0b0601020f03 71
    0x103450309205004040c461400340c04204500482100c2c01000022040880981041c09d2a4040d07c0407070400c0703c04000c89181c1c48120341e003c2c40514050450591184a022102000141610312020043e07100c1e104070006211203a07042801c8030314840384440a82c9407002050a401707400001d4013801e88800c0407100030001002c0c0e0101d0040284c50120303408105030b04042900721080010403000401c0416551031442c881e00d4103c41c3d059991400078121142076480340e585809440c001c507545004070340c000c20140b0070204240420032529803400c03840c030f043c94a40000103c400803030000000e489075035065070309141c01c1c264002002010000d08407144e042020320b402d100400c070440f0349400141c40c030782025422000b03d5a03044225030700400350024000b85200c1010b090541d000303081080d0320a0501d92520700c49020081c2008110091014008021922010709000340b021000d10007900100704110050380c1109441300020781101040070180e882000603442d040702d0103070842c3c07144000308443c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359273911 1250 359272661 359272703
    0x307080606190f0305010905040c03020603090a050a060e06130503040506090d0b0906100b070c090c030b0d030e0109060e030a110a08100f06080102030402061621050304110a06050405010813 83
    0xd090b60f03000c0c4e03000c101c00c0e0303030720b96001e0304842c02614000c1031741074090002c00c05481c0c26005550815200e8042d560325549903a41c551818600c2c59080b41c080b9220306030f910b2500f1007840341a902210440f1420140c140390340e205901e9114900405200341d40114521456464100600741d605038400701d4107201d07062128000740d80340c10840d0401c00849600e9000300c0d0074030304801a6003186511116407c020303400c0c480d03242e01601d800500502016904e440c0d02e40c01d50344500c0100403180c0030351100c1c01c18240100004240b203449801c220107000d11000d000000d0b131400100c0031101d68001c40080e440d034400d076000800d5000164854819842009000d04d000701155004840d94075907141c0810041c1c2d40c4002c480e080c0e0108640c00303540000f00344090400c850140c940892100e1280d20b0070081030002d8450001c18000d040300580c00100e010041108119440074040e80e10071007140d005d41c41c0d034a0410020030300e200700d00450741040316090202e040914000203031900e40742c1c001c0c1074005041a1100300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359275161 1250 359273911 359273927
    0x4050c0a0506041203030906150e07080a0203010e01260d020f100e060403051c0c1d190b1c020d02090118061d130515040606080c030708060619 63
    0x10a10400c9900000181407815400b181d045901c0003108040050322034400f070b0024492400c003641d45503114141c10300030003c40401e4001610141d0540402828400001000e5070401051034a03000e10401c0144440124500741d40e044521040e0000f8280340c1d900034440d0316482d10100000c991203242168040702da00441c1e14883c106001088825001018801d6000d460902034505082e4100001140100e84a40b000302001e1454256001d088040400c0c10411212402d110f0800181e5040100350840c00040702150a04002c661494020001c150440d2640c03140f84154804404002400042040000200305100200780030031500c8900389007160700607500000c2d4003400201044007485249070410202c0c000c0d51034550303403d051031154242611510203030000a81e0300c00c58852140600c03140c180980c61141c081000000c0802210b80c7c00d000c1540c906d50049828000c1082c1080340d107941040c11b40390f100c256890314444540360300001c21070601c9019801070982e0300504d01ea841568108c0c105e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359276411 1250 359275161 359275183
    0x80d0f020601030b161b0303050402150333030f030706060f0f090c090305031803011d19020a0807030605010e0c280521060a0b0c100507020a0b0405 65
    0x1110020240a001241c03210002d01004019030b050802003107070010400f000300400340480c00c207050303c401d0f201140765903880f40b001c0480009450314100300450400c102c0d0f010b8807640441c0050f0031801e01c1150100e0403a4a01d008038031401c0288000800f0050071500b500c000c02000c0e0a0780c2c519195122043d40340c0d44040c0090350a01c2c00d00074005000e00c0e0205102089901404010704810706100c502d80c00f030407412010408100800d407002c004114240002d00303e40c000c00081030503c0d8048018035081d103071075000e050541c4109801404444501054000f0b0310f01c040740c0e8010319a40c40d840010000e90054110f01c515219458010003080460f9104d18180c4400e040b01c512190b07148a440c0341141f245041a440c001d61042203d15200c042e422480c603100c8540c20081d040070f80a00307000c0400c1042180e04041881004180304060601c85050006005070300e2240303107411761621005a81c1c4880c03648841501d903130780000605451091044100140e441040c0c0e0b0700f1418607003006680c07507840350a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359277661 1250 359276411 359276417
    0x1113110304120c05060f09010912081e060604060509030703050708031809010f030b180102034f03020321070305181c231c0207150b0301090507080d 65
    0x203080102c1c1d4011020440c6565004009000c15684c00002e00741554000d01400640c0d9210f01080001031341c281c2c260307650700c1c1c1c0c29941c801440c03400c0c05a9444481e5152108030030412004148215a101d100c203e4080d5a50390134025661003008010a1401000e5400900203005000001c241460040000c00e0142c5c3d6024100b14010440000c000c1d49071000e20413071202c0d075401c0100b04001200018001c0e44a0101c001802d000b403000e01c0708a013664402c460034203598182450102d441c4103030b800140e4a50288841209203201146480321164200190b800310120f0480750740b00030036201700211034100d480040c0405018207417400120558a00303688080102c0d05180004030b00b090144030504441c00010004c203180000ca03400040d0068030f81c0301d5001000500e107000e03060010040e0690400403201452140d0359030300b648400c0800c00c817007080010140e0041141c400800c00441e020142d580c107601c400108a0340c5480041d004140341c0a000309540514003001449000c00301d25a1a81c40540d2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359278911 1250 359277661 359277683
    0x8040803070515090f06040f050a061b1101051611120d0204330302031024080c130501030213091a010e030d050435071809030c1113110304 61
    0x110b00940c80703081c100d40b082d117580d00281c00200829102003141c0080740c02102540c11781c8886407103480c143c4100c0c00b401c48a400300c4240d101d8010340e000024030100540c0c00020851070410300d00d020791203d25040303204100700c5440b641149000090014006542614000503a00d00c1d45407003980203500188070781b000080c1c100d451244c042c400fa09800d444450800c01004031007441e11000d40082d0005842c55a052152007070210b2100d200002c1480c4201159114100502920000428072003000b03102c401c2c084820f014400c1448000d175491001d507942400d02580340c07414510a24400318040d400b4583c0c007403d0102c816141034106010340240107003030760380009520031340b424275581c0c1040c10b0010000400030081041050aa40b00d20000c0d00f070401102c00720850341c010240a402c00800c02c89103a81c000c90b0b0308010301c50252403010244595141d051101000644014005451688000d04546a0740b2064201d40c1d8486140303070000c0c21401c404100001e203c0b1444022070700211000c503980c0d1101c0d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359280161 1250 359278911 359278921
    0xc12011116120809030a0c080d450b0a0f05130201111f0b0406050405090f0c0a060f030203060d021003090c1403122b09120305090c0d08040803070515 66
    0x707203d03d80c1c0721341c005100852802c1030141c411076000a8034981500c0685040c410205164828015030080d6000c1c42a240000081f901012201d0114024034100d4480d10f030303410f42040300840d04200c04080d00588076401d25a20180c0c050040c001d01c2d0100700145140c042080f10882c40a08250505030007079036541c102581c02680b1560300d240b00c410a4020703c80151000c201102c09170018070707a0913400b4002040d0315944001240654006030b07580801c0750000222000c0e01c19081010414002c070490380410b00c585081001350680302802c00c030000f0142c0000c00201142c0380c00b2030f80182c0a5000d41074200e082d1032044002d0081054440481d0aa009410001402201d9180070015080b004010304680003520340da45010782d1180d25815a075580c05290005404c045c03807006200109402800325148035145044a00781d100d1184100600d40343c0801d0080000340080c80e0440d00c002aa10041c0c45000f0b81803c0e845406998881b07401c500c4001800801c00c0004503d000c0104c10703040c0040c0c0e042d2a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 359281411 1250 359280161 359280167
    0x3040b09061b070201020c03100b030d0e10030207020f03060c041a18011b0803090307020406170a350a030b060403050c09070c080c0703050f0a03020c1201111612 71
    0xd94034412010650000d452800c0803202c000c0101c1403050049801421b1050046420002c80b218034480103a42c845407248075003018000d41034401d1451802c00042d031a5640090307001800c031a250000c050740070603030a0454880968072024210020704a921a203001403120150340d1183c01941c2c122880c080d5415155444041940c0c4482c1c00402201d582041600046418100c604003c15006510101d4217011a81040c02075004000c02d030007459031090a070040c40282d806651102c2000701c00e840d2212051440883d04610241e400313160744940034800b10000e4884003a142c8404e15500082c2d200745200f500c00e0380100300d2801252014080690b5004c100107450140e4031001d031441d000308000c50030030325000c1c0155901181d5400d0145420015407503d0300700341c10009444030641c0c0084018002c0c06001c0150203144038511005109950060350000c0d110302d00c001c10f4a0081d000010310a1544400303401c42c540016201d5081c903180c15803250b008280c1d200c40c41055039085840011900100d03c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 359282661 1250 359281411 359281423
    0x5181b0109211b0e0a0b0a331e02030309011506052b020c030a09050402160602090d060903020a0b09060c04060e190b040515040f060f090f060503040b09 67
    0x44503610280004045032180c81e8014021800c2c00300f924401d2902207083d088003211240030744e0409400151161a400510041c02e840e0b03005403010300b400000015103a401d42550051802c400c0210402a920321241a03030005814504241d8279801c1001590b86168008041c5200302c4a8500034010510070048001d070391001802261300282081001c400180c200c088000c0c04803280341c064540c54160811480c00b02d0304110600c40064200040b5460441d0303004150700c0280108542c114500950f41890a04500101000828a58010900c64200c1e922201507030911500084c05002c100c1c4c01b403030025111140300c1000c4031403040020110b50100300001300c040c8903282d002641403425040500c2641d40706440446a0781c4a2288880d10301d400019a0301c0100404400e9682c5856a042c90304101801c00140e5000c421010113210400484a03001e18100c100c400780c1c00c0c5241494164001210b141c08036800c443d110220780600011101d9104006509c030741d024110003196a211480f410352118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 359283911 1250 359282661 359282699
    0x1e0e07020d110f0303190b010905031b01030f02041d01062f03090409051b01020c0a030b250c031d011706060c0f06090d081905181b0109 60
    0x603001c0500004501c1c01005500c00340a9200101d94002640020381465a401145d802d8130360180f0040d40217100106025003007010f8002d0800142031803d19002c60b41d07900c0500c035401c00c50000900c0c0c80150364025440902c00c101c0504055603034948501c0380c1040107000140149001c80d41400001e080e038400d24020020300c003010075034000440c81c40c1c070f0304202d030b1030030400300d840c6002c10840c1c0c2c00c072581d59100308402540b2030000b6003c0400400d40040a44a00742a198155000300500d6102c560703401c070102c41a02c6d840802a00a07817540407400261205910f10720840480b1003071414085501b0208040e0b00320312035950054600d0010340c0c90201100140c40700e034040351035900042e19104483e074450740c4c003410190207141801d81c5aa4100d180c07441040c280c09154004600f400200b95082c0304900306242142000302c510308105100c1c0c1811214854070f840d0143d9508040f80c540c440a003094007800c10400100c4402e454030440c20500d0540000c3c1c03840c04902d83c3c002c00907004a0080b001c00c004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 359285161 1250 359283911 359283913
    0x306130f0204050a020c0f0109020f12030301150c0206072a1202010807030b06040e220503030f1b0408011446060b04060f0212040b0a020109020301061e0e0702 70
    0x6185500b4400980302c0a040400507076001e0000551450041105469180e068400820450180e00502c40d042c1c111410740303406207003030f0f0700c070459803a00000869044603500d01000320407151400c8200c60014414034000c0d44034100240030428490106420f6114820f5149045a002c9503103082d404811080c0c0305410143e103001d131480c409503000d45402680040c0304d0401048818401d400140c2503407040d0041c00e503203500b40052024041b2000480b1010a4030141150700050164440c00d0f44da0100034021101081d00f4000103070810a0b032061101ca0000240300c0c13a846d21b0304c1c0c2c1140d501a00010019030b40d0021101c5c00510408106050801c0b0881c0072020381107409180d040315100c1002c071010052085203160b620141036422881050b00a01c95aa0f00c1c81e00ca0b810104d0040050130142d0003002150320100d4440c05040c0558126800c8450387d801d6903590b11300c040300a0780948061301019502d0b5107080c50000d50700a20040b00e00c00f0300c240e0b60000200fa5100c1011080704c00003500c0902c01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 359286411 1250 359285161 359285183
    0x10c030507020a0506032d1314100c05090f010e0a05040218031608060c042312100b0a0603020f0d0b030a0b1302040c0e01080402190504021602030613 66
    0x100340100000e201590000e07242c800100d8545010070166442a900313042c4044840f004030400c4248110341c05019410036030078031510b04056504c0410082c030f4020149c00003401c4c0040600344078040000c0403c0b50076010040c803c04010f22000b400581114417841d002d5840c020349509558851b94180c130802c2801000b92042c2c3d0f00300303000d0100031341010200355581c00880300f100c211035604100b1b242440c2a01f102d018103081c00d020071603051510207052015440002d02040c007603113030307100b0481152900380b001407003688641200080f4446094844403a035805504c40d0a805c5450541000e280c0d00b000341c84102e004c0c1c2e0303122000c40891243c041d8006c40d40000f408a201041c245130010403010700010100c0351540e00036180c0c0140d0b42c101342c40d1504052403110008045007024040c00d151020302d428500048044400007800201c2e009100900c44d46840b401e061800e1400e5805401030721002e042103444020684161410f00182d0000742c0c8a44160380001f01007425404199840d41d0b03001d1180e5603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 359287661 1250 359286411 359286413
    0x109091503062a1409120604060605060712050d180606031b0803030105060912060a02040e10060c0210030f09050f01141b090a05100e040605120d05030604060806040b0a0b010c02010c 80
    0x40e425948102a0b40c03d10010480c1451750341e0b54030140f0a408000d04050202800c080c81c2034030885903640d000034001c0105200c43d1010030322015942c01c00192608049540b400c07d0039440c801400031311420950050720030f550344148001d81c0d11078425240300c1c507074019041045002740c22000300030b4803415185900c20801400f6504099000c2c08100b1001744c00130b0804d10740c07034485070f0a110742280e039842c816a004c00c0c02c12a10245c0440301e9041860765020403000d50400b10000c0c00792005100c003a000d180e80e015045000c1303209601600c05210340701e0b001c010070281c40c5005515251085416415507081403111600680788000b454050401e03540c0c40a11072100c0654071820390002c42c2e071940d2140040390005101e450315074120142c041c5980c0c6064500c1e0920b8208800c541658120f180141c51042c032910b12107a001910300c5840c01d03d810400e8a079a95103000501034121038126850070b008072130a100402c0848111140240e40021083c4201e1803442e004603002c4002500c06400030f410306025074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 359288911 1250 359287661 359287667
    0x60501031104290f060d020301150912080d02160b10051305010f05010f0207090c0801030515070f0c0c1205150a090803010e09010b0d031805010c08040b090109091503062a 75
    0x400244d602914079414038800e46804800c9800980c0074054042c6030780c145401040d0702140b10002350682154070580680183c80d0b001c4e4501a403040d00304c50a034000b6010420300310614410800d5a0b04c48001481482d2462601102d82514400d181c050800c13402041040d80860180f0b40c10b880c403a00c0080c4c0d00b40c5c0740000444000d9400c41c4c00c0d44c03c7d8000e9800c04602189103010758414401140c40b400200e501d10301e00940303402d13100d14494a540c00030700c0c140820654030941104202075945421000b03030341c1320308241c41001e00c0f0394800c20380d05003900da581c0208280401c0071010030101110101e007a0f9104407100301610050b04004091040400041c03150010140d04139404c03090800000481c288030354042036107130783d0800301a030216a82d200c00804e4031154005003006441c0130301c0c012103800c0540e901e0405500860045500740c22010805000e243d00c204465002483c01400500c101410309062a1520195000607a40780707050000241c6941e00c5e20344010058101400c0c2265501400c135011 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 359290161 1250 359288911 359288929
    0x423060a030c0512010f03030e1210020f090307030f031b050a02090c0d0e100c09060912050f120d06120f14070512030301170d05071e06050103110429 66
    0xc8018004140209031504c0d82c1c10810324040c142e044180c060060450801525288031390900d1489100250b00241d4160404101d12070303d2900344202603155020001d41e00114000d50fa9110f80510608a00009010303495109400042c025260280d9040c01c001a0107149518084080c0040c7d11002d10f050060802190455010003400d0000b420007948004c100203071030301e21a0078401e55211240ba50300b84074080c4241650758002d81805001e0615010001d001074050348030703a00648102e0100c1c1420b000c070074041c1c910a644038505440c10040715210762202500900c0c049880d4034908840485d000340800364149140f90401940c2c0714060b119904c1c045070b845400e85a0020740a030580008141e1600c0c032026980c094100013942e240c0d81042c85030111401410401061544104c00340401940c000048860990f0807503042017005041d80c580200300141d40c0f8000300000e02d00070002041c41718140340e18545131000c483c1800f409200e2802454194200d00c01420b8803808241c40d10030915010b000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 359291411 1250 359290161 359290181
    0x120702070f0e0c093705010212032a04030516050105030a020903150c090108060405060f060f1903020414030109021e010207030b070302030612030403051e03070c08030423060a03 78
    0x69540742002007030200e100b205d0007001c41115800c16443c422a90308004c0c85200c0750100b0b00c00300000d65440d00d40001e6860304907051720001300f0700000120740061246c209031031081c200b58000c04200c51003507103080c8042e40a44001d481030301401c003646481a04500c02c503012a1016550142141c540d4138180000b98403445505515104a01542c0030401e110119180304040d041c401640740d40f41c80b0b00140142038004c0200d0320035440c010803c8030582e90080e800c100d00c074054030603a80f0784a0113503101c8402d20600d1035101d10040741d00e52032100140d258009200340c030800d124055455440b881450300b6034603000f100950015a01403007241c860080550000f40038414030481b41c45564a03110142c8807107080e9502e10000742c001080088605100d510b003142c07248000011480c20f459900d4290311504408264030f000c2a09511a680301c4a003042610500b503009404400c246a44e02c182d25038a0f40213100750202500500780e00401c840d0380c8500c103192500003429441c50700380206800c178020054800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 359292661 1250 359291411 359291431
    0x809060a02060f0a094701290711060d0e100c030b101101090602030a02030f0708040503070818090712180f02060c030f0c010c02100902010c030c020f040f02120702070f0e 75
    0x141026881c09104841c403600071506e840b8019541041040490140ca900c104a200c40103a007801e420131040104584c0c069030408401b01d013007080c850029503148146000d4042d8541041d00002085101043c2d803149000f02c06801c0049100700c5400f41c00340c03403804003440d0303100c8103140324015414081c00b0102c495055440c00021116841d0751254100c0c0c0003a152040a954040300b002020503407000c02a03042141801e00c0e0603a8642696180d43e40d1280020003058041c01280c000c0d803c83d80740d01507404015004003101303642d28061100401004910311000b40007030810b800001100c02284404e4243c0b504920050b07010311954007031116940c00004000c165100801400e01d0300c2c01d90038054204d85048200104130680c060038000c7c0341c8498010350441c484d02d854100700c0142c1e00203c1c802407007503050401c01000f01c50303400025500c044940307407a40c1040c1881001da80060351a03000740340c3c40740c000d06500055290808201d81d035072118010342000b44404401484000c60001001d9803203200c40c8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 359293911 1250 359292661 359292743
    0x602061305211b0c0a0f0b03010b160c090f05070f02030a0804050c10051207021204050d020a17071706091228030609050a05041e0809060a02060f0a09 66
    0x260030400a01c815581d05041c82e0081c400136030441c030b01000d040b40146040c0c25401102414001000300030f2006100c0c610440382d00295500d4860641418850881d81101241c28002c0e6100c40c0c0300023508000760a40d0240d80380c400010700103401075240b401d40700000da00075403c00c035288405441d02440a88292030500c203400790400190703070b00b01c0820310b44909a6180c60304c40500030b05048a07403502900d88002e6400042c1007600400c1098241d03421110300704c5048010007060f0001c00c3d41d0403c0b42d003025a10300c00f4410201c1c2e031403800147c01c2c000c4541a03032034034420030880d84016840300c0381921051640d8006012201c0c0324800343e0050502c202d1130f01013405003440040000700504070761000190210380c4800d810007101c7e007644223403640841034540c180f00c03628083e51010300d20b2821000c1070f40812411031040051090400584282030000340010b60388400f104c0e400307941c4010454140d803801c2041d00004410040314000d003000640c1c0061502c4000c50f604080c66924040c1c4800610040550 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 359295161 1250 359293911 359293927
    0x7020a08010c0203070c0b030c03040204180501060608090f0303040b0a155127090203060a170304091802062a070e01031101030b12030301060206130521 67
    0x2c0c8180c40445070325400450380e038a024500546070320b0301030340328401244c401d0080041010781c8104507a4410f038111000035120f02040c0c604407070b09481c203201404561800707401013109504030b100c1340e0103000d10004036400108020a07007962480101c0d80200424040d1000c500c0c4980603411851545410304a1001c04070303213841191011030000c000c43c0304c0c102d440c01381c02c050001c3d41600000b203803a002c000c814861800c4104443c001c40005501d04100300d451800310a200f0090140c1c000100d1505024001250360340c00d403207010b034209851491085a5003040003c0c1d0049600304001011100c070055402c191500180d030000341080700c803a20784449055504401641c90800078842e1000140413080d0003107400181e821404200c08940495034000442803004048140d50a811240e0010015442c0c001007401240900303100305181c0e030061142c0a041c2d0241c08040040d5040e03900d603a003110200d5480d512aa05111160b08001c3c0681d00f007840c8405001d10b181d445c4d60407036000d0820043ca84040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 359296411 1250 359295161 359295163
    0xc09050319062a030f05060d11220f140a0203070c170d0c0201020c06061002150604060801020403030906080a050f06010f02120a091e0f0501081009050f013807020a08 73
    0x3c11400c0e90010b56140c0f1010349480607032042503001802500c0190080d4550307a41d0140c90b5401070720007485038001c000e82c05034914007844440070b11020b41e0701c01c2c03001255480b640000750046018002c078040000c1c000469541d228030907a48910682e81e00e110782c00309291a4204c3d640c0c905c4030035000d5040c00700003004c0c0031202d074001c4040810300c540c00160350b8900c20000504054025040c6446801c960154052295000400c2a184003141654102980360040082c4c0105419840f5903169400460008103244e0010034100c00c6071840d03101c07495550786000c088401c88404a400d8140135583c1000711b401944a03800050094030540110794411086110b0403056421980031003000030144441800b003600d05e400040b00d1521001c12240c80d0505120303407138104c140240030311070400c005000051015502510700c90020030618108200c1801c18000a24125000740074000035162407515240942e140e081c0550b10388804003020b500301040500103c0d40951200070f0680e8444030640000c070354114 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 359297661 1250 359296411 359296481
    0xe1e03030f03090c04090215090f0904030c0b07020705130207030302070c03050601141f0e180103200d0201020c01080604020d0203010b0307110604050a0305070305070b0a0c0905031906 81
    0x341588020b85a01d040c3c1d039254034040703c0c0c03450180654180604580140c86103002107c00c0100d100c8141d440303107400c0c2d000c150150008c03000b01e907102c030f11a4280030074150010201c4200c24007800000c0582d0340c5044040e81d4546043c418590011800c8807903003072002c1d403a8043c08034540b180c6405450301c9402d0300c4126610b4038a800c20341d000c0d04075600400441c0c4018005840100c030983d21951203200000160300d040001c450396a0622042d03065145070340c0c0d50720141c020404450191446256180c3c01d015006060140c020081500f00703c40c510743c03d2400c0d542d503058440d4164028410503c80704011900380001900702c0780c00c240c081c0045085016107001031b50281201c0411241c40b0f20308002d00805007d800510180316410500500010410210f4103e03140303500340c100a0f50310240792400302d44500c682d640c05445001501c051056049a581002c1c4003026a076481e11402c58441c0205502d410f0400002c1c24a0306c980c041010001c0d6058000091266003911360211040386881c243c0b6080f0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 359298911 1250 359297661 359297677
    0x31a041406040c05010801060201090201140c010e0d12060e04021e130f0902040605010309081204030c020405090604260a120b0a0e01090f0504030903150e011112160e1e0303 76
    0x643c92418070007540c6c00302e1640d0042c00705100a00c103040540e000a030283c440400e4540708404005401d0210711425007100c40480c030707402c0031035440c1041103900038038807142c184010880ca4241000013403521890300720140910303001444683c4c017444001001d841003000d03010386070700300b0301406034071450b203507a440307603490002c458070000c9615040d920401040b40d0302504624103143ca4456094042201f00341175550413002c10024909946450805032005d40c401c50000307503c00e0425080012400300802c40314011740c859031004080404502c4580042014100c1042c1d181c10107110214000780b10f4003100d0400811041d0010b80c048506000c0750603219240c00c02594a810040100070703408041c80b4018002001c41020006804e1035034006089807900d1202500244003041010b11049260340a04040f142c660b00810124240c000d483ca80e0750813603d800700702c0100d1880001c03201122095804181c0d201940c13680c0380d9081007030803c0140a915510120021030400620800e030320f08100400d0b41c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 359300161 1250 359298911 359298923
    0x2a0108041a07120e031602060d02072907020d0522050306100519050919021303062004080d05030c07051213140904021c020301090f0c0e01031a04140604 67
    0x200640c00c10394401e03210180c10310800e40c0d20810010414050180142541030390403a00d2341c0d968013100f180e000c042e0007000f0010740000741c00c00d0746503001024a5031110600200030405011907581c40d4042e40c54881d07100100011501c2041107100d00c000131402c1d17200b107100070a040300101c0d8803a40071902d429404c442006411a40401c14401d0f481c10f8003045207983d10403030121b02c1e454101340214203a0070020f01303428048103204611220400b041d07019078101c64604a1855a00c7e81d0300d040c408040c10525044039101112002100076460201048a044c1d400c503400401002c0b240706000c50b0365038002004500c00240c1805440b001400500031001200c540e03101641d02c461081c010385500b42003603031144141c80110045600c4a807100042940d10039012640c06251420004031101d06501c4030100941c035510b407101070700400130158451400d003402042210511340e16420150300011003030001a01141c07c07009440211120040032660051051010540700c3ea0b9040303c5602e445000e0ba41141c034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 359301411 1250 359300161 359300177
    0x9140a0305012903070b0a03180f0609021c080301031e02060313022e120216060504150e0a060207031b0308062818020421052a0108041a07 61
    0x21443c00d1001d4010070000c201d010780a69890030480c03850030700c203000d07464050580f170f0324045200315101c030b0000b582e26400a209490085591074000004e0000c403804038818650003172680d00d10344030045401c2d2400d40c094000c0780341d40d003542c580c65103c000d046250b00803407030405c5207000142c49070006107010300d6903c460001c1c84c114500c10007402140d081c8201d80b4050360015412102078403000708002051250800c40c0343c0c650700089100c068800e07287d004a001c0c12402d21a0200310303055000340e10582c003c10048010790020323407070345054406440b402480e561104a150000c9000c5500a00b030030b80c424240215101c10b0101910b0601b045941c0c01d80200e8280d40400016051400000040f0000d110303140410428402010719540800d0007111409070001c10251110701d000c6d8115006030220410107103a0070070321402e405115520800c11652405011064050016004140c454001c1e80f012095103c0341440f00454030140e0041c030580d08800c0c90301c1e5441174032000861032030140358a541c072403034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 359302661 1250 359301411 359301461
    0x2040216080d050a0515040504020f030106060e0a090204050a2c1303030506100815120609060106090e070905040f0b040e0606041406030c1011010e01060303080105060a09140a030501 80
    0xb04842c030051690791190f09100801880d107000c0c00071301c07194000803500004c058882c3d001281c06000c03040440c035015880c12502080c1c0039004440a03035070714400ca882c1c040c0d00d40c503543c6103403d901130b1344101ea400031803808090001c0c0a203142c00c94010842031080d485100807460208204c200107841d43c0c00400302141503101419418040c86138004010364403071591129240f0003c0c41d03044020b104400d400300303184410009075600c1020313a8265210104903a05400c0c0075410750b407a543c0030700c1458042400400000b5001c110408414405c04540d00d401c1f4540c1d1401c0240005003041441300b2800981c0c0d4110038203d513950f40301d00c00124100c4001402c1c0e52801005110846180c540307034441d004a02d6041040681e00010140f48004007034468044400c0b4a240075643d42c85182400100c03942409004c0010000540c0010700300c074003c3d40c0b0071a143c0d070f80e00d00b4006548241c50001c00000d100c03000c00d01289040c3d424040c0301e144060202d4801d280c0d01c1d15140d00310f581140417618070201d10f80d00d1031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 359303911 1250 359302661 359302687
    0x180a030c0c210201030e0f070e150a030b0105010818030703030c08240d0c030b070203030405120c101505060a05090301110a02031b07032102071a040302040203040204021608 76
    0x4009850b0030300440900c0c081c0324400a00707200d02e085000b0304058494070b9946003254184100c4800c45d6100741100c010a49842c05800d5400c1c0441b258010720441c0b404100d0350b0f1030062095001c90b03801034003081859003407000458501d02c0040421024018202c0d41c01e2085038100001d102080c0070349d80001d01c0c9921180c00400008002d0300606d400710b0700102042080d44904458501048101d1b09809084408e26000111941d59480a014240350008000d01d0b41c1d008001188180d110b603040d41d00c040c4549503204980e0050010040a551090031007050f03c5070726500180c4a0701c18a0214400c580d6564000360300360f44420b29040004d0303000b1a58601a0400b40aa83e05109462030010304000c46840c009640e80541d81c010b40c074404881c400922a01018002100a103400c024040c0c4180c0c0f440d1912070021100d201c40c40018803139081c0004e44464000c044600408000344006e00d0203155808103c007a41000c0c00030b030381c003941c2044400a8024403540f8524107511400e030307044c0c580368004214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 359305161 1250 359303911 359303933
    0x30109050f0c04050604140406030611120a05010608010e06040f0e07060e1507020607060b0a120b070905062205210f06040b2206110c010b0a031a180a030c 68
    0x321202950a000500c090345d600300c2601c064884d0001034150300016407001501030041940302400d03c0e450300c142d07003e0744180742d001046040c03221841205142c561003040d8080310300074412500050b041d00d005104007081300b404160480b400400100c0c0144100d204136003144d0556511030700950150b48104042034002d45000791010b07040f030304007001c2710351118922003902c40c155000748512000104541045035a40c4a048800f034050815480181c449400c200c0303900e050748041d140030b620080025003003842030310000d0a84001a00880c01c105244009550100398452603440c060820381c00407480e92602d1100c4914070010b9107080a034041e81015040c1031154005d12089141c000390700704070100b140c41e03082d960040d81c00c1c0c070020100e00200c4c0d1029400e40258500509060501c011081641080805000140c0c2d00400070045110034000700400c880480c4001441080040fa10f60380d038948200c1c860f03521061408507080c044584441d480c1c181008840200d004c1403142c0c04003000e100d10b003502 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 359306411 1250 359305161 359305171
    0x3030c0c06060f050a17030d02031012051b0603060d0809030106090e0c1206070c02190801020a08040203120403050c0904020118030c03060b1002150403030f06120506070f050304030e0f06030109050f 87
    0x2400c0040046c0950b0b48a01c2101c10b000c0c556500000030841000f1400c2680c0c0041411201c489080d1080d460541c2e200ca40c0902008402941c92001c0021031519001b1a4010035004006d041081c00680d22044582c03ca44806c6505558030310380007903000e519010b0484800e2940c005006142c4141040125000d5040030313143c1641d1003841040703002034000003103800e6507804036425a42c0d80b80b0351301100c2c44280d29400068040d40041000501240c109001e6805140b0840a48100c03c1a0b40480f0710280590300c4050840e0f844851850030a05084100a40103030040c50400030a2084403450605940250701c00c86a8032607181c0c027001888070383e01c64562000002c840034011010020300003503603440762041007420300000002140c205806940502c0641040000500015940382811203203041081340641d0140296400201828460805240c0d0750100d512840e04584941c3c030229040d6103c0000a9008582ca0009000030b696041c065402800c00700004145454a040e26044201000d00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 359307661 1250 359306411 359306429
    0x309120801050102121c02220b1602040207060207021503040501150f180e0d03150e130b090304031a071b032c060406081f030f03030c0c06060f050a 65
    0xc0140400c0c2c0e40802c0b40340ba41508012181d449544a8a061700c00d0702a1080742100f0610005070070601100c20240c9005441e0001409513410350342c3d68092541d481500101e40c0011001e400b0072005103003640c064002680500c00050a04480e03501090612a10024030601090080100800c10000340254003400c10b1076260441d0480c6001140140d1000a029502c00000c1d081580010500590700110b110807001c01140c407210000403009d4010708050700c9a0741000e103040404a0ae0700c0d0301d242c82e18040c0510040c1a003000c0c11989400000c480090091030300c5000030000000860a9196102502c0c8a248ad014415080850340502514a45480c00e05a1150706000c4000f09400800e103440491400c240d44076003229409a42c0380140034000303010b901036030100d40031400c40d40c410031762440303400c0c4008504440d101c440664001c0e808244801444000741031100f42c0080c1c8a0f4006a0918615040c450384868450f92100140d50564000c944600e84e00d034002c02c8070345042e215860040034450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 359308911 1250 359307661 359307677
    0x20c0a1b21080a080c07020d0b071101060b0304080c070803040b0d0501050306060f010806012a05070509150d0303060306021c0606181517070207180c020d0f030219030912 75
    0x540c4542c2d203070094508081c20b04c581c001c0001c0c0d1041101040300d003869030044c41d40955200500d4040c051000989401c800a410f400308511090390501c11a03098801d04624941140c0d110f6480c3c2107103601121035800d15015a0f500010b00d203d04101900c00307440320f805826190425200039008550b0140d00044c440d50243d0f042c01450b03101e0380803000075103500707103403901d1702d40d852b00016a411a44041e03185070030319881c005000e05d56140441e07210200d1080c0705076285103640d94100a482c00c02a075080d22000800e50000344103140c1513803402e03d1184079050100d10159139444031005c90700654101510108a041071001d219440c7c42000d010700140d00304200c10b500c031255000301100150048181702040141c0b404c0f030b19801040c9100030074116041d0b185407803601d034800948980b041d1043c200740c0c0e10802c80181d0540502c2c0600c60016596a000b0308600340040c0044401200a81604003810350030014812030307020643c0d8101200d03902c0d46011410a4040c0307011211011300c159000c0411400c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 359310161 1250 359308911 359308913
    0xf4504020f0a05010503040311120721020f070603020703120e010e0d0504210c03060516020f03040e191d010e060c03130f0312020324120c04020c0a1b21 67
    0x80804da1f50096090b1820110001e0039460027890482c02a020440d54080810224100403440f02c0d8400010200082c90313003240072001c41030b03aa504203540250f10a0f00814002e20003c7d100b5406004040d0080c50020901c07141101c1c1c00080b2414641c080800d651112401020913404104d6050081468138009252a1070580c004005a0740c60100403905404510b046040c80103140b80309020f1600100100420b040078a0040c02c4c0903204003029000d8010b800c1c1110040b100881650700701c4c0d0310318603005140d43d9680c1d0740031848111580c80341c0c0060340e21048940c44941090b0200240c512020001444510145139140360000040048108a80c2001000078000759a00007004a950100c0084805d0b9200d2609541c10720702200010b800d1071012003000348800f024400c0340c071101107008081340c0304140c9605100d43d441d44900c52104650001109011701d0520358001c121315429042641c1d031410b5a0f60741d00324169000e20700c05080c400426000d20806008422107065200d508111618454107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 359311411 1250 359310161 359310167
    0xf060801061d0604090b041b0c02130606050a0c0320030301080111072319080307030f0b0904020910080304030506090f030a0212090a030f060c08060f4504020f0a0501 73
    0x1c50151301d140d03540b01d070786025040c7c407907800034152196100301c280e290840728a03001b02a451140c200364454015103080b00c105000d64461074007941d03025541c0074504040c1c000240c0324400040000c6042104114039036412114449880f183c2006800240d541c951601051a0070748035a048a08180b140400c200740c000744060210303042c81d8124804100c180d08090204500f481d00c071034845004100144c0345c19041104507001544900c0e05903c00304120105040180104e0343d44503501a00305400360003040240c41e1004c249680a40790040300008240c0310300038141107400c207a000300e41c1540100d0a0064025060043c101e08108100041d0704040c07641800030360300d1a06100300e0609140002d00210f281e11141805c40c06035030012501d4000c490a071400740c0083c2600e03002c2c400021480000701700f0341d2621001d6485a400d0041140740d070303122484800c8076111402c61982514658803580030340c110049800c183c0c030300210300c9594031542c0707081d0052001d40c44501d1401c601c2640c10764424030250703030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 359312661 1250 359311411 359311417
    0x181203060d05010e0703030207030606121a0411060c1506030c03060403030c020c181b18011b0b071e0302042711040807090f05101703040f060801061d06 67
    0x804551035046039201e400d106005001d00001c1d552640100361011090540019101d401c5920864081141d9580d50300e1b00300d83e0ba4800726004100b0344a8104250106802c5020385802600506401606508100000d600b0340e0000b8003000540c4c0180805408411407241c082c0d512001c01c0c0c0c050300c1610800000261207010041c00201031698520039261701074400c102c1410700e002d0290481d00c045090800440e0100001c5890742a90145904589110100281910804046481f0044d10740310751030015502e501c4145620a204a044040030020030302e50319915001e5009500c8060508401c1c014480745060003140c86010303d40104410407810700300040340f461081104181442c09012910f0480140065190041701c840307011901060082010a80208980f51444104411354010200500360350044403000190f02405604100c1c08020a10b001080d101039401c6d6498207440c0c030310740707001c4030380d603400020001d403285005000d02600040d1008480c1465207800c43e04007807e40014070688 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 359313911 1250 359312661 359312671
    0x50a02030c031311062a0c1e0105120109050702060a1e090206090901030503190e0d0b040c03050123150d11181503070608040803010306050c0d02070b181203 69
    0x2680555103e824800c82290015a8510040209a442c07500c4101100782c0402031202002c010b070384e042840700f5101c6c0000c0c1101c2203038020f85400103003140c4e07587c4a0f0500c0c0c102d03242039040c054100444240d9078002040c03940a010340517400540c90074004c00003480c0142c001e2031540014a000c540f8620051301c01c0b51841407041a03000031412594134800300b0014000d11680c160098110340000c070412030088094803040d410388050a5482d40c002c05c1c1111403000145030310345c008640342e01d010049805119060ba009014410803400740ea44d960303405084031000d481c07643c41e8031a1400042c2501503800da22540141450b40c08140c0c03641240f00250051954030802000780c50b143d0030000040d1074218410180c06580c4102202ea4904031060301e100e0080800603d1090141c102c01142e25800307000c00e0f074043c98118131128103507802d6568000c014007003e48100060b40303040c0b041c041b2140207400141103551003a03018070014280074880e46404c0904042c03829441d00540c1d00d40287c2408001502d5103c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 359315161 1250 359313911 359313931
    0x504030f02150703020c1e060d02030903070c2706140f03010f0608060105090609010f060503040201020c0603130c24030207020f0a06080103050f06070e060a0e04061404050a02030c03 80
    0x9030064030014040388022000040040c01c00301c0d82109260700442c900321000d00c01e850501e105682124a802c000b80350341350030741c1c0c00304080c403038100c1528480d0301079070b4018001d400301c92426401c1d0305c400c3d00303441c49a40300c61900003c4d817100420140c1d060f00300c0440e02e40419020300c0020705150004010b0b03000e501001d030003a40c4040460019035000d40250b05400f275020001c102d85900c40c1c160341d403200d20034095903018201040204541e401e001c24018100d038100810400101d0030400100e0b03ca90020380180e04620800141880c507544260007035001c3c61402d60140c11104407403a0500b00c20945038031001000900195810b4171020007501001200220b14006a0b03400040c40002c0588070001c42c0a900004d200b840800e4a42d04050300078141e9000d481100c4110b44290030840e5250300881359040014009507040c500790a02c10044c00d24850341742030444100012801150840303000da40300d450700c00100014901a41005c0c45120b400c0349100c5015441c61500f03003423038021448054410412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 359316411 1250 359315161 359315183
    0x11040603020a1e090609020d0e06040b1602070e01060f1b080f0904060e010306050402120706091703071a15030102030402061219050708070e010e031f0f0e07091506050403 75
    0x80d40707200180d03d6000d4250081c00b000519180c0b5801e030000c0d0008480f4014031440c040c0c03045505400010103a1265601440c01c00d55076540710780190402c51001251415441865404116500450103083c00707012140d030b0f03043c59040801c0c001080780c6260011224038014640303d000100b00050300719141304909809041d9210391441c0420300905142c2c3c058040c81610600200802c25540c012034080c42c004c070790010855401c02e0f40151075510074800d040205040100401c124445a50700000560210040d80d040034020f0715081c44008000000e913402500840400c0703021082d51168544e002d4003076000b14218501640843c090b0701c15261400400c28003540052604200c845091040280c190300c1403010341003025010f4600c03807083d100b10000c20000708041119520540c04c0301c0d1035004c01401003103001e84032a14680c0c2e08146003110940e85442d0405016000814003900d100c080303200b001450524606014442200d00048545401500710700f002c002e42980003040c2c2d41134942040810362 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 359317661 1250 359316411 359316449
    0x30807050403060e010e01050c0f03060d110d1a01120308180a080f2104020303091e100509030d030605130b01050910080f0c090102190606170a11040603020a 69
    0x80d0034000c41c0d0008050b541054035940301d500d810b410805004030300328020710680e00d070540c21402d14011440308100940050000520502d08100c8005203903001f24811079550014002045006400d0007060b9100c48180c02e0b103880c2c442010f206c0c1401050000c140c2060110f482c2d900034040403001c1e056201114051080c0c03502d80005100c01402240c1c04585903a803940c92410304d00080d008179003410030601917841004407441501d521180302da9801000b039454040d40a0802291820401002c051700c054112030b2195929440d07507000c504865030304c1e5161070300c950200705450701c1c1505448100309410103e0402440d19004c0c00c031381051000b4000410185a0800102c41c540101c0d00c22550003280303c8000d20540390441030300c500640c0b0044614031140e4403009002801d1056444035030042c6d0045000032a040b10002c50503201901c00c0780c02090f00b503076403c107900340405800146d10540c2c0008418904100550101030801001a030302809040d00d160002090180c15106118480300881100382c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 359318911 1250 359317661 359317667
    0xb10030b0d11180414010506040b06041217210603032505010e0303070e03011b12020c07150201051015080c0d021c0c111b040207140f010b04060608040b04030807 71
    0x82c074200d15403c600000e518081c01c085080000040724a03144d9460b1101180e040e04007406140c914160242140b0300e0a0b14218036020f400140d41c1080c2d824501700d400100001d07882c2d80c000d002c000c031040740401c210440340c00607681c102c60180100f44240d000b0004044810810102d40340c25075124032035036042940c9410160301409100d00d400145020004c20050304d25040001910340300025002081004001c411034000c0c2140000b1000c0440c0c2100861000e20000707400400c40500d403801034401c0c480c4d07101c15013000c0c3c2c0c2c008020000942d4641c800c100705910503804a01c0141a14440d55440214200000d414200068080701c4007810010b540d8410b032840c0c0c0c040741c038030510b1426600209501c8510300d80040114400100002c2d901c1c1e10144201900010301040e052110440e650801c9801c00800c002540b05110880301e00f82902d042c004001401d01407a03209501c240c0c0007094500f07900042008844564000005214802e003e20011403001d00001354403d50500f04844140c44041c010303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 359320161 1250 359318911 359318929
    0xa020904150204030308040b0106050a02060f2e03061b0e1306031e021302041a0703030e06040609111008060f0102160816050609011d0a180b10030b0d11 67
    0x41e500490000600208142d8440f0403035109500960710070880b0390b220070707048400344140c0d08a040140d00c5000403076a111030102040c0e4101e4411140c08800880110129000c0201405800c1140015020420900200d4090380c0ba40c075800c100001d003120b000320405441d1144003030015011304d2445825030048525680040007461300680754144034540d03164150310070002070100700d005001108070452019654000c0d0341c26039a2050714189200e5840042400941208405508040e200e4500c10ba0f20042804418041c9000b28808074a02880d810f000520180140d0064018040c040c00b511103a640650710f01c2e0480c204407204441c100030000100e103400301d004180f5103010140800082c09040c001041000103a03000641800b01c2c0c1e0314410040c450065101c0c032408a0200c2040c01da0410b00c0070740c0c2c541d009800500c0052910b4541021060048015889491196031002d498840f4501010300c2c02440c51146810301c0121403410210708040c42c08800244600300e49544182c40d65999448 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 359321411 1250 359320161 359320193
    0x409020a12060b010305070f0e0a0f0b0406020f1b130b060c03090a05040b0a030b09011104030602071a07120c0207033e06030c09030309180105031902030a020904 71
    0xc031501601d030740c990710031602550000c4424900c1c002c0900e400354001d000b400c3c840c1b641501e600075002e02c0d40c2c4040c1d410100d84a911903014605074408160590210301940140828100003502c650905c20080d00e03140c100c001d80c0d403075903015a0f02d0003002d1740200400b0b04618801d48080f004190120603420240c03c0740160550b0140f40403032060f160b10b800001a0284000c21520741c5c00c1c05680c3c0c02400700715a05c1040c3c480d045800e0710000d0002c61000407109401802500c0001101600411541c416411075002120440d4000a600061080c007030341207a024809071015102a08040e0805007140c0d00d0210541040c43d1514222480c540c0240001b100640e0801c1c0881c03500c0c6d014030070306c2020301102c044483c4604410500015181c1b1254544c411600700a045245113482c2d440758003038260014074985e5414842048140340340e80720000002983c0000c58014003030b0b94140b0042504022965986440e42161121900007594000810420039030f01690140e80c1c9848a00700036a0141e0381210f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 359322661 1250 359321411 359321419
    0x1903050d091104150f06050f22031a06031018150e06090a03080402040b280e01060509031002070309120c06020601270507120e0304091a0105030106030b040902 70
    0x70741020711412241d1000d01242c21a803c100c1c1840181e050010044a8050f000701803035040c0041c4a01c902400040c81450604112a41400005000e4840d0202889090450340422a000f0000c01007282c02c01521812054080340151510f100401c1d9200c0c0c4110005880b1030702e4400c91184076500074161400c494001c0c3c00c10040c202c0c89510240600200c2030302410922480e00001c114040100788240c120390700d6942c03480a600d0b56000c001c0a40720940203180d000075521804403030b00c1c45001e040c440800e003010940b8681031400b00d42d414034140507441002880003c00c0170b050f00307a602080403da991018071005840301c9542c20101c0b10040c95402070381640c1c5030461803a007800f000307040c00402c44100b40e0840c0c03210384c2c0761000500b00c0340640007aa0012000001001110056900030a600041a1a05900e00c2c6003104d440e0301079a4108c540d01c802c0f5000044e09000101b05c9000da2041c2c0400c4001080b043d01500000810b42d2105120b035004140c2d5421061074166955040304042d0390f0010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 359323911 1250 359322661 359322671
    0x7050c070801020c0d080405030406210905060901150803040b0d0b0d080c0c03030901120c0201090b0c1329130302041e141005131b080115050304051903050d 69
    0x301d50036000b03500010a0035010301c00d01003000d0740984501043c5200c0c84e4440081d5061a01e0240151404202030b030010000700a081d2122032200034a00c00d1b4010303140541e0080601d03007404c5200b1800c640031244801c4941c540c2c5401444085000021030b81114455603107940e64511500d40350307001b803100b040f00d81c0d407040d58200e0701380074041c0e00301c081c05480c15514140e4081105040c01c0540c0ca1284005450124102c501c400c114000e4030741c01444010304500021540041c1641c0710144000c0843d8813820481020a042c0003a0034400380e80e1703020340b0840480c044401c00003108820000d1107804500048003001a10803841c54041c02c11800540d400703481440b00010200445941c0d42c2090951034501d0b14040070328140002d035802050180840d400d01c0714142e428141405070403901c0c115282c6041382c8407445d01210003a45614102c401a40b0394400f0810350400f001da404d802074201d00801004014002e01c004200302060841200526541000c10310186160941d114000d108260310352074940 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 359325161 1250 359323911 359323919
    0x11205040f0b090d12090503092101060803030c31030501020307031a01120509070b070602180d0503031501270510030603050a06050a0219050d0f0903020a02010807050c07 75
    0x10480c140307103075104100082c0c0550f22400020307504c8a82c4403100c40055085001c00c01100d40c02d40c0142001c40c0200c0550b0726000d594070108400402c46048902d102e5812180020145420b10075500078183c410040d51942c140f10b800d103003d900030250340101c0da103070301c402d4010a410b60040b440124000d01030700d801c0040e40c03400c0a82c000e41044a034040864201100415500c100101040c1107100503120307100300b880880c010200420300142044039a101341c13040424140703140c501a00c8464400c00015a45008041e09a004004060b0165009000113051140040d1003c029280d00142d414030013990365004500403203c20840014020449060703170201c0158103017825a060940e4001d072000004165801012411a481440080c007607401c21101003001030155001f8641140d002c50015003000240e01c4102c140201016034800480c20004440c02c2107891409405c40b094401d80c403c003c4150303580c6003e9110400c2c0711009042028000009134170501078003d40300031403078001c2203806c140e4403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 359326411 1250 359325161 359325173
    0x70806130b06120613080f0c100f2c0c04020705032713020d0b030d020a0c060503060904030503092a030c1002030405010f111506090906060a1401120504 67
    0x100803040d03070018103050002d0900d00784684404480a0b004004210654800301d0644250000c540100d5500700c00700500c01103c1042c0d40a4910707090424050441e04400c1d500c500e040700c1006c41c0c400e000070b0408864800700e00000c1640d04e03880c03078290100b51002c02003201c018207100c040710f400e80c1e000e44045840070900c04008044e112425110032040607880407504410421852600309646c416001d04500114900c542c01a02100301003901c04070f940c44c68240044e0500d1045100035005911405480342030103072074244a4000c15080c2000352650402c00c2c0415800c142c02071001d803e1140c0040860100c2a0402c202103a00c0d902150405c84100c6214900002070350940b0140c0c4648244031031210249000c0c40c0c0c0c1800f21401d0740017145003600d0580103441080101c00a1000e2055684902e081d102c1c00b845505080c0504513561035180c9441d80400402c040c010b00400c401d580400200b16958640455100c19200281452464030001c480100c824501e5140e101c15024101400c1c881000a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 359327661 1250 359326411 359326441
    0xe010507080624090607030201090203030a02032a0a08031905010305061005040510090c1103070b0109060b0703121503052b0503070e09100b2d0a020c04020c070806 72
    0xe085075200741215216088480078248043c4507642c148042080518914080e0f00400c4411700c6030001090910071900001e043d500b1003080e5001507040050082952040c600341d0b80807041b81414440e28074a80d03202620361303605d080d0200074545030000011a40c580d1030102d0b1807100240c0c90905100d1582c4030300e48680c8880090707900c00040131000740041800d25190141c0303413180303042c8a4b400e03003507516000154000e0304a0710748002c144001024a00000b0000303100074600c0c9801070603030a66a5247c550b00ba41241d90319481184001c005001c141e000a07400700080480100d00d150100b16400f45800b1205503400c145d10007410b0b40b150340e4103040301070002001d0f900f5242c200c1e0036400c01c414510605403000d2000702c409200055411a815034a4540180200d810612030380b26000f040d900d40d00c01c03403155881704000b107000e4040402d418803e88c030500301464421000d400c05606209030417001075039130031440004030710686e000304040500c92420800340f40200055801c4405508081d03444228102c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 359328911 1250 359327661 359327671
    0x91d0706050421170703030507140301030b07031a0303040801150e09030d0903050d1a09100b1b031e03150307030f02010810030611041d01060c14010e01050708 70
    0x100481000003030403406441640c1c203c808540b9210844510038102c0d203005003981d141100e240b82022680c070941e102030b00161040340c0c4240c80000e191305000381c1c082d048250f9140401510030f0100014000030711034600c0b0325004049801e010955074500000c0d0b1019120b04480140c041c40f01050003c1c054005411600b101e2143c089480000c40d1203c00040c000b9000300d0364207441d0780c01000300104d041499480300c1c54850203494210700384501d8461303101c199171082c0c400003a049003e041d10b40701403900310703291a00520070104050086181040c07040351401880401c1d00802c10450300d51092641c10300c203e505400804916182c00004190510159082911002003107241100c8140e110f05000074130780c054a82103c95452440c40300c1c0e00440d00f901c002001400482c010440000000d0100e014801016110301141602d69040c16482c034901200c0c00220300383c1a56040040041c40d4204060206240d0072200b0091224810301e116405000215040d119541c40d00c01007181041e4040d600750701031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 359330161 1250 359328911 359328913
    0x20303030a06031416121b0f06020c030a03091512150807170307060b04020d050c0912070e0c130314010507030b0102010b2d091302030d021c1404091d 66
    0x3030403991307016641e0386200310b1864004503a520074410306000601c00b04041e8801e09001800c2020801d019403c403886038800c050084415005002c40344d010310078508005004c0d4003c00404803980c500610f182030510403203008411000200c0500c51184980e1785200ea503245050189017010300c1c108c0442344251041105e64006c44001144001d8007643c1482845200402141031901d0381c0c50b00b00062051141c0c082e4081e5003003201543c24049030242a01c42c0c80040141c0761181101014003074a516080d03807400003504101024070810000d001200d8202565401c5d843e1280310340da94210340240302d074201900000c4050782024020710150025032040c441d80d03505002c0354034413030016401d0b00c204da048943d000d24280044070160426880d6640c1c103030b520700c42c52140314411b00c0120b1a440c10984051000038008a50b407070030740c1010449414040c10038030003825000f001c00c21070540440f04090134001c100340c01800507007149100099802038424504100030b680c0b1070100a41c200c044040d03a800709 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 359331411 1250 359330161 359330183
    0xf0102010b0d23011d0d090b1903020d1e060603020f0304110f1305010501121b0804020411270d050a06052a0309150105030c040906022a0f0601060f050a020a020303030a0603 76
    0x40513128003c507804580c62300e1042800d183c10051901c841e0000e004803201055400c0c05407901c00e2000d07005400c000513030917128010003150b03030032003070155940341d0412024140100071031038440785030342c0c1221785c0180c1240403a1250050600003400c01041102c1255104151b038034101103410311903209504890003600da200020034242416800d45100c4140c051030302802c490040c200c603005125283e88203100030400624003505111a01d0b2603005481ca407842b9091b000c55a10710603034a0700348083c88041c119604040d9414030390714560b603110300420081900b41c83d040410500101401281d86a0500070481e031040031801c407401e0041d03042216000d01910610984000303000244455906071480540034203190040241804058030810800719031440d800c104d0034044048021088104c0c500784400714040e04641c035004d92402e40080c00300d100c5600828010410581c00101d446031071416800c01c0d94403004040030903418180f85a1010b03405000c00401c00c10a684550300c6101030781d1180e188018 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 359332661 1250 359331411 359331433
    0x8010501020115030f0507050307090209090105031605150d0501060c031806140a02070b0c0102041d010f0e0c0d14090f0705030a0311030d0c020c0f0102010b0d23011d 73
    0x100343c819070302d800210f000703100400344082150010308043c0399004000b21038615950f18042032a00c200d82c0c0c4403803002d0707501007590501c40c81d001a04900414003180103061020380c04a941044c0c1e6003e00c1224880d0900700c50110682c1020070550340440b0424001b00a25030791100080c02c80e0082c20400c600280d0902182612070710382160f42c209032030491f40e56402c201606020303a180c991001824106502c80d0440000d80f070b15200c001082d940300c80400168640785006485400490802d4140040401900c014840b443c074011481c030484031201030280301d988608100700e8844c81551582d844042c10300c1d034418103c808c81206503008107254000c0768180c041405519880b4031241c01400d6041d0080c0c01c1e00001b03c1c0c40340315002e20041e403450a507460404550102c070102c1d03500013a41c0f005608010a05c8410b442c003540300c400588820300007401149203100000c1c3d0b05803072542e0000c04c034044010030900300d08102508009612039050081190703070007055031000490980c000c0a80b1911526403000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 359333911 1250 359332661 359332663
    0x32406050a030f2f0d06290316050d0f0f0519020702030c100302161b06140306040c02030f07030302070b010515030420060715050609070504051e0415060801050102 72
    0x80b1342c05100c040740444046098080c1061108551000440034050048000c4074180e440340c1001042014001c100301c007880b5880100c00591011a080c3c0240141b040003034809204500b00032110140c60460b95134048440050001c01d15802001800d034584101c800411798107131702590242c40811100501403159218034002c0c3c4c8103041009401d41c01440107101e0901384000a010061050f04000d801c21140c01441c01c041c01e401e06c820340381490042c46c111801d0f001c400040d00940701d140781460039503408800b40002d9100141070365010310754034154181424070a000f41c5145450260501e951a8002e0600401070340102301b0079960300d90001e000290f40d1404c000c964410b1200d038126941181d4854443e0340300110314841000c00d50510707403036103451341d6a640f008040c20340c4240c5a1016040612648200310780008001a0085004800f03002000f40c124060f00c04865080ba0b0301c0241e01041c11400e0b903103000142c40c6541203410300c05515817031161f0040480950358565103203d466aa184012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 359335161 1250 359333911 359333921
    0xf170f07060c2705060912060f01060806010e0a030b270f0c09040c0e090f070b0a0216050114130801020301122904060506010c0f030e030c0a050907032406050a030f 72
    0xa80c040d40700340801c10a03411700d0000740c10407100040c15003416100e0045c1d9503060400864500650841203030060200390342203144590064400e2a00400402048010800030001c1e0300010b440d0420f8000001c001076003400d4810a2582100c54050880d245d04880740c1d905c441101100b41180144400c0908608200030460320a80d00314014014191501e481f202c4101030140042400f070103811941401c0910802c801320007041c0c80d444860703a80c880108000c2c00c0c83c144500d244007855030240100f05076a07002e81d000040b0b000a00b103195030707910b18030102001e2201075800041c2550001c00005014190896400a01c0c2c0c06203000320f12100c00520321780c00003a043c2c80d0806403a940c000c0441c0105143c1d6218aa0100c2c2c1814401410040e64039402d4110303041403011000920350700b9001c841e504007480b031b008000b0703425035070711707140b203080100051001d20300404010405540b031181c85205218607032000320518484843d0340e901500d4100003003184d4407824491004c41e040640306055000c1038850 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 359336411 1250 359335161 359335217
    0x706050c0709020304050f030f0403020f042c0115030c0305070e0f011a16141612020609041e0903170403020a06050403260901050601020303040f170f07060c 69
    0x16000715801c140c020070007500090300964552142d4a25009807850400013003445414180c1841e40b01d92441c810022100c01c801110b9004da410103445c1c0c0c407055400310484465220b40c80c50a80a0312500454500402e90710410b020700c1084d0060000070301901500d580d040c0d81c002c20903138000340d440c2c40d512075001d041900e416405c400460f00401440c40c400d10003086000317088100758540f504c00c03450748c240300b00100810f80b80d46283c082d0321030b03003540100014400c00c5110f1036680b415074500814400d03031020300c10000e40075040000ba164070030f80d1141d110007502d2401c14030b2291200300c6510580c5c001d22074403404501042104c03400d0122b86c407000d60306600c201e515a00406c1200e074955a030300701074500900b08500740803071800501e40b242c13100b00c00f08801d200030082c0751007503140540c07015083d42d402424650554200b00180f0001c102d401c0f8178000410780183c10b680c400c03000d01e0042151480f0b40c6480c04400c0030045140030030070126801004100045948841001145030900c40c910345040705 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 359337661 1250 359336411 359336413
    0x61309080301170607170403020138040605060f03040c0f08060a0c18090e1608030703080c09060702091015050a0e030606060a1101091403070b1008030d11090a06110706050c 76
    0x255061186c0c1c06600075039001d840380c400400c00704020810524140c1450504100d0003e003462001225030280c010a0307240700c411070b0140705480c1352001062161185590410703a41c400040082c0511140765051001048100d0010501039650034026444007020340e80940d10390306240c03400b003e070340c49070350701281c11501c0c00c1d0b0603c00d40b850501008001e00d4102044070140c000d8480060b1075a0200d1000e4005100d980065036440c0711601d0000e107840c10007844404070b400248503c4419403151030540701101c0c0e05440d01c9509458500400e1a451515803205080d12420701c0d89000041c0d03c000900170300c1407107841d00340c4500b0016003011784410b011181c40790081401d2000801852184181505895040d0f00000d0b8100454850010643c4059801a1290b20000300700003001181004030f43d00c0a580344580000600b8040c3c03c0e42c90340b0640040c040d0b84d9843d22907160301c5120880c1100c00400340180100040d83d078851014020354400a6222a03a0064040008146000e50126411261040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 359338911 1250 359337661 359337677
    0x3030c12050601051c090f030207260a121404030606050a080a0201020a020415030f080309060106080112030c0201050d050a0c021e0a02100e031b03010513050a0b061309080301170607 80
    0x504241000707001c2c6030b0301e00032180c84204450115040d1100c8103401d50080d07024000b524180b1a101c038001d03152f09540c944041200b2040e4020b0b040100e001e09040d60300590001025081501c1112443d03000c141c0b490560200040004c2048400e074021400c540c001c0e16418002551540415100e005006000c1c0c0503030003030400d402c018a0164804289140d4480c2d11645140d2280c8039802d0300502034800f200d402d18008244142c100e410001580144420b24009044d0340c14507090784c29681d80608000c0c10302513902c03a01c400316070081d019119a00b50680d010801c504c0c10303402c5400941080382070b5a025015080300807100d418442c6205041120790300041170b003200503900b0300a460245a03c0b0100f0017603005030300e80d61650140080c803842c8040a841c01a0b03401c50701c2c00c15003103a0380907041d12011880c0c10303550800508040340000704a6000013101c00160740360004a03406510540700e10040b10319001d010b5041100c2c41c4003a43c140c2d005101a174240070b0360812016a160401c2e112940460401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 359340161 1250 359338911 359338927
    0x111b100501060f0804020a120308060a050301090c12030207091a040506040204050f1509180403080610090e130c0605040e0112020906061605031303030f03271e03030c1205060105 78
    0x540c4d5800d4002c0c0c8090721a0441603a502501c9403102c07481c100071400501402d05001d800d2802c49210006070400318020091a104e03a5520400e50701e10f0301c04c0c069140304141504003414002e2040800400b0051030a1105007820540d200038070244010035840750b4502004121182010b20940c1d065030f00182031003c10b00c402008001c52040b80c101500711a0100f000b0019180d260070782c404950409040c0104500d00381854050250310380144560301039101d00e1004452107a000f50014100e62562048100b5907e1b082480f1144521000004d040c00000600000385a64040f006108403222351a1b4203800d641c840d40003241070841d800010f5806070103000403549918120001f0980c0341d41004030114040c406030f64850840d08201d0007180360070801c500400c245504026024070005203440e040040074031003801144107464541c9840b10580c54008040e0401162094024601e0409070b080219400079280c001d0180000e41c4189001695040e4000680781c0e0303030300601d0300514050719824103101304 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 359341411 1250 359340161 359340167
    0x809010b011b06020918090706140f03070c0b10180513020609031e0a110f030d11150108030a0e0a08030d0c051c050a0e070806130204111b100501060f 66
    0x80440550f03205a080040c926165110107204c0b004140c941d8005125180200c04642042602d5018800384413440404002005000003162005120005c0c100e40b2603e03500c0b0304440a807492040203001900003000d220040320a1802c0400b10f690007501110810810101d402c107803802a03680c01802900909810300500d03000015096034400541183e049010a0324124109542c5020401c0c00382c001440c52800c0c4206003c4a00d204002541c401030b00305941c03c0482d9a40c46550505020040000440e01400300c3c20700407072181529001c221683e41d42c5414074581c599001f007001c40e010483c1b010510205007013007181d00f8222415940a54240003646850740003400c9603500c02001c000080220b0100403180401c5c01120401c002c00c005000d24142c040b61080726000e4600c00e5180e841a00c080000c200005101c0d5400016080030461140d01071001c0741c0907000c0a924400c1e8201e0100307940b40c03a05d041c0c0c042e800740890385000f11a044c03c00130200c141160000c1c095040044c2c3e07548096841640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 359342661 1250 359341411 359341457
    0x20011e0c0c0f060c0e03070902090436111011061312140d0204030809180c0703050d15060815150a0e0a08010f0c0908070b0a080403110105160809010b01 67
    0x10760343c02c01c0c002107044080080d060402e203230400c0c1d01c0c0940c04030301720f83c01d8103161003489015a44003c00314060485200b0075100400031800704043d090340c0c103000c5000c005440300c42500c0800080c0c02c01e000d84460f01030241c0100d0b21100340b1489031291300000f401520035020003009085d00104a055025402c8500726400500c8441c2e00104202c2000003890311400740c802000114054001c0584038010340080083c040440c184000706c0012903410b00c80341c00348440071145290b40c5030514541e0340041c2c0c140c0394042c0440041d07001815680700800034403544c01c605091705c0385080ca0264210380d042401000210b000c0308041d070030b410713800f03004402c6924080ca481031212180142031210865035541802d09440008500d00e001c00d0f21080303c03030800c0b40c0294600703000c1c00b44074001c3c080e220704000f0702d5005400b405104008203d140e03408070341410b02600381c1c0c1a40c120101c0003484a072400d09880a40510790516a4000401910000c1d0707004c2410708c28180e40a00507035a030072002400000c00a2422 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 359343911 1250 359342661 359342681
    0x20108070c050303070917010501060504211b06020609030f03070e0303120c0a02010c05160219090510061d1f02280c0b030f040320011e0c0c0f06 64
    0x40300441c4401d021800800c040d5206000070b654030154103080022141a60508404600880e81407038014003c0da44c0000548041d6040d1006902041405400551107007000c0c280103007600748403c20b001c030a6085c08244030b0036210075808a40c40ba0300c1d01c14180782d03a071249680310768180c40140301203405548228005102c0d80b00003012a0f080429254500d0720580041d0744003117480b000060b00c90f403401d4080c024a04202100d00b412402c00044011141c01d1101c036140081c412202810203094003140300c0c4140020b09032002c010881898401410340c1407035150300500300440c01c140d0442c8070810100c5058010b500024210003c1c10119080000b843e10180f40d510b01036001d0110000b41000d44100c000c40040da4241c1042440300160401c0f9064401a40298081c404100200190450b0f6082d4403074003d9454907001c0468120700210f850001d01071015642c0035400e29440c0014491140c0004484a0440b0b40802140901310410b0f80c806007400c200801e4007401340030900208d8007135400400d10b4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 359345161 1250 359343911 359343917
    0x30c12100305030a0305040b0105010e0603220f030c0203011406031c02100c2106032f090103080d05010e1003031202040302030712050607080c1b010f1a191202010807 73
    0x350340307a50b121401d6030010b80c0d459002039926030400c000c0c00003500c1c2140c0141001c0c01c11540410303900c408921a440002c01d001450f15107600880c002e03407000c070310b01201140c00030040454030426103001800d00c0e40000301a8421b608160002c14001d4800c503003d402584001d004000094002c90f040d040d04a4144000082d400f5030314080d0081c076058041d0ba550300780d440e610b00c24202c01d2001c1d4050004d134102507044400340347c440d0500004d00101081514902c0e51018141101300b14101d516814801400b1207802c188007400000802c14400060140c6403982c9509100380da8a422a0031109c03602201e03520540da01d894070170070210380030701c202007804d02c2e8911015103403945a4012a113800c446a200b24248544d1098030000c0c031a0034003c4a401c41450714044103541070000da01a031500480002c0820704003002101c0d641840c095100403115040ea260602c0307100d0b1050303c003100015030f100c0700c1d80c0158040b19046422b24210300180c815038154140002980010360011100c0341d800400400c24 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 359346411 1250 359345161 359345191
    0x9010c021207090f0f1b05121008070b040612090b0c0d060e040c050324010311010c1202030322021003020c03070503040b0702040b01031b0311090a0b0a0311030c12 72
    0x3015440e00a1180701340c030150022514003080c010190880b00303010400b803844030b000246c100313805901400303c0e0400c11130300c0d100e80b809840d40048004105242d9100c940c1610808000003a650701c0a4064401c55520fa114019000d541c0220041541ca54031002407021a0b85800543c001d00301d04003404c401c400d00700000404645808912420700400e5600382d580c203021610400c1545802c00080c2d0344410030ba004100204111601480e900c203040c04024042200f100d8030541c541d1281400e42e003103540100c1030402c82100c846002c1c2d00c90f8400c1d0385c8841134000010700d8140013500c07240007804c266405003032441c40014190040b002900310360800030540c0801c00001011850410240c4041c04491a4441c1d0381d03031541c410002102c0e00585054141402c244c062141d00402e003c04142c138101c24100464880c5000213070344100d02c1101c00040e4882c408500104140071000041c3c21700802e01d89007048a03400c1190a48a1400104c8080400d90320070480450704490418641e42c00c80384052100380 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 359347661 1250 359346411 359346419
    0x9040323093a111c050319020c03030406170702010b0904030306060306090513030f030b04090c03020301050c13060f03020409020a050721200a020a080d0801050609010c021207 77
    0xe51020780c1200000020030151a440c1d00c41e0815030301c0342116826a00e01940442d0380c2d03120031081084640051040000404000c01c040000100e20049540302c0c0941f079440c00640703061311a99504000070305c01072080b08036a07072540c100001214143c1c0c00315221203002028036601c201210b00014100d40465484050a071125100c0c000c03140d009503c652004607026003410001402c0315520b41c0031442d01030400c414440140303c00a000903003a81c15103050900c0068004c0164050b0105000e40758000b440d04040105004e501008a82902d100b10024002501ea41c000c0f20168018022044900301c40a0742c20414240110700188102c00c01d810050b0400780d0750303007500302240c02c90890807022550018008041000c90b1040042c0540159121005a42daa180050205500c02c07125a090007804130f1034082c0b030504001030100707203900a00070b00c801c0c0e0311012a0b603201c4210a442074040b80308407001040c9480c240e002d079900a034040c0c1d111042040c95808028030110361240711001405202d0000c0307 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 359348911 1250 359347661 359347669
    0x5091c020d0c080f12030412030e030a23030403090b070f0512040302030c0415260f0c03070e010302060d021c05150a0603060b03161e0804110904032309 67
    0x2100c1d030740190b01010240785041040b500308010342c4c02842558100d2075908041d0403c11058a8000b034000248d014038480004080c0c0007490104031480d0188008590006d185501050300240c030030341c030300580503005a40703040205107000540f0020f0126291304800e00031011404041c0c4503d03400f0ba0103564000c2d0143d122641055415020458613140c0000c06000b075040400150f060001d05440c02c0040307889805c000010400d8902070000d038400004441400401c42d0031000ba001c450010540303181490183d500e0345c1d14417804e1000b0340680075460002a90b81400d888a038101e0b0b0700030b44481d24100c01014a40000d502114002140100709800d0344203181c52441840e2080807102c44800706010700b4000c200c4c0f00702443d445801050309021061122260000c03d40e0b40001030900e28540d0780c9254041500c13080b40008100c2d0303054249006200003540e015041c02c0c0168010704080c440d5590343e20a01c000c0c85021a4094003040c0c12080c0d000003801c050f50030148032040c0030209404c0094840000f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 359350161 1250 359348911 359348929
    0x60903020105180303040b0c0a021f050601081303050702040504150518060a060f05120a08120105040c050a0f080702010e0d110601050109060c0602070c05040e06040c050105030705091c02 82
    0x2940140c0d92401049810449500a03903181507512008504500d0940c2e07445035803120052140d40c0008000c954416003034000c2010704141780c9013064040c2d034041070042c1380000b000120384040c005080703070b404220802d07000f480c50b00c203031901562000d00c6e00b0704039000d01c005060f000e031040b90305254650f0345000c07803209440754a001d400d40040c2412049044c003211440c04074060160f9a206140c0384d0104074003001078034010704071002511840c5a4000d10014075083c13a03001740c0c014182c40c0c0001428105526210a8203050341d40c121000c00001d10809000c41c2c1a0080e6601030001c10510364441000314080c1d10820340c03014051001049200c6000c0c14281842a00c0302c04a000c52070301704141d0b000800030320040c0c0c0582820b19210105034036001c0000d02e51070701030750060800352b40044d0301400c0c04031600400d0302404015009000c0320100040b62a5556030845003502c1d08240481d01068a621a201b228020700083d61054100280402002101c82d01c221039a03900c07540364030041005071210405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 359351411 1250 359350161 359350163
    0xe0108040305131505030f1602150c04030b0f240604050108092b02150609071103121303032d02090102012004150c03020703080a260901062c070c0609 66
    0x44586a040c450b100307c08500006c0e1001002018038544108001e500184110184003040e601091035100d00740d1410480c402ca030009040c00307585074204104002c021900768001d03605801d40c4072144000040244440c8008484980c3c0308008020401917503100b0019660407510030710a40704005055910a895540c40401010b0b482610b503198001864040c40003242003030554201c0710703052034494005070b102400100f060052121042038400c07005400c0041d220414804211888203040141c0580080e000101040740020b0500c2d41c1085145004105240c1050f0045031100952103c02a200040d401a40d10981150b5803a440c010808100b65100040342c0c0c0590703203042e515401c001d0910700402080b401c43d014494010172090000380c0c005660300807a070304074500c1c0f52194800d10080300c03541c10010b074603030803456055110501c1680c4e07c24002c2c02421548000c12a00d0354039401000740c0054503e04002c038031110080c080800c5030b034140e42e540c0300381c4a14000d001d204056441030201d03113481e54 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359352517 1106 359351411 359351417
    0xb0a0906210c0e010b09100e030d1b050717191a0703062607081219020a0c0b03041a060f040e191a06010e01080403051315 54
    0xb944030040c0000c44144442c5503550002c0da1269003104008074441e0740700d000c111207101e002d215000788120000d8050f00c0307075800201095900c41c8050070140d031402e44540080c1c00244d02881420080c00e640c0061010f1208030302156460005080001000307854450344d20004035481a09082c980e001c000e45ca4955039851103000c8010b0103c0e580300800e002502040081204044400d43c0d038150240012620f8a039070300c84019036200c5030345c50300c12035035801084021881c1388144080c880c04817013401100c805416950352000302d000c40307900020703001801000780402c01070039240c0e40200040411509845041240005484800302e41c480d80c0710f86e564040c003800c900b5090004100b808140099481c0f0071031903060180040c00285d10300c4040c1c0c044840000d689602500c6000d03020030042c6d4482c8520b0f40e856600f0f82b101d43c48540e824460b1052030300000345210360305842860824482d6 = true := by decide +kernel

theorem cover : BRFrame.Cov 359172661 359352517 := by
  have h0 := BRFrame.cov_init 359172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359172661 ≤ n) (h2 : n < 359352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
