-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:05:29.578297+00:00
-- url     : https://prove2.me/submissions/5c7d0d56-0ee2-414d-9beb-105c39eba1db

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 935971223 ≤ n < 936151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 935972473 1250 935971223 935971229
    0xd03060815130602210a0902092d0c070302062202150d0c08010f0609050d020f0f03120d0c09053a081e0f300906150406 53
    0x159002107109004400003400459010040b241030720921a81c0d0390300c000690744045043d41682998024a2001250400c4800e0f0014020300c0d04100125255002c2950141d0090420364042c0c8880100e040c0059213440000c002807101c41094407030300c1e1540762443c458002c072500703400522032400021300c40b1042207424444412a03070001c2031845295802c22107002e0040703602000d41c103014012106450342c0c1d4044d180c03950f0300380d8031080890742c10170700e00086104080e4400001c00400c6d40c030400c00d541b160840300d2071503070301502ca101503c801800801c02c910310740d0201c0c9405104a9004c000e4801d080320140040040508090000030b08202044a105603117024803030740401e14581400d03a10083e10aa40c104188201204030818050995440c0381d070301c4801c00b41c0c0e07038900001c0c0c030014203081a03003502482c40e090b01406040250b1385a40659900555210b15404092600c0040660901e640c40b9404c14006914070a4249001c1e20f0b51900d4500907a880d000072030408203d0b0034185094042c0c0416 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 935973723 1250 935972473 935972489
    0xc09030605160c0f0516080615040c0903061a060714061015030509070e101d0403080f0c0903030d0c0e03071514090a03050a12051602101205040605090d0306 69
    0x300110a8460740b01d040030b02c0c0c0c821600d51007032480c00000c1b9410703114204002d14400300036050504c0e010420a2541d03034050303409481980707407071480c054080c1c00086100550740c0100d0006500c52610a00c030011102008507140d0010f4003140c050100000585444005414401a1200c41c1c0340c125102d074803005d250048090031240394603001e641c00d1099100540c40503107e03046074285a81c80d040010040c405442c03d0001c11001e0209000041c507651412407040905000000240341c035842c02001040042c001d840c00c0c4614001080c00c04100401799022184010281c0e41d580f2040301c1860300521200c0e12000224003203c004071024900840c50703504990000d10318068404041c1c004490055600218807440c0c0b0f4180500d07012921452546405144200c00506061600341400508040303c2034901e01000400c016500001d000700c400c0031210f90f4151913002c01d14891641c03d48407440725251040c0300034940b1040106001e1070340c00c410f0041c502801600c5000b0b030144400c9003aa411780c05400a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 935974973 1250 935973723 935973737
    0x30a02030f0d1209050c091905010308191701060f0c050318090109020a020c090a1d010501171c0f0c151b050f070b0c07210f030608100903030f0c0903060516 69
    0x3c0b1420301e00045644802142308180f06070f04079502d03100880710203800a0b580454040384003038078401e41007003400c11800182091000c403400110414554203050040d00200300044c414806002e00401000040950103005d4075201d1050200c2c640164148580061140824000001c4c12034124400c452000c0190341c05442102242d1041c03042da6400503010804080c0e486a107a08036a240c00c1200944900c840008650b40d40350000e00c08520805200004190b00003024541c05480340100c40c01505065050540d80a000c560f419100030a9454000d00344140c0c1041c000c4d070681e2160b0244c0112468508008000d02401c403040310780d4040c075140ea201720401000420041180c06100652005070060000e140801654503e803565440d80b100d1801304504184c107903072181d004209100301814910b4100290b500d000c0348a5600c911210004c64019501c60b9241c042c54800e800851040c0c0c8252006d00c0b12014065000b040c503911403009030b541904c0e02c0040342407608035200300d50380c0c03914a0795052 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 935976223 1250 935974973 935974993
    0xa0603090b130507051c05010c0315090905100207050f070b0a091403100e070807050d0b07110115060c061a09070815030d0905090a050c030c09030a02030f0d120905 72
    0x304404800740c070242e0f10341c4a0130f28001059030300e401851605030003510598051100615050b401d440300d0071420b00a1504003c0d21070140d51400018800712269914089005850b07814100d0800000c850141101400061040d082c084001101041091000100e0705820760311002d9040900402240350001688510108801aa80002e080c07034078a008050b5440c0c42211021a0704031290703456005042c2d045080c3c1040042801c1c4400801400143d90800080000d50750b48165440700808031011701105807526412080e003540100310038610055038800d00da48a02c40680204110401251607605090405000710500200d407814603130043c2c00c119141d101e041707055400440042c021010080401180c29441c3c0d01000054400c0744d054507841e18550905041c403841031801003180841034106024420185132100880c1d40c0300704010340072502c640d20140007900b00359640c2800f80d410320610311401007a0401191a51440c5181e4450384940c0205200c0c03c4141c1c3d104820207800c9801510210b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 935977473 1250 935976223 935976241
    0x30d090f09021803030d0b031005070c0f03030e070306062105100b0102030f04030605070809300c0703050303070905101e05090d0b0108101406060a090b040b090a0603090b 75
    0x30b032164004500c021181060014013003803464001403180c11107070380c071004220090304080c0900847c00302c900c1c4052055180c100000b9010407103200e8000d012001007054401810701c01d5002142d903014242c181d9501135682c0c10601c0c040c0045000d0170703013602200d02d200c2d45411030040024041a900001404c0d00c2204403501d20000d184080805065001c01c00c98860b80720140d8000b0300280d880351000043d6810402401450242d0040c03c2c00b61030b9124048280282013581b450030300103140071103440c1c440c0150990440e00d80c004d42c44103c803184508071000c010000080055403003071425030b44000000307a940301007003000b454082d48400412008102611241840440340e00d20642604015113482c0c4040d001c40c2025580107021365003060410014428000300380711054400b00f2403201032103090708030600386a8142c0c020b00014800c610000f03485140e607000d00c02e0000104183e00740c0540710340d603480440c52541d000104c02486a62104004115540a40726240c1419001850a00d4980e548051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 935978723 1250 935977473 935977477
    0x10506031015181503060f0f052509080118062316020307290612120702130216030f0207140120010c030f05060402030603210d1a030d090f0902 63
    0x10100c000e9182c803010044c1d1807040b012440218442d0100245151440d4002c80c11200a000c08118403801c00060090341d0600078185880d182010340106050310346808241d600680035407081d402035081c60f040420b1554171040d006a007a001305030034050f03191001c078000011401903a12050311000c01d40490424070740800001a90203d44c0100c03840e0480070b40310407212010240300c600012945c0c200303400ea4060b00440860300700b10166150180f0660180d07104d074903441c010001c201c0303414000c5918415941c89022f5080b1511058000710740c1c1e80801000c94808070740500e403d03000700703d0100c0000c00e01d6100140c0a02129031050141400c40890300045485084068000b861020750740d00000b4480ca0a00c1110b104080700d450004640044002c1c2c00143d4000402c0c451041d0300c14802c12141e502c011078450841d11500c82c030410001817402d079151031400380d01d028034809480e0803c100c00003e00c0e609180b20f2003c0450440d088101c6c041c0d411240c640850151408161281004000d41949500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 935979973 1250 935978723 935978759
    0x406090501060c2a030f230d0c0f0b010902120c03060108041e0b0903091201021606051b030c0306010806030f0703032f011506090b0703121b02010506031015 69
    0x1a8854481124401310407103954000740d940740003103045502040701c041c0300d03a05c650b0b480446152061a0f607042c0305441c0c841c03140da000e0074058101115010000c0012416404541c0721000220658460f08450000c1d0004845540c0e6809004085214074800d04103a0340319070016580c40401d41c0e6103542e01c03000d00810b48079400e1700b0814455507100083c442510503100d564020b000316100c0040e10100440c00030200321904003a44104020421a0b21040516039240e400072408241ca86448011780602c40f2040c480c005a94004070030700c009c00584100a50240c81c00341c6e00c8070398945404c01059140c90442103030309681d42c0b14000030000240120180a684403164201d82000e50f220340c0f861755200a8566080780ca071359a4216010850b6414401034003410325450b1100c03000c0e00b000046020f0740f2841c0405800d01c112078034614003100c1c854000707588608140b10315180c049100c10001c0d000e000d040c1e4445100340108941001d0441c101d206031004415000140e0b44501d1400d541e50032440b420744 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 935981223 1250 935979973 935980013
    0xf0c0108040b19090b040b0a050711060f060303041502070f053c0307080a05071707091e0f0c03060e07050f0927100609180c2c0406090501060c 63
    0xc28132804a580803994520a40c0100300c0301c90795182ca821a40c0445030010203410a0064040300c2024980c00010890b0b4401305140014010b501c82500183c17650161382d018540d0168405800c150a6501051060485405103000550300340c55408101f850304041c100018201d0380103120001c4030060009428450800c01c142010800360320011034141074a81c0c004110036406107188800f003001c00c0140900410240d07030340310b40c03e0b081364034443e454039424420311100d56182c030b8036003001c041c0070b01c0d0400000b41c890b402000107508541d018000781c04944a404082884d1035800520701016500081c414000c69861510744041d000800c1896040040d8031030b0401c1007000d20300306802e0030040c4040c5d00d081101c000e0710f0516003d1030068241405030054000c01121850402ca85040c20f80681700c4504203074000704080d04c50786421500c00911002d00079a0001038400c1c060320940f0840a11070b009800e40f41071107902d03128020310703007903132020f20032b03103000541c41c0e41d0110100e07281c2104003044c2d800007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 935982473 1250 935981223 935981231
    0x60313120905040615020f0f2a0918011d19170408012a0e0603070c06110a03200901050c120705030a030509010536010e0f0c0108040b19 60
    0x28001050032903130b540d00b2080340100301c00304020809404014010320001c0120003880401c01112001f510381108050311901c02c0041050b8688000744070880e1000d95a001e46801418030300155000101034240510404070751030811800e001060f4200e0b41001c41c0e5180c03008004e44015150780005c21b80300410142c90b010380011a9043c54291800100000c1c11003000100d45441804507421401c0c1c0d450400c040720220a5540a00c029000072081036818402c9a145480780e0300c0390f0040d907000348504c500928444ca00748099218138065401352040307a100d96802c114560008a46002540d100d080e9002000d105011020056100340002e1054214080541e203a0310b07040e010204481c0c1010404072000c0d040420041881a0701d80304030381e40000890b000307001a09144805005480303006165241d94002000c001c954110a000440140300300b98000b04109194510b0240e1500fa041c088807815024078184410658401d0b000d50b8061a08944c044d0b904c0c1c1c8614444c03040c14070b0002130070170480e925 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 935983723 1250 935982473 935982479
    0x14090a020a14130207050304030c0b030f360106140402040b04120f1e060f060509060d261314090a020913050a09050607031a011d101205060603131209 66
    0x280050178100b807180d0000d648650075450b1111440600d034200031810350041c01017107800c20340c1100e4190417104014000030400880340e4150390300000f4141c0c0e84102000150480012001540100115040040c0c440440010202003100381e104a01c1a420480014002032021003102e040450741c2520816140040f00c040e0f0f40c40340001d038028881c0c0d004400c100400b1005225860003528001c03840c031503080000b2402e1100042c003082021b80110f001d40c07640300c0240708010450350394260700984003031040c841520702c6404548230786c01500e5600f040c20101e10002400b0f28032806580b1a4a030080180d240c560301c000c04100203402001409038460600d0000801101f8244076807030084d14a40f00c081040c03c1c1c5e5007045807402e80d0240c006c0c020540351229441c1c140f203070305880e0a0811000d2a0041c9091aa01d580c040c054402e003055a5000620100b48035031250080035000f4400c00e840d006000079a943da040000c04e000440d0300b00000100ca0140c40009003100f45100b41c0c80c401800c0926885403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 935984973 1250 935983723 935983759
    0x40519141314030c01051801050c070804120201030f051003060e0a020f0613090216020102010c0f091e05030303150a080109020a060819050c0a0e04110906130b07030314090a020a14 79
    0xc141c0b11f000d00c200000d141c0300d001d610207008440d0300581c00107041303141208550b1041400c2c4218404c40a032200c82044174000c42e88a5008613141c901455410f01042c28800d02c4a100350000d880100c4220340b400b1201c50751540040390741d24056400400d50480f824800c024007101d40c0c8060721161300201000c0f03011402c56850f00c054000780c0c4081031003040f01000d074400a03085a40c0c1041d4101408802614415010750000302c90055501403c04044684403400101e00c514102e0740150354140804020016110002c5c404c86080e01412610908640e81e2048103070f01f210f07070614001c0d400004e02c20051102500464800d900f01784181041d0249410f941d0100040380e00550700c1210302d140c001240e001c5290311085801000608035020490b2103056090b03445284901c400b041d021303840100703100700e0f402c0c1c80d0b560a800809003403008aa65000500d0010001d0000d0139071a5102203c810204000f041c0000d28034004950150620881c10704000250100610503090070381e11542035900c508a2071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 935986223 1250 935984973 935984981
    0x908041217131a12060112020f030a33150912030215010b040509130206040b04120c1215270503040e010602010c1e02010b040519141314030c01 63
    0x620a40300c20010504100d90030640c107119070410414030f0410301080c0c440001c66004150400c03800d00300344122810300d50a00300131307000d072940c003081e219070100c2001144125600242190300d8502035040351200406444866400d84100d90700a54600740710034400310020f802e43c1806842c00d81070032014150381c1c0e2100c2c40c0702c0d20000000c80050b040403002245075240382d51394502510811600505241c100b0b804070b280658000d101400c4410900220b40554072010200c03005004000d01d4155500d4403840841d600800d1094111101d5171441d4000030785841c00154140d209500c00c1880001782603005449014190905d510507907016803840200085031180310703070101c2038070401c0515280c92401e048500c0b00081680510300b96410f00f5007050b101c90b840646070061400c840c240d6150107026040c00ca00424445d0300c0550880d280805010082d6003c490450a10407101303810300c40c161020310040c01100c0290b691803a0a03800121100000b249c030a43c80c0301500711001101d007094105a0480d0a41e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 935987473 1250 935986223 935986237
    0xc0a0b06060d11070210020c0d02060f1e071406010b0304081e0408010b09090601060206180c10031a010207060813060f050f060a080f03180607060e010516030908041217 74
    0x9090005413007011400c2120910100e03043e540050100581c0200c0403130062811903800034803404000490f4105140c1c00700030390750100079001c50002642040c0ea9115100d5112600c141c410036400d10b0300310032200c0d00007822416103600e03c0800b400c41d141c59039000110b412007424040345442d4881c1e0410612001e8000e0b2009010b1000003144085500d4140018000c0c06044030809030000c0b0014850241c00281c03050b044070b801c4841e440b900340c1400029040084860344c0303680c003071304007145040c1050b819000240004080d070303104c1c60f084a2880040e030b070f1003071580304120210b0342040000c3c4401500c04103280071a406041c0200300d152807007074030f4011540304841a40702ca118600c140212810180403100241c20f66030020706400d084044009d961303016814604200003201c402c103068070b031120340580703c0345a4020380600003540c070540c04c24040c0c0000c40366505078144075400f0035940361003030241800807504411041d180c0760400d040042e8403402c460b800e0310318110709144a4054182d0368018602 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 935988723 1250 935987473 935987501
    0xe04051b1210060f050f06040501050913060b030a0501091404060c050c0a080c0606240a030e0604120e04020f1c11070f112715060715060b0c0a0b06060d 67
    0x103441c10320b544140001c03002e420486c0511242010f0841544400c01100d05a070310034204562101c02030000148142483d03c41c101c00a03040101c00100e5400042c055801846d190700c0900c0541e07200c40c050012514440c01e500c00703d5288001050210700190311441e9070961a1400d41e00d0003054400461800d910244100c07804040084c0503400c2e82028843c43d6041101181d100f20350250030001c0b1901660144141e06044400003070440729240280c3c44100c1140d156001d60700140f6041c03c054024150100c0d008010400c1002c00f801d0304e26007071007103424600744803c1e41030801001301015400511101c1209042598031000c111000c3d0300038000d0720019100e8010790b00c40403090f107066030810801d0200d04d400340c0c0c18488207a034a040c04060440104449071000c040d00d940d43e41c0d41013040c3d43c0e10440f194100ca800a8001c0c07d1001c0d600c40028440c0e0190010310410381d41d090080c5062251410710030140d00280d84e0f020014254040e11a00440700410a609012100d9020412a0703040708071109 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 935989973 1250 935988723 935988731
    0x6060d060e01030213060501120e0a12020f2e0e120c0304080d050304020607081602060f0a0905030f2d030d020301031209031e05120a080f010e04051b1210 68
    0x11481c0c202c40d005c070403803c9508140105442d1200103170642c8031180b610301c40760341c0766085002800c00400c080a9070a4004a12078030013000c1602c080c0d00c0380703d01c2d02454885c1c02660686061280100082502880003016001d0b00f40e00c18588a4002c0582603c00a0300d1301503580708d02e00340402d603005810300c5441070001c0c6a80c0c1d8a000040d40c40c05580f075090b0401d0010a00800c00940d803408243c8103401d0b0440f512a0340c0c1c9000740708001d62190070401c001c1d4000e0b008107000010040c11030190a191085840c1c5141080c0c541c0d080698515001c01c0421203548554882102042d4490071580580304c140110050f00e04600c0855003950042c580b541c4101340d000c00104140400c3c80c082074030f0300c26241440100e06086032220130395000d00302410200c800b140e2904400700031081214440b411001c04c011a110300c64040001d000160075600050307981025800820342002c40900c0b5805036a105004024500b01e007a46118151904520180d00098040020304040c0061082d10058400404001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 935991223 1250 935989973 935989979
    0x2006160207080c22020d050718050307240c080409020d05060d120503091906020414270c0702090f060108070c030504091802100807031b020a0b06060d060e01 69
    0xe140c6841c40c0d100c402d090780903c0c01c40c2000e0321000403c0404108480e000700e012400124450040c2c03183c21948030240740361104001b0030035401038100f025824195031030440303035954204159a070552406040030034590f02d100240541f10b440900c110000a50074000401043c0740c035185000e401a5205587c0c038cd40020f0a031911002611525078007440c1100c101c400860f8580310b0b0042900c14070011800d011000012a24400c02080520066452001607010011a510308000690001d11034140150801000c04440d46040f1610303500c0701c994540035140440000880d000c0a2002030165542000c0170481c00c80945c4504c16854441c0b508a00811024281007000601c1c203080140081308104640c513031103000035480421170b0b0407201003d40206140680c40400101540d50041c0254884d00b0721b464281c1e00340d040035580344190132075142046440c40e0f01c01d08510203000111150010b80006c03907504000303001c00342c5c3c1d90340116015048a0800700b4110b078400459425401a440c2107445070010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 935992473 1250 935991223 935991227
    0xa06050306090c0901060f120504050f030d0204090c03200d090b070f020f0304060c15320c12010e0411090108070e100e070c030e06030f15030d0e01200616 68
    0x2140100706c1c504e4062800d40380880c0050000c0d0600748070000c156124070228052080c10400841980445401c0c0ca030340f0300960b190302000754898401c045480d0305040090812500a10a440a038484d0441070001e281c01d40d400290700e548400202100c0c65a15216030b400f098007030005a2141101c1c3d2100d00751400b29041c040e2074008892400c08650f0300c03c0205100d4a03902020300f080041d4005490040c98013a00c14030009424140151205003d03602c070342401ca500050350441200c10300410403040c42d1500d080b014024498207142d40a40d440707050040181003a14020b25074001e0081900c0c810040f09007000074114402a405000316602c40401480841e803800e4845410041d880c0c0c03095406868005c140881900080c13500040c40b40707590386501414051111140d4140f03008100a41c1c0e0314200b504001100002d03a54910a4540c0450950560800040080301b81010307898a00801032070348011205942e90090340c12210080c41c6840345028820854640101c1d200d111100070140c8403100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 935993723 1250 935992473 935992489
    0x90f15050604110a0f090b0a051308070b120411040905070f12050a03031515090e0109090b010e060d0f08070b1006080c07021f0e03011b020c06030a06050306090c 71
    0x1c54803592620315101c034880454030840308240294180300b01e016044000548515489602c5504803220000741c403402d6aa002c0024403c20049280a111244d10f5503010781e070b10b045501070011446800c0011006003e101180f00364410700c2401500f01c0c0481c4000840e00303481c007000d401c0300c080c0e01c07440341400040d03d4845110060b081c1c120030203c2800c1c00d070710b0741a5510000d61020382855950720340803c3d59100158104094040034a12000c03105c200e44004089001900c41c0f1040105c484002241c00c0c0c14500800101d56001000d0360441c0e404c10300c41503d5070002400c12903211b4030600c40c880001b00f850080d07040a60103403114580321409810102c201a40040c010b2030303181b560380030901c90142c01a048a401c0403007840d201d0349951882c40461010503a401d20060702c032000a5076000b00e83d90019140071039103410744c024011070050381001001c0020083d1000c0141e00200d1100009003030940245500210480c070114280341d551000c40d00b400c800f9201030000790402c0c107080344d10b4108004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 935994973 1250 935993723 935993731
    0x601060c2d11040c081b190e0f0108040807170903010f0b09060607170d020708072a0f0e0a150303020604210e011b1205072003030715090f1505 63
    0x1000c1c010b81c10484d030024110040201072902c003410404041045000100c10f545607941031101c0c03104208182c0704050b00c0301c45405000791155000e004400055449401d1060180f54800c01650402e101585e5110f2628201103104004c40d00a011541450f83c0901a031540f80d4442540001c0f0200c00c0c100788000071600031700e41c601840e401c00001000841010503a1500d00000209036103c00c40010084040c2c0b04011001d840e2140105e0701c0e0080c85521191621800704d01c480400284400303030a82c0c0d64031030070392007009804010200100f11404480e0507451748a1081000007447d07000c90010416450302c2c40d08154010392140c0204800c03c2036640012413142500180028181b000300c000401b01001c0f9100c042c100500c0188203140810214503100c89298010903500c064908400c0060040d00001001e981002804203110100803103071b540300c01218005006145482c901e42c071500700d0401c89102e0001171564070f00101c404111b020092108040c840d005044e0000c45440f151815540090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 935996223 1250 935994973 935994979
    0x303020f0c03030f0a180b0a0f030c1b0302330901021c09140d050c0c120d080711010c030504230d030e1203010816170601060c2d11 58
    0x7804000c0305a8001060340e10081506020a44c3d40170f607002c044964003113103461150b207645090340108006c3d00f140c026160401c0300e9565000444148001107082e11940b0184030003182100407810321034400703070b810707550388030b010340100c0350040c05140200c1030a100080942c020901c51404503543c0b080080c04040e040130070b81c4001d42c02c0c120750204d044800d2000e03d0540c0f2595546840003810480306100258000c500d072030990b014004000f4025050b44d10003c0a01a280a5000012a0791415074000350071099205e005008401d4800c40503210310101924500a02c4014156a0a094401d028a403541440ca95003c0340e80e0900d481c20f91000410303c0c07518030000d01400a1000c1aa00000d1a4000c66401786000b096980514660500388480030040c06170169001001154a8400141c0c080880f000000244007103a51510200d444410007088105641c00403001049154452802d015100307004412040542944864001c0e01d200c4140403201900c0e110a2040140314500141c458050703016 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 935997473 1250 935996223 935996233
    0x30a140c09100803040e190c0e01120e120f0712032708030708100f06020a020a090501121401180b0601120e030a2105010b270f091806100303020f 64
    0x30303c0d07120f000d0740c050003c3c0f03442c2220000b014205040010a0300b01010001000b0307040340e040c2c0c0101a07030940c00c101c5d40414050280d410001045100303c540715411000904407401202c6c103a614160f02c4401142510502480841d000ca62800040072a00c4080c2c1c0700081e503074403005005030059058444640107850580c20110205036801304030b952114051901488503900c03031210b50114400d980044031103040101000c9103c0ea0000b64001003180210348104c403032036171005007005640090040e0018826511501000600300c415195401c0b0304d400c00103d8500307400c160300d040a00140740c0950b110381c0000280509942c0046913040c00386101030060051044421030b690341c81c03080f0303c5003408000c03d004981b0b009031000400302aa640e8000000d0045503520790009000b41c010440f1001d00e1342914108a0380c3e2010308008204e8640050880c24411900000708540300070000c240300c1600390045c0c2d210b120f040c02032026510512070300825a52841c02e6060013481d210400c7d803002065880 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 935998723 1250 935997473 935997479
    0x6070834050106211101020f060709091b2304151e0c05071203051c020c0d090509060105090f03101a03120712210c08060d0b010b09030a140c0910 64
    0x45403440c2c8044a1704a07402102c034912090040b4640002d05040c83c0381c40c041e48003071000703055101213400100d81c461031051000c0c0c05000090074a071700300003500c4004249241c3ea004000e07458400742c460306156080105091030303552032059039440083d1001c04000f03481001c4000d0101d110007a00e84100610340b50a1038445015911543e850215005482c1c10051420a0004141c8610202c0e4010100e043c40104078045000546001c2d402181100c0c025018060040c0c9400d4031440190040329401817480c45261110001034031580e00c48088650083d1084410b608540c904122280680096841c0040c610003503065410803401841c051500c240c00000003070000310761110a99100e103270000f01002451000d030606592140707445016555800d04414014440f0001d80c0c4110044d00c4140c035810040d41c0c521f4104541ca100040c80100703204024001801200c40132000382007210300c0070f000ca41c0003100c0d503110141400482c402c0342d85540e1150119590900348616015009400309050504544c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 935999973 1250 935998723 935998769
    0x6030303140a1a040b0d0f0501090c050102150708040606090e15090a02010c020f012003031603020306210708100f0f020306030604060e0109080d090302010506010e06070834050106 79
    0x1e0400402441583c035410484115603481c0360079000e490740040700b40100d4900742307001c0780a0442510309651648010200080030b5001040c80b2140003001d403140c010b1640c540c0010b540d54172020704295021645d8500102d403804a612030030340391040c02401002c1c0400181c0751002d440d070004050b01c145030014804c600060f40c1000071002c000303074100d519071141001040101d403110001603605820000002a20078034070b01c00f20081d03002d00ca0400e0742500d00d0080001c29001d81c402551f2594010482402802440c20f401e0040855a403040041d1000309a035003400070310f49002d400c40000402d5641760645030000e89482420080301f0580d5041d070075442c0000000341c0300c8800410241c20035441c3c0d80790004121007944020b10284d44800c50b0b03501c81010900400051051420450143d8a03003000b0a10310360164010344085d1000038005842d0001c41c1d5030f4401250481360038141c1c0750701c0c642c07007038000651814420a03002e54081c085110a003c41e0820909480e007035404a0209441e00458450b800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 936001223 1250 935999973 936000011
    0x703021c021803010606080702010e03031e0405070312020f070510081f08030a050c06060102010e06070f140703020a020312040b04170a02090f07180f060e1306030303140a 75
    0x40319103540140c031900b15514614103a14915115541946004400f0802a800400301170240c615030380200050b4446c060386503070360b110980e00d00103901d04046100c007500b40d15a00050703015210b501074992550343ca40ea03c0c54046c568020040240c1c01600943d012400b0030000580105006c40d004410080c04410203850640c0141001000d00fa00c04a10215003601040f900c0042c1070580880b0381e034008000740241a078001022005a42c02440c2c08250b03150301c1401480030604055000d407049488001e8181c610317002c080382034018022101041c1d4882500f05000d0100a030007a009040007012520415080401d22100c0d41e8a4035024041071102801c0c99003a076003036a0b5074079010359607691041d0314149031140c1608000d60055100c410041c40c080000c00d114050400740d00c40540311640c0ba00a4031524045002d090324a618044080201501c1440e208102110181882540c0e0041c1c410300030035074406c2d4100386c000c240c40d80e00b070386228280210520b0341301c2c801e11401c000c2c00f600c10070140102 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 936002473 1250 936001223 936001267
    0x60c2109080909060a0e040302070302040e0d080c0a0c0f12140a0e040f14190c02210304020a05060c030c0c062104050111070b090c04050402061b03070804090212070302 74
    0x43c00e01070001181511100d4840e8041c1c10301c04c10b0400da030728092500950303401050104034000c3d4105000780044d218000ba82c11103448480d01c1e40c0c4695178070380c0b0301d246054004544a608011800c038449010070748071a4a886c4560140c030200c2c1100f49442000740403000c101980c580a00b604002e444421540304903409100c14007150086200c81c0c0300719400000e84890340301c85210301c01010038001000596981c0300402015107030f0901010641d0302081e030b2103000136556040308000400304501001045001180e00520060550b000d590b01d85000c21000e410460400d0702c650300000707050640f400c0401c074a0301060781c201c4a80d071400e0355810322002c6180d04062814140c103141000b0030100712082d040089010000003100e500d900349d600704440340c000169060701070741c060310740140850f00705809880d06c2141c0181c90039180040e001007800807030404500d03441c020b0005000e900001140c6c0f400820042c07030040c00268450191000e00f20b00b6400c0a0010028980f0411886014500d40750710b1500d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 936003723 1250 936002473 936002479
    0xc03010501144803180d021503090d090e060a09020307090e160e06071e0314030f01150905031c020c040606020f101a0f0409060c21090809 61
    0x3e5404192002031400c003109500d800140410f20b1115080422644180c5a10035001c3c07042c0300b03001107290b4191a8400c8007510203c502c0200c800c0382c1c150800c80d255010355440503002400f403070240c0449000e19041560303110000e400040b0460111640049408080c2c80c01c211045480d040401c009008007285101d00340d000c50f00070001586d00e03030040d042c60b002820884500521454510000c554146000610380007241070584491414100070702642c0c5019444201000b62008481c00644200b140c10402c4040011042900030400096005107008032298005580c0035410711401030011101088001c0c10404080c104015030750f0001a01d126203140d1006034512554000800c07810f000025560b940c201d81046c40000d03c055000480304804c401c0350090f12502511341603490251402c82d40c8610012444091424651520360085565644014400940034801d030742c1c2c160544d42c3d40c501c114082055101c0a8284105a8004010b480b11601d0100110740841c0e940703400314080c0000c4680 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 936004973 1250 936003723 936003727
    0x7050604091a03010606050d29010324260f0606060928091b05090f01031404050a020f030a030210050907050a0305031309090308040b042303040e0c0301050114 70
    0xa01c82c19118020210628040c00030310880c6d0300c03900050590740c04104c1e8a40701610304004020381044072045c0349aa030b0022464100001c1c00200110301904546501151a007282d01d030003009500518400b2009014001c01c0c02924014007140c400782c1508800503003030980080c8401d5181000104a1540c0020110f502c540c8031140180441e00030702a01d170314002108588050070045c101d10b41c00460480d06404028040202030000c07110780308242080c00c0300490814484030200b890300b0074910311003400601d800110382c00001c043d02c1017036400703407015107640d004000031f0340030345c103000050f50380004054008003502c032007a81d00296242106034018552690310b0001c16807104091001030020302009154a8030217840e030411580b01d900c040304400b00354aa5600004590000c1e029951a440c1c050701e4542c5155100d4860320542180100211007e038100309a030000044803042c0749090806500095072610b0501002d6004d0900280c09078205200900c0100416a800000b005007081741d03000d030036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 936006223 1250 936004973 936004991
    0x120402130605030102070317071b030f0e130b0310020306011d041803090806250f0201060308040b070b0a050105030705060c160603050601021501080d0c03020a02030706031d0705060409 81
    0x20001e001c240c01440c0c0c03550000a80005140c0c2c0901030041400600040241c1512540021359549440c921845940c0e504840f2000102e800b512600001d4540303414000c0540340664002000074030140c01c010f45160356170342a01d810f0300f42000008100c4501c603500714954203000700045d0444030100001a140040030b8060a01a2030f40c2e001a10101001c0d02c001d80c0c0132032a450041c000e540c250140c00e0852085d0800211040c0c000d1407181d0700703040041d20741d07082521162001c6a0f000c19103001c0b98150342d280c010010005a003c00107000404144d001603440381d049240c81415044042c10300ca0078a400c10340140703c80e680c00f082410171031b00e0846041742e581c2040308045040044e410704102507000000c400089170342e01608024410902682591392030900064000d540d44000c0c0100d079503560090032052805409a001103a255000f80102d45030001d2950000f4500000ba4202030300290300c03070300c4426408200c1c00800c02002022070142ca101410030020844600448c0b01e1409825201c4003da = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 936007473 1250 936006223 936006259
    0x60912061503240204050d021c0507081b0603040804090b0a090f050103060c1d0114090901080313121703070e06030f06090c0a200f07090c0e010302120402 68
    0x8000c01e020369103911200c10796a0510740891142c0c038501440c00a1001c900c030305190303118821601500c038024040d0590401c01d400b842561305041d480140510780d40d02802000c02c0c02006441c00500540000780201c8810f039a02e00751040c610481076010b90300c18401d010000e107230501030390103954518a000a4440c01d000020f4119007255000c00c03011441c3c86248070250566801c4541a0780c081c4d0024003400c808414100c504032002d02c600e00755006400d001480c250312910f003030025010450019410007518000107076107040300381e01840e00c40e03000251095840c048ac1a09100511142c00c810f40c964400b6110748507064500c3d4540124580d0000c0015401c82c055140c1c3c0c1164080608a43d03202d01c0c111003841c117400320640f201c0d4072800403a400503e00040b58402c940e040680b0b80e84442c0b000205c0c08018081107865801d101c4140100401c0621000c81008000c0062400050100e040804414013920001080e04000d04050040002c46110200012140d0700564191803440c403140c001001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 936008723 1250 936007473 936007481
    0xd0209010315110d0c08060d0305160c080f0f01230711210901020c12030418180318090204060503012115091a040c0e091501030c080105070906091206 66
    0x500002c900000c11040c86814942d17001240750030301e039160300c07800352501010410044e8402c0002000600200310700d40030242c07640314a410251050a0b42e203003154603818514142450040400b503aa8800700139021660024040c10f0155811410400602041146101c1c40707a807000340b20343c0078005030003003116242a0400680d00b00000040d0b1540c003885005081034460340c840301d4054018400c692009101c1c0c98041c00c42c44e130503c00c00c4011840c00b450030b44141560b20161400504c3e69588061306050510440c400c02d800f24401c0c0e80720819070112012000d8000001c0c0c10098030300384148000d0109980013400c882c151444ea045004142d400000d410303880118407113004046d1000c0c003e5120024000e50005400d980c403540c1c07044000700100e112203400e82800ca03006000170420f00c00411400503888c01d02a0405d6082c0f0070768a10100300400c2d148401020f0388111740d503441c0c47c14100308035803080c801d441e04401340785060108036140c600003d20b50030344c0707000303841d000c0740710416020400510340d00c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 936009973 1250 936008723 936008741
    0xe0105011b0f120503180606060d0c09030b15031002030603030d090f050a1103010b15180a150e041103040302060c0d14311703191404030e0d0209010315 67
    0x4403843e500b0b08100c0c401851a0819038000c840c1644c00f0010300b550b1030b808100c4138460000078200f41c0c10300c201148802e01500580b6011000d0041681010003c42c1c040070703500b40705691200412400242040c24140341076402d043d401050782c818002d12000b5036010003110910305007000c0c0401e002030582083c42200791030b0040100544601c0c0c800e44100502c1814600d11004100c00070046d5240303403814098031801508604800000c108030042c4681308000e044c80d401400500f1031801e541c1c031803030a16120403c0b80b1407000030a440410290103440c00340114050300d14513020407411800c15980195a80002800a9411410108804118030000c0c1d1140300b1f401808918a895403e0034a540740406412040c001d0b548540d03035201c80c08184987c61b04200c942d9106007000580030350103241000c40d40024003012031085190030005110701d00d500030030307510110030701c01850030f400c181c41c002c1c2201010b0b402c21402050410001405a0386148100b41180d802c0420020407140c0c0004403001040c03040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 936011223 1250 936009973 936009983
    0x2306221104180501140d080304080d15090f1503111002010b04180209010504022809091103101403030405220c020a05120f0a0c020a0515130e0105011b0f 67
    0x70303103580403100981d00f01c541240c0d03904a80d01c2684d030380102884005001e10030702030404031081001c94009410640240001045004000340c2401e403000822244d1980741d00040c01c468a400c2c1020740c0082512508107082c141c0d000d031010891031503540c844d07904a400d04a5110314102031007240454002e400c0031904440041c01004aa81c1c15a800a2644800b0105038052000c0e6400829181090302c22640100d6241e090b0311581c00c12190000c4d050303036070314025508101c2400310028840f0840d029a80315105010402501da25251503d0b900b2010941e01052504200082c0e280e20782d20048102e5007a5074054402c0a03960b0001c049400703112403204410a40c2c0740c07030885000260f5901080b40059640300d0000d8420040408142c05424001c1c40c0082a58160420510201c10b000b05400212584040d1602106650b10b90004886400c140442044440d0000380a441909140b071a0406405641682c135410350408000928000d0055400300c91154405c40e91400d1100e11080101d01c26409 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 936012473 1250 936011223 936011249
    0x80d0c0b0106032a091a0a170f2d010311030613080a0f0e0d0602070201021014010510022103011d0f010509040804030c150807020c09190e012306221104 67
    0x1c040700c07600d9507100ba07c1c3e500002c1c06008042051529010009000b44c4401c945d100c100d40740c0c118001030490001003c00c90070b0403244011154540e44100c82ca000314010392925a00a03010750516060510040250240541c207406130000551000700380d4180807118905101d111141703210550700c29140c642c445602c4240554000100700300f035002094442d100ba03081d6840b028420640c0800c0c7e90140140742014100103005102d00d003401c0b800b030300780100d161044400c052004410441c44840c4015264140740c00000140807020310080071078900e01003a80d081000d807900403450410680c2c10b01a080c07046407103030086000e104940c1d040e40d010310307004400031504a03603c280c441498440101c18030003203520800041e11103400803401c042400405050030780c0781c0c0e03074444100b40c509001e0b85005401964500c03c0a15a0109104090b4185100d001c103000000c2140c003840c001c00c0c401041a0720920328a00c030f20b040c1034090901102c4114500310302060344054111908a00c7c0104c0e00b200d00040b000e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 936013723 1250 936012473 936012509
    0x1f09091505010e0d0b1504091b06111209040b03030c0d02030307081e191518050114010207030f0f1a0a0e0609190c080d0c0b0106032a09 60
    0x215144820454400340c032a218840c00050500c13054041c02d4a016228001c8100003440c4100d42940c401c40c484001000007813015855a17071600d600045d48200b00c0c04450703014050002c15000300d4403500040010700180b060042181e4440114460641ca00d40503507103070f1040c0c128984040055481d011400c605580b03061540210082d601c3d0000c4400c200043c040301d01203a082c555203400303444480000f440044599071003481a0032000c600d0420713041707070a90f1510300c080c440310b50080c2900500f20746601100c0112030700400341e00756041038100c00c0ca0210102441c818a82c0c0001301c280480781c1c00003546048454504110141001d4000083d22110407500482c004928880d0603520805100740100082c3c4005041956030780d0301260340d0410381d400442e008822245c02511584081d1090042c44e0000d5140c800103401c004080c0e00442c0464809801b100c00c100d100e20810307002d8911468108000710b01e40920b040d0101840a04440c44126800260364092054480e00003078a03c800075030b071402034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 936014973 1250 936013723 936013751
    0x20d051510181a03070810030f030810051c05161413020d02040b21042a0302030102070f1a04030c060906150b0c070b090f06030702030c12031608061f0909 68
    0x481190400002a105e5001600701410001f040d82540d4007c461440b440b80560340550b0300c000040d00000da031103800fa10014003903403400c0140940c00342340089555045e1181c0f920742e1500328410041951601d101d1030901180d02000c814020180d41142d00d15500711004607a01d00070301c03801c48642481c6000003004030302002c0c80002005041080d06500d42504140805000008800e40d0000c2c01500810b22a650115100200c0c0030660000100e6420171039a03035000a0880e4000e00d4101d03500310304031240605002e00660440440c8090200c5001540b40c039a600410201c0d000400610207a9210104428052944e214007810544440c044c0b0b070050303c80351400d4094201c2041048940704a0901040501503402900d504120207424a10800c2400f4104621034100520301c404502c0300344070b1074016402c20840703002d0030108004c400c0d83d00d00f001e1405c204503034030041007d000d01c011182885440d46510689040b0034010b0741020a16a1100c00e0480c0c0704c00e4281e20041e8003509150800b10309038 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 936016223 1250 936014973 936014977
    0xc0b10030213090317060f0901030b04211202030c07140c031209011b020409080f071527021f031407020109170c01020913020d051510181a 61
    0xe000b19a0700000d218095420030076035a0b850001000980c1070081c20904076640c401d0f035908000024195110001c0c0500420b003000002d0b44156096102d1005000900510f40b600700d0b62444045402219040c00041c003034075092000440215055001000420b010071140907111641e0344541c0121550602d100f10b99500c40440001900c00d01852901105628442017203403900c44045e1140f086246446801c41c0100c0010441642c00c243c0301c40180d07002a4500d00200083e80040005c0c980301c81913420700c1c0c3d0b00e80b60b603006507a444501c0c00c07021203003400065200e220b10800780710429101c0902440131600f00d003c0b0510b00404007a42e47c070724a42960301a049594402c081641405090742c2d00d880032802d81d46050400780454002540e1524a160020002c1440e02c07505c50001d4940342c404004102480c158892000d103c550201b50009003900d0303401020f40140100c2081c0c7d110b003075921300140e2112481d013420400d018099500c00c2c113810070f000c2d000006054040c0507007850345d010170130342c4803036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 936017473 1250 936016223 936016229
    0xf09080304021206060f060d090c0803030a0b010801060905120106081c020615060a0f090521060f280f2406020d0c030503270d1d03030a0f0c0b10 64
    0x183c2c20790b410251921000007480e5110b0100101b50020201606c0140300701d990150303090401143d254a032000105071090000002044c0703c50080d1740c2ca10f003400c140001c86070450115410090850b00410016501130305007000e0340d004540020078800c041c1903050042c00654841f80d503e00542d400c44d00ca0301122910100c0d50b04940d02071341d01d80c5d42c80d51205030b004049644030b07651040c818800700400f907109580b075100d180e800d410425882601e420028a1408a000c400414a00c07114aa0700d070404003031120581011003075150111030305082251040440848845000000f90b400200c1c01082c0305810940000a071503408114002c140341c5070f08134030315098852012080c407000c00001c0c050701c00112890040f103662342d9504020407c1d40c0071a0b60b980090401410b5800480c0100b84020118500c0700204801d1002810040e504150240503c140104034004091080c004d1601c1620080111411090103140049545440070001e4030300802726000508844454002c01c048070039084425008d0b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 936018723 1250 936017473 936017479
    0x20d03060b130312090905131505090c06130509010314010b090106021207020d080a11011503030525080c06041104020f124804080d050d0f0908030402 66
    0x1654680144012521524550b61500285031600700081001031000340a51343c0c01746800d0081c4c0b640c03040343d10300f034071825901d004031003c01c01e4501e4104840344204020900c2c03d0881407006103030021140783c4540c00b03c020076000340030024000303d00813112038030007014000081074516203503100d0900d801c40d030f8940741901d54113601c1c107100c9041c5442d110200074101c070b80c1ca0b402000c8038030480901da0071076004181e089070407100b400022800541040b0103406046100d91701c0c148040f4002100da42541d0807084c59200020071848140f010030b03482012903036105034020407000c13400300c01240303c0b264071f001c203401074203241000c070300390046005c04140180514000c11301808880303400c00c03c0004038440e0041060140f241000941c2580004184056000c80922242c128102150b200b4804e801c4850200c1005100140403c0c0503981030244031810088500001508017410300e84200d0742d0f5800500001d05001e40840d4445020490341c00501004d02244418040e840045c40c002c0d107160001d45040344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 936019973 1250 936018723 936018731
    0x31906061d04201003020706141509010905010b0706021b070308040f0807053d0c0209010803031608090a0f060b0102010f050903091e03010c0e190e1803070c06020d03 73
    0x40b03000040040da81c40c002d402442841d00c40001d0901760000d51040c40308681030350b03c5584400050b044107500b1440303603403485440110001b800080080200c0d050300644191403074180140145c488503400d41d0b0506070301c0480165107000b01c07880c10802c01180d0180121310311a643c0d02200f000108400340045400000e02d0b110150303290482651151158000c16401c03040d00c2001420540e0415000440190440210318100d07542244003500d40006107150004102c01b844118114103080303103028010240c1c0c0015600b94103102c41800c21601280100b074040005c1179010a21040041c0982218550310181c0141c5d4000e061401a0185c1742c0b0503509801b651034861441c603098140e00555204200342c0000e10310b80f041400c1000a840c001d140b0218480c810300143c0310041d1401d10803080340e29001e8440b41c141c204910100040c900caa07041e403409030540c940d001c00003820058947c68001000081018007803241e04e800c0341c40d5014511000d00282520800080d0300e5801203020780d424010b941d0188 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 936021223 1250 936019973 936020003
    0x828060324020c0d05160f080c07080102190305100f3c05060c012004031103030c0601120330050c090f0409061503121d031906061d04 59
    0x1203016103d0501015000b05a560010601c64402000d50355a07601080c810680b5980700d400c0380302ea00d508126849000003c1d002072200041008000514145000354a0027420800465030342000e01004002e01d61101c0100700022003490000d405000c2c030b100c501c2e040c85d5035032043c0600e2112009094490140004460700f0981180c0e4241a0414022400c814400d1410302030100790750000414840703a540c0c905804980c030030500310601c11400d41401c40303500c55045040042d80f00c04c1000d03840b4400c0c2c0c4100034000b03214034041220b5045031a01d0550f2801800b15080c251081e000213034004c20300c02c00305100d08818009110424005040150042142c0d80c0da02145003524400d24a446502c080d180b1805211840c0c0343d00a124140d108941c08078400c0503042d04500f141466800031100d8225070a511b00c1226400a001028030001c124020924001440865190404882180b00b000c6d8043d0300c0b9814003084e0340140c4001c05141d04600e40d050007003520380403212815142210343c40c581c01424 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 936022473 1250 936021223 936021293
    0x90601030b0f12011e0902040f06031a070c1208180f030d0e0f03040608090c01030216081b030a020c0a290706060e0f0f0f0708280603 59
    0x10192684080e104600b1101d40108005a00c0b008009a0403903640300e25140035282003003149001407502d0901d01003600d81061040105a5401c2c000101d0203920b001c4c3c2c00c00104900b0042d011210420f1882c003e42c98031114002c0302ca90040d9031010b0072440c4490144006c45070311952180c0711340c00e002c00056548028218180d2600403001c0703240c03850761050124030071445003540030505240c0f1407800c890703000503401d84013811038000741d0040c008608940204446513200b8420011864000d290461516500c1d62010b10304246500000c0d098410108640d14040d00c16814444080c80c09011292104c03807451000790f0381d505006210340607027111034000030031191071242201031034441d0441c011880460207104203140c00c50b20f03041d125035845080001e903000350150054014140d03441041c181c0d11748440080c0107080040c0079980c00601130030800c01030039031200c11160001d40c542e51100e0040229501c82d0a007000c3e040c2420026490300200004001c12a0040f20005580c402041000c1d4004c0c010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 936023723 1250 936022473 936022481
    0xc050306100b0d0e010b03190b01080c0a03110324100603090f141212061516020f01050f0c0a0203190b06010503040201030207080a030606020c0303040305030f0f1603030b09060103 79
    0x1d5030440b44010320a250480003141c11915101c01e00c13400003d03580b0302e8500001d2030080741042495600c100c1441e08428021280703040ca024180503001080300e03960341008605203055070f12000c0c14404407044484a20396042c080c0006401080800303161141c0c07030940100d5070310029201c0408131050044c000034400c1c0a4081e010129821200000f44c080c0641c51f29031000159507041007141c0248000482c40000381805410f40c50050b40c08070103d49040800c0c410545243d490319400d4180511944501c0c071f080d003181d00d1070710340d060b95038110f1010344900586480c0504090314898400118580c42c420310000b60b481d10590080f400c90b00744c08000300302c80f21100081c80001d403e07070440c4030020b44103500960003150024410314006103408916242d0070015086920a940043c4d2602010050a6410400b01440c0e160840c080c501d0a45569103060303aa00c10602141d880744404110020320b1091017082c0d95807040042c1c142240035100c1c0c6001001861035100091103040350201180721941300740f01d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 936024973 1250 936023723 936023729
    0x301050a0f06120c1e0e070503040203010b1816020319020a05060601030e0a030302093610060e19030602030c040e011d011403010605150a230f0708070b040c05030610 73
    0x20740501054100380001d001c0b5840300501da06056100345c00010b0420341d03080064820800b13a56100d8490520348101400d445040f503031584261442c40d0b0f1071120607000c1600a42181d8000515001100103040c143e003507018201b00340c0c19044c0021255000d094011800c4020a03114000755205555000019400c680104402d140e00f40d00207149500028000e03402401030040c000d0000c00b0240c1c1d0300901142e21b0441c0c0d8054112840e07100a445160b1a49009494101003482c901002d03060030301800502003006c10405510410003509001c140d14a180a00b034041c0d90000000d658a181c100b15100540e8420300c03d2844004042000042c158040414045410096001c001d09039103450000207c2c481c03040041c59055680307181c0045d03260359060407984030a4055003c0c1d0788400f41c29501801081a51160310301c00d40c1c000268550340101c00c030464020884072525540ca41c8541d05101b01e59002d550f000414030003582042c04288018081d820341111011000c80d415603403440581e000100d6144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 936026223 1250 936024973 936024983
    0xa140a1b080a0b0705070c150828150506030103050c01110c010e0405271b040b0f061e0f0d0b0f010221070c0314011b08130309050301050a0f0612 64
    0x20300c10900050b03d403d4442d400c080d140c41d046040c41655100c0080b0b00c10154441107010566107001200c1580069103507500c40406d0518030102c208041440c1c00304e40c500b00c503007261695142c001e03122002025451201902014040707a841e5a12840d010395114603030151140881d40122021000c0c81d40042c1206200c1e0040e5150f00500b01010144070140c03402902d0100302040944210000b443c071071414248200f070003c0108440e0070180e02408000704901505801603003005044c0840d5100d507001c40910140a942c0d6687d903142e41c18203200c003580304e021804040503002039500d800400582c0600b8042119020030083c0c4084130302003101c0750400c0c04c58680960421040c044031030808500e80d41c40480080301032071502c6a20b90710011800301c640c00850364040180407015440f4070900c034a00800084407051305c50004c0c06180640000d40040600b4043c07040042c10f8010180f02d030500100425010740203102d103042891001c00904040d80d082d107002480c10324005440d10f002145001c2141d045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 936027473 1250 936026223 936026233
    0xf030c06080a0b100903031d030a0f080702060309010e0c04090b060f031204120605060406081b01030204090606020f0105070503161d0603101e030809040e0a140a1b08 73
    0x11440c162404440100300c0c80c02c5a583d08042d52480d1581c440e8901240702c0c96864804e294250300c1d002d012000c0d03000504180583c0c0440d00d00741034500141250940f900720b9108019503040346040d11041c4240c0400079041003020040c0100c80320150003500056000200361800515040207200032500000310203040b610142011480c181017140300038a840314042c06955600000350400520380d80540e0280b0700c0e000c1e03904011010300080344a0290480703c207d40501000d0f00d080f84103a620682c03040703050199561002e1b601c445a000e03904480040c402e0b90024010a55034030000ba446400d40465000c3e50b508081c00147c1151003401120700c2200d82500c0f0100036284000d040b61200c0b441000008201004804603440303542c2c09014512440c11303c1180203415080c40464003001201a0031b14817009042c40d030500c001204401580c880d600300b5100050404841120b4038942805034902400c00d100c1c40c00503003402000030801c0001180108004a0b19110040d41c007030510700d6511500c4915001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 936028723 1250 936027473 936027479
    0x120a09020907110c09090c0a1a070209130210030615231605010e070609121a060301140c1308150103260307021f02070309050f12011d070f030c 63
    0x140e1034041e088110b43c0f00b1100640c40400c0464550b00c420390b2101c125600806041005241250041001d40380a0032103001e500324045c102003040c007074008000d01c16402100014607080c0780321810040c25400034850300c000652000c001e8010306003806030300710900086102106580c003564054100003c229000e0700008480d40081c10603403c200c1d0207541c860060305034403000c02c82c2400b40308520b25124015081c16842c1a0004e010401030b0342c01110202c509051002c08180c541c85500030400892000200660320034000a00400c3d0403031205100b038103820188642c0380120005040e00d50300b420070351004c254441c40712980e200d104403492500200c0d00c40c01070001a0640689040c962800c0300380015924515500a507a0380003181d001006a01c0f08000800b0b0b007980021398015001454000c500e40301d10350b06d001380501c10a0242900903030401c007054019403a002800450240d03484004c10010000b0000100c6107003a103103100d0b903c0c1c410001c0120f031100351902800d044903801001028584c0c0f03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 936029973 1250 936028723 936028727
    0xc070210030f022215020d022509140a050c04030f08390d0f0c0204151a030115090e041b0b070f061401121e17120a09020907 55
    0x10982d84081ea040380c01340289051495084080702e060b1032140301000307003942000700803000d09000c96003040031584141c04003401030360045204401c0605401036216001540c20f0345108503251a484100850b1420995590841401d0719035401035852910900c0b00342c40c0c20746c600100d03006a00010b081402ca01d0040c00c000790240c03004000307e0b200d07024800d801c241c40203a5030210920308100e2504d4140d0075070344403130418402d00c032a0740090101d041c40400b004007008020714a4001040c028040d540d52828490f00e003940c500e140c0001c2020344101140100b0901c800ca80e1500300f881180072124525032042805401042000251006c0212044031035441d6100d071110000d00c0413008018400d4640040f42c400a441c0050503070b0b40c050b189103000c0526624003036040754800c0385003109402091005101e0184074089408465400004003014110001004000e503a8101c0008003001c900c01114220481e4071300c090001d40700e8001c1011103d588221411058a414400003544540b907480003900640c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 936031223 1250 936029973 936029981
    0xf0603031c150b070b01080c190312030608033708190b1c110114090111011103070e090114011707110d0806030118050601031e0c090507080c07021003 66
    0x101e000071454840e1940e80f148010160700c070b05010703903046228400501030540100003510340c424041d45c45185017400f49114940d45c40c40f40c040207007030725a050811080903100760088001751000c0c0080d01c1d5500c001c41c0402900c03050041035503c0452040e90b0100e51f83c900307039102d4060ba51490b10740841d1980c0b11080c03645500c02109030718850690381c0d8529880ea0301c44000038039103039510100804d003044103418400303404600c0328592410810480140c035100c01e029000d03915070325000c2c00d01c0c046090503002d00300d000d00234145000e01d002c00003200700b001c003e520207000d0303a01c01000d0740e8614807071342c82d09020b02039000030005940c04901400d806000c0c00d084580740300c2d80440581b40500610b00c46102c01030400710801c65180000300d83e43d041c80024502071081c002d041560107504003c42840b41e480980300c0c01c05101c0a000da04018949080c80c000612658403e5540000151009515280d90f0001094180c0e041e0000940500001d00c04002d1007089a205540040501d001c44610a204030050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 936032473 1250 936031223 936031241
    0x30d080f0c090a0e0405030904050a0b0d0305030a14361b010507051920090606160206190e01030203040f02090a02040b040b0d0f020307090909020105120f0f0603031c 73
    0x10100307a20b00080c41104140641c5d0050b4440ca02039035942d00090100015950060400c003555450710b003c0e060075644464200c1c078a03d5050a110f0f03101d5883d041080001d00c000481101c010480b0800c10030001e20040205160660f8030440200c0b4045220030b60118054504802d06507901108000c03091407802403519216010505d4003514004103540d40720b0a141d075000fa9010040d03504c0815a00300701e100360152043e0200c2c2d85000c1c0e250700c2d00d0400030b03c007c0009840340303010348000a180c2061180301000d4002440c0c000e4070440e0f48040c00d04a0149040251107484001554807070038003011361080c000c0342e010380e4001041420242c0c0580030807000c0030b809009075090303e508120000310000010060801880518001600c44100e2a5100103079511b2210391844c284c410020000202d8201419205640b5500c000156140300c7e0f1006a40501c10750b190b2405240203c401c201c3c22440f00c045c024412100b44908214946460041c10b65900465071a0045001e02c480045a861010341c881c40315 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 936033723 1250 936032473 936032479
    0x1020d051e0a030c030f050c0a050c030d090b0a050f010e0c132c090105010501080417120a020705190c0611160b090a0e0c0702040c0509030601060e030d080f0c09 71
    0x10010a034105140e42d100b8000440803d443d000150582501441045440c1404485c140114038050a409656100e10f02c5c2040901001140c1400e52600400a8545141141c0f10401640301a402c00c60b11701201141d00c0741d113981c20540000c00081080c901103040b035025002c1d04441c0d132120754104103107070004010a440c0707070040c1100003032001c0c80c3c3c20b0440300d01c590f402507421601001034086190803401000280c00ba07060500401c016640484c0b8690b000b5081a1419544c0d00e01c0c0d08954002c0c03103045030742d0100300510700c01e11550b07090507401489e00c0b84c4224119124116270704d41e45031100000b29800780440c0c000d14410030a442c040c0c4515000c043c00078003a00c0c51288034050300d0440031203940007038a40c0340000c500c0c802c09082002c0c80201510084032800b4480c45c2c0006600c400b44600100203000b540c503190301003d07481c015000e841d1506c00050aa0300e440d80c4a40b0002c3c403140d50000d6540c4079102ea17403003c0c0c3c803840c007540c4518014004800030ba006661f40040310002c1d50b00c00d0080a0b0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 936034973 1250 936033723 936033757
    0x6010501030207021f050c0d091514070f06021b21090f0901090207060b032a15030406050417130e0c0c1c020717100c0318030207090c020c01020d05 65
    0x400c0300c00e40866840d00043d0748800d1f0700c90f100541c0300c61825a52910b00c40c140000d00707009101c902803005003102c0d8192a0315019010070084a8802e005025010703000700310b403403044084010400c0e190060074203031819602c805110003403a40b00e43d98640351a1325500c45564401c0f01c910301c42480342c0082c000944083c0c000803c40b00e00c00041080c135003023684007403151640030500c08100042030058101c0380f041140201450380960300b05545170703c0d003034190b0403540780340000b07e003880d4558408009104a04038030b16502c9103450305101c03014010440701115080304c604240502142c203c010341d1414528080d2605460b41005d02084007008003a04488c07140c0d82c240038583d69800c00700b10244020040d51143c6586103d02d080c042d14184003500604030f404206c0418641011000030320581940a550010a01040e480401c2d0014640d014540038181c1040300c420080c1900002c1580860310641c000304031200e20724030b049854000e0501324a005030000c03240d00d040588200040c101d154040381202e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 936036223 1250 936034973 936034999
    0xd091d09030f042706031a0910050a0b090703061d0406060b07030c050705030303190513021504030203071e05090711070e04021206281d060105150c0601050103020702 73
    0x95081d000799020701d03554040c0b1659010a04e08000714055190700500701844414116612150f012a603d0a11469440000b000407481c503000c0045082c25040f950701044107040942c2c0b6407001e00306810f00c03640503240710f00c045612503103c0e01c160000c039210861000e02c1084020b480b00b07002030000c0c10030345a190f100c4202244460381c4100625040d0302c42d450310284950140b40c21070512500d0f41c03095100e81c01c207000b00b100c00580c20141401554070020002903503038402d01080890301102002a400204507128015858032200c001c10907680218100c419281c1e448039000405d13120b204824030440c01e4840e0401c545d04082214079004411810640702542210680c5071a11410742d1182d9036a14444003404254100b030b120000540415102910b8130b440e0400301d0010320340c2041c07400c0d040d2414404a02c0c0540c0d440d42d100c440003280307148099025081e07200516540303d80a0040c0d0707202d884c10030b803e500e803d0308690403100a081d217030001e85a1a0b01c0c2c070f0010340094210b40b50507600841808994 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 936037473 1250 936036223 936036247
    0x916210f05100f0b0309120901110d03020c0c0d120305040c1d0a0b300f01150e1f03060209040204181b23090a08060f01030201020d091d0903 62
    0x2062184203007914022445107801c0003c040514030b0307070088542000400500490800205a21008410172180160703110302e44801258003210b6000c98035494014180040e10003a4142c00a00c6140855821207882c030a02e0750070081c0e410a0410020800c541e00d003486000700740039400c020740c000d02400c2c041500941d5000780610007000c241c42066089010420803d180f05944180c1e00c034a80305990f4045212000303da000000da07060398105281000405225021800400040200540d40c10091000350b1800040341c8400307420b40101c050700c1000c100007800803442c007100741001c1c02949800220440c5140c80e07010080d448000120780046e02000f0118030350110815024040e1055900060a0511401c3d50640d040d05554010100300d42d800707582000c8000590480c40052a0b216043c1d0781d50f8642001400754000d40c0d11102080c0240c01c20088070481407a201d034101c900030303000d603000c151041e1001c03201804240a11002d11010f8601d0740b448280b17a032601607100c440442100d240040d04140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 936038723 1250 936037473 936037481
    0x5030f041806060504031e060204080f0109140c1318080c0d080a050603030406031a0306090a050c010807050406030218310b030a140106031a01050916210f 68
    0xc1c1c585a2102201024450824480c0300c006100341e2074018249811595220b8102d5030b502d441c0c029412211210101b4041144d0440b0001d00c1844100d4942c5000c0c010302c0e41c080c08042c030303040e105d0002c24500410141400326034108441001042c082102c030007583c000c0010a00680348405541e042c04401e0001030303c0400500720b00603290300402c1c1d0490315900082c0b00c4000106940070b45410b14091000030380780042660305a0340103003000308045008450034101000d000c65901e90501c21b13407052001055000c903200304003e02074410345d509040d41c0da005482100303040c0e442000180040004110880c482d03809042200740304803005208005040000300345420a42000d01c520b00000012000d20400c0c01b10b49608400030344003444401407100c0000e45900d442003014210520200864500580a50001c000b8503032000c400015140c40007107441250509020b01c0380500700c0300001c905405020102200b001ca25035076102e9996075010a078511200e05070354a000314036141d0020140d41149030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 936039973 1250 936038723 936038729
    0x1120503251a151504060509060706150f060e03070e0c0d0c050405120a020607260a020303040b15090c2b09020406120507120c0902030f0f0915060d05030f04 69
    0x704407002e0309200090840740c1c24a00a0580304244903603460181c85015800d079411901c250401d213860b01180c00100e6035030701c11220010000d620b083d11107140d8200c01c12600066500c803c0d00c0c03010701030b1214000d60340c002e80398040c035038181d20910b010046401070701f405686c84626000701720700701901c10b000481550728400f4108081000481c080c00203081c2006400c500184140083c03402e01a180c010a41038880d50002405002030700d0441d1005011450400f40302c2c58400c4011a42c48201420007502da41056404032069021100410680028108034480d642c82c02082a030494403489544105a48039440c05403c2c03d00881c28800641c0004c02c140b0f10b10103400101103410030982c4104401c0f40c0d000d030032000710300c481041c031400807840004071501901c100701c20030004000319003400043d000b041d51000c1c504500010811a038054030321107503400350390818442062a00d480059544995103200080070344480e92000131003074507042c0280c848a5014034266480d0110540c503000d85540150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 936041223 1250 936039973 936040013
    0x417220e0c040617060a0b0a030b180115200a0c0302090c070b07110705040c021501170c0904021206010f08100203160e0a0f14090112050325 62
    0x100400c15140c000c4515a404003600304240e00e45410808080c10030a20a40500640da034140e001407101e0301c039002544050a0f0121340991500300c0c1c41d0004001e08540c03515580100e00646a0190000804100c2d40c160f409030031040e07014150a02044601c0d42c540d006110040400d03000042c03c10f8800d100d6162030500601484003802c0c114018404514005001c80e80c03848410402d20300801c81c00144250070613424a011120200802c071814640300f49904000da02c545043e02441e900c2d500010030341c10700355240c80b84e6407081c0e903200b01040b1400001220002039402c90901c8404525100702c2c1103902c544001c1074085907580800050b860001d09801503002d00c0002001800701280030801c010b0301800c3c48006620f50320f402d2070040075004442c030b00c10007402030041d510966651802e407058050308030366440014aa984a880d03040c030051080c04240281001000403c016001140415070250000011458050b540821894200700700580060744d82541c0380940018140c003440300c020404507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 936042473 1250 936041223 936041287
    0x92109060a14041e0503060702032704062402012d021201080a032c0f01020319020c0a0503030408060c250516060318081b0a1b06080c030417 62
    0x4c142400c41000042e00154440d900000410020513400030844441d561800403c64285001b509441c0b4402004010264800d05103030002c50305400681d070082c01980d1085800c464040180e0041e800c941071010088900c02288083ca20060055166500340d41c000e80310040c036080220f00c441c22180e10a0f00f003c0401c2d041403889906160740440d140c00071a00600b803661200c508402030140070b6201d100094014007044864481d643e0080c02a01d13008000e481d01d10444050042d0000d41340c6001b5212a40304805100c0b0200c0c0c41e042c0081541d0940c1d841c0c00c01803100c1c2d01e6848914070180c0103030b5400c0120b00c40c42440001c081d100c182c503142c07005114600505951101115880c21400983c01610030107281c910301d40c1420411b0003a03201390640042c18259601440c3e0444298444038003a03020044c8078840648003001040e01c07402400c2c860200e00200c102e501c07800c00b16660301c0181c0d00050a08010b2000c80d000c41c1c0c20b210015071207000e41e0784035071400c0509144c0b0111845c03d6000f1000100072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 936043723 1250 936042473 936042509
    0xa0204060306020726091c0803040c0f080a150f020c1002070c12030c02010c03050c1b130b03060103110414071701060e0303070803060f0d0803092109060a1404 70
    0x1910341e03c1d0200017224000b50007643d44070030002c00180168440241700f00d4104d29039084d29060341c3c404003a0103422100c615a240b806003015a20364519225105003644040c000180c08032022503d52412540030750031240c2114070035070342d0014050110b1601a034a508200101e4155010040c00100d42d03115400981c854005003446040e07402550301008139500750322034110010350300c900744003103240d42420003980c0000e40d800e08403607038091a82240384e548142041181100e03101603841c2c0c491502210131182000a1140340010f032030241c032502e41c040c1d2002c0011b0000480000711408085c40141c00040c0510400d90030f00d03c3c80320152400c4001c0313107107500707030060110044030190b015040e00d04009190300c034103401081e90791088010282000780080081140780c0d0b2100c4003116100300c02048907070f119156042c02245640142e540751010f1068100a0248600816154052580c10b040180c2401811030034802c4a070310034004001040a01d003460750664010002420180581855610070414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 936044973 1250 936043723 936043733
    0xa05040f290a0915150f0e010c080f1305090717161407060e0709050108011d0718090209161704020a03121808070f050102150a0b030f0a060b1e100806030a02040603060207 75
    0xc0302c104e0141c10001c0c03400c0e00d10701083d05902140e12f10821107550742d41d01d079889505038011105503004554015130ba1014002d065034400c41280071000040606100c1d9128200e12001c00c041031800c42300404e420112100040790408007401c40c2600032400411148000e015090620000341c010310000c075034800050001540911503001307a11044803010400041c0700c00351550300c0310a48502c041200c1c0b5075008040048464101c00c041d90360140c188205800c2c00d0181400e80b400301e00806000905405010340c1c03003000d00d1104ca000f00d4028003601c94080c1191030381003500c4902c28000e021720000c04d16154a024501c030031000282015405004510b041002001c1840300e02e601007030465000220f00b026031505000350039005500e0340c80004a0b4007418010030b08000350012510213030b000380c408071410f00115411110b80707650304072480500d800e40d00c0c0c0741c40c09030b0140f03d03001d0780c01c0aa0802041d8195000d000d0f09a0003400040444814691513030000e426110241c0040318481c0d004201c82c01040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 936046223 1250 936044973 936044987
    0xa08030c0f040f18020309150703020403020607050307140604150f02091903060f0c1d0103060e0c0c0607090e060d0606170a0c0501090b07110a05040f290a0915150f 72
    0x90712101c2540b441c204400919500e013180d803c023040500310003000c00c00d06402a812200110b5019104548501c0e584c1001074881d0403202060780c80000440e031816243e100440c201c2d101d00d07407211960076601c52143c0014020813021009003d801e13420014002c080d070351407030740804551203038400b41c000504620788003098400e00032042175003e0a000714040b019401c424071132052005400c0c500000c050090048016040340e41c09050300401c4001403003800c1c9407a900a0001c0e0354003108840c001d0301c03055070454842506114100d9200651342c0420790910f41b0001484010b4011040030a0240d2910040d0031902d0041515000320340c40300052108100000031404000c1c8824204030b86168686251801d4070321880400a010344449032443e03c4030340c4e4181c1942e010348001742040104040881c651001003a914a130b041c1241700f07643d4804e2044030101010918040040c0090012504d400691006040401c2122400c002c048001040100c05910313100c80c82c8905e9070f603104948100b41800340c001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 936047473 1250 936046223 936046259
    0x181a090f0108010f14130c050304210e01051b03040b090f0904020a0e1902030a0f0b0409110d05010603020d060c1107030b070806190308030a110c0a08030c0f040f 71
    0x2c4101100100f1000240580104c111840412090400d084003400560b03c11103030790b5106080c6140a0160010326840703800f0310320442c8100c0840c564000d215440d0001c0800480d00c020010b814822482c815521030340c00380c050b007043c240942040a60011003942145c0148e0024160300c0408074141c507291406910b180010403054490580d50305040d00400c80c41045070091351404400c6170040b6032480440020b03c2c18044d07040004540381d0909000d100068050b070040e00c0301060908905121915007441019141640482c200c3c02144030f241c18000380e510241c0d01500d055607200d03000005078a400098941301e83c8079800004440700c11020141030a285400100c1c221b5200745070078000a5100b100a541103045820803051a03034038a80003401401c0344208204012a250b4000010051b0100181d406008181d2061100c9660900c800905000d04948402c1c41d6124020f00404115054001c50f08114555221890402012401c045561166201c8508031045500400c099040c0c518003401c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 936048723 1250 936047473 936047477
    0x12110a090f080d03020a0525030305090f0a02040c03020d050f010e0903031501030f0b130501060207120201170720030702010e04020306060702100504080d08010e100b0703181a090f01 80
    0x39003400d040c040b0355a650342d01031000c10f00d5800200d1500a9001d482038070500f1480c8036002003664030f0149031421080184400310042414880407400140d4081071000407289038a0041c903182801d0307001c00000d400a404210281a0300b0030003260102802e008140c880c0e0300c0110624030035407410700c403400c4100b802060f03142d59070403d01c00d000340c05800726815452010700740780c042580706401103034070014221a20816800000c0c0501d052240495401c424101c1d421134003500c000a40d90400d60070300d245c030b00c0c2d8001d0000e03403208031081d2200c1110a410390001c6443c6402e80796180010308418011005050440203035001207426000c40d039120010040c0c80105171303029815410101c01041d428000c2000c028412401d62125401c0d2a01c560302f078038000c00100040b21070303a504008010f00321013028003078400d1a200300d20010318503051207002c000403030741001c680b54680980744d00c04480c6090034074080100c0c124003440010b840c0b40b80d40181c0710041510381c41c02e6561001c200410a0403002c405000381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 936049973 1250 936048723 936048749
    0x3121523010503061c06140414010e011517100513061b05090d030c1707060b0f03120a050415050d0b011701120305120403030518010504080a030c12110a09 68
    0x103601e8080c440448202000303200017420300e0074a0410080d00c01c003101507100010100400c41400354207a001c41703941000c05e00802400800107811801d854085000208a503000201040031f10304603c18084d5a0302610152016400d03030864280c10380d403095510525080105e09142c00780007103441000a040802c0015082c0302d01440405010780c06400032603403080b010001c00d0010b140c09030300c21111065004160201900054000380c180e60020081038401c0d07807801801c105075051100c9804828074001f402000e910b29000418904d80d40079100c03181c1004828000000c2c81d030350546220945030a20b8441c0ba8a030400311800d0012103c0586040c5e0421448a0912150041569906064400d2014890706e9a00f06003402c0e202c922840100c0d0122125020810080c1585680014000c18008584200e89615018803909844040c0c038040c08924007082031203000c40c000c0c1d00c410400111820240c4900e1440481d00b021606418007060440d403002039140c4610f0361010030113001e880d900074590 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 936051223 1250 936049973 936049981
    0x4021e1b0708210702090f1f1a03130b2401030c1202030a1d0105070807110d180510020615010302360307060f08130f03121523010503 59
    0xe9035a41041c14442c00f40c0c4031500c400d5000345a07681100c280e50380107031005c1c20342e040c116044040038004841d0004030305041080c0e03200900c080c001c000c08689a400600760101c05288992038181d2002e890341c03600050741c6402d4000190821505803250341c5002c1e50400d030080065405005201b58141c2d03504040c5004050210703680c02c241030a600340080c079070050f1290748541c1d8140007000c0000c16040c070840c2e48032036a8600141500524801c08590340c6040c540d8480716000d032041d000044600c409900114401c0d00c5503841403426401d16103942c0704018405643d48080740c0c80141841d14040142c01480400103a0002c03e24407404494007071030118a420031b14184004a4105811303c40082101043c0d85030302505590114114000e0060a40c9c84043e60340502070520002c210700c04000c03030107038800107801c501d40c51130078201c80d50811800c2d4007840b090360f001c07180e2103c80302c42c80740000d6485900c40e4040c03e540700c401d8081d08440320054801040c5da003104440200502e0043c0c10010100104 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 936052473 1250 936051223 936051239
    0x16030206270a03080a0b04060f09060b16060e031611010f02120d0b0307030c0608041203020f0901080714040f030506060603040c0e090c030111072906010e04021e1b07 73
    0x3030003500352030562485c0e140c20022a02400301e21030b41c59845400d001000c69000601d0719650102c805005041240f20f980d815941010300500001030a045403404040022a80c1a040a003001400310f080e40d24243d030742c0c40c0d403007500d890a840a42c3c04540c2c1e110384072503958000754140304442d114001003803603c482e0300840785031b071140c007030442c0300300d621001d56040c9a1420400907001d19444180103880c0d603241c403001442d40c0004c071410350300d600741000c01c00b0489020b0f1086600e412000d54400b4504002c82005650b100c1c8040c10400c104020614007140780c0711700c14081c00142c102c0c0c40c0d941080c2850341c00e0035480e000000e44894800d000c104240000212181c1c200021100b510f24060308030f59903100303010304029130704907100e0301542402e42203400000d0800041c140184200c032410807031100c0c1160803890038501d1282840c01c500c0c000200d10950301403401c907034117148020009442c1c0b428408400044207110f414035040210041200d011801c040c0752038241c030fa1405001028070324a03003049 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 936053723 1250 936052473 936052483
    0x70605091e1f020a020d140601120f0206160c080c0f1912030c12090501030e01140f0a0e010218100203130311012f0f0706051e1603020627 61
    0x10060800302c607410b6845400e0007440342c4101c40d07400070808220b0000509003a541c502140080c0e0b0050700952001103158800d01c516010126004280321050302d00e00d6003444030590204407680a10000300c15403000069904100201404c0c2d00c001a14100101c4014090b0100d4009106403140640210440030240c0460010702251800f107030b01005001035060980300410240405001c2c000d80c2c4141404503a00300351090211341c1c0a0340e080000c02684044a8225031100d81c1444c0040c0009001c582e6020400703807020b0700304203a08800a4100e042a1206089038008248034099410a94a1402c1890051401200c1002600243d464554182148045c1200e0390200902d83c000d4a214030b4490b1b44200300304100c40c0c90040041c0c00d1004407100c00a005480902204128461181c4501112801041038000c90b03c00c0e80340d003414410881d200d06503c07801c940b80c00302c211600307001c0e52094024500105ca01540603401624040c181109440340a0b14602840e404a1740c040030951208400021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 936054973 1250 936053723 936053749
    0x31d06030c090423070216080303150109170114060a03051504050c090702010516020d12020d0e030304380609040203010f0507020312010f060806060c030408070605091e 74
    0x41c101d0303a10041003000800400380c070882c80590109804002d50089102c2c14030b58080c0c0780c19004c440c00b5512039103824220740250300500c1221b030400e02c00718140301514856440400b074141408080795807a00300300c0c0d4100e02b0300040d2405603911101010075541e0f01c800302940081c8103940701c031461404c646906a880c9840c600d4003185010040024003480f000740b01d20400301d40c0c020503a40305402e159000a000c2c010035504c04880300f6048510304503c90002800c4805c00752103807142024400c0181c1c03841c000f134111030003a40340c403502c8410300580100203100440c4514821202d000c031410f000c800208040b10039003145d4803940929a01017801101100781c49502480464003003c907680d5074404a0b02620508a40c02c91290a22081c020455004400b8108909444100c3c491980e0f0718401040344080c0c0d44240000b0070300c0ca00100d901414510010448000a401220720b4190b03184405480c05d0401e900110002d0000f0a4448661600f85021131006901c28584d1400480200000701e03e241c2102c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 936056223 1250 936054973 936054991
    0xf0d180506070b0907120f1218050d020d060f0c02060c090a0e130f210c0209042613060f0f0f0e040e010501180b010903051002070825031d0603 63
    0x100080d02d1141c041040348090b001400116101080d54507001c800b07c0e0040c40101c4041040401d001e1641d442a09103101300f0f0903080241032201d00c0c280901816195900040c0d82090341d00d100303040440d074503020780c2c0855006d45000203108540101c00a0500348003406407840711800700007101c1d01d42d840d10740744019943c180c2400107441d280d0a0710b048100500040017403c807951101380100780103940c40088503601c42c440c1e1005c070390b03501194100c420001210300258060124800704000c26070000301c0038803c1c8258100780c0302411009681c81401e401144020310380028908052108982c092600c0f810844c85051185180c1c81020020781705403100c808080400c148046010140e031351300d400003266141d05d00020000703540c403502d4243c00310f20410300500c0c9003801c00c0b2020030300354858103005c0200d070f400c403000e02040d20001c0d00c204060740c0410815501c11006002c544050503401e69040702c00018907109045e05083c620b4040c010b0b1703c8406807180075032240f943e8815581c80d4001102d5110b1008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 936057473 1250 936056223 936056243
    0x2108130b070302071a1009021314010216030b0907090608060a0902011b03050d11030106090e040302030d0c080a1109030d0e3f0a0807021e030f0d18050607 68
    0x241c404800038082c0794006001310404840d5000c00501000240c0d010750701c082e1089501075180c446031001e80c807845040440100c6403000c10003031100e010751841034103401441a1500700c40750120040340c440039500242d510800074018880d140404011900003000c51500500035a850140301075150400104030f90080e58a81e003070001168894000710007a800c2015404c264500380f800c00514640101410b40348851905554505004220b02580d04a6200e6070301c81d04040e042014000e2141c60140040707040d44002d00c040712454005010306540084030365203460042c944880f00c04251043c9604280452700c04101c1c4181d60f032004100695200c0c01400c1c4078030b0b98400040801c00458021a070000c40ea10000801004803007034060039501c09a100c0d407034a14081d1801c048a4890003441d80c0200340c12820840c03100107061035aa4151202802d40c8581c0c03800f00904007007030810050000758120b41d0804074100315029082501d2403040c942204503400381c1c2d810000401d0042c0324040e0041d003c0e65103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 936058723 1250 936057473 936057481
    0xe010819020f130515012a1b0b0403030e0405070c0309061b1401050103141f050c390a02030309090c1903150503160b1303050303042108130b 62
    0x1c840118196034180b000800032407078484100c5000ea42c3c0003170201d0014016540013900c5903440d0031078844a0140c041901040300d0b41e551803440d903992842d03469000c4a544200061100305080141c402140240c80d030004020001c1c00700021107000602e10030500500c0460407010980c00400c800070707103c1034241032460f03d2070212800305c400340007500108800300ca80e06aa66080f0103410003812284036440ea41e602c41050350388180c85110001700807921100c44410300c18080e10307940083d60424011040c01d031410041500d650003003d6990198000c00034a00707004c80d0b850700381a0491821195903400f804200750a42d00081d200c0c810031300384a10407003410010514040c8964111020744214110b81c02000b12140d0014018001c0d00a5843c1e104070081400912070130041000d804042c6101080d407420f0313061505038081a004400e9158034503c1d41c007000700000f402000207502550190500f1a0310900b0511104602c03c000e2001e0030804c061801401040a0128001c9020702e1748910000780c1e0350340d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 936059973 1250 936058723 936058729
    0xe0105041b052b0c020f0607080f04020406050306070c02211203090f06100f0b0a0804060c0e03030a08060405060f01120c033306050408120d021e03010e010819020f 72
    0xa0840f40e46150a610407803503d9a9060340e00000040407550255406103c4c0502001d8662a0440301300010031110800030f104142a94807481e8094401000060380135111000b181c80c00c04201c0e01040440c4250b00302200b945802c00c451680b603148103400e00550310036205000c0c0c07100f404030345e403400c90000400410501c4a0501c21800000542c030220f1f0514604041107003860750f081d2040401310b909200001c02e0034a00241150036800d100c0d01c40094580703559540c1802040e6254141007000300610356010690703018401070011002c1e903503450756140bc20104000880c5c0010b824188945041206861240d8000315001e501c105000700004601d202c1c0d94003078002c0c1a00a880c1d40700202d0024624842107a50180940c05505071510421a117031601070965081c400c0b80201d03107095000c100760303491010544000703000c81108042c0250802500200030021f10728040c03e20303410701001100500440d49650f2030580102410780c0105012075025043c085d4032020500b0203400358084000b01440e0762 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 936061223 1250 936059973 936060007
    0x18031e0708070b1504140402061b031b010e01180f170304080309060901090503030604200310080d050a05042c0906070215091507090b130e0105041b05 66
    0x981041c5610703960300c01890400b020701000c44440c03c070035104040d0540c41d414244628980703001c51404500c20f039251602044190b4108040201d40d0001c0c16a540c108005c040c0040d0400c070b0032000c0c199864082040045007500c03035800407c4102d0b171500300085c0000904a903183c0c8000d1f080410440510342d1820700500340103140740146030200c0b0000501c0208443d580080d40300310441c006544154640c40d00d440c0c01d864220802070201d034000c1c000f04084c0e1030964444540c03490246c0086000c41c0c52401c0302c00081d00308640c0070310081000e02c000c004443c1c0070f01c40300008105a00c0c00038134140700194050041e002e00e00402c0d0021010440e480c4007055101c2480d0040e03076030901d401004e03213440381d207181d5180403c45450006014106112803c180e07030000c06401007402901418181c061540c9903241c03400d0091040c030400c402120000b07549104800280241d05207580b034100402e041601c180000f6806a001c280220702d0304c03820119407002002c0b00003001c0390901c0d050b941d9140d41d03012b0780111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 936062473 1250 936061223 936061237
    0x1050c030408011109040515010906080a021209100e0303070c030e060f071b0f26070513090515131103010605130207060c0e010f0305060a030b070e030618031e 70
    0x381d072808014600071000d1340040c14045004450601990b52005da02d044002c2c041c4840c1404a09402c40078031016001d01d9910394003140300c950041c2411b00665000c0c0510405850a00e2036400419180c040304e80d060150b90081003410000f0361440c14020402414142e0754032020302001145000e10b4030581c0c0750301c2252a452104603034982c9551460504002c040c04050b2680c101103200c880024020300e24050150860b0012007000a6140c01c0602031403e150118602030100c0c011440089101c0d56008440000060719220000305034140d4900640382440c2c01b11014082e0070b0384400c00008eaa8075031641d020050b03005465000144200b00400e000d02455000181c2c809a2403000104a42c21540640f004c07900403401808517011082c0c003a41c00303107500703044140018010b040d0041514041e40001350401d01c048c0002c0d03000c80d500e032108401c00505903071a10000c2d80c54200765019183c2041120341148801c0040303544641d2500701c41d6581e22901c0707414a9241510034192516071118803d03038201e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 936063723 1250 936062473 936062489
    0x5010c0c021c0c231e030a02120c090108030d0b030703080d090311030c010c120203010302091f1208041e0e1603090507090c021e0604020609030a2f01180501050c0304 73
    0x5103100b201085410210010301c5c003c0f190034000c0006100664038403080354070098007408850030240c0a0016000d040b040da07014502c90680c0780103071a203034480b409000b010702002a645620024013480103484a504090b4880e50099500f800401c0c03c40f01113550541458033f0000b508842880c0c16146030006407000c0b41240404942c0803070780c400c19000511080c1c0556a030307001c2022604034003000c0340801e00000c1d4124500ca800540501e481c241b072286241c030380d041c20380f121541e03500c0c00801d40c1c1c20f0700c07a0895030318a0101d4100104044c0d88000800b2490a2100d84445401c0c08486544030314010b001e58400c444200c01b0f4060b140c0a58454181c060300001035030b0800352222561030142548a48402c014868621031101a400d542e20507102000c0c5640981156180e0790200700154000c100fa56606009810401c80051200c020386a89030010411401000b07407184a81d200e13a00511a9503418811034001c58699010f020300c19509844090804a4442c039803698200c0c6180030300d40020791 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 936064973 1250 936063723 936063749
    0x21f0b150307170c03060109080120090d08040311090f0402031213051504080f0d05040e0403090e0a0c0f02010e0a0f031b110415030803060922030c05010c0c021c0c 72
    0x24071382e01140110f106003030a880e01044a50303226a2242201c00d43c10969945801148152104802250040590360301c02071180d500c41d440e945031502298881c0c4c0c400c03110001d9009558095040070000c490307004242041090861806c0d402281d00c2e0101054a03002d240400280d110b001c000701e956010240c80c02030722202094010a013011596845030107004254844c981c00318291070320010340c170401501c0d40c0d9255030506180582142c03a0030030240044042c041428004644100d141c0045c512803050340b580854008186003000d0701d0300440140c05011641814820039605d240003400440c00c59214945010204580c10101d40c1041ea400700880760902c40007480301032080042c81c4401590084030f08012001c2c01c548000c0030303601c1070310005040340320510010b00c0c2803801c80c106540c081c044621954102c4452004070038042003030f00040b00890154030382c80c1c0c18031009100300d14180c0510700300644181920740010700128149011030110359554941c56080150303100c001801403c907010510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 936066223 1250 936064973 936064981
    0xf230406030e010b040c0c060c120c12110a0c0b0402040f050c0c070816090b030f1e061b070f080c07060806010e0103060303050315150a021f0b15030717 67
    0x70068900030260414960030006210042d00c0c0501c84c60511007003544926007900125500c1038003a100e01090329040c05406483c5012050704c500404000700c8299941c2220000c0d5508901d00702c0d1030720814600070701801d20143da0070682148601c084980c101d04e50808075942ca00c005030107404d4520300f10940c54104801e000150001001426070204c0d02d0b03058840c20340e12490340c00d59034050703e04403070300c0f418900c1420445c0012642c402401a54098142c0e044004141c022034a49504004600032020240100038a900301c207226084e040200d10003880021041403000c848a801100b070090660803000f1960b008010146003101e000e5a51042134894490340c610001d070a00300100c2d080f50110790b0180307024129610130320900064990503161542540c44034444c16441c1055080d102d6000b880120760f504080c12008090401e6a00c168014107003410100713000c1030b06101eaa104e48040314148450707500d440e940c2d600340b003000f40100551183c882d0350b07000c401c8941c04010b00d00400c0181c40d05080c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 936067473 1250 936066223 936066227
    0x6120f09030e03070914041104090512031008030415052d040f0b0316210f0b030c0d0b060d0602040909060917040e011e08060a06080712030f230406 65
    0x40d20b802e0b01201078a1407196254007038000d0310900000c4200304a580c0300040c00041149403441321090700500001881e5080b55074661901c81c41d2508403020200c040304010840f80c000010344040c1205001030b5003090310b8001010201c12402c440305040c084041600004d00c1c203c4440200c0d0b140141d10403152078000b1301300c0c40803c0e40c480e00038040d040004040200b100070ba80b000304e9000d811103c0c4002d02802c0c8030002180d00d00900641e018411491100d1110380c0407450140700070220b03080800003840c150310010135160641803c0980c1c0980340b882c1015020654003080b641c2d0001080c1d5400150f8407062400750001d1107590040d4241a141c0303a00202440000d80c86101d04030b20900794500030f50f9201d03584040901451099140c007080060041c8080031414001c0e928102440c59424101c42e210901241420720480310500c545684080420a07d90100061070050252100306501010a0344004000345080d000301024003442500700c0c100000b180c01a0314400c24030300200c607281c40d01c0c1e40b80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 936068723 1250 936067473 936067487
    0x80f0a03090204051506071b0b0703020105090d0e06030a02090406181e0519020705151e0a1415030a021302070b0604181205040e0c07050d02070f06120f0903 69
    0xc02d9014528040018070080302e80b0f0640d45000b0802400d850615609640d40d0702e8000c010b90180d041500e20500000c0c284140b40003804800d8030a030008103044c900700d1106407802003480e419008101500c100ca014a40307420b41200d40103804104050380e43e8a4040c04203000d4001135110303d09001c054040d14400000b594824490f003000e007185040c4118081d100d0009903281a5410018207d201c0910030420996a0090025604c104103039689442c900d003246503869011500e00203007946800b410402c10b0201d4008075842071503070030104036000075203560203698800104091195100588803481c01e030703010050380002940c000c1031289805400001ea4020703421036002128002c11200210b11249428015601a59945649031b2400b100c41c0c0c075032002c2256140f40c4003042c80020072001c55603010040d86030781314144070702d4200d03640c04082c40c040303103402203c108110464202100600040246030018011100d0501d000d400c24944a40110008e08692800040c65464a0b80b03082c00c250304022 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 936069973 1250 936068723 936068741
    0x31d06040e07030c110c010f0207050402070c03050d081302010309020f150a2604020d020d050703032102120c0307091d0604060e010f050d0821040203011a0319080f0a03 74
    0x5411300c000500d0000c182c3d500c040d1784800102d90341094203c980d2a512550301034120032a18411649115034a801081c200c0c0e0151805a40d5540700c2c41050007400420040002201360342d04d0601a03500d8003ca601c0282c2c42440c80c003d041589909401c0d042d0f5540d01e1010007001001000d221400d50281b0b1405541d6220351100000704042011400d0946060055002218103c4010a040e41e88070f03801c000401c5100401268880900c010520109008101d40342c003030361080d201c3c209000969204451026014800111194010860840ba0260065405030020340000c00300d80c80391120301c3d00f612000141e03000700d2038070080000c0c690080d00c01680017030300405040e2800c01080c2d854028004011009029255912110b50702c20065800c0410410104600540e005818407908098040f009d406140f40c89900100341002e004c19441d081c0701c0c54144240c400c5070400c002c001c0c0c401080c0c48034101c51010382209409090f1070280700540701116242c44d0880003041d40c51070044000303801030103428 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 936071223 1250 936069973 936069977
    0xb0d05160f0611100e070f030309030312050c190e03010f1e0c1e090506210610020d080c0403050d020604050709021c0f090c1d06060a050304031d06040e07 68
    0x54009440c0d40a83c0c59407120500c144060100b151200b103040001d03192034032040f21140714200c000101040f070b2400c0319024620a41d24101d48524605005020625414492180714505418071861003640b4044030304001443c114542031081150064a406442240440e010b508284003101e5401d03441c1e114000c5d190115603848a04007040c002d4034119504900340d003002c160080300752003104190149121580358035203003e80d822500ea0000c20a5034004c50015100c0c082481c60880400068481c400e90081c2c00381d0b450b43c440141d45030025a24204490b1601c203010900c00452206d00f070315001c80f0301458111080710f2040d10060706c000e6550404580c256003034040c0b5900450201894022290610040300c4031110f0b60200d41c0780000200340d030924640305280d4400e01c0000040c0216410b400030209000c00543d0710040c81c0d2031002e1440001d08440c4143c0c810400c842c500c581107025260010b0f01483d00b01364440e882030801090f030f203140c007009620800100c2d000910b60b0146102d9071040c0421b07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 936072473 1250 936071223 936071249
    0x506010911041509091a090c0c03070f0c0504020703120e0109051f02040902040b0703020d02011b0e0d0b0108010e12030408030703180c0b0306120a0b2e0902090117190b0d0516 77
    0x8e48482034460080c41d41003021074000300002070104840302421a04140544158400c080d62140010102e03880f00074101c01003071105810000907a42c52089003002660039009104e80700c51555126202d1100c030740c0e81000e070031600c0503218031078a403030341a10040c240d00c03d02151b886496201780600380d00030007022001485202641d13010701c2d1040c0034036400c0c0004e0040b241e035503603481e10040e07500c0e08070b11000c690081100e04441f008242c0248a6600800d001d400005210f244055410308204010402c1c0b6101030040080c0400030f5410401c40383d1103213040c13a00181011041078030f400c041900400152950f80c1010340810804034010066029080440300000c1030100710201e19140c1c0c403600c6014013045181381c0003885152016040030344512000c070585d000050020508040c642c0b5640100914640c00724618945503006075100c0e07010510014040514608485042c1618010f040d03901700050300d0300200c05007606e03441c41d0a05420350203015101c03030702c00f2140e0401c0382b42414441c040404944c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 936073723 1250 936072473 936072481
    0x3010f06081216060c111501030b0c0f09040509120a0801090b0a03050318030c21060106091203120f06120204050a0b101b0c030b040506010911041509091a09 69
    0x900032280d0088084400c80f030580c202c1e440e000020955504920701348031180481194445041c010410101000c0d510a10b40c0d505500f0074001c0007100400c8031100d01c0c010400703105001c00b400309403400e054041701c0c0031805698800e00c950802034000c40cad0340182c000108541d03020640107542a4140d582c42d50b02041a88010380030013484003214400900719400411421410b443c042410070b0b20340c80090100c8441000781000718844100031600c04088420848015802642c2030003181c2c0104030780e14086014500b4052200c0d11802c00c0580241807064004510b04024a55000080380d0442c0f800304002c142d40d9080d031440b11180c4003408900c10b03450b1000007880240544a44640d00f50040c002012400c0d6840d0300740c0c2c1040031594011454444410300c0000038160b0319003200610301c00c0d030f560009414a8031703140d480c040341078211001860402000c03a100c4035406065508030f540d80390300140e10000702101540c100c0000d4001820880c28500000742e2030a14403403176445004150780400f01b5070b407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 936074973 1250 936073723 936073753
    0x90919050d080a14130606030b010f06120603050c2202041211040501060806060936100305030901141207020d0e01030b06041401020f0102070b150904020904060c0e03010f0608 77
    0x1c2240d6450307000b081180106141d50b004c00e10880c480b91146c1d400080d00b40e01c948440c49100c100b40c0c4402b00c1542640f5060006039409803d102c80b0b203a040d0303410300c1414115520340780ca948101c0302050150032406c00101d030607600d00522031001f02014400315511a220390703100042c502c410340151031500b003d14904110f41480d1080c207040f42c7e042c0d560040181c50390b00800c842a4003248495600c08040c8800003440301d000c5c3c40c0703032000d00130304001d0082c0309400e82c0c02c8103800340e002068190300141d0040208081400401269130b111403d103040c401e00d050703045884925000f510424450b81803000c00300008180c0004103524400119200c0c0f03013001000b4801101a03c1c1404903040e08410140700c00c0143d903482d42d40d1800305070014015603000482d801502800c80c0c0117a10180c40d032420791814002d1541c0d2403d007030081c0f010150391000e400e01d40b80e00420200340004c2d20040015a07142001c5403018401e9002d4540114010028000c040000380190081e00c01d41c01459094040c505019404032 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 936076223 1250 936074973 936074981
    0x804030b1e090c01180f090b15120a1104170606040f02040b0403060f06151701050406260c060a03060f0603090f06050606120a0f060602010b0a0302090919050d080a 72
    0x40c0b241c070014182100d0100045030b1800c85d500da19a0140d000120115030755800080400162500e4800050440303c008200700d04501380c0703501c01c4404a070400c0201c00c200648951031707500c124481004602203201c0c00384d4010620613a842404c01c0310340d114140c0300f804130100b421409030b101101c047c4122080800442c0032807045203e5403c03006c504000400005000750080513800d41402400640542d940b5403044082c1010171110f07002072a900304620954500c0c084c02400344c40141e038100b21080c18407000c41e0342881941d1004008644a403010220b220301001280d0303140d04040c1146450f03903c213080280c00383c4402d019480d0751b000441e002240700e62080c403824100b250081301d0807500350303642d4440c01c0090002502c4160415001c0040c2100100c240394124002d1021007000a848001d1200803000c031401508420211b90601c0504190b5030340d22711415040c0c03901100c504050f42c8400d244240381c4080450108020700540d841c40c0d050080115600050030402c1d01c8070040ba5587d0a0311a0441e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 936077473 1250 936076223 936076231
    0x5010b01050910081902031609210b0a0603141005151c080408060c0703030506030106030c09020f0c01090813081c030c030b04090803010f0506120105010509010c0804030b1e 76
    0x303c8601d59240c8406486031080c150004240c41c092403140160201030000c0e03030720446130403c541d0800815000d4032680030075040020011040394a0821911240e5110100307840384014040440c0e4a021820800c065406503000310b610185010032940140341c142c3e00c0744480802020641d18290020760030101905a0801e0500c0c01040d4864503040400c002c941e00c4080c01d816521640180004900201c04114880c0070748170f210b100d01e8a85001d0300d00102a5140100ba06010381d043c6942040050141c102202c142c071358100e400b6886060704526510706029216050940c4d60030100c110041c0445e600060070001d000310460300100c1d0b00d4040041d83c941c13208404c103403240c50303004e881c0e98400d101e85d1050382c0055492401044100c186800101590003110703040d00c0402000004000390f4150004003402008207407038080c18864816580d52151205103d144e041c4803000401244a80c03080031486a001e5100703070490713121610b070b007015003803000d04442061603000041402129581140000c45c82 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 936078723 1250 936077473 936077479
    0x10c021e0613030c0c120515011e0b090105090a0b0301050a050901082a1f0201050a0b13050901061e09050c070206090409050c041e240e070c080c060405010b010509 72
    0x1c9561540e80031613007011100c5080e035126114010101b025500003d004c3c090758043c800030a07006050900c06140448103034049460001074481040901412455107802c0740c42e64280c054841440d8801660079114120701942d02155404010a0b03c0d241c440246060320819107114803066101c0042c410201404e003e6450658460090204c00f01c00400001c2f08c200c419400c1c20300054a904049070301440400c01a03444603d0040740b0090752036091013459400040b41100344490401030010580811420819802c6039860740c0001d4a003040941001e80108546c110311001c0322800d407800721140b282401203601e443e09110200b074203c150b4100350395005400400052504001104010080c000b038034003200c060213401004403299446106015905001d6266100010701d54040d5400300d42064403020098540040181051a441500d18040d900304002030103503a140c07600203468001c50f5000080201a00140601260501145060040344110001d00424840c100190380e240940d00031a60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 936079973 1250 936078723 936078751
    0x204090f09080d020c011b0c060b0907140c0313060c0302060609040309091503080d020d0509030f12180106031a1b09060723070e0f160c03050903010c021e06 69
    0x1603800f0a03500825601c16010000540010140347c11524440c2e030fa846c40d00030960305814201444507601a80e5000c08040f24503508526000e04045e02640c0c05005001e20303c1b40105040540c110100700301c85c03881c0380c3d00a8405605944210007032a0403900c007001c40040c06010b001c100e090610140c041e000300da2688641540a00f0030700450000c1c604100c2810030400070070000004204160b0040042000c1c01c038001d07945d560f030600305100b6510b001e8840c2403164020024004005001401d4941c1d4070607071800c00c1c0c0700d602d5080380d41101c020301c0030303a8036280d520303190000080100180700401502c100b181e050b03403e80d40701040300a540c10000e00c91400454100700f10321031440d04000814050388030b407007068040701081e0103040d00001042c18078030056100c6001800a00d9016964590014020400420074a0440320b0089403401600c4100d00b80320803000001e081500440035100a04800744c000c10404840c20350080da0703070240045180800b440c0a041c0304080b000802e800b0b01c100001e03040e1340 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 936081223 1250 936079973 936079987
    0x1905030c092209141b1507050f060a020a1403060a0e0c041d01050a21030c020a0509041208090c030a0f0c12050c010201051305151f08010204090f0908 66
    0x1104240d108401c2ca00c1d100701c0c040c1c007a9458a842c0c0300c3c0c80da0881c022007009403a02c60a0f020503207000208981c0c610741c800159070448480d610610314115101785200c0964484111b880d1051416014411000b5140201c0c01080102c00082e8050019003d0740d540c3d1081c1d00c503502c0c4840e1614401a0342c45900700c0c042e01c006000d444c211b4010aa001100d48100a04d0159101130183d0b9860b0001521444207800e00010810341c6816070010300a4966070791008030003807100300c26140b001308c948001028008041d42c1c60080d551170300d280400814014201c42038070724041c50b01c20161510740c1d0070b10f40491641000300c1e51042c4001062011440301a008100b4000662a103d6070f40b40414022102d031261460041880c524091040d1000703441030006112035005800060300350395008000411503c1d44c05901004181c0004100d0200b0301222a82c40042d240c440018000107103080d20960703180710600c0c00050002c1c1c154000d000b00c80b18000c080107801a0865650300f50743d000341010340a40f4040c8101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 936082473 1250 936081223 936081229
    0x6040606090b031b160606050312090a0311130509010c3213090e0703060c0c15051302030f0a03231207090801111809010608010614070b010b1905030c09 67
    0x198040d0040c044c200c13402d2030b80c4620060511080e11104071841074480d802004a400d08000c0715164000000816080001c41c1c00442c0c1c04a110f440060154002c840803000152507880d07010414400a00b01808980b0307107440083e0181c0015403c0318000740e180c540e0120b061030b8401881403070522412140868034180341e001c02d040c3c0c00c0008540c40415281c100040c6c44c0e40148502443e00c5e0880307029115003455070030205d0803210707098001001e12400d901caa00000d55541a448c01c01c3c8148140002d042d160a02110704000b01030400a40501c500080301e0704034000000d0814170103101781d941e107454210f0110f1a06044842c800c070110501001d00c007500208181c0c2508036800000c920b0581c4445a440c17885c1400c0d43c905001d8900e00b81c0001901141000c80f40e0344c40002c2c10300545030007c141d450910010070580c01445048204400d044c10f407142c64006c0c501f280d40d40b5800500c0307481c842d61100b4400000e94400f002030640f0300d0501e00032820050081707007500d01c180a48021207040c4081c103014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 936083723 1250 936082473 936082501
    0xa030e0d03020c09090703031e1202311a1602010c051c030605040e03090904020105030a1e0506040b12060c030a140702010e0708150402150f0a0806040606090b03 71
    0x481c25400303220101d55071520340541092003001c8820003410751740c2c40c504018101c98180c83c0e20740070b128012268210442d4103c1681102c41c1007181c40160b440c0008e1211071080343c68040350491031074400d2147c0d4410444160340c0000e071600e0840c2d04a020350112406001d5100700300421152103080586500550f0050a254140074045c0d0f080d50f40384000d402c9600c0c010f2001056400c0070036030703505041c40300b81080d1080500d000301550080d850170080e1030020300f0940b00284000c1c10028000005081c9040a0300b080125800102c00714100020000c0304401130722088a055005501e004021201da00d840901d0511003d60700700038044540721050060060f03400242095081512424514090108400054844c08141e0700004455821901d45810040c407030780061902d500000e1201500c0d07600001030b540060b81102c2c040010a09030100151030f00a48401c5c5c20412404140b0a62158000078407520a900c03c540801041c1d46510f02920904c2450081c0c00030381c1c03418000a05102441c0070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 936084973 1250 936083723 936083749
    0x503012d0c0e100c0203030a030905060708072304051903150203040f060b01021207061a1909090f0f0336060807020c150d0e07080d0f0302041d0609090a030e 69
    0x1800c4050f0028580219147d48c1c8107070468400aa40ca072003142c24840c0902406800c14601e140007001420042d8000f02036450022900c03840c0c91a600d072030500460342d0805c41d4010074001d003d03816000b2100e401c01540581c1840243c588030030b11b207000700a9076824401c803845150f101070850700202441d11501d00074071349024880e05500ca803004001e42c40c00300d84098261503200d03403400300300c0129020503542c56000070280316004002a500310100c0b10070120032101600c610700e10000303e000c41814039100f030900816001d03007080f00001902051580c01002400e2540a441d4400c0d4140d403030504590102218580030401c0f407a8410342405024400d002c202c0d0410200c0c81210300d0070020700001041c01004800850602500064205400640e03001e002e29a1441d4005800b4852170407440035180e10501001000b082102d95440d9102402941a00e010b0840c0540d0401d2100316850f240c02c2001d41607910361301c0b44180b0b20001d500e4100000d20803c18aa2659500c1184411181405400d5074404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 936086223 1250 936084973 936084977
    0x10080a0902061206130e032502041b090b1201030f03031407080601030c0e090c031801022b0203041101031107050a12030605090f130c0503012d0c0e10 66
    0x3410480940c0c1d84002910469041d03208070019800d040c1d04000010700c001941072040e90a00034282d800d0000801582c2c0045540042842c212651000c401720440311410029401464007071265810407090801114610781a143c0000300c0d44c0720400e4003402c0c01030b050341c0031040307070004010700c000340c3c4084d08204424131a00f8082440d44a038608100d03008011518540010951801c0084035a03240c060001892020b00b44030700900034210201c0d4851400a20b1303020f9161000002ca0700d4204210980041604620002c540780d01c203448403042a80500d0300090003c0141d030070000310424a910840e40640c0d40440b001c08104c60402c01580589903101c3c1c00d01c541e4406010703140102c0c4085c060340300014813406090084010421018045074030940016001c0c40962040144c102c040720a460b030080802d412000c003500d001e141c10103094109400c40380d0594203040c2e01842c1c402042091040e50ac030f10700c0554000c200242c4104084030440c04104000440d40051403c3d103041140c80110349241e24 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 936087473 1250 936086223 936086231
    0x307060b0609100c0309140f040c1404030c050f06040e0a0e07081f051b07030c020a05120f06070e0d260406080115050717090a030b010801091a0610080a 67
    0x2a0001480e48801c0c0c4010030b004c21101d10840c010940c3c0403000802428000f011030360008075010109240e1442000c0041c0603568698081c0200d501a13951242d0100407040482c3e40e8039220b20f0300301324154103807045500644007107075034100d01d182040549051700c1a20103211f01e00da440004000151810181c8140b15008140c03010540e1388050015001c1c00703201c2c1c003d40005074040201c01e42162002001c031041c4040c0c25010310700c04141e890403262000e405240c041d41c030762a1400040c00b044643d40c03000b0b5204442c0200581100804152404801d10040c01d8a0281d540c00d001035403034215222a0076807000c10800300b00d0008050b00808802c05807109480002c2600c42440042c090340f01e03810210202d2444d20042020302e8554083d1402e0030920300e0101c0c1030404590301d50591200b42200d000c000342000c10500490f072030340c81032240215003198042085503900c0c420103000f490300000a460128282400310302c1c043c0316050440c0a03080c043c1ca500d111820041c01140c14000160181c0401625 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 936088723 1250 936087473 936087487
    0x60d0506010e091f05060c06060d1a0112050c0f091b0f0f04080706021204030821010b1309200c1c18060309110909030f0708070c0509090307060b06 65
    0x902c0b14480c0316002c10f904120104000882d000016021381e0b02c001d100b901304001460031540003107181a080300042d94801c81d002803031303d483c0f1100613080c903070aa4000c000c840005410b1404803080300c6040c0c041c0007038a800090341000e11040781520142d1540002201c00411051080e4200b403940c0c40c40010652820406100199040ca6002021150b84c1e010081400e1100c54418400320004113050b0004008904241155070964010351201404190010030505015410400764202a54500065006541e140c072149480c0360031000d24840e004180000100d01d004031449191680310030070042900c05040c05102100503446070150244900070b01034180702c0d2280b440000d86c003811641d121440d22524072091001c201c4000d900232400c25081401510106100c0000908410f0082e40e05400c2c60381c40325074007407840c400c0542d051041440000e410007070140110142490b90300c41c500c414840e81c0e4442c200080d645068946610b00d402c02c114020000e6950750000030105000382040c0e042000d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 936089973 1250 936088723 936088729
    0x1502070c03050703050601170c19030206221403120a021c0e01020d031109010e012a060c0201020304021302030a0908040306051f0609060311071b0602010506030c060d0506010e 77
    0x1955070003200c1c00d6010010600400c102480580d014080342000180c010305110b03800b44d43c0d0f10071451f0040c0111012005140c1e00c032059443d09010303507000351105030348284910740710b005040250034a80845042c071501144114100800307000c1d0300d4009005290007060801e0440301a8403040d9190306500c0f41c1c080c03800d0106800e60503c2c00075600fa031079442c0807401031713000a410074050b02c3d001c1d41050710b0401d2003104448200b0036a0b444007400c3c600000341d4815040181d90100382080580c1d1031641c048a100c400920407002200802c5c4546014000349170440d000b41d0a0740019034001790710581d00ba00d0a4a5620240d001d5a80201c007100f002c1044525503c0703503946ca07030281d003080d64025101c82c1000050b04001010300d2249003440112010395140480040031082c450142108158035040e18002d07130352410040c0d503071590704100c444503402616a50800941d485100d090055400c010014203289000b140aa8a451020b4100e43ca44840c3c40b50841c01403200070405170500c81009043e10641e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 936091223 1250 936089973 936089993
    0xd03020f0702041107050109080a1107031a07111006060e090f07050c01020f18090907061b0303390903030903020d030c050f030414061c15091401050f010c050a150207 73
    0x28000c000d100c2d0340301e0449400401c4900e445184103940d0344030a0cc204001242801d9034900700490108610441d19040b90031681004007031460342081c49045010b1b006ca080540c80301c01160391545404008803111002d11207810f02c00c41d0340400040c405000140700c10f00410080840e140d40200051414986110088054200c0e43c000c480311909555458002d00300f400d1540c2c0c01c031111600404665240c80030040008003c024901406842290f010781018001d40000c0301e0302014549580c480c3c9250140b046c0003010441031000c50f030800505201025002c2d1101c903040e2505541d8202e0100d08580910426600c040d00c110100507400440d1000304909200400007402920051645d440c50b080c0e642d49013170340e007900540c0300c0c44041080503c000a610702e07003c0902900300001c40e82070048101c2c06054404c0e50301c0881001c0c10104660320340c0303c206c43c4550584004403000d895074140b49004691081020000030704652242c031201d40030850038100a61010f5066501620341036065403001200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 936092473 1250 936091223 936091241
    0x6080705150c0303100311040e3c03070b07080c03010501050a11031b010608030405010e130605030d021501090603110d0602130801020c07090203060604030303200316020d03020f07020411070501 85
    0x2200c5d030740420310030403070905103900ca903110071242402100c8030b12542d1500c580000b845500c0040e070f6000c119010440074000120b00d00f892070404159000f48030221070b213071380c00700c00b08640d48981003000465090080001901520882c1007441c1503a08040056541d40e100030201c409100c00c80b540603880c80d20800081455100308500c0c580180c00080025007136488503040b1400c55001031009229503644082c4462421808030307418a45903035034854220081100740c1100d03400d13010386000b046002e90006501216a4254416990680e0f40c1e4031680301201e6050100509807800321400803140d00e45092020f040c107000b82401840d0444542074140d61a100364409111070750040f990201c20103040c40350f4801401911010f41c954607101000070307140d00c17840c0002014199503142c200d1001c420042a50700001041080c90740d070341003505104481c4100c1a042c0710040c4120440c2c0c6010510a00071344e20a040c48004041c140403466003004054100000f200003220414440c11022607000d000700c60351 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 936093723 1250 936092473 936092491
    0x507030602030a1a011409040b0a0b0316120902011407140d090914010605030412051e0d0507091521060b07020118051c1a01030c05011206080705150c0303 68
    0x45180e0f00002c10034820004204d1034140305156090807a5064070300110303a02c04c44110b5000404400d1a40040d10151950708402d030354002c04820040351124410300e041c0304030242c1e22100c08040410420106694139600b000380024262a6014045a011030140c110f00d441010310b0780c1005013010b201c92911070751b01c403c40c0c006a4007240030081442948035031641e50b01461000e40301c56051600280044c400030380b000b4030003081104a01034241c854001d44400d6014029200414178074171489000f075420200c01084180c0c80d04002c18541e90080507044202c0d51108801c00305910102c1054420200070319031220741107403100100b851011582305150281c1528158192242e080c2c0c000102031854040700d00078072020007542405150707140b001d07007c100b10004002d14210314640c41c00041041500f010320f20b5540c1143c001204214403030034000241d074400c0e40c445164880c000032400680d8058450b0005680103c0014400350500090203542240c1c00003100d0b2505004c49071444c5180e10403112908 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 936094973 1250 936093723 936093731
    0x10c030f1e081b090a06050a020f030d06150c020f120c060415020c010908070b0f09060c1e011e0509070312030b03010f020a0509010e011803080309010e0712030c0507030602030a 78
    0x44a446800f02046184a400701c3c1d5040a0559001c03400c01c10303071805030500348000071030503030085803003040764031003840350b50003926150600a4046000381c2128015401d036511000380503c2c1d01403103506c0c06864250001c010791a0903401d20f05001850a0381e981001e0203000d5464070314071720f13141d900082c0000d100d0800700346881d109041c0c0003030800035245031580c104880f900707042003e100f00007141307010f4072036048844e44c0d2010f1000441c040c42c0304d0250401d07048a40803c01c5c1547c80004a00b1500461940c0c00c0015003482c826900c5080b41c08034003541003001c4503130020300e007030076126403210303901182c80c5044901c0c440d00c0313488401d05481d00d6112800000c5e118803200d03060741028016044120040801581000040702c0c000c4c02c14041c500401d0304100185141c06450307032152000c01034424810484c041010340740e04041c3c640707034011503840c1c51030340c00c10040024030400043e00301e040358102a14000c10101580d0215460002d0382c0e4280c41e03912403403901201040d46440290301440010300001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 936096223 1250 936094973 936094981
    0x60f020f0c0f0c010909050702030412110a0501022e0914060709060206011a090321210408073009170f0706030b01030e190c090b010c030f1e08 63
    0x80d14102d007a421045a41d0445582440666003007111141078588511000c9281d03504d50900700d1460003181d000303004514081c2881014070a1003921a8810300d400e0707403582c0550342c41313000590b61401140d200e802c11503941112900955400b88426100040c242c0020030302da901511550300010035000401019003054040c800419008080c100040c920781c00a4015989000400f0000c00205061140313098400942e80030140d40511a050280025905001c8034100c16010b24240b03804c25a010701141c1080d0082c045185071004c5854407482e4001c0e910362820b00d0780e6443c100c540130b030340500c03052080c810b00c130f4103c01030b02055405444528569550954500d8004001070b400b0141c00303102d8503a0800707651050340f60800304444040d10120b0801151455540004800505207040c25480c02e00a0703180042400080e10902d0540c139011301120f4800d5900d07019a00100c0e130342c04142038041a0402070043c0080c2c042c0001654403189414520446000001860303510002c4c1c004007000141410104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 936097473 1250 936096223 936096247
    0x90f0907052a0d080a181407090e0a060b1306091a09070f08060d0807140d092405120a05250918150608040302120304030e0409060f020f 60
    0x800042520050680405100d402d80e4070b403038040310166901040420720000e55040300c140c000800d29180c0120103441c021440c1040e0280d8000a0341405140c0148030000481c041c1070301480107036074018400b81008004a03950780c00100743c0740248a81058026680c15850021440350704020519a100400c42e040c40c0c40c00101a002e480840364480c89056051003e0694081c40c0844036112a0924001544038400080e402102080d070081c440c0c100041c0e10700400c1400c800f214011150a81224602401c61a00380d4500444c0d00640c1d00740404494117000807000d440d515882e0a8450504030714081c60f010710540714201c01c079442d85806072101c0c1403182c0f084480582030484640b040ca403002c01c2a107000001c0c00180c161003540c28400041404860744001c5900002610551100800d100c0d6030310030015041c184d0446d020750142c0180c140515030340855101f16841030350b05590311580890070508000c010161000c06680d1309a4608090070300109500c01449000c03481760303055498070104896 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 936098723 1250 936097473 936097507
    0x20403031701060c0b040203190c05040e210a1e111506030705150d050907211104020d090501020408030d06050a0302060f0c25080d0305010806010902090f090705 71
    0x1c14040300003070040080f2a07200000c51086a4800000c0c09a40c54a0001a107420500007040c0101440e00c50004100910311903807004881040c1c0b820711090100d90b44d460b031030b0310042640c0c151003101341c0b044003484d00c51800103201124a9003081c1d041d0070071a20180403806e41d8148044080744a064038004010010801c0389108024500c1c4058146002c40c0800c0d01c80740188142c40c051082c0102a89058166600303807171042c46076100c1000b6a1810b41c180564179081441405042c2e00d1298400040f42c3d40b01d000d48a25940181c407409151180e407007480025030003c100c4806095a0b07041003000a00f00380011720041103004015034503101716961900031118143d0001e071140e52a81d20030401619054103079581c8800c1104540d88030240c0c1400d841c1050200820703c4144655140801030145040d040481511030120840344140c01c407160030383c2116001e000300180340c2d103c0c1d40100300c101c41035001041c101c040a00070541c058804000305400e48001d4480e90003050300482c2da440c80180ca200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 936099973 1250 936098723 936098747
    0x705010e0c130f020913020712020604120c141b01020706020703050c150408060907060e040213050f010c1520130e040804050d030c0201030501080a02091303090b040902040303 77
    0x202404100801d81c001030070400b00d51040d2003040d91150003c210204195041d5903106070082c0081000c2d030940c21428000754000c2801311400200960701c9403146100091183c4140d5010060f1001e81d10142001d440074241c451044451075040c000401d0920b209001300750802040c3d4a0f40103804035110000ba0400105402030001c41d409148104049540021580c481003004c2e00c1006001d500c11003011202d101350740149166200300814000d20005c0000d080301200c00550714032408a040c0e404100581c0f00b202da41400b60b95048409000c2c42c500724245d201c1c91603050411503011506691161001c0307078229600c00420b40c0e540954209050004421241c1c84484e038141c5280c58415141650600700c140507603c20b106000300000c0c1080408030440e4041c0500500c503084203005480e00420080700a0720403400a030410000085aa0002429907609070340200b290f01103503201c00c00b480d1602d40d1780ea811340801940c6040010300c00c0e5035100030300c00f0f07140d401c0300981c0d500c3c203504003c2c100d90450b80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 936101223 1250 936099973 936100001
    0x80403030605031501090213080a030203030106300b1c030c11030120090307120b071116120203010222031712060112060902031e0a060302010f050d06120602070501 72
    0x10408101c19204c0103202d040d40d071404001030302ea5034a000811400440d41c0c108499078401c03160044241a00000618125400fa5035464a60038288000c04828540b80c05400e10008003050311008840e42a00903051100c00545100c00700c0e145005000c044c4000741e2819000318031048107400c00e014280d5a0f1441d4580e0941c020710001a01d00c1c0c2c056221017000c82c003a5160381021502c0d0031135035424801c100007088802c0c5c41103042d0f010f904005440c45403d8486001041222910f14200c10f804203013075110791100d86500041030720305440c001041d002d0290480c5c1c595401c000381c0746030b0254000b40d0484522000742c071880082c00c61801909840d086100e0326400c0c0006d001c0d2010441c07040c402c8070751050007880c0500000f241c42a5a9000e041c3d5034014090302800072080000070500035103130b14007440b2940c00030031710307600c520302e0b12000c030381e03240c00042c1c006140400b92070305050250004240c1d500c40e0400c0094050f82c0c407210400c424421403000c41e02c258000801d9424000f00b405403e0250742e01c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 936102473 1250 936101223 936101233
    0xa06110a0e0411161104020703111b130b0a0815090d02030c0d0c0203152a030c0f090619020a031106100608070201141009060b042106020c010c08040303060503 70
    0xc0282940c1601130550380c107584410103014074040001426008075107040260055450301403503d4003030603081d261301a860b61f500c00c0b400f90002d004480c020020190001030a66800b40503401103800280075040c404c1a001079070f000c0c0018040208210441a500003e2051085030800c8035166040001c030311441c40c1150300c10300500c80854000f00307010060030481d0409010714402480402c0c2800410b01e9400002780c2000c081040800c3c010755415003100240c0f0340941045101c114205a900003500c0031180c3d448103110007401850410021f0100c0030004201130f00b080769030b8100e141820300301e8404100680000d80903c0406400080e4105041e685001610942c41d000e800940c1c4d6940ba4420300041003910f0700451030041c002c2d805a500304100a801203014906600014420070300c51040e541d0316850168001203d2460500356800d13580c580d500042440c56030510320708400e0079900140d440c180d00b00b0121690030000d1003001400071054031000c0842c502410702070201c90403540704034000d03048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 936103723 1250 936102473 936102491
    0x1812090e040b07200a030f140403200a0f0602010f0b0904030e040507030e01090b060901150503040305070c12060b0a06020708100905120c10060501020a030512090a06110a0e04 77
    0x90080c5a0341c07081d5189004140d9041002d03440d0300b40400e1507030850b454000c3c03094060031b060b4001070302548940713207850782c15030750700c00040044c054815440054100c9202405022034071102490b00b099840d001410b0703800d51615407412200d00b1105610040240c0c0d500c0300f0464140026002da210103000c100d030140e94610b016140608070101d5008424850756944000802d45030003940310750a40a071070703c000c2000241c58548200004e20565078a44206070b00b9000080d074a203610040f60703920b1001d40c1d410b421078642c4d45d030a5490f90040001184c0c1c050a164020450348040044c281a6501440e000f203108200c240c107214103014942c20000454020308418054000002003071070613100f400f600041c101d0110308000c0d007401001540c50904d120f0019a158074580d0000701c044641101038003c000413507503800166550b541d0b20b030b00203020940a20180000342003400c8204d9010f0091030a03034850918681e03c1c20100d85030300380c10582c4240302003540f0f00345950144e01c04c1c00c004001d42d01008404c403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 936104973 1250 936103723 936103733
    0x7090605030a170702011112040302040b0307060f1b120305270706050904110406030b03060901140a0f0f2d050411040e030409110706050c091302030702011812090e04 73
    0x40d603580c010743c4490001e441c00c1164031a04d0a00c80d80100402512280c4840c940b81d0400380d4040c0c442a44030740d042104800c10b514000c50f02c142200d940c3c2d15a000c1c3c403420020141c0d004030320b1050000020580c41c8580b0007080d05850f0b0340700c2100079a500002c0e90b2070300e03251210180001121844980c80108006d50482c0300c00100001a10050300303000307440e001d0100004e4003500e0012440302c0190004580000d405815800c403407400901242501c00941e1a20012801c941711030540300303040500e071800300313101c0d030712980c050600b00c0d0b80c0c05e001007040c03c03004d00c0316401c7e82d138246003d141c14204181440c9482e1026254180022034a2000748101d0a00d038650070041600d15080c0b42c41183c0d6800c0c4c070910000f0800454006225002051001c843c05242180440e00400c0055407400e003410002004220304c24102d0b01d43d0b0800030900305500c0000f0075254020b401c02040030003035643c0d400e80428047d40840d01801800d2051455000d41d80d6408801040c40200350302c03244001d0440c900f8400020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 936106223 1250 936104973 936104993
    0x30702100506120102071104110c030412080403050f100606050c0604080a050c070e060a0b0f180a1802070c090209060a03050c130b070201080906060112180c060207090605030a 77
    0x800300c40800c8548410000662030010b4003611201c80d80300007002d8080040a003076014a21000300c030104510f03403204801015500c01d452603044290410441800000e6480e0280e14210740a0400c41742003d4503a942c880c80c0c0152110318600b01c1e8490804805000140e0142030040c0c0304910b415410503006561941c2d48110140000b06402d60209240541d54465010f88001981e41800c99030300039504d0251003078995043c0d03242c0e03019103003030180030680f012010115030b5064410301030f181c60301c1c00440c0541c1c0d0010804405075404410b44200080203198070013680391040044c040141e98004910f084c100d2103a950303000d00711550040c030a174001c580d2000b09542c0b610303509040202c1c65913038442684015105411144000381003000b0041000382444024101da80d100f070b218070308130380c0b50b109060b41e440e101180d41ca0700180c105031032001500c0190f00000d1020190004995422200d6501c0c160741400b5608481c0059021403070421840c9054000e07803006050640107000c41c0205a26807440c0340c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 936107473 1250 936106223 936106243
    0x71107060503040f0606170115050d0f052113090b0a1e050d0c090b0d020a0b0d0209060a020a02180105090c03060d0c08010b0a0501050f03180f150f010605030702 71
    0x1101e00440050140108203000403001940010b0402c415a150020703070140e004203411241c01d03903181c410000041ca010f0b0fa411815903c00070038554094802c1da0740c0c03032207201c402e00d400c40e2a070041c00100290350440d01c2d007000d201030074100c40c65150159202d8541c804c1c8510f90106840b2070808003000020b03203543c0464801d4600a003d00d21010050b2110b80102204543c002c60308006000c00a01c14011111501005c3c1d45800d1800c0c02010699070400a0819112001950083d502c400401c51f60300320300001c11026000030b202500307101e44c1c2000141e050700105c00640241c0c0090440d0021803425880b8a0340d0580800e219030001e50400300032a41180d0700a008036405040040481d80d0750395021030f420b0b4120f600011000700c0640f2510014043e00d0b0290300507000740f240ba440400c01c7d60007007040c3c407403148148071078906640d100744910100f01941c03c21084c0a0040d4141000c0038403050011564180160100b190b103030034440f0041c0403441c0e059010404102041c414010f2032540030a051200e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 936108723 1250 936107473 936107477
    0x7030c030803070527011e0e010e0f041805010e061b070311100f0509010905190215030c120105011106070e031009140601150f0309150504061407110706 67
    0x80e555118000e0750580715001641c1d4203013000141d50304441e04a28a00140e071417003030740c8052101d03548a0140181d840f10600f401701040c007640c80b81200c2e5220740040a10040c008000c03041105111340410211905618500202140c9445060a11509004404007403a099009120610300005080d403c0c0b00e071400700d0314840e00002008001c1c18418403c2000d4042414180c40381d074010201508001c0940400120350a804c020014104d51418070072055281d8001018200c003064140e40c0d00800c036109101207034000405c640310480c0b0209000958840c40b40d0904242d91000150070390201d17460305900c01c1d410040d0320103a1410185021441c6600b211203401c1c0404019082c00000f820300c50b100b5505014140707041460f00c1803129030700150740b0240216050341e000d80d889450386d003004003032992040007044c18241d0f400d0665101c0c2e40071000b4540030705101851541208002d00503190141d400707a41150300c0c0c94038030717168280c000c90803600044941048101500214031841e1649100d12422017 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 936109973 1250 936108723 936108727
    0xc080708070501060306021b0610050604090f060b1606111809040302010b030d0c1b1d180a12020606220207020301020906040f0609091509020904020d09150b0307030c0308 75
    0x8000b4250442c1d000386074000c60030740d1224102c180405a100001596181c58400c26000c1040243c8040510040e04c0c1c01600300e5250a0074500440054807514008061507540e80c107000406290280180c034100001c01c400000601140c00c040c41500e80102103c01070038001c000c20200c8121513114101066400e8940d00600c1d5541c0c203003a40100202c2e014541c050040c4043c0006103a400174450082c0d82c070a0070703600c00c065a07031000d02040c643d0030f014902c989920240405000c244110426a0010089120b81d0707420140c103009500748014134204840c0b4a00021280d0907203901403003041d41c0b1020560750340d8265041014103404903584001a05045a8002142010364030203404889040c1e0024203c5503646688880c000a1461f16105200025000317001c0400c04946078041d203024414413100001120382450a442c1c000e500140115610a5007000641d074401c0740c5028018000c0d00400429003500303418280101a43c1078200c1c8280319800c0300400303100007820196030f241500e03042082d1036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 936111223 1250 936109973 936109987
    0x702030f0f0a02010e010210060b041e0315180c06090e010b0c0a0209090c120c010807020a05060615090d110406050111070b130b03040c1d041a09121c0c0c080708 71
    0x42c1c10600888e1810079070605204002c100b080d50395005104840e00f007100c00007900300009400228080c0c5020081c840043c44c034019070308680310342103203c107807a107000307074003024a29a91080030014081d07020002082010745c040151040b20803d0314010228188264540784461a010780c0750318400b00024495000da00c0811480ca40410580f5856503010f1b0451710302c0c0c0da50382c182955410802072890300056048000480d0244040380304500c0650000c01400d07a521030f0401c001c5215a14440741c089528140141131041d544d0701c100740a141d0080d103001620f00d100ba0203000a48020307402007814003142d1200d200251a0001d03130030f0111148004c0b410f031a03100c3c00580f0400000e003940079445251002c02407006003c0d094107164100da42ca14805030a00c0002c107400e47c1045030881d4090143e0114101040080c48408801c1e54005010015202c49104c0d40c072605842d5042040c0142c05400c03484407400d422103080c85060204c9486041a0300807040a82d100340c0c10380b0558100404480303022a02c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 936112473 1250 936111223 936111227
    0xb180114120c100507020406060f0c120e06071104051006170a090f05030d0f29010e131e0218060f0f030c0715060b0334050702030f0f0a02010e01 64
    0x500c020840104407884080f10214010b104c1d4201e0324041c0d20aa10f40303080019480e00030307078960303803003850b1500c0d2540c410955441d0603110b00901c08008040c07010030b2f000c80031665110801010602c0c8580f1003407100920710404c0c081103400c014800360704048800018480d06400070112521070002184045140d52001014000b511582800600e0890340851803010403030702001821b00382c0d00b014400c204001c502d24124003034455001c4800d021405801e1480c0382112003c0f010200c0540c181402c0c0c1c0310000300c5c03000c500e00200c401d6000c0c04540c0d82d030b54054841d0f00d4007444098401c2501805500700415555050311034102000124803840c80054000180381c980015181004908201603869280407002440c04d80d01030807046501791408a20010821442d100e401c4c1903036140403101d41543d03a0f0042c0d0305400c2c1d58014000e4150f125081c0d071060005c0c00800481404001955069219500751041c1450407900607102000c82d08404900004403900241c07280180f9024649504120118801 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 936113723 1250 936112473 936112483
    0xf03032706010f150201060b07060f0915050702010b0f0901151e02160b07151505060d02090102010b0a0e160306150804050c010309030206040b090c090a0b18011412 72
    0x25601003805038000000f0700950495800f01220710024221000030307a0003070124202c4582c0c0c01000668003040c00701e04040307849030f8402070b00044800800120001507484030718415030502d00720340c2e040da150410000c9503542801244e41941017990403110303e0034640300188a0050500075010409480c07044400210701c10504540c1d130664058003041c98802c1044001c2d140c6400f4a66100c0320301c110782000546888400c00c880070380b80c119000070804e860942c0b07503501070a0541c0e50044110601e1501280547c2c424004100c6001c0c0404016900c2950000180c250340140742e0b540c1c403424034014100500000380c0d107066070046244030700c05144295120182c5c0200b1141e00300c061021005c03005243c10641019401e40074600900172100085105c4004409440e00c005004006030015401702c1c00040c190188aa0030460000948445004090104110030700484952070300c0c81d110b645d000c00c142017284c920500c103d2802c21181c1d50b5810812011041c4490145242c025030b1107d0f040000d4040500c0303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 936114973 1250 936113723 936113791
    0x306090a18030305010617040503070b071e03050f0f0402130f2307230a050c0a1a040611070f0821091f05011410020307060504080408010b030f0303 65
    0x2181c101240709041c000c009007000d008280114199450030000d000f000400d8500c5107500c034000714508100717542c5903d00d444026000d24188196802c181105001d8142c0b982101c851540c0c0024031864101b030110070162000c0c1440d001560b901c03041c0005a200e9511106c26101100d901048000300620060010000c24180d04000b10b41180403844602643c0c202501071110341d91404e007000d074050003462203103950b140810700c0c40404010f040181c41c02003000c0c155200305001501d031000402d849600f14a084c8901ca82c02d0900780c001017008006951203070304001e407108240181001d5480d550809032440b20403010301030035001f1500007411018010081250003444590110506111101c0e0740e59500751038040005052514650a0005584c82254102c960050385000280d41035410310449607080081001140400c00000d408108a4061540501c1c800c10f600d030740e80c900c1c094125084841480c241d511940102803581b40b2044000b041d241c21078510310202105141c044014000800680 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 936116223 1250 936114973 936115001
    0x402070807212c03030d022a0c0114070204110c010b0414041e082a0102070c0501030510050901090903170c0703030515060310170d050306090a 63
    0x128041048880005000514842e884a00d400940d884604212840c001010400100a070343d030b1a1450a200c80141c0c080303258072050201d600e0420010906580c885403201c0005034000450708070a8416034150000c13003035140d61240095176001c40841d265015003c440e4100000e07030076280440400f041c00c0320075207580100708010800150460a50f1508140002521946010780303001c8a0306140c0940303003102440c84180343d400d03604c6981364800280001c1e821447d200600b0811400564143c000b001c0000720200034040052003000760661104241001c628164010312503080000c1012425105071002400c021541c0c0c3d0728041da46008554542c000d07940f26454a00014016400780c0c004180a07000e03950744100c441c1d15940240c3c0003003099900d00c640c1d02c0200040b80109200ba0312950700f241c1c1500100e86105182400100190001d6800691541d6400c42c100440f8004045000c0360360009000745c2180108103101900a00001b00544d019102e400009480c02625610203100c500b009 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 936117473 1250 936116223 936116227
    0x90603020d1107030804060f1a040c03110408070509010911090d020f03070e1f0521011404140706140406030207050705041503050c1507060c0207080d11010b0618060f090402 76
    0x2a04001708140d4003030314150780852906010094024582c080d01c80001c110714204e021440c101d0003840001d0503449038040030144e488884084024502000300024801c100040100c0ca00702020482e00c41ca0691100303091900d01700741c640707250002c00191900307000116540340082a29001042400c541002c110354540100c160115000403849071590107402030309032001e0502d2a2070341c440c6440069005039680046030950502a07500341e00d2142d083c045415002054001102a03000a400b1007a6021070b00400d480b220a18980c400f041104000c203807078a400011034480b460b12040c10300c6580128000c241d00041c10900740141013100718020100a032007044002d4032189400f402c151180022100c500a4418801080c5040e40b48080e8038201035612603e007142c281e4904004040c0c50304150107601541e440004d071540103200072551990151a20a02c140d0300f0802d00e82122140000503204600a01425450644642c038013107a2081c01c0c2c4150b82c0d030740700d102280f510714000e00036800e601c0307400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 936118723 1250 936117473 936117487
    0x30602040602070e06030106080604080f0403060501030309080c040504170c03040b04080309150a12020c0a0b0a2313030f110d0f03050702061915080f010504030e030706090603020d11 80
    0x300081000c104e03007101c18041313466100d4078101400d0b90317120b100d1a00d039a40306030041400704501c07900130000c40d1400e03481d071440c1513940d645902c1660070980c01a00842c0b84444100420b20041c00139540031801160100100c0c40c2c142e80b080c440c1414110f900505002c081070340350b07599004004450184c10ba11810381d44690b51201840d039a80c6c400c5910b035004000700e1840c10700b40070b00e04e02594044800394030740043c29901510703600000d4010410300300e02480f0b410101404581501e103254000c4103041000b00e10003028074481c0740fa0008042250b82c8440d144020080d2045122900d02c45c042c2d4146440800d039810618203c036402c0880480e6040350045501c0c1c0105240c0000c0c070024000c0854806001d980d0715894142e071200701c2228050740f02d0301e482c184404141c00c2903000d544404507442074004c0036910b07155054507000a004d1001c00c141e43d15410301c000d05801c41107400d0607040c1280100790103030800350002c00910051240c01c05254020800c8a02d01510b600301080343c0850192403504c3c0c00d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 936119973 1250 936118723 936118727
    0x6060f04090b0a080a0302031206061903270305091e0a0b030708010f05011209140d0e0f0301050103031b021c03081608150105160c2909090601180306020406 69
    0xb002c042c1520603122080c00040d802e90110756151001d030180c01031418406455035200040c0340c000d080d035600c03100c10400039854081038480359855000c542c1d4001814221004017003c038004140d06400c580104680e00070010341d0160854107a0041503984503224820105903a107001c009071034840d8001c20212010a80140b60005944142c482380d0341d03d219070740d0760700b04400f075140039020362400507030030507610509101c00d6040786025a00c90b001204204d0550307101e06040150000600d000a82a40c28588962030403646840c2a030904900800c80c951640e50043c190b001844002120b184188100c1002c0d0340d5455450701200480d1317654240e94031030381c1c90010b00250040f504101c07001085c40060000600c5840f44610800c590803502c5400c1c0100001502c0c10f4101c052440f17400b9002c4c20100002a4a0390b00da2002031140c071907100b03080c0c210789003480420f42040c80c0510f84c5070020310010126544941c02c41da0068820300303000301894060010f01082e1445e541014095900000d400920a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 936121223 1250 936119973 936119981
    0xf050c0d0c03050402010806060c070803180a1502150a0204051c12020604030801170c040e0304030b0f061f0e04090c14031504030806131503030801140a03060506060f0409 75
    0x9461030504210420101206504641e01900c1c0039000406000000c0c48078102503004104075148042255a696940d40501e883c50b44400d1503465480e02c0000741170b1050410101340b001a2403808400c915011000e54020b5881d024000640a0100440042464404103904070707400b42c100a0300c07614686020a6940b2024014840c04a541c0d54081c280505001d20104405004590655490302603074030307040c9907040e94484d2035004589070090320b55103002ca5690f81700b0400582c0f400c138040c54807030303280d401d008000440c01080100852020400c00605c1e55868000080800c030319410070030b51280001044400000301c0039120f420524081d141418406d40c24003800c01c9a41c52a20302074049001814551100d1590000350944141d80007c24000b03401014a01d500c04c85c040c10110729542560613000540c1d0340c80020501076041c1c4103040c801d042d0301419507805400e5444280340821516804603043d4842848051b010076583d10124869a82d82c004880b05d02c0344c0500425110ba0320303142000028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 936122473 1250 936121223 936121237
    0xc1b090b12010203090a0b090304051809070b1306050a031103270f060c030a0e104506110f03011d0f130309170d0e0103110f0d0f050c 59
    0x24a4200035000784055050003107074400d12074800903001e07030145a0703105200080c01070490789441c0814000481e05840e0b542009840744609019002e107400c150000750300b80300c030540001c1401b410822a0700781d80341504900300300315001468595500d40d602102100144031501220b01c840c2d200005010107698000341803803140b8060407400049440180d103031035075242c062101090a0b00705000190005050b040990b42c02004480007040c03403841d10440d1400c015100d040e03803c0c09a07a64034800ca03110102d48054010500c0011020024542ca2030318216115a000195101d5000c16800004004054000101c0c2d01d00c800300074ae17194001100b9402c1190424066405c404940224842c000103544954a004000440020001d80c550040d032408242990301c06a060007065200000c1010203250b1810600c3d00140180c8040210340034010844c0c0e10402c00c05040500b0320010165103a1510200c0b4035041c0c5c08290342d41d5440304403248001400c50030801d201600e2500b0b00300703c85500808024022 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 936123723 1250 936122473 936122479
    0x204031a091e0c10081311030307020306040b150904021c1104062d0f0513290f0a0e0c0c0a0507060e03071a04050405090a02040f06050f011e0c1b090b 66
    0x20313003a071010494440008030741d18048410312504420101d110304013140a81c1c0c4000d0f081d61302d0080186c004c00e1400005950071a40c0c1c911080410554450307102950b901c0820460380d1048606142d00010309020040c0300703021800072800154400c02401c92006144140d0103030052000680e0360f0003402001c84882d0482a4604406400c0101501601840d8007518406440d00b0042800c08041c0000d14054280002c0e2555842c031004c940e85800160405508504d24012141c1007140814402d00100845450b03000e10b030034070310501c80b80b03010801c2194000c500c05503440d02c542e40c3c100300c2c80c508030280e10054241c1c0110344011411030341c81800030180140a41c00c03503103180d070b4840104014501220200e05903032820301090090340b9264000c0d40d00a01c885003150361114290f00090304440c0d20b02404c0554a42d2003101f0011804d0201040c1424242401d20740c10b40c24803882c4071010030340742c4040300040010711044c3c41c08001b00c21000381010303990482c01d801103549400e0061700400c40410120701c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 936124973 1250 936123723 936123739
    0x318050f0d02010e1c050d1404120e03060723071a09030403080f0f04052e03020a020703110a0f09050702070f050d0210050c100603150204031a091e0c 66
    0x61142e0050242a042d1100440244a0a0364032440c40d00b0503079030310203120f0030400200a40c681c2851140200404511745440c9203085041600d041480c8100c1c1c40001030a01405040f808181c0c6c3d0f000c9041076005080c1c0c24400c00c803809800000e02100b0042243d0201080d0110b090014044a041c6a9000507111150b172041070b2a000003444d9240030ba803000070005034081003413145031407100000d88600360983c040a4141a210700003ea01070020040300041043c41400175195020030b017103100c110110a0a0440c50161130002c000d40b18229030001401c00b80340f0441c40000b503100d00b42d8410050070b058190f800c200c0d8640790b00b0009807101f0782c0c8010040c4940c0c2c40202d00941140c44075030850b000141050f10501860f400d0207210755803040c001c02444414000c800003d0300500040c51442126a03000605504501e00310702c54400100f40e65003014414041800000c0018030041c0c076403508181c04401540d118106545841c64198034080c1602d07244581d0b001d201d03c0025000c016443c1150a08 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 936126223 1250 936124973 936124993
    0x602010b0306180a0305220306091106040b04031410110c0706051c0c03240527012102060706140618011401020304090c091e0609050f010318050f 64
    0x80c03c50f00c0d20084040305600004502030000e0302a0005201803a207100250901007030540d00c059121055500c207895140e1160070800402c0f441c6e03048001484d004480300d41c01c150804050360528002c9002c0140352002c1c11a1084101804002c0c000040d450708400740300f45c1c40714184034005900205000c6038544146040800c070a03019100741c84900350310f110500e00e04000091090040c00407680d20909142d525504400414100440c9900051085002c03030a600e103004240004070480960001d6121843e41c803001440e40800c1d0094119048800414280c0b0102c04046c40d174001d0100000b54072000c002001c408100440d0090110788484070008185640d0341420710501c2d401c0c0307480000395000050010300891020400310105044184100e070304050301da92110080752640c001c0c0201184d44100204074000344a054444600d0390840904c041915014014080000034000c003881444c0054240302c159210b075000c0001c00003000c40400310030000c0d060945c0c44503060440d407441c90140307031480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 936127473 1250 936126223 936126241
    0x20603070507051b10031805070f1a160b04051207050d030f090c0323070e160c05030d0504020f0301150e060319080f0f0309030d060f061b1b0602010b0306 68
    0x503d03803018105d2610341e031030503404400511500414100007010140314101240b81084000d01400380b1011132000c031f60811070a04480e007000354400300e4040d41080030700da46800b84a420185180e1100c500801503c076031800c9130816202d84010001c030b100200e803c106002001843c03103d5051581c508100d5210009a110f0070703500d1040020f88079001442d4104001003000c101060f0002408440b16401e106d8843e82c58142079042c3d1081111403950740074030200300d4503021502070082190401880054056950310348900401c2c1e204000a5618000101952580100303900d005100800820000e8031050056065141c0740c02500162028180000e45a0130000303484c20a81c0894200c0341c0100b42140d0707804025600542c14041c01c00002e004010120b64404003450003020880b000d0358481180032140022103009a10142078005603020801181e904111400c21032002c8010b22030b0f181071141040700302da21840c002494080e860700c2000807455410341c44090803c500700c00365641501e4080d88 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 936128723 1250 936127473 936127513
    0x91b030c120a0c1b021309030203091f02100209190b0304060b01140f071106131d16030c0c0506010915080109050c010c0c030b2d010b030a0c0203040302060307050705 73
    0x40b402c04120002440318080140030480403850b8802004140c14030020304c001815184107c10840240c0e2002c52400c5162800810152806030508100d922035180054000e40d18000c0500746100c46034001000031f0161960f5041c8a420f03074040481084007a03445580001c190700885080d28039503e0314403d40b0040d0710035085441c0c02070507200040d00700100316184130082e80c01100c08960140d15985003040716110381c000f800740d10690065114a9030314001410146806401040050080c00001c100300c0c40d01c580ca2440240146150000b00112190000d43c1c15050001c405011842204000144480e21f5040303020301103410b01c0d10b540310b55030b80d417007003426607a20500081c0b05400c4040c621006520440c90807001074014149140c445581c0d44844a121000340c6d446104411a0342031482e082000344042021028000e0381c0390007940c504803280c40b1501000e44662b500325122101c1010051080050b10043c0d44c00030001c568074100210041c0c0154450310f012110760040c0000209440c40d4458 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 936129973 1250 936128723 936128741
    0x315220e070311040f02071415010602060906040609050a0f061d01060810050615120a0b010c030f1808070b0301150c05100b04020c03070b0a0614010905091b030c120a 73
    0x305244042a6881007101414044075400004c550078071a00008c2144040940300244848001c0c04039a1214884003000850582014003994031603c01c0c04500340001800541c05600044009144082460324034280026000060b00e00c015030120041800340a60080e402d500d03090b10f000782c0240c0640b100d0b0b401e030f448e00d10951445400003849091103508a0308500d500c841c000b03000c15030342d281c802c01d0030382150030a2000c0206a55901c0c100311040c0c4039840349000040090800140a0344280d4008040b00304049401d410007502c02c00030110f0b0200900a00e009d041e14100743c42000e5210346081c0501d0f0801d1003142030113001e409107118214007070241c24190a4100d000b410201d084e884c4514064071710f20510707a400c2a402c000103800003805101810080e44a440100418207004000800f80c40e51074002c0c0000c1c10208106d207034142c6e00304081c0303c11504d0950740d0705030940c4c40121600d10301202c603085030a401c0f130001c204121004540d00402505524140340c000a031540c81e11501101ca80c40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 936131223 1250 936129973 936129983
    0x606090302061801020307240f05090613030e060a0c05060f090d11071715010e060f0906032407121107021e130b1f140315220e0703 58
    0x60644500c0101c2e80c042560f80c01801102c2c0b415500c1d82d2201d200140200141e170081410503005029164140100c42c0d00c0002c0c5c8000340420308013400d509444090151000216a01d003012003420180203282c0000190002401e4a403600c06100e00501004d5503030004485038000c0500040d0110300c0700c007040c2e000b40c0c603040040140840465055580c400000c40c19150b510411800040e01964010340c05103446018007d400e5503417400c041c840c56200180c10550700c104400080101546409800c042444011105039070a41c44401c00300b410710a01c2c07800d11407481515116200103407110300c85103019090690b1510f51241211903c00c044a4014503a078041c96000c1101501600d020701c010480302c0c42c070303c0f01441091405000101e5180c1c4200c1c181407120b8880c4007601c02c1c4d00c1c10245034620080f1188802000b020329030780c014001d201203040da01d03c080011011440b41c072140078030a030102001814992484611000c9101411480301c1c18481140c14036004d50080c1c8008540c420442e40c1c01 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 936132473 1250 936131223 936131227
    0xc05040302010f02101506020f0d05090105071b09090201020f060f0c0304061d07052806051b12090f1f140c100c0809030703080613091b0603060609030206 68
    0x1507030044984480b51440c0340c04510811003208600301103841110101050550030b0f2844034a007000c00b0b405c1041d28036030307084950081213008ac10a0707085001c894a80c4002d2030419616401450322000001000041891601e5081e0010400240d6640240c400f94001d8084800b01c01c0d4548449685003401c80704040320305064004140100c41c11800341d9081841003d020a42104412020550300340781d442c20b010300e901c120b40030070090510800d1420384010b030b04646500c030451080c041c20208154172801c01007001c0040c01a80c1c00000b0307541d00b0980d01c004011344060700e1480d14010303038070b4001c2d0401d00d11404034079207079842a00e448000c111203101038007a08a2803c2c0e02e18820b95074041c1c2929441c001e074a0410070740c5100c02c024005692030b000145000285005400300081c44070500400341405940700300032000200740c20102c5990700c5038044540300c0024041c001c0c46d2001d0900ca0038010541e101110302031520724001180101581c085a42c20010310344d950308201e07418811880069040303401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 936133723 1250 936132473 936132479
    0x305130c061d04020d1d280f05100b04060e04051c1806091805010608011202030a02060a030509011121060427030e010905010f0e1810180c0504 63
    0x8450103040420344400038095100d030382d008503041e640b004074407100c11641c80420812511640c0044800441c200c0000d201c031034003413220043d1110141a944240140084d018820000001c0b001c06149a102007a28a0340162a60300b40c054080a100a0310803424140042103146064121510954010300100102648007810030041890b111740102000000d031040000c0b0484281901c00404c0c00e030741c07440010703840c284a00c1c0001c18014010002c050a02d4010420b05500c92440390544641c144401411001880024a490080c60303009401603800b250008034103401d54003807882020400024004442e0408070064039201d460ba0380b942002040d0a01c44c1d9040948a103039500c140098400036601e2891102000e000002005440301070031180044002c0507801251408a10310a08140240b14149030020b05141c142880d01402c1080d0304854000c80d903039a5802d141d003054081c52900c02e90410360b04000c40504980030b0300d05903180356011080441c1c07080c46903140006440d5106803c02c0c1c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 936134973 1250 936133723 936133727
    0x1c030908040b0a0c140a050f010e060103021009031208150904121407060e0c0a06030c020303311511030c0d050c0c190314031915090f06060305130c06 66
    0x3c124506420450700000741c030b0010703681c114901c4e80480090010090f805c5240b421500d00583d445194606034141241c80c0b001d440001041410342c1d5040300c2c003401c00030302e4a0701100c0401803644040c0036000b114081c00c0985401800d81401381e95900d03032241049032007500303124810400740c400810a020544d1140440381c0325401021111030032600c0645844019100c1000342c0c4c4414000c40c0c00c1e0b03040131040200c0c17440c00e07440d50001401c5604041c00b00030140030029481e404007c2151288858821708104d008290b01c4030100600390000d004580313900c4e60304000c2400540c0c070b00903010316864800c401d008440c40d40d095130701c0303603212003100ca1034203100301501c001620300030b40300d07180f240300a01001e40c220700d0900c031604104110000c1d030400c8074000c0c00e000700103151001003c20005010010700c40031050800340c0c0c0400f80d550400c0800c41000d881001c40d6801880d900c641000c614020025103920368039003104c0d003200d0190f40d0600440e21401c1842400c1c008400d03000b040250300d00810881c282c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 936136223 1250 936134973 936134977
    0x90303051006030c0f1b1502090918030301090b0117090d020105010f0e010b0703020a0b041a0601050a05090d0314040608100e07090e13021e04050a0e1b060c030c1c030908040b 77
    0x224400140000c8032030340c0e80c3c0306945210b2880311a0701f440d4010032656081d08200e503d8a620070204051761554404d40c0c0030454807480180611100c8079127980040d94a40d0081e0004015041c41c546101d0051a008010039265224000c0f454015403d05000052600c01c04100400b50341c000c02403040e0341d9181c80c11071409540b00d503004400f94040c9480c01030119162191f143d20503802143c05e10481c108078440ca0189080040515052140501c041c1d40d80b0b40d0301000781d4070400c0003030342d9082401d104d03410f058075042e44207540c1314102e407000200402d965611501440c00360f002c0102e10150b00c0c0d155040740016020440d4031000182d0300074010000310038025541900320300390086241120285801181454285031500080001e144560420a007054400e4950189a8400400c000642d800307a9030384402d9580180100f2103da1907d40c080382c1d981764100c0d107103001d840c01100d81c0d645030069200e4445c00c0b800104900d204d8a90144003815000c0d00030400c80c4c0d80c0c403d0f0064509824015005070355 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 936137473 1250 936136223 936136247
    0x80c0603060414180705061201050d0213020a0f0210200328060e070c0b0c0a05090405040b04030f050c06040b13020a0602011e0905072601090303051006030c0f 70
    0x10540b91043d82240e1408860307014011168240d401c00005a0380141e9407400e003081c0c0c04107000790020003003610030384500c50340541580c034200ca042d140c505050000071a0b0300c0003860030214951000840c10355154010058020041d911740940d149000006101403c0f14410b0407511907810415007035010003507a0400441d8480454402a0f0307030800c0200c00100d4000014010406041c1e94260902c101c12910903000da010303806241200008802ea034801c112501c0207032141042d900b011400f40c0040340110250b402b90080600200601e240034185100455001e84050700420811500742d5800f5204004440e105901c00d0020b01064469540f641c0c0c009400500c5400009503486e80c2d4030040c1e0700d42e02070174020b01c060b50000c03c800c0389404455150b41c46e64101860854500168000011004a0104200c89500b03c0c0f00325440c8542e1403100034020405010400da5282200d036008140d01544081c5c05030301084c08680760786131542c5080e412210400c89080108040703280b040c0642d0f10031402d168007 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 936138723 1250 936137473 936137479
    0xc150702031c02030d1406090a05090a03030b0411030c040e010609060f08040212030a021c0207050d0213090b010807060f030c050712090f090e010b0607030912031803110310020301080c060306 84
    0x85d0850091041044412030b00c289a484040c4500340183c614010744403940010845608111314200340804540d40c204141c1c0080504d034941c4000f04141d5a9548440e528182e85040b00ba80ca1174040304006041d405401801e440381c108100124140741f04200a10541d02a0740700d094540c500e030481902c00324401042203a2012564100102441c41031018102a40103a00208007801e103503d05410302414240038a0119841000200b240f1b0780d607080210080c907019550381070207003004070200014003850314020345592006400020b451100054139001c80c1d07445d40d42c0714905441030344101c042c0e5010030010300000740f013403002c1c10100f51302800001d4180410b05241000c203555a04c12480c51820341e000060070303541c0e401d00d80f001850038040c0b070304045021103405180c0181990003400d00300f0507010725001100302580000070140030304c0c13030050700c14600c546200d441541d030329140540900602a8070701a0003603100340710400c20b460090ba4140c905080142003010000c6090280703a4000400301c540c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 936139973 1250 936138723 936138727
    0xb030a080705030702010908010c1b1103120c070b0405090408030601030e0f031e030405060c131a0c0c010e03060a0906111206010f050717070515090c150702031c0203 73
    0x814120003424010310a2003d55194245800050070940d010b520014082c1d0401c055204412ba000b001a00d6207101e01081000130300380d90030b11001e1503200011440c0c040c800c03440040c08411415010305500080c1200300d0348140d4807500b952415001c0c5200d165081144900842d0005010030040c0d58414010300d40080e5661180b00380c18a03008002d070505e9441c1d00002021454502c50305003a00e1488044070401e4550309003a60b4169458078002e0810001c0c08021900e017540401d404101002440b07103090b444101011404282a980d0043d028581c41d882948000903481d4000c22004139403840080190005039900f03410800a003c850300120340c0f031a03403603c0b00f4440620b00c901038101030f281c80300e801503185032400c009448404100302c260b0900c142800b003100004c1d9421074500724001e42201440c0c541140786061458494140941030b008668402049120744000650340b40c0b64034111111103402c90228003400044c42501000717034040d0012034506000b4032580071146d0f40d1074000d01c1100c3c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 936141223 1250 936139973 936139993
    0x303030908130b090301060602061e040203070807030c0f060f0909020901050904050c0c060609040b13140f0f011125020a080a060501030308220201210f021b0a080a030b03 75
    0x80c4002c00716400c01501d090000c030340c2078584c0c00e0910070000903160341e0000f0003031030601d0150610f0910403070581c1007a200705040003504548082c0f1400c40100014012105220f80341c3c40c0100c860b102e1030145c1c4486000300c00c2c0000b041d61084d54a404507106c5074884030100c42c2000500b0380a50b020003a0a8103100040010618540380c81c81420300c2000c07101121625029102c01d00b42c10301c08040d00040c4119801d4080c0400b00c0e0030002055001030080d000c0c541e080316613150a0066080311000160940078680c070068000901140701c24000483e030008000d0580c400b284607005003c2d4850001e0103150f040c00e05600240050800070566000038001ca100954480700310303140c807030b80000440d0b50980341c400400826401644094114218407c0c4182c01030719490702c0c1e8071101514102904011026051812a40c0d0002c0d9800710083c5414090002110008501000e58031442040c0e04200d24402a504440000b00f00001e003a070340f080409261290b00a01100582040b454890341401142000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 936142473 1250 936141223 936141247
    0x5090409030e1e040506010302070803180a0b0c03060405010812071401060b160302011512022e0309030e0607050705060a0210023006060a0f020a291b040303030908 72
    0x14200620701d020002a0003030070740f050209070340001d0b00790b506050041c043d00000964600580ea400701c103a60b0400d4411721410121840c0c402c0c1d40d5005000421100e00344100680c80c0b000440c0700e0401030300c062040e80d0b6100c0b0b005035a110900c242c7c1c400b54009000010000d0900900182c0e83d00c0e1a90010034501d8440c0400ca01580c0f1400e0b4527403d41190f900580101502805404000c0480912940303d40c0d2801e030040112071006540248100801c03800e140d0b544150000c4080380180d107076044450038510748805030060034400d8095011406400b904d844070b29055044500c0e050340300000d403428600d000c06000c010f41001000f0820340c001c540c5c44012450840c03001d00b082240c0c900500e068540c41500c1c1d00881e0081503203500520180c01c04000a54035100110b840500b050f151941146845500403400e016110b03000510342c0048401e9448918003021a00400e0b00c1c1401e4800e0305900c50031140f441001050701d0341c8110100900041021902a503c820921401140340510700011280e81c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 936143723 1250 936142473 936142489
    0x703180b0901020c160f060822111806060d05060d0b070e040507030b0d15090605010803091504150804030c08031602160b040b070807240b040b0105090409030e 70
    0x200c041c039a6001c02c0c8035044540401c0303106011504281c0030340da035905050140c494903d0034003500081c03145140c041f6601c01410021034000354540600c0d103800d0740d110f2410b40350b0800041c1505116402d03e0300340c80200c10749240c0d0f2501840005020030b01e4074084108074030143c003000f0907042d400f000b221240d8002c20610380e45540719071203c2c0e1341d4052061142041108444025002e54200b5283c2100c0c41104d4444100359000d40b5080719142c640c042e24006070300064070045000501250814000240a15001016184922007100d90120a190101690350903020381d10400c41d0852412140c0b084030b5000d01320070381d0003a0080c6440990144c183d1607520942d030041d16420008400c09030400c5a10354148040380d181c01d80d16a1414005151600c044118080e601036130307650030fa00162100400c031071081200c007030f5a44003c8000d118030f040040c03c0191112503e0f244133480c2005c2c000842440c1c070384110617603008140c480606217103d5000340002440c2482046050250781c0c0244406959190300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 936144973 1250 936143723 936143731
    0x120f110d050f010614091503031306050304020906121009080910020a050f0318130209091006091203080106030b040608011a04060e070e061c15090b0d02090703180b 72
    0x500c041c2c46448512400c40b240c50b0b000691040003488103e00640d40c4091454001100a00c4150f117080041c0000b42103214000e0917409100084000103801d0342c1217805584114000c60b18a10150ba801050210105548040d002c10743c02c810f00000508815500000101d4010049641080e030094045500d90700c2074406540036910803411a000c00a0400c01c10354020850006503080c0700e03007030202d5020708011501003840b0b4011080945004892903050390254240109005c0c5181880000c0c000c0382206c0c1d015460004000c13000100b01c0004002815007455030555480000c2c4c0c2c030707102044000300285242d0035401501d07802d0000b02d18809004606d011011040300c1071114406000700000c0b01e8155010300301d0748004000b04070965411031180c42c80a5020394017555100380c8406411014201090a03841c0d05150880e4130220703110f10141841034034416842081600f6582d0200300421a82900c002e50010410340001d00c02403098100c0a00c0c01800c4100c2c1845480725501c880d00d0000031a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 936146223 1250 936144973 936144983
    0x92f090a020c0c120309011b0209010608071d0d0b1e040b0114240a0c15020d060b120103060b0a050d050c01022a0d080f07050a0209010b04120f110d 65
    0x81a021480c8000f0310210450000c2101c2074400000c0325140251a0301074103180905002c044e840c0404403c51009045c031003643d0007055501550384403007000d400c4460942c0d04a0010300381c440004210004408280000c40008041c503085201c40e68400120200050260154248034541e039000103605801f0607010368407558070541c807503040040b072a40d503130000010341384504130900701869580c240c055001d0104840da901943e46800c40d0200b13882208440c0305c002d01c103010b0032501b620121601e80c040c0c0403034000c1000605c922075075000b001d1241d0246003032680c03803003215500400000e403242c1d0051004520140c50344880c2030f52800022070b18480d400060b25240c01200c0598407640e418001c0c0074059040a031204035071005100e2002d102d462400480c1e001d8520104204180100c01d41554200803540141030740d21000d928003152240500d0004034041c83d1036800104000300ea41054070261003030340701140c00a901d079490f4117404070300410098070071602c0e9080c804030980301c003048404494055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 936147473 1250 936146223 936146227
    0xe030a03020c090601032c0102270a05062106030f2a040504080f070305090d0f02030106091e0b0a0807170d1b02130605090a0e10092f090a02 62
    0x105092010803c0010442410140b40000082800700030600c001500e10728004000b0524842c400b1841c024883c09006240c0c1c4144100c00c02c211418a61214180503420b44040c29442d55840c10302002e406198111141d0310710580b5804056400c5880c100d910000c003d04039000c4801044100b81000495407110311041d8501400c01c0342032099601c12000c03080180c800b04003501e41070310380c41414042c03031902584107000029550103061003542601c0c0c210768018183c4000b140130349000c450300b401848080b40203500305900002c1d2100248228151074a4410400b00f000210542160003480302c916400d074007044a400114101c0404c01200d00038182011404500300f421442c0c292400740740a20f08030401c000403c1e00841c02458400300600079034140c5244450700196001c04000d450148c1009401c06404020065143d020750040076416a5600a464a00425682e00d20665500c1c8001901e0002c04aa400f4403248043d014060035409034811103031345080c4100041d4810100307a4103d5509600 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 936148723 1250 936147473 936147493
    0x507091a0d1a0d0314070206040909050105060301140105010c15060f061e0c111f180f08070506030c0d06080109140c0f040b060d140f01080d1409010e030a0302 70
    0x45032040c0d60408002505002da80909800000e480e20b440841c02800c103c007816000941108000607108416401402c56403a40d4079240442d0040031206000d941d41d40c240008600300b4101845010020040c20708042c0c0c080c2e007000c0040d60081c2411500703c41040850404c0c121000140c4503d202034070b94022900b005e03e00d040c100030f2220014140030701c1081003030540e00703007681d410100c5e200d101640241d1b0040c007000e0140009100c0c04550f21000440310340702c0304581007035030700c00c40c1c00890b0b0703000780070001c0071130344515845101c1c1c801e9010310402175000d000b040c00546800c1c00170310b0384400d0511510b45403d030104200425101c41e5800000c09030345900b00c21040000d044034004140281000414100710044000303500010b00c9035046000b1945c17481c00d0501038a8840403516800c044040900050840741c980003000c4004503040640008400004258048089012416000d40e0341d181030217001d070b019494000d80e1010398040d042c0000c072044031865490900102c4000ca0294000d4075403070003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 936149973 1250 936148723 936148747
    0x92711211302040e010e1c0207090b1201050a060923131416050a17060426130e010e01061d03160e0702100509030d0504230d02070501051c0507091a 65
    0x80c187c5da0795190301b2401d00710349103000d50004480c0100d0b464a03002143c034400d0400030030005440c00190103555400e003400c1020b146500d07000700080700c14481c010400b0140440b90301030084071100003921012200070109408600701148000800e00448000402e00030601c1024500355002d91386001503030300d2040030000c91034404040b0006020305180a000810549c00d81b030f8440304014401041103140302146900c081050301d400007207001e10341010f541d4103600e585124100d90588110000140c0c83d500106058800d080d07414100c68154407070710000691401604001385501c0300031501032050303031030b0003261100c2890004020240c400c104d401c0b5003010b0800030708054840c14422040f5040209005108400108584c491341b6488000902c58a40d450a0346001c0c494040d910b02c0040401d402c40d584140205880c81080300355001c0300c0348076543c2e00065940f03004454410181c140420440b200201d41600b11962000103442c22081c029224401d80011900249941c09108404600104842 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 936151079 1106 936149973 936149983
    0x3120804030c120201062603040303050304050c060307030f0b0118051002070b040902091002120d050a140705130b03040f030f092711211302040e010e 66
    0x250003010085c007030200741c00b91180540f420760407034811144a480b000016400d04000c2c6040c41c0c95901e003944e031740d040100103941da40070b1003442c1c0701c1c02d81e98400154400c96441d1000a41c1070100021b0508803011400490b051028860a4052404940e50b44000325982281d9184a06108940881c14900181c1c0910544c003404940454400025006030101440980e1030086071280c2846c1280c1c2d554200c940b00e08040070810400c05407964641049901655044011408413844441030b4152a02150341600007840170840c410f40704007140360b110060148004407419410251102142c04003104402030a00c4a400d50485015000d0510003001b0140c0764000f110311202d8032a034101040c111b000b2000e07075525007002524104103103c00d0303d152981c6080740c06400c04140083d458900400b80a040d0141103200724200140e455004200b0009030b00000030801c0c4407c05a03c520300 = true := by decide +kernel

theorem cover : BRFrame.Cov 935971223 936151079 := by
  have h0 := BRFrame.cov_init 935971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 935971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 935971223 ≤ n) (h2 : n < 936151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
