-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2982
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:18:59.78849+00:00
-- url     : https://prove2.me/submissions/5d97195d-d320-4be2-9e52-a69c635e034c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 536151079 ≤ n < 536330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 536152329 1250 536151079 536151089
    0x50d0917070c060905090123061b1e01050603072c041202070b04050a050108130f0c061101151202210d0e030d02120c0f030d05071205010b04090e07 65
    0x28686039119401c00514250b030314012107000c1468100c0110307452600c2a007441c12a100d07625281d00840c400440114030600b0a0755450b084081401400c03e03041d11070020740f210390300000081c078210751466081c002c030188070703c00c4403083d0f4035003000d104441c0c03400300d040342c2640ca11084040c82c40c1512098041d010030852601c07000c1002110502c41006408503107612000016402c07110b1107500c07103000103221f215900c15268810b8004008200950095224a030b200385110400d4000500b9038998611340074015500b20391780301f8031030410300109801110b050f10282251000700010300002e41342c2c42e400b500500504801e01c010b003071030078110750306c80c0b9159840454411082001521025046070f0f00c0040011210104d10158604845070070005a0382c1007400ca607600400c0e298060800c000c9183c1d02002600c045401921081020128100010202404211000a998502400028528940454031a00d45400c0200410010000d8802c0d90180c1c1c0360960300085042c040b84060340782420581c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 536153579 1250 536152329 536152373
    0x614332d430209070f1e03060503031b06010b03010b0409020903011515020d0201090506070f1b03020d03390905091003061b09090c03020906071103120901050d09 71
    0x40e124041c62601a440254402e41d2481c0090b01c40c001c0a540c00282c0180c001c0c002142800b001c000414151020080d084442c100021110345407000301e419a480f40c580c140e500030501114029101c0c08120b12030050400030b414609650410394040b84a00c914401c800d915a004200c4198941c0c082d480300d0543c51b00c0c0e070b5414000940c0d46040d101980c414402800160061200008202e4018020b01900580c880094291035892400988589001000c00410411200d07682042c071040611500a983c0c020740091441c010545001002d8480718042c00010800707612800304050380e05004a0002d080e40c4154400407118100c00b11400c4070140d000c00d600012600901560380100c03504500ad40340601414401d840080c00203000c01c0070351941910018049080800c0428141d034082d00c0b4803481840c02608d00040e4000103041900001005e40708450303001809001c601d003c0101600d08208840868107040580d40003810038025030b0b041c000c081d07480303604110400c8191001101e03400c0d54195 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 536154829 1250 536153579 536153677
    0x40207030e090a050105040506010c03050403060504030e0a03060209100f1b02040b1504050306250807050d1a0307061d0d0c12140606040614332d 64
    0x840c4004d41020300c565806203103814041091548504000b0b04115015210686090301c1c680d00e800007048018025402c206201e07505405580d103032202c000056001c2c1d040541c4a000b01010080b60111000c8140e05100d00319400c100046d81006903400080a41c400404211401e800400c0180442c000030550080207400180c00c141c0d03078600130300140d48040c0d04656180d13941460420020358851982c0c002100d04030003103070040b8810802540d21003003529001d401e002d1040100c00a80b8010315860000003000c18410351036040c1044910018001c900d0940880106041c061141250501c03d142c01020f1018200007480401d0803c0c2d401000e241e403506030342400c0da00f0169403052500c0802c0d4020300070180414241e2500d03000f10410f5403081c0e80c00d0b000d420481420001c4c0c20a0041e05a05000c102810a80800207040200311100c0c21141c8074507683c2c05a8442c22a0b41c4400d05070561011801640240350400308400355105d810541c500b280d26006011003400720b4000005402c07640350f000d05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 536156079 1250 536154829 536154841
    0x11270a0e01110c0c0a0503031b0a05241e0604020c0a1a100f030b01180b1002060601090e01080c040c020a080706060e280b0f03030309011505030a11040207030e09 71
    0xb0000b040809902010307034100c201020b0400c0001d400f01d01c5965032540c818040f940ea025600e190001209544c1c1d0202d039541b0500d541c8080c00c0036042d5920500b10034100418003134580e54160f8069125150f2010b4020042212003c80d00ca00342c0580882c0c05541c0c0407400d084544410068144001d411181a0920480c80312012420900446845402e05046200005e104816144200c00c0d260b002e041401c590b820000d03100c90110100c04003800007a101c26213000180c0303481c218001384841e964080c081520f0800000361012169030701480c0240070031401042140408281011441d2041b00c1c04901d840240a04034502a5551005407000200140d410200039456000c88111889140110b01c659a241c00c100083c195a2020702c0e801c85051000401484541d8071103040c642c001400640c0c041541c1011a207150801c6034500480c0e90b466604804400d01c51304042d000300012001812085042d5881c030016584000080c0d00440d000b054100801d80039003d154212107010f480d6541524040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 536157329 1250 536156079 536156111
    0x121e0c0d08030105010207080a0f02040b0d0b160e0d0f0b0405030f1201030c0504021204170c070e060405090115060f1202160201080603010b01090e0604090203030a090311270a0e01 79
    0x4c0c030030316015100f044800203141c0c02c081420000b21750443c001d494408a9a02880050400c0e1003403a0392191207000c1e150001510641482e00610400034508620002984050700100314404070510a0203201010304c00100014501c0c15071070760100181c3c02c40d44862600714a54040c44500382520f51010840900030034400308000e048038000c05c0b10b16121566030091004901ca440321000340c100c0d9510000e00855200703441d0100400034003000314948080011501c0c1488030a03049007140c060604248002403a0078000d071904010a90020440da65003001c0c00500c0108600c01e48080c0889003c46041e0030340141c505841a0034050019950b55110303445200c1c0907860361508901094000703000c2032081c101485800207055060f104e50108904241032011815070040c020f990050302c030310220780182c5092024000030981c50700d4518a040c1035103002103030490007201c1c060090065a0f60440c50728002d10303454043d800d0741c4002e82590385030507182e9170140101c01c010f5a855070130712203100c46503001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 536158579 1250 536157329 536157331
    0xe03030403020d1b080a030c0c0b1611010b01020c01272408010e070c02041b080402150f03060d110d0507181a01030e1509030a030b121e0c0d0803 64
    0x1c2c03940c40d030704e41882103440003d0202210501070240842404000946800303a849100ca02406090040c2c00080e250b0303815480c05011100c2001200742c0c0c00c030070700641c0c0e00100c0500f181270100e4000e000945600740005e42e036550821029040210b0501d032101a1004042ca45c20841010404202c40301d4132a54541d03260340071101300380c0c5050980c1c6007016140744601c50715810b032007008aa04103035840c3c08004aa1117207501c50305984c866920a0b42e8500074072003000e04284d1401546554400c0e140a004011441c00002240341002c00204410006020480b0807258005801c42d400400c942d21420680101c0008000060300b001019409a00f80580080c103a01250441040802c2c041641c400c400c0c15607120760320a803803000fa2040000d540d580250440c01c0004a040304490301c01c550310101100020301a9000c0004e5040003030150300241e07041c0240002440143c03207813a042900c038086256140741c5d042c94079407880c00c0311080c030306021801e00c918110090020200d442c501007038101030b681030b84 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 536159829 1250 536158579 536158603
    0x1050906060f190524030f01051801030f0f150f1b0201060f2903190501050901031505090c03100e0705030715230c010f11090a06030f0e0303040302 65
    0x10000502c1c0740b14504200c41c0b40007030041444907200140303004140100b41d4000c403078298075004c8000391342040d542c3c80e9002c1e6208200c0259803001552408040c4030724010385240c1d884203104d0070030040c00070541d9110b080706c08684c003030214043e10089050005075031140300b0440412508010121050204a81083c0c0c0c4090007c0640602240c201000b80d089a042d486440715a00300b1083c10060206455a14526102608484018010310010624280d4400c071510301320001e101030480c5604080f42320f004c0c090502510090103550454580c2da1030080400d0043ca1460380352000142e5080061018003d8908050129401c1d82260641c4001078500380c4a0900903114002002855140008450040b10520180380300e0020107032004481c28290350901545d0104100070100b03103480310500a04208a650000140d041c181559440a03514110064031180e9802e00c41c0402d00d42d180000d00301101c0d101d04000588083e007940c810054840e00008544038000402080b00745034001c11089a045 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 536161079 1250 536159829 536159839
    0xc06030506010e0906030a080f0d1401030309061403060f0d0b01091e09030e061303020a0e04051902130e0111040f0608070804080403030804020f03100c03151a1303050105090606 78
    0x140d805020003844101c5d01070303915502102d5141d01285600d07000b0210041002102c0b45021034100c400411356010780d076244900c4001c20010420f160340041c40401918292130403032a00c1e05142011540346c0000b4000c24807500308a82d0021060f035940681170744503035009a09400e50740e55000284014003241c001c01d24001d24940301c40c14011218400c140d070311580b41e211035405003c2001400000d40050800110741c01c8010004070240eaa01500c040c002e0001460a0409103031034600fa1781840c494903000500c00703010b0f880080050351a01c6c00050220b81409000521041c4402c10030302418080f0034120401c0d0000501003080c2d0102002c07001590f0054036014180d440b049800c9410740021180030b820300000b0301040c00001c3c0f0036006650041c1c0010452074141a003035000908040742c42050321800c1d039407001451a49605401201103520b918040d800b480d503d0008441102c00400300d400c0d111500010b200f8407010280200b1002840e0000300800c4146001c502e0a50b41d85d81c184c50091180c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 536162329 1250 536161079 536161097
    0x607140c060a0c20060a15030506010806060109080a230c04090c03030f02031c0b041d0715050403030801031211160e010905061f11030c06010e09030708031b04030c0603050601 77
    0x140032103490300e0382c8950368005043e17658500740220014028100c404407202298840000451381c2000140e010b401040c02904d481e0400c0c000143c41d05d505030340f014101d40c111041c00008940f82007400e104819880e480c14460807010450141032030700050a4950007403402a880045c0004e4250740001c3da0300c640c44090050f981c80e4010b030303036900600480e95480c1c0c2c1030407200aa60344440d00903800c9041e01800c0450100f07040c00c1c4890001d601c210b42e2032a258000041040341140625074003a281c11b850412034501425501e00602d5004140400f41100c0c501065964180c0e2044a241c103006401006489a080c040c80380702c42509420b00c1858081100c800005c1504065445494021040105203a0a06407041409a8280c0d40d000a80007403180d041c3d12050a6107084c4001c00340212210007038081b0350f041c01500d41100c000585200300f80d034800d10410340090096000c891300b040b60180045e40c0d22a402d001d030340881c400d68000405041e024072001602a40582102740540802d0f00c40500c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 536163579 1250 536162329 536162357
    0x190e070b09031e07090c0509041a0a05060306011718061e0108012702191401080108030c0c0d1401020a08070206250e060c0111040302031005090607140c060a0c 70
    0x303c0040d9000300c0101c2e04011030400450442d54041007645030381e414140c0c201041c2c100000c0841d041341107110410b0700f1054481c8114030300b910022001e40300c1142d01d1811810300500090900c062895100301034850f10000c1a030840b80030750341920108006c01241e81d149440c00800044140d9020307050b4258206400206030172406001d0b404200c2240501c80c2c0e20f00740340b041000200c0c0a03101050760003101100f080c1c0d056001c1c00040c0f40207811042ea4030324207450a00001402c0702c10503800358069030000d2140310603a030f20100c0e2040030141c2c2151011840d04050410445d070700103122100b4100c0d032000840341c01c580e80040103203208420903000e640180d03903003000380c0142d400484103280c1880d0280040c41c500038004c0069264100c0040c140c94101071810f240f950860303645a00d0107628240100341003085280400c51107103d17810b1030006101604151510035030b03c00c3c000c3c044100f803041c80c2748441b240368401010341c0c000019807011113485003408200000242419850800069a104040c20f6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 536164829 1250 536163579 536163613
    0x18030f0109050a290420041107080f0f0310062007091d0708060103051905030301061b1208100518160c021305061c02010206190e070b0903 61
    0x180c150410043c0a02104030f6542c42d015a0004400c200b510500424440c6640c903c4000c80340310303078890a081001801c0240d1070b20412040901e6503803080b1b0a1143c09081e5464030410398003032603440901c2d0b03a154580d003d0000018040c05038207440c1081c02104002040c4e00641540d0304458840c0c86440e0740803024092042600c41d034061001c5280c2c4007150400c0388141592110f8041d0102c0740645141300b540034541c5e0b080001943c000e4015911000040c801d1240611560fa0f501c032842c00100c124441c07665a45889000504c80c0c0c034103018a54882c000c1c54000e82c600c00c50204d45c001c2d013150090b2410070010344118800d81c0d20000402044c00e002c14241070080300004190500e0f0401041941c5085504401040d10442e03002040050b41c010341c0140c4030300240286c40d03008000003050500d0076074144034281d035001c4800001c41d4003035402c0c0009030340c000c01d00c1a00102010107040d140034406540074050810b1000c0c03014a17125100b070000b074491101000d8842110300311b090300e4007240c900b0400d039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 536166079 1250 536164829 536164841
    0x50a0b0a051804050715090e0f01060f050f12130501050702190b0402030f01060608240f060304060e060106050919050a060c0317010b2104120e06090618030f01 70
    0x6038101e9051211040e80a40b4080b049601503c12000c039225551900c11b034025031641a90403c011580c41032080c48a507944088141d407040031564045140c0d89089401484040100030320001e00c100000d80940c2c03405030344215401c01c0c510740000c0310141080061800401807110042e00e03d9482e113000305d16628804101000d840240781c0703075804207891350340342d0707101a800c05002280d1501c14402c040203011fa0a000b02d90090032a0340341c08080740340c000300d8000310030030104801403110a414444442c5030341d02c00c601c82054000f9102c113500c0790b0307031460140300a0010032000794061161100010368a51301100401140303d00782e44c0ca81092003840c000b0000b4a0490050356400038820000340480c40c030500724000864047d1409011828140c0d0003401030381c0c003e0b00100300e2030b040003a501031081203003010524002071070707001200a440d20341c54040082051545c034204000e059126203100765140d005485101e50002c1269580d8582130004180b082003918400e4024050003900050002c0180710f20 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 536167329 1250 536166079 536166089
    0xb10081e0613020a0b0d0b030111030601090602060108100203071809050703180b2d0709030b0702030319050a1d030706061a030402010e04020d18030216051c0f0213050a0b0a 76
    0x101c151070405c26080c401d508580c400e40011503450494501a69090003103401007071900c0061a40d07414000700050459805802c00f500b51342c041001004400d00025400032000d09044005841740c07143c40c1c088600c490480e07a00c0b00c0b20080001c01007140c5180e030b8001e50044685071000c100f5004400071032031a03884e5002c0040c08501104000032000003c002001003000d000c0d1035040b03100a102c800b94030780400255580340004000c18010320070404900d02403a0072960a0000f503040d40342c00841c115441410380f0340310905546510214202c2d9040e81c1201e020004031441414403002604001c5991360130000041d82c1584c103180300050300c06680300c00c440f4180040764500386150f89a40040d1005d03903141000581080d8200201c028010082c0314140444090118100960040d8100249014101c0e050001100c18060040000c0da581180b030080358510120340700103400303250404040c144400d501c040d410040c480c0d0b900d041c3c40f100d075000300e1181000100800c0b2810207801402180982d40c021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 536168579 1250 536167329 536167339
    0x20f030f101b09090e0106050d060506040507050705030921010905030d0b0111070909080d050901021b16030224030f1603050f0414070f0b0c01051e040b10081e061302 73
    0x44c80b0075507040e0130103031203c004013001103043c9540c1d8000c240c0c104956031040da00f0360b588406001c002e2070700340541c41d0024018a8400c5c205030b201e0f11066105d101c0d00742614440c5074182082945105221600891002601c00802c943c0440f0b041c420344942c00b40c420080394619100c0c14407819800740001003550448103004107411410240080d00030a0b55400039140701078140190b003a201040e014451103883d91500168690084800e402d00704200345a44480c140c100300006284c00c0361030b207840740c1207940441d51258030210403d0b5034050700b940300310006204100002040854007613001c0c428060000d0071f0b140c944003000c2540403070031180252105180c695984020602284440244803007190500e000c1c0d403482d0b9501e8204020b6141150b210034007264010428000c1101d0030302c030b1903510452640d1255040c02c150740e0340c0b0210704d00042c001082c001c0e0190118444200d207019501c054054030741100c606928000f41c09039850600741c007600841c0b0510001520b200d62079159803800f690301400e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 536169829 1250 536168579 536168597
    0x304030309170a1707150905061311040c020a021203040602030a0f05190819110d09050f060c12221101030213090917030121020f030f101b 61
    0x80e00c0700d8010255070840d90510542040d8400316000b030720144188815280560382d52620b61606e4540f00d00c60141c103007003817840c01170040c6c080b810100e402a4060070b4102054024015403520400ea507845508541d041840d002c41d00f25159000100c20b00402e000300c1e48036045c2180304410a40d60f204601816006070018011000c070b190040d441a41010040e041c01c40c10500a2101082d840d00900b1a100000756000c0500c400c0701040710080b518a102c4001c1030100700101810151b040c450141c0d540c8845907030714400070034031500744002c0d440c242042c030948856052031040301d01150000d420003140080d4a00204903100321945012800100110740c40c00c40d503009885201802e210075208030306151302040715002d0503040184500240c00c1146000446003400d04200c0c403411402892160f04060800c01809404105a12404540b269808980b854005803000c03c8102c4010f00742590584075201c00001d51000c0031a040d554100944c00401c901a00700b40b40282d0046042284c80105d00686 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 536171079 1250 536169829 536169839
    0xb1c050a03031104090203151201060b071b080a060c0f0c030e0d14010c08040c09060e0c13121101030506030c061c14010816140a0b070609050f0706110304030309 71
    0x14101c07443c00303207041d803400381003903503a210080903a07100300c8015024051048894242d403801000560202d448070000b080000d041c09905641881410b0303010788404240401c410781c00c1075801c130400241295000b9102d8680142c605000501103052410b8003084030340900300c003078038400d0404c8914560035a48211044a03100c090146a001d42801a518414000841b0710b41c002c9c00d003c1c030751782c400040e41c07481c4840c81c1504003440a429950030948086003030210822400466181450300300c41c103450b0303840e0740d030402d105e245030102419840786400741151840c1c0301c148296080e58006aa20a803418451030317588100701a25050000c1020b60711400a003c2030304000960104c40403c0300c3c8800c9c0010780c01241991950780030343c090740011400d80c8075042c4c501102501000000040c15072540d200340a5212900040d00c0f031940c0e002e00031814002017103840900103141c00403621503030044103031041c07105801441d51311103942d40600404140211014070052200008907011a41c1580d50a12014202 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 536172329 1250 536171079 536171081
    0x905040201141303031e0519020106081c1115150a030501050c040312090605041205030720030106050a1a032509060e0102011a0105030901090b04060b1c050a0303 71
    0x14206038104585112071600412040c00240303040294449a02040c0d442e61a00801a036002c1601c0403c242c0c91a4103603e040d50441d0a840d01500717020006000c88009807001c9006201983c450398403803081c0c0207002200d444074500714840610716074071044502103510900b5034420400003007459081e50040021680804112610500400140303070783d175010340d06d4440a003502c10036202c2c003c1c00c801c000307000c0042044075880103480026504010081500d0508081c0150242e481085402090b10000404000c030600c1112131690b4000300c0c0c021080740b54101c5012010743c0c91140d5002c2c1d03190060210303052400d242083d04454080417a9141d50006106100050700b005d058107d81c0c2c80c0704440414101c007107140c2420404000c3e034406e080b02d46444030062180c0030100c1e000f415a454a0380c030201d0103140074801c5424030000e0a2450380d94a590440034010001801c010380b140c0c129109000c1003000e030350400c4205203030896840309006220341001c259818480001402d913070202c0740200c0082d0003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 536173579 1250 536172329 536172331
    0x2209061d011a0c06010f0e0907080607080c0c1009110f150705010204080709020a090e0702060a0c0504050604030303091103010c0503130206090402030a230910150f0e0a240905 77
    0x20b08240c14400400e80c0c0c1841d1410070b8110080181c140103007406564400082d00d036000d02094010101c5914000c0c00949440e80174104034200b00c01c0700001442109424100e80041c003104003120701054411245400402c001c24044904800d0038a200c0c1c2c03146003010310000340071001400320a4078a072444218403941c0c4140d90484903550207000010710345805200000c01022030140250362000d005100410100341030b0000d441200c1120103000b142580003a0013a808441d981c0c002502c1c00d1400030a441600941d442250b02c1030b4005404400c2641c180c0001688a124041d6085829201c41c1090300340c41c1106404000150f05100051003c400c560030310007450b00281100b40381442c4280407409a07482262881c07038140e181c00500441c40403000c0403050311150306200f44074038140401401d4940c044000e00780602e68403100c0b1715040c61030900e580d00080c003051801e600a0b0740c0e00d013680c40c9140006c48040642038640480c04043c05901010201110701c00c54074040200d042c00d24140080070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 536174829 1250 536173579 536173619
    0x1009060e0310060b04090b09040f03080a0b031222050306041b0806150f180a0b0a0f03050609070806040201121107020a0e090d0203070f11062209061d01 67
    0x840c0400080010403940700f554060800300c00255511820320441c1010744005031503442c060b081410070030012500085083d1126541881d1510803600c40d10039220141940000c0e0300d50502804c8510040030810304003d040f84900c0d41880801142c06403030b440b1405101d40f00345a01608030720700280014142040450f201d405591061600c00c0d100c400d550300d003100486104000170b44030a68103003149801030075160307404c0b411144800c855503103845809a03c0c502510702c40c0e07025210034900c40749640e00040e2002070680d03160303180c00a5a90303082044e0b582c0d43c10748213800c81d806590000308032040d002c2074103482640c0603103030401610b0741200000014038074407420080130202407183e54011703524050395000030080b600401c80c81d070070702c5080350303043c00e031046c84404c190b42c41040301c0070000300c40c041420801ea40041071111080805004a0303a0b5100705401819485c4500c132508407120000b01d002002c1e5900303a10300b080303055210005001d818052803d1041e005541000400c20301d60f0840c00384e28500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 536176079 1250 536174829 536174833
    0x15080c0d0e0307060605060a2f0604060212240d2d03030b03150412020a050a15050c0702011d0a09060303051215090f070c0f05010c0206061009060e03 66
    0xa0641904402201da400d140c14295410000300d0320b09010103402040041d0004541d0140740c000e0703544002d8400c0a81441d0000a03c8042075081108501440d0840c5a5403c003415034000745040d1401800940c09081d0f031200720107110011800c0c880303031151020048130b8111604402040441c080094034405080c0844064040020b44034000c06800705040f64036030074021201d041aa20b14004d13080d0b6050114160007648035103541d0840340ea500660700d400c6a00310a4065401c11800c4080303040447e8440f0280081c802d100c1001700300402208058514200034008200c2da07212440d0b0301d8000e03c2040406800281e0b030120f141503020214401140803c0010092403c2581d41c04503142654032662055020410120354600f141c803031000103d620451075901944c2e0220701000082d01c0e800003174018001ca076074242c0050074283c05030f41110403244d04039282c0c9100308014134000d4040e113a125500e0005008640c08546e1500b0401ca1803000c44c902074407030110381d50810341300300e5070090304590b11a414 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 536177329 1250 536176079 536176087
    0x3051e04051804030f0201050c0d090f0c0b07060f0b0d1101170903041404020c07060c0804030b1306140712111b0c0120070303080a02120a050a0b060415080c 69
    0x1961110002c425003504800404418a09820050700c1d46040342c2140040d641032404129501c5c00c070300d0844a07411032a04000518080b1418400c0d600884148002c20200d100704002c260034000078080c01d029841008148130840c03565000500341c0e81802d084640000f00140410000b495240010406250614118490301c4035040c1084a55805503603240d080d4200150911040404608244010109a03410761404100050301d81e9102514030075030b0200200803a0314820800c017407046400035504490044418140b4465890900003001c0c011124103182c03800c000400110b8000b01c5125001c144c49842d4005203031400c1001801021016641c2c0402c1003103040040100e400c80380ca80b10008100030300746010407030700141019146c51691203482c0d008140c01d500081d40016158140e83d81483c00902540f14020b2a501a010311001a004009013000f000200300f195445a4401d10001e007061240c0c1180100f4270806100c1da010340c01854000f0142d5001890007150119002004003a480380380c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 536178579 1250 536177329 536177339
    0x10b09180408090109080703020303220b07050309040f140c0c01090501050411030114010b0732210403110d020d12030c0e0108010e060120010c050417030703051e04 72
    0x30242168211610030020640c8003482d64084105405041ea842c010603c4906540000e50340e8010401c00304000021544100c2045a140d549034000740040000c4507120b84651402d240c82e41c01111040e40a00e20703105102c075041d0b20600845410742420b03140d0110344d032140c03031340210b203540441510480c56494550303d00000d1024840c09106d0341c0202032105803002c501040500b03456002403141c5030010200018840180424100c804c4158841040031400ca0340021480040b007403c07039940300b04007080c1c0d0326000c141c10104d94031507180b030044d801544c45250761507866001d00441c000641480f103264100016414080305800c21980000c1c9184d00c1a0310582e14482000c00d040c0d000d400080d15002c4071560a41c0162144084c21402d00f41024190b0501d114680180c800400090400c214071203410100205d400c21100c010001070000e01c9103070408400600194414400d0074034041c0d0b00200f10711442d4000c0284c8507103590680c2d800c2d207440710310000d01c03001840d88810070544080030000064 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 536179829 1250 536178579 536178619
    0xe09060d141501090606080702150919050a030f05040f090b310501050609010e010e121c020c0402040305250504050a0c08090a0b070507170d150909050303010b09 71
    0xc611410b00b21410515030404440d1402d60b40c05034810824810030324213100b42c540e0041408603032031545e82c41d441201d0752000849803a1805501a294559452043c200180300003c61844000d50103501e403c01d004260710021145480746201d034607140800840240803104c91900030341c05410740145842040013000100380d8403506102d4902c20114504881c081001040340506801014100c0e10a410403200b0300010b441c100c0c02c9514107040001214600c0309030780d0717080d80b1800007034007000446801c240c0702c0d402c50500314601038011015205007007844149181c00e008840030f40350301078040e0000d104800724090340c042d0305001d4020058581240804e050300c8e14800da03446000030000c00318010061403000341c2900e901414004580e006800500003052041083c01e811041c1031174100d6907440c00d030030030f082001d030204400b000700e40c00010000c032a02a29000032001800f0701c0401d408140c0d50304008803c854110300010811307002400100182c41c0d07070b10302a20001001030400c030340c0e000038040404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 536181079 1250 536179829 536179843
    0x20c0f070f0501020d0207180509100f02030a3b030c100609060b0c070311030c0904052812030906090209130b0c0906030c0a0e0d210e09060d14 63
    0x103150060507408201541e41003151020b809068005802d56909101d0080c1c10700e40d0440481c4191501c92001c103040c00420804040706191446007001251711980341440a58819551440220300300703081b11a0b00310074404454401140040355030050482c0344e4008a1241e1008141c0c00980020712079441b052400303001580d4244000600010710781e040a04c89030498586400c4800e54071008d0094110148000420205803600700d144600e240e6001c20009180c01c18a082c0260080c550009000c2000703000507081501e00d0b250b2150184010f841e44450154904c1008060211a8541c3c0e5002d1024040c0c2d22900c0e6007409550301280b004900d4010800c82e41003680d2490003016008480d81c14000c0200205400100c02251549006000c02c0040c103c0d0101801c20b01c4401e400080300d074181409807189030030780c00003d007441a0400032802c00326080000802c0c13424100d854546d0407130720310703104440d41e58072030800a01d03520840d118403040c400d002c0c501c1c800842d44c00c3c944101d1071480d031302e0401850b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 536182329 1250 536181079 536181089
    0x3070f051213080706140904050a020d0f02090f0103140114060d0501030809030607090f03022101050103120f08040210112a041a09040f06110d0c02010c08010513020c0f07 75
    0x164040501c0d0140c0e5900d000029070001040109184031074046c100d0740403c8607055201220040703240d403a0a400d40009108010907041c0300703490001a00c00001e1990090114803108031141c1c00340c541031a0041d82520405400400c0280d1040d00512904d02002c5080241030307006450181003410b8407140b81e040743d0b020b030011b490b41d06010502040f40c1c90b080100c1030b0f10172071524105a90903c0c151a400d24428180030091080d010030900402014450319036820b4201914020b20240d45e41707081242000e000c049400001a0100c0c82d000f1150740543d0409000302e81c003412340d0105004000b02240c040b01c0100340c0702e0302801032450315a015120841800c0c0b200076013240d4035071607080160400040b03d1205854005000040710742c803801da0b41351520140c0c000d4210400c2c0030781e8191441c200e0000c007084a03840a24040104140d0171a1120382d010110408158008012810b10140292002d030303070911172190302000d8401015601d46894026015134141c07142161506020b49101c0d500f0300032aa041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 536183579 1250 536182329 536182357
    0x20f06210406090813230618190611061003020a0506030a020c01060609050a0e040c0605210703060504050a02131401050c1e1507050a0c1e0b06030f01020c03070f0512 73
    0x1031014881b4681817203400042032481c2d00000c030100d00426a1030003458601c401503902d00000341550b03214030b100c148030b081407004140c0105807100340140600e200d9030b40040f05031180500040307203038440c41114410349070000d10003003202c2d00c0e100401245500c0140848100c1c1e40070301c00142c0f100c00901906002c2c0c42151070301d200f46c9042100348040e036800d59005203a0303401400e0900011504d03c0d4034030002e0786c0b441d14105a88503440c52020155500b4800030ba12180400310800540343da041d400300090b60405c903810f011985500b6207400581c015000e4050f41070400401c01c0219646440708044844011305202d401d100f034461099081c00500d0301c3e4809210001c0584000150b8244100c450209040c0588001c604001100078071b103000311403154080c00b1074031084406024466800211401c07101065201c079100514000c0220101603d140340a8410f044d2140f81c80103041c000c0c3c401040b20480150305056a0f038883c2c10300f045010201380c6450040c0d0344d01043c0300044100a00f41c2c0980031075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 536184829 1250 536183579 536183617
    0x6040306180302010e01020a09050d0309150503150a03030f12061d0609070201021215010210020a022407020c010e0a080a05030304330905120313020f062104060908 72
    0x1406030075176551108002c000c6e44100040b40006410200000544d2420b85008505000c0f614054540341d50b81c2e002880c0044001d14400003c07580000110700c203400c00340880b20a00390a40901c92142020b000040c00708007961a0910410b02c41c0d007410111a04148001c60030f00da440b0f0900080c4149801c905405089c000200680750900f40240c0e90030034000c1c4021450300d800b40040c02c03502800a042c087c02c00e00d00a0722502582e01c20004284203501d0b0540441d80d9502c4800c01940e070303682290340048041140158455450142e4403040c0c81942c807500601003964000e001140d21602440800b54490240740001c6030420081040340d00243c860030085549041500388070100741007034a400d42140383c1e031842103941120710841c3307092420701c56000491460704520f07041d410514401c3c1005501c100c08410001e1341d15445c00351041c1c02d8000c0c2e40c0058509418001e00104c0d200d03071212000000d03c07983c902e240617110303d4240d80d03000d4001c5800044003421642c0303040b0558800000c050074003001c28 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 536186079 1250 536184829 536184833
    0x20a0203060c070c030f0609020402030114131e020f04092309060601121a030d051e090f060f071514090f0a0b06010e090f04110114090d020604030618 66
    0x101c11600310401c60071040c00c0000c0c82c0d4944d401040c4500008245180c020100c13800c00005410040c0c0c0c05a0080040d51079603180d0181603010700015070541d208081c0c0d1b810881d5801640d2060008403001c0141d0542c030441d092418401960000080c02140c14003084001070034206841812205810301034144400c11042610548000014285a045410036403c0c000e00342c0c2c00a0341d2114010098402041802e1039040c8100d4041d0804a1039400d0300a8540003c003003680040141046043e941d0004200c0c0300001000ca064015140040e0300100d0300300b83c903021450004060418407000306145031402146035648030700f002640502122094940103808051221000002d0b0700c014070100800640031550f500303d50392442c03400e01030310700350950340421000e900c0303024009040d84014006410a0800c880c044103000c0e0111819a0356403100c4440041941c4901c00743c807060b0402032880f500b03043c0b10804000c0440b0107000102e901200c10031001001444501400319101d680c1c5000861204080c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 536187329 1250 536186079 536186083
    0x30403050318010e060c0d2a0b01030b181b0a1a070201020c1f0c1b0608060a05030d0210051f03081c02040f090b030a0f080316021204210210020a0203 66
    0x104c80442c8104014001401c07a1500000e501d9070400c01850316041e9600c110140c0840d09140e01803282d0320149032181041400030400740c09040702d11a5007a450243c0c0d903100e168245403120003070b003203480d00032989a10301d1a40c2146080c0b4190300082000b1405559449101881000d50b090391401401c0420740c1c8080d5a018013a0b07011860050710a10340c40021840042c0641d92094105002d000349510172b5028048185030b103c54194086c00c9917031145444140180c603d52084803c0340c81000c02010104e1141408203040311510859001082d208210381440f03030261400400c440c40c1194102600d9444106040c200c100540c002c00101c2d940e40d02c07009030383e1140000c09a841d00740d580104010000d850031a0718400c02c449444100044902d2448006414074400340e03400707003150300e0520154092007080700c01940900b04003600c081c00e4200c040c0d001c0c1d0721001c0110104200e88010300c000c100e043c0d0451010b11030a100e440b0038130035401c20340e40001d010703c0105100200617801007905034218202 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 536188579 1250 536187329 536187347
    0x15041d070e040812070c061e0e0a020906120a020d1a15090a09060207050a062901050d0c02010b150309010c0302180d0203030409020f120105040213051203040305031801 74
    0x3010310781c070406150940b5808241d1042070080a8108900c90014041714441d10351454010f50013181800280c0220b0500b40442c408200151071892038048a800d41d0790000501d81e51196004d04064115a10350040290304c407103880551126001c0c3c0c200701401039880c9003810544a114018030610680c0c004004569100300420012801051207100c012070360350341900ca680904602c8000c20000720501d00314020b4050403000400511656001d03008015403a00301c610200e03406040c10320180c1c4001c4136071003540140c01d50720740440d06c1041400000b4080fa00178525600e0031f80004118507a148011039904801c4401520700032002105209007558280140000031039180741c10740c10150003800c045004d9020282a0f449940c9180c28401191002e2050700c000701106481103444d000743c0c40301e00b042da138028001c00d1515002c18002144902d09407094554100d40c0403040030940b414802406001800c00c0c100c01401e10003848004005081040103084241d001c10700c0e10318080c21840007400c0c000c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 536189829 1250 536188579 536188589
    0x70b0601030c020a0809030307140f0f0303041208060612070201050a0f1a10030e0a0f1b0308180406080115050307050901060c061119050c070603051e15041d07 70
    0x1003070041042c1c00329400500c0001d40751304031918075501e40740100002d00c1d506c04e10100504400e09020940310160020500d0b070500c8444e00d0543d40d40c2e120700700f0807540740c0c4000c5500400c511743d00341051411310b00c42c05000d0350180f00035004500d4a60310360a80d603a000030844400d00140c0d1a0030030400c0d01841800303015002102c1d1001880301c110038100c48549280e41c165034501820a44100c1d2804034400e802c540805079190040e80c508480508210600d4118100e05076402d21a440c28190904400c4820008490300f01c20040c2c1007140801001c00e26440482c8407a900c10384134030021840e10380070301c95043c01840c3c0018417403c0c1440c210901d070034a03084e540114821400e0038010008503070000e81c585500d40e400310000501020000c503500150141c1c840500105054000001500d50000000c02408603100304484020b66a100c00300d003030b0b88080b100c1d40560b0400012410501410000d4942c101c1c94a4000c01800c64240c000f04045908940000407070500d556001c0007100710030312811025107 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 536191079 1250 536189829 536189831
    0x201090e060a0306051f080307031701050607060221150405010503190f032f16030213020d06090207050319050a081314010509030d0b0415060f12020c03070b060103 72
    0x718284000034a800c1492002400c401d0329a40040e40181e1351841150800344000307014860145c5515000f0fa41e40c2240f41e044021950000c4101140004104001c0c1203403401403100e803900b401c41c1c1d03612000e90022400c1c0140c00800084c1c400310802c0b44000688240d00c0c181034004030b0b04015042209860042e400380d402600542d200c043c40c4c80c0480c9003088419004000c01c1c18411040c03600b181c81050980705107103448a0215001009a001c0a4050f00d14401004569040b0002100b002c0c480c01d241c0300081d4404000700d0040c2054a507a00908020103200c00300003001a41e9141c15403d1303a002c0e041c111110340000820010041000d80c495410245500e003140c1400c400e80c0c00030700300c00c0300544500015000ca1500d40c1c100720020300050891801c0307000070301450619850056030f80d08150030794010b083c202002144942854469031260400c06413500b454140f800c441902c0e010765004942e820000e204600280c40103007030004128608030300c0c0046035141d8075400d106203039100281501d8101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 536192329 1250 536191079 536191081
    0x19050402030604020105090d050f06042306161103070809041103150603041e050a060501150c1205070c0308190302040320060d150e0106020d020706030c030b1503040201090e 76
    0xd600c0c00240180c0c802d5080c2401c1d551101d03030000051000c1115580240240306800300840180c20200781c1c140146c0c0f240303459082200d030603188450700306000d4426407103d03804100055401102d0104080030a403071030902c001700342481d901c6103046034064202034078030050001e010503190400d4461007104461408050b42141440c9041c01202d91101d140706201e003038040041418070505041d002c180f9440301d20450b14054a41c54921788840c80313408180e1340c162401c000040d449043c0003401102301c00c0e0741e8070411a017805035903902c48640d1208040c1d0801030700344046000a05c445100002440c050070206484248442200030752100c1940084105401070000300009510440201e9281c51500740d2038070013282e100b01003869030260418801101341030207141c260f9004105030000c01e480300000c4a000d542e0700c80b2426030360b4404404065005034010201000014880d40c4210800c6250b8500407808030341c00d600058940d80e40607001d20f20b1144c000148003c640e00705a1a00c002d2441c48104045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 536193579 1250 536192329 536192333
    0xc030c1b0f0806010b0a32120406060501050a0c0609050c090103030228111c060609020c0609010b100807051c050708072c0402040503010903030501052d0f010309060c08190504 77
    0x1000c807100c41100d1f03603620204900c41400c440207558010400889201c15140c514507001c000702d403042941d050703518525009021449510a008448540c074458480d01c031002d00310303500e100c000d00702c4441c1606c0074000c00c1c6a072404c0d5600d0421f0701d4000c0d80690300802c0d080303901c40d40011605510402c2c081c064dd40d440c0d02080000e074403121801415000326429400c40c92101c15684100308491001000c0a28203440482d0400e4190b0140860303070302c140110f03900740d6074010525089940d05000d16a0240d620380f4100c0c030b8a8420080d1782e034401b032a03143c450f060101901c2d2018149004402800c0050303143c00c208010b259021f45859444411407038a1041d581c3e4203e8148000480c0d4020303c00d81001d00d0241e2013040e00e0300c2d01107900900014000b00148801400c000b00105002e0068500c03c0c00020141c4011142c40145403e001c220101000c120a14803800c129102180c94081e40c103054445044c440811a60322415203c0601500c594416141100405003a15180f10214810030302c0e000505c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 536194829 1250 536193579 536193587
    0x6060f090d14280f060905013b0114040b040f12030644010b0a030506070806010507240b210601090606050d0207050c03060405071a0a0c030c1b0f0806010b0a 69
    0x120542200000030706c0c40990400a0161900894109480301034804641c15028079603d20507481e1034904c8281d6220000c40c4500c5e080c0d620800500e02c03a666801c010038042445905c0240d045407140350100300d90401d40c1e54500441e26681c4036403003c0313591064200022605140da03900385050b04165940e088071f083c540070492003607440b4800203004403030040c044900e2b400d610030b001000c4001d185100b642d599241081e078a482c00c90b0b04000051110010a0a43d4010401d0f5010580d006003003111000c000c01c0d040c0030912404050030340b56a200d81c0581c09a03100c2231306441d4060034601101c1c61030500e090031249049010391008040c140b4103c0c0c01c0140315408000c3d902000001c0e200503035281c40500f06a89441d500307448680c0d140c010003062108001000860004507005807070702924440449982103458007030316210f8404031750340c00b040000003441b48220150b134910401e0300d1a0903058900080105c0041c41c0c0058035043e601600a02100c48104000380c01440b0b403500c094900390b00d60100034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 536196079 1250 536194829 536194853
    0xb03040302060411031f0f0c0809032b05191406030c0d020607140d09080a030503010e180f030d052a07050f03120610030506060f090d1428 61
    0xc2c20180075135810400d0b540d0b05000078600c1010185101c18080c1d2003641d0762005001200c504c0d130b4140e182800b813010a50007176440c248a5060100550b080081800b9030460042c1c0315081060f40000e68014030440c000d0318803401d401846100c440c5040841800441d004407202000b0091441c8a00c1d4104130660340e0000318281801000c0d58841c40d40185840170034000d00a00714000d001036000034460400c8880001c81807001d0045566007450246e5644003942c0320101c1030000385c0042d000b04014060000d401d0303881c80e0484039075580100800d07000e0f0001d90816044005450154000242c2506103000740d0081c2d83c0c1040714480e03200b000107146004400340c42800100d00e81c4011001c2104004c0c00800d200d4054115645410350307030344080200c0111342c0c0c4001100c0b00d61081c282541c0b9030358410f2281c45001d1113160060030b43d51900c10910940105a000f107040f00390702004071031000c00020340c10464650811007030001445280e1150080e036142d100880000d49039025040205404942c1501d114 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 536197329 1250 536196079 536196083
    0x1707032103090803090c15030105130c020a0611031626060102030d0501081f05041a0907090603060b0a050607212a1416090209040905070914010b030403020604 70
    0x45140d00c20410154064511000041c0020381c1c0030042021252011440071102c1e0350031101034110038482ca040d02c4490100380140c98100d80d0039501301000da500ca9000d580d90000c0d40c0100c45103241c80340c0d214415200180314070320140c42c1c04418000d0504403990808514007442c10b11048414084d40f81042e140c2c654851401292000808206140d0083c000c60788001588007042c003603980c4078450b443d81d07145000702c07043c09019982d80760801003a16103e258003880e032210900c0303c102c060700d805101c1f421000d4581d0710030b0701500c02d000840c08500c1c0724400c001e500c580c001148050490041060170341c50740d0701c458050b000c1003100b140000c0900100ad402542c240e03141d4103500f06041000c58900c111460b00680c0b070120b046645c4c04004004400c850281d1064400a00d030000c901c0740b141c0c85030150754108000303d100007030510101700141c016140c0050040e100141004054030396601d4003003207a11111810765030f807040101c006040c64102d409407165015003803850a103668007d40d60301d001000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 536198579 1250 536197329 536197373
    0x3050106020a2f060d090c091404060924050105030c01090810020a180303020a02040c0504120809120601121101020607050702091e0c090310050105011b03050d0504030504170703 78
    0x81403020048550f80e00e4078107003d0701007502c95001c0000c0c1d000400440f9000d85089a4041c40065080d103207019003010f107a41d21015885a0700c607a03843ca4042c00b215041240c400c072003243c8031070b50000300d8000340c100389440580125842d4501401e0505000101005a0400071060028010700c4030008203050840d1b003a501c0140d86051070f407812a140b1200324111005020701590000c00d0560005091030303098000c4a04000c0002c4604041e40d02e8440c900c1404680c2c800d4198820104803c3c402400742c0c540b0180c202c20720310020031380880c140102600042020045c000c111414005242d404000071002030005002c98103254902400600401c4c1c0700030310a0300382000084c14061000076542c10044082043c80c4a400d142032441201d400003c0c040d03020384101d00548942011500410741200e80c1078440454034800300700310002501b0b0303200c010340c01d015040003080b81000e0907204591140e402952019203071418502184004003180064030b90a43c07100c2c40c10b0005c81c2c45c2201da01006441004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 536199829 1250 536198579 536198633
    0x110c030a12020c03160305060a090c14031c080118050f06130e010c050a0e06040f0902092404051806010807030c14030c0d060f060f120605130c03050106020a 69
    0x4901d401080c121454160140301c46001ca02c02510178060305483c403d40c01c4d100c02d9615032000c41c0456882141c0030340151000541080f1128000c0c08200c4005005010b83e4041c01500060401403403468020134001050180100492408200040c42030f0600440038040c0c2d00b0400000c075030304200038100510403440b0446204100380681d2005884020300c20007403200c01d120810203862130f00160080c0c0040352407203100c0d0703605e0b103840d0040707070b05859142c81d04400300303400c00c00140c00940102d2081034108560000d003040c8080385070030f2104101c2e00340d101a9526804c140c10301140d0fa0100c0040d0381c40a00303942c18082c560f80c000780b1450f8070036014a000121560b07181412203011000705942a0001800002e20000d410040018200c5e5007242c0c0003842a01c2e5241e01e003010400c024800c0c0720005004124203016540301e6124415034800002d0003103002c5803105c3c000380c04041c8084807040703042e80d280800e40100383c0601440e0300600741800603282c80c0601ea141c0c411413603000401c0d0610201100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 536201079 1250 536199829 536199863
    0xf0c0405010315171018020108040b0402011b0b04053f04090204060504083f040504061805060411040603051f080d0305010f1805060409061b110c030a 66
    0x3140f0000506400c8003040c1c0b00090071000940b541205030800700d90301e003080004008041c003100c01e40d40031541a900c8044903603458884811000c400b5008a040019981a000049030b64440d01d4801500410280c1d4846c1454a0101d01c1d00c2c804130180104101508425810b103242c03c10f084440d00c6020b440390034407408000c1c100e4464440e980204a04a01c0480c003c10310a1344070016100341d03800320713007180c1e4800609100d000550b0380e4110315400e08001e9080300d0554000017012495a05080d000281c10551180c0024041d00c0c01c1d81c000f11810240b485000c5201c1410703008a03034109009607020884003919150000711842140111000c1c03585500210f294401501804881c1c1980309203440c3e41c003a15524415140c0d0b00c1001d035140024204000403c00c602501030410482c0d400ca0300411043c0010010b0078040d002c001c0080b5401a03482c2070f1040840d00d1401031500a2010300c50341d84182035000c0000d40b075220882900465907001176024052507c0014446a07465080a20340d21000d40d00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 536202329 1250 536201079 536201111
    0x103080904051902040909111206060105070c0503010c05280f0c020102030c1207050d0e0d0f0f051f0c050301050907030b0d1a0f13020a0b030c1204080a080f0c04050103 74
    0xf050031101c0301e40c40050001001c659552200300c3c010301c0780181c00402c100300f10400c4079407400c000703200c1d481d508481d0205010350301400c020700f00b05200b0003464001c00c2c0c2c0e400c0003d007124030341031040d4082040082c42b02100c142112120340041c102c2d84101160500300ca20003400c48601e148809d041c00b4135082c840041da8003c00030743c0d030100d41c600308440301f0b048402404032081d080000200d6044c0725103810201030501507582d0082402014100b06c84d405c0280d2a24020b8205080d03090760001c581b400b95501061040c0b046081218078407444400700e00002d0000c1d000c54100394501001c100092005100079901c200311103401810500e804180c604c0c408000480e0002082c800400b030500382c0500072134890f07031022460303c0f0b0203070440aa0015504c8000428031004d8101c00203520201e0003506010483d030400c082c64000c0003c040e640c0c2840d103441748507c0d51000943d015074011001240b003c44650780701071050b40c4444890250005400c0400b032108550042d4002c4074103154031028229440b904e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 536203579 1250 536202329 536202361
    0x70b160c06051003030809060403080f04020109080d030501050316030b060918060f0702060a0501120f2409150c0c15180f061b02030d0216020301090b010e010e010308090405 76
    0x10301d0800c03050818016902c01e43c1d5041c4400c80100c2c010304001148080b0202c0c0f420b2103583c1607192103506984081c080119442d000380704a0510a500307101041c482d800700081c8070200483e8500040f954108802c061030804a11000000b01419000a100003170300d01e110540c100034180e035049810b866100d480242c1e40000042040c442c4640d5042003000c1480c0054940910400d800b99029619070650b4041a0307a000d004058461401f2a50140001c10420440000c540608400d4000c040002038844100d6401c040089035039803a40c100b403081c00f2813224401d90343c5416900410004030070480c0076181902000c030140040717810110f2400c10302107940100802c9220f40946400c040040e181404003000304040544103580303007021400c0c11885030b00c824014405990011824a01e54040143c060760008070814001000302d0404801600d0034040e0030902c40c4242e040e01899030418a034124400816031241c1103251244004002107201801191100700065130007140a90f120040c820401035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 536204829 1250 536203579 536203583
    0x2031005040c170f0103080a081e070c1709032e09061a0406060e060d0605030304060203030106021c0c0314120f090f0c2107120501060911070b160c 65
    0x1c10841600b103400c1d484050148181512035040181d901c4050048120100c240802020180300704000f0040703034003c02c210b5904c90103218100c41a030811003042c0d030501509441010108241d00108010020032210300180100394084260601c504070300002e50303032400403300c0780141c00c038050210400c00119a9070030440000d4801440400c12601c0d10500919400301c00405107201410081e00c545030074040d110440300c0550300c1c50540c003521030400c04541e20101602c1c42140e0380b0480000d03661020300103013005250a8010b1034480d0b140040c080d0900301e0400f1201d89040045582903200c0b50403683e400e007caa0103181c11100300d203426891040d580308040c58111070515841c2040701c8040d0400f00c551040000c0303000e0310582c58280c81c0b1145d40341480d010b030661040000e4811251540150151003c0c00415030031100e20950342e41342d2007003e04a090055030643d45541d8140702850403805903001140c48002424030344142e80c0c59000014002812002c5a1030f01e409103000c503244a01064041c550b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 536206079 1250 536204829 536204831
    0x503070512030a0e0616080c0903010f050709081f090c0905160f0201020906041401021f0903080f04021f0207080313030501050105180106051e0a0e090a1e0203100504 73
    0x1101c468101e00c5420895003500514104110b00100f100e021400324007403418403460071415203981c1016104048000c00381318604205000140e03081e40e09006802120154000000c0c090900200c020040792454010014a50046000486018a4450a0003124002d50000500820130300c0c215a11003202c0d0301029400342440180402c0f440388407c01d0007600d00c10746403001c240200d160b050f400c5c3c2c05241029580324800f4402008207600c81c0d41080003406051040d6040c031111164003440cbc14080902c5e151401d0355a9035444201908001d80681203544411603120701c0c07529900040e0b00c00220308042426042d100c0c2e1200f0158000c03c2305101910b408001c1e691100030034030801416040a210640d429801c1400009a0781052101411000710b42440030141c0e0b03081150640e6590b0004a0752048460b00b400c1d220203400300c10340030700030f0b080607035913401c0c10012818108101868084d00000c59140f618840d01940c0f0450407002c401403403018405170b00c0f581da800144021009543c08107400c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 536207329 1250 536206079 536206093
    0x109020406030b160906020a08131d09070801050112064d0306030a03180b070804090c03053c0108011d0f0c1e2e020a020a0b0705030705 60
    0x440f488801d01c3c40341d421380b10161000f4100403411501c5109910510015801c02d4001502040d8002d0081800881e1440c101d89406d646002d0804508420107282c1a03009a500500800a005110890051150400034041d43d4108406002c9005c0d50020080815603201030103114208610f080007441000b049100e144801035400002613090000c441030f840948609800c202d64400c582030b2800780201a000340f11001d480e5070180c541c28800e51001e0404020305d00000740800c2420000c040b0704d881401c036261641d24080f05441910f62011050041c5401d040810410003890302459100c41c4035005040d0b401303c205000895496148a01c504010b04190008159400150801194042440d0a840442c22510380c85500c03044841310441c0103810400300c042c202d14124020040c1074603962221420b01d272503100043c40c5406005191f4842c0103080700a00303003141d01640801100581130000d813000040c00c1e400607021581c1ca01904038000c00104028080c041d080050b25445a8000211108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 536208579 1250 536207329 536207333
    0x6071b0b010321020f030a14040b0a120b01031811010509060c030c0601150c03030c11011803030f060506120a09050f07030c0b040b0d050408160b040204051308030f09010902040603 79
    0x600c540880d00c125a035800200302024501c001003030350107164044003550900c0c9585800304c40a00e500d55490b0723a030308400d001c0403a414004400030a254030245e00d805410b1070240c844c03c4c09842c86d441819042c140707001ca134015060000c555040c2903075400204180e2007030400d070058606001d00c20b55203400600c0824841c42c080c400100500c00c06101000700c4455a80e21440e181c21583d00000040008490341c40b1000081e00a410410007003100b801d04c10800c1d1025600c0d142142c20b600d0281d04d40008800400c0e052541501c82d0342031070584d600c4244a11030034030300800c401d8898024000030412640c000107118003680e81c4526142c07503012082c1c8040d450034a101c19a100603600090b81d58880070000000d074091500219412244803030030039800e10700440e40b110010140280103942801007000454a40d109152203036040c548500454021400c00303006100c11078000a046803129010310003100c020800c1c23503081d01d511848114500c43d1603030341e0405d270078094620060000d402600384000401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 536209829 1250 536208579 536208593
    0x605030105030f0d20010902100512010902030105010e010c0f1b0e090109150903020f03030a1d030918040312050c0405090f01140d03142206090806071b0b0103 70
    0x10480d038085044032080359100f1420394503440a2504003012450f4410360482e00f901210f442040d0540e01800080c002c0740c1c54000c5008448801c0302c00d000107600040303181d00d0480303034000c071405480560402c50131581040000f030490100620703128103002503281c95408000f107034082c1e1141d02d680090300021803401c02181c0080c06403203000d800e00c2c400e880f1001862000c4140b140141058010340c0c1041000000c002c214000c1014190980c110300a140c100c4100541c01c10065000d0390300c81d40c000440340c0c0c64181518005035062a250503581041084042550360f10084040004030511a451680ca43e031800340c1d22660542c101c42d00d000c1c1020104180b00c14000060001c441c0c0a41d0760682c540c0d03a002c070f260400c01090054030701d11400307100c1c0700c0e903503050120000e80d10b0b51090410081d1307180c02c05d4034440140c02170410000108180c0042c1542d00c1500341c0c500c80100401c5c03c0200c400c3e414144c0241d1242c0e4020031308030420220081d0407500034891204108a07a8001c0d540e4507955840c6e003400b170 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 536211079 1250 536209829 536209831
    0x12060c110c1309052104060e0a2301020304232b061e090c080d0903110609040908181c0507052707021005070306050d1203020c07060503 60
    0x2095640c80100031001000c5144103540030000c12161020280208200003041d280074143c41c1442403480196540002203480c0c2400c4071510085510fa40c90b24030010b0050035140c03040c80c01140510810040d00309115000c00100c2c142d00045501102000c1c0100d02e50301035039005801008000b2045e4003400504c0c3c045e001446c805a40700929070384907101c15502082c1d502c030034a05030074181c03840002184042e170100e0300d0900500300891240c1e0380d4810480c2581c02a10301030740c150401020800100100708034a010720991824042041d81c40c50b102c40b044c065000e85014094180090b141c66117560315445002e2665010407156202da05001010450304c000c50f2110b8064030f00702030b4130b100c070300480c0b00107000c200c2d03000000308032050400b010703c41040c0d08803620388034084020700031404c01075800c5c100504c00c0d441d0383d0040c000c1c202d40c1d41c01380f425503202400d0b540505140003018046600e8683da00908290080807650302040c01800c21402403040503111442400354035008a20b50340d1101c021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 536212329 1250 536211079 536211101
    0x70b0601021603032d12050c130905011d0c0a0e060f030103060e0d0e0604030f020a2106240b0a0c0506011502011413140705030114090d0f0206060103151206 69
    0x42c0d0750310a500340201c0420030780141c008042860030745804882e06c040d42140340d000f030014600c02d04001610b202070800040303507006031403155140c0f0014007030707441c000f1142c0f4a204009100c2c013000e403c010744500031512401550004002255080001c19101c08040b10100b00742032800565a42c1e403410590000d00d51a03418031a24080c039151a00400d10403ca2009407075002418585014510795a4400c264060032080b60001e1000c1400200f4100c03c0d8408140780e8000748022100050a15011040781e8030ba1034281449650950908070004903a01c101c0c0548441904499480780c071fa41041d9810120b140000301544900070022400000c074501d42c20048000d17030021300c00d004009a404013010401c80b01104000c0c481803440c000325142682e03e82c80c00801000f61010b954a840c040390035a103039014040442101c60040c800a41c034100f008501c1c15495141c01010407441e44c400948804000d840e55041546581010100041001c0c00e00001e00183c1c81042491040d441c00c0406000d002000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 536213579 1250 536212329 536212367
    0x1a0705090909060f0a0f0e0f0309010f09080717030909070207050f0d0b0a0203100905100f1203020d05090427060c02030f2703010207060e06070c08070b060102160303 73
    0x12840710080002c0d03c50246603502c84802560313540000480c010082c2201c0002903980340d040d442c15040e402d03c80c12024051313400155070385030b54680016010703200c4031440d0802c01102600401c2565408920001600d02c03402c030101c000303074040b440f0794518050442c1a0390b0000c07605c01032016180c0c001951008503103080d07412200e0b188016040010103d208035028100011580000302c4643c40c51b07000795032041646440781c1e6090703140c00c1818200c82c002c545003035030b0b0031038041c0a016511402d003400c0d0040c00300b520254015800c0d0355009480d55592011001808400b03c0c00d001580da50360000da108035840511140380119070000d0345141004903401fa1a405d14141c1c0c80e01405101208540004014903000d91400c1020010a03c2d2404d8100107030742c81e142e0305640c400c1ca0390390a000800900b030007400d003c6400240c07040d011342003003c06030042c000c2c403104280e03d00010b04903000381c5442e250003811000e0540e030380900507410410b007007038003620f40c56012202104040c1c000344078510054900203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 536214829 1250 536213579 536213581
    0x70903080d05040c050d03092c040302070e1b09040510120b01031202010c14030901060906080a0201120b0f1509120f150105010804080309010e070807081513020d1a07050909 76
    0x406c1c407000c095030a0f00a000120081d00602a419260700c200804800c3d42044035131914000c2d00210310007400f52404c400507042100d00700200c3c0c200d480740e550045240ea0058405910910780b0740a20b205199985004940300c01c0019513900321052040010035401202c10821086407803c0d18105200340012038202c8101190088880d10520a404901e145500c0e59038100c070680d5a8814250801000d07045950340318040840c000c2d80302d01441c0000c1003200020040101c5510001d005208d407003d62480551609101c60025907641d0640d420071030044e034418001242c600011001c51052481254000140092072028001c00042085802103104151076022aa000c140d55491800303200307003400184a1004100410007540003940c003c00740100001d814500348034102e085c900f055220105039003203c2d2040240a00620007103081c0500d14a022946141c10700f1035502601c01c0f040068001c0030003011001c00c002c5604050350b18a4503404151070103241c480c0000306542c0c004240d19003c0c0071410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 536216079 1250 536214829 536214839
    0x1401110d060608150906240706091a0702060703091a2a090f1c0506010303111002130909020a090906020912030c0c0621100303092705070903080d05040c 67
    0x540e50354800342c0d00500450342500c84004220a01440c2c1017018845647c2246035030604d08404001c0010703900c100804103c610040c20150504500000c5c425024074000d020040560340c0030602c968030229a050000c0c0718613075800d020303100040c517100d60542102c221080c030415074001904820040c040540e4500b295051000c003c01c2400b88422032500307c082e5001c80942c0d460000d00894481481c0030501c2c1e90358003aa1103080ca00b0000380c2c8254003041c0e646642d046078030383c00d110a15070031161178010f5180440c0c8480031549440140300309103030140d40303407481340442d030700d43c1c91b25401401854018400e896843c18104000e6002660350381c841c1114085c994006400402990700741988030780501491250b000900405034482d0129200124a950409001c0696105014020341451050102880c1146400341c80c803007075038010f03850285c65040300059100800e0b0042507444503411001c54070340c48140d0140e601d24043e410050484001241c540b20900a80c0d205078400c9000c1c43d01c1d000075681c3c03a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 536217329 1250 536216079 536216101
    0x1050609090d05040b0706510311060f0301090213060908150a0f0e161205031902100e0312060402270a050303121605161401110d060608 60
    0xe411100030442c04e110411440800d40050700300903010f4100440e12403c0700c80500300094884410462034140010701281041c683c445801d142044131060122500040640c484a186244002011502c40b044125480e84171041034842e90340d20030a0f4103031a941c40e01c600070302941003003028006d040003070710b0001031942c420750f4420700702e03000d19000d010080c3c03210260941c17103400104540070752616250007001c584254030480703400c80c40c0c0c0000b030406200440351400d1108c807190b01202a03801140c0c1d50303502180003c801c6481e2060704d9441c0c200d100384118402d90504a0314901c0302d801500c0c101000c0c95404021000709440204482001495910ba104000880c0039011080700725900e0007541007544400081d8080d0020b8000340701c01e040b9031faa0f800092441e440782000068400c011028130810f040d200004150064060602508250202841118064031107901070100201079020340340c0200c0030750221040094030318210341c1c1c59100004400c040d200511541001901440000e20000c00c2 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 536218579 1250 536217329 536217343
    0x1101020307050f07110a0602031e0c15040c0302090c041e081b03100f38041d06040606060e031606030b060d090f1a090c04050705070c080105060909 65
    0xc0b512014145103512401d0801e54000700d504942c50404114085640da580340c4100c80104899030096036124543c062103140354400b00c034109000d14040c01070201525001c10780c107045000e10214100d0507911401c01400fa80210f03403029400000741d105004070156881c008005980b0084960301c0742c02240050618604610321410503107401c0030084030740607480d1921503858840010111081d8003850104c6504545510800c01501651180c21446040b0708030760b28044074181c0340c03003021400c6865003d10700100000c0c1016201c5c50340c40200c40c4004000c0c006040204100c10215070700e9160600c0d051008180a0041401180508045c99058500000d610070b01120520500a04601d004000d4001d40748070b80d00594801c0c0180982d605c4240c00348202c0d910300d070042c020b140c141c407041d06007003054980055036100c00640c104200310294400050004001405460002e42641c45030011a07150207945001481c00d5052600060428015000180541d10446411015440d048180350343c803a6 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 536219829 1250 536218579 536218591
    0x1e240e030f0c091b03090d0e091b03130b041406011a0f0c0102090d050c01090b121902090301020a08041a090717120d0c17060312071e0b0711010203 65
    0x3019080300c0c2214100702c4200c503045041d5040841402c035404c0c2c800525a0412a244082640000050300155030702819107500450b05440c0015141030545802900b41c51944040c038182d070000011807402041e2000441e500c2e03800c100c070001c00e4209403400e0a46012411003c913030074410f40c0004900440c3c0820300d8966140c820642030300d0100700012a03607054000828400305550700307100d00130250315841ca0034a040ba209402a041d002043d40001d001802a900a0b0b001c1850522502400e0305001c0d0010b0342140301d49414900150000c0c1c6403000bc5d01c2000185909540007181c41c041a5030840206030040c3d1240d12280d902500e45011a2170b15070044a060117213610184007000124800210300c004c00d5100b5003640c0282502940061140c0c1c402c6c40c0440f001c80d03840c10410b20665103e111342210b01100d4903040018103205d030003c1d03039801510740c0b00d240d0746d800022903100b00641403500d02005038a40b41043d02d0048141091480d05c6030403984079001c540c01d804803205485041c400c0302d05c541c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 536221079 1250 536219829 536219833
    0x20f0a0513110702120f010501090b0d0807022b060e12070f0c050a030b04050c04050412030f06091d0607030c020a060c0c0c09020414010507020303041e240e030f 71
    0x81881d168071001d0b0000d0b072180c0d04818800c22441c40940c9403209004900701c500d0004000004000c0012800c4440503400910024508101c0c4041030b580c00d8190201c081d003002c800b42d200c103040e0000030083c00f44001703102d01c40c01000300c01b20903c890305c040b5611030030f000c1d50b420410040450090354883d6040e40c0e8845007610100401ea001802c0e004120300c146015400c410006c0b51140040784203c0c0c1140c04c140c40250010782004104901017020881498041d9010301caa400c060b624241c014000140000600d501d03049903c3c22409146c1c000001005100c405101000e2001241c00140800400b84069805860b0000d1111402406a10710360f6095600510200100c1d032a410300608001c0b0340703542000300f04045040416080c205280107400450001a0744074940b554901c407900102074041d050100a101020160364040161004c448a00b20301c0d01c4204d100b09040b820b400901d0f040a558100c00000342c1d90112485003400c6001c1415444880704242150209527582403007a84900c465 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 536222329 1250 536221079 536221099
    0x302100b030703020f1f1214270a140a14011a09072a02040506010507080313031101090b0115020a020901090b040b120c0906010c020f0f010201020d0f05160c080a1d0a06020a020f0a05 80
    0x107616924003481c0ca505414060300c590703070b1090b50741ca2030003404031401030116446070f1686410b2103e1400c0c000b01d0080000b00030444030320b110130160944084510003434400e5403004009501c0324050007072a0410008006481c518003007008a407045481030074001d90040e07150000040080d4010801c5560840d00140d52078110b689440c1c0200060294040443c1000290704e82400b07040b42c240101040d040c801c2c4d04c281460341c10080000407040e075002c40981158003010713a03100580c8803006a030b410750341032000100d403821154001c10050400c0307a81c40d9030401540041c0154481021401040040c01110050050345401004407170710104d00402950007103240000d0021481c02d8101c1d0407251006000141c20101d1249502c0d048900c9107000341001c90f15281000a101c07458560700e0150b1100b41010039620b00c03992030701c191900948000390140b010340104d202d6040c001440201076114000c08249205481d01c000a440385080305040380a228032042c1c094042c9007042010080ea0005880322010b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 536223579 1250 536222329 536222371
    0x803070f0c0f170c03120d0b041d060106030b0a0513230a02040302040509010e1c170403031406040e0607140c0115030302100b030703020f1f1214 64
    0x15100c560044440c00154000010800d14104520000b03200c18641c0d2035100a85003451030624184601c060f201e504602a0f0101c00e8038441c0641e0082c071380c40ca200040c20a000000301d4000e0980d02c81070384511044496501180303d0014a05059905996042c0081d4006005000400155004656001d80f0b00c0680c090454690b034890026041c400090381c50060440d0130041c4048010b0b10360441517a0001000d00940c00d09016264009010200800681c0303c5117981c1c0762107044010981d8540c0b540d5480004d1100d1045202d0f0150b0031401400c8400d900f42458040d00420030442c40b14241100c00000450910b414400e185500d007040c00501100d5840d01011100701142d590300c0301c42e581d010310105013181d00900c95802d4644000205000150450078081e15000d6110312414045041014640d165100424100212035041e1201c140b20160200001e012003013030103040020b0302400000c1c00546500c1000e280841e400214200a103046c00301c0b0301041010100c4030074055080c0b003000121 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 536224829 1250 536223579 536223593
    0x6030d0e0d060c02101109031203010b04120f0503030702010f05070219080307090902040806060108180705210d030507200c060f040b0a09060e04050603060a05040201201510080307 79
    0x36610251050b178038040c0800b6a40300403628104c01c00d4414076408101400c42e81401c00550440d2203402111070704540c503081c2c03001054030940c01040089002c031040b04041003000f4070034042c40e9901c04252a03c92914500003402403131400a000425820180800c03034050000c94900941c2c4450422a01d03a0102d940b900002a88060305201c100a030b12076000407d80c0c101d1003e0305c05400b18101414250500100052158801405a01450050075600b24480500194050032a0020748203020b0209905a01d5030025000c0380310059240541c568005140d603040c1e09c031510611841d190801c0001515400c1d041643d02c000b2443c41951101007058994549a0041c1ca19107103030750003891800d51581101840e540201c0390000110f81110340c248803440d0010140020f00c501502c1c10045468140006503880d00c0160001c00b0882e9140d0216056900c105c40c040e91600407500203031802046005c00e96a140c480c00d140300a003440040200d5500b1201ca8948000c803030300308005604124141d2151340c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 536226079 1250 536224829 536224841
    0x6170d0305060102070510021005060105130905060d06090b060108010b0307050406030504020f1909050a02130510120c0e21060402090c2203021011061503100e0606030d0e0d06 77
    0x103410b5200313017040090142e580308803040150034154081d04d048503113811003c0640f44042d000c0d41c10700c5820703c031004854040303020020031160030f4000810180c880c1c8021810302c18250070040d1107241050399440074040c04002e0b8130b000301001c0c2c2c0c880b0340030ba9844601010501007682c2610010704104010466244a9040b1a0300940003d00e51400c4107101c00004003004280303002c003550b40e170078044100000103807417082c694000031898041d454200d03000c100b03007895041c46c000d49200302d10a12410b0343c02407103a110342203000030355242000021072140700501400380c040721061050900f081503a800400c121800790024111200400d0a81c1b250340c01c012806000401142c000030091100c500c054060740702c02e8901201c40310014141c28150300501000c1d5180c03050060074031055004800a0103000240540d1104082c1e954601a10141001904040c10503000c507280604151402031007a80c045176060164404400301d40c03040d0207965043d102010324446a541c414980a9080e010030915000b103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 536227329 1250 536226079 536226091
    0xe012702160c032006031501050c01090b01050108090d2a021011010b040209030307030305190c08010620100c020f03070515090607050d0207060e06150109080313260703060f06170d0305 81
    0x9140ae01511000715030850f000030400b83e42581e500070041000c2e50b0440291500b240650010b0310366110907000c060140e990b1448903440d803030a15040407250081d201418145158010700303d94107505040d0f0000c20040d44441e12034031951030301039007210130f00e00740c0700f00c80c00c00d40c014015505000c0d458401350003d04008050b00c030030006a13000e000181ea078602c1038041e030142da501c56402c05d50401400610000d614540851039410307261841410307a100089032807002071101c002060f9154844000c9092954190aa086a120218001c4200840401c144841d22522002000c0d1a9203161140c1d0f40d5000c11340f240408500b08002107001d0903103035001004124080c4a0106203981410415480d102007203c0000d0380e45290303481403030550391140c02c1500400d0003900541c00e140da4040000365415191284064401415961807590380c80d20500d00c40801003c016113140d0383d40d0382400006000400d0803001030507d02035010401c0407119404450907011480148980c0051117410380080801a0807 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 536228579 1250 536227329 536227337
    0x10606021917090103021e04140d1110140a021c030204060f030c03140108061b03150906040603080a0507031107270e010c05090a0e012702160c032006031501 69
    0x7d800d03e685c2000b6012441c100c00101e00780da50300d180c84001802c0c1d40340001075901c5842410300500216508800c1c000115104943d49106100754400686003165441030150481c800401e1103601190040b60b40c01d00c103003d02e00c00c5001154003800490491049003c1c07400844c1503900210402842a40418a282218140025a602e00500445428009a006642650001d4108204010104c82070400040264041800c0d070030034048003118944040c0d022401000320400041a554894105800950f0010150703a078542441d41c00520b658000101500880c681007840450b1180c00144641110120060501a941c10950813502c080d180081c2608560f1149071205c9114402e101d9413100411540320941d9070920f0806002010189a01c80340005401500401010005403180d900f48000c0a003008054420000b0400c0280540d4800c52b0740c619100356003900f0003100a0840c0140e90062400703d90607001c2030004440150305000e0150061024804200d08101440300d8008403081410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 536229829 1250 536228579 536228587
    0x60910180b0d0b061309020f15160606030302060702060106170403203906070f1209063c020f15060906100206040201121b0201060602191709010302 65
    0x1c0041c02c1c42001c2d140903202c01080006100b41e0b8584444070449252a9082c140401c00c095000158001454105a8081c07002d0300d2942601d50000c80440b005c0000078140d0180b030140c5400c020000780903231300080300584103680210b0a640c2c00062482d049030314603174500503440c00000d440706400001600403800d00101d540003a6401c400b50740c0f0b8804104220f0000d00c164141480140c00c80744080031040052072541c54900d2840c072000b24003071030a81040c0d808950b02e407000c0c50320b182c00e0743c0305035005441c02176000c5813003490b10751010344601221441c0e9101a9030480300c1c1c0c6030700b21880c1c2c00804e203040445054810420305401006501e070100c000c0c010741c0c8625185402c10b501705140c1c600b00007140c01125040001515118840640100050310340b204032551119000e95218405800681808030505017550142d140e40c2180b018140c0d082600d6480c04600700019000e080d50340a03240c0980070740e0303036107101c00104d070740c3c4440d2055013040640c1d1078014541100381250740314441e11030406400b00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 536231079 1250 536229829 536229851
    0x60c0c050907180b120c07080708040305070302010e2d01030e07060201090c08010b091f0510051b01050c0f070510020714101e0e1c03090b06091018 65
    0x80341c98480c241c581c94020101d0341e048016040301c00240c200e6049800113000340d0040c0d0141c01d0300c0300e07400340c1c1c0a62174965411081c2419940b60086d944010011500018048200100803035130f042109c0c402e0322010120f04013642000807044c1080e142050580b40c0a0f200c481e0245030710381c0000c10001c18140010b0607482152440d007040f1881e005100540c0d1509494401c01011540001c0244400f8008100c51401d0000082c400b1801401c54003405264120142d408286500e4400042900070581802582c0206000c0d0054020a0a000031481038540b5800320700ca041c001e4a10903032242c07003821701d0034600f8028071001d50407280c41070365580f107000d40040c0010303824401040d020303000b0611200c80ea12003036400d03171500d1500e1070190a0b06040c00909100c1e032a540c85404100201140081404040d4010f254030304141a001185948440364001a107107402d030303200c7c1104c540280312020040da9040c05201d8442015109100043d00e9040c04000180303030701c002c1c0c0c0c1c0034045218010500304411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 536232329 1250 536231079 536231089
    0x5030a0b040f0903080a0905060c030901150303080114030a0804090c0c02030a0b10150804030e040f1e0c03050402060a08090f0a0813150c02060a09050a090e0f0303090601060c0c05 79
    0x4450400c11a40c4198070f009254000c003055074020300108040c049001c4941e80c1503241d01c0043c01c401a50314001c030101d5044be40c20b4002c04403040c4000d194000c401d07a01d00f40208114001e11520f0090740c4005080600350901180c500030080c0c0180c1c00070b140928001c000c800500d1012650020800c46006a600503a018049480b0940c01508150050306107540984c2c140c01c0c40f45e00c0039480803104620310544982014031650b105415042c5000c090a03a0340c00718001d8030b015485000301c1480c0c440320b0804501d006400f803919038003148003000004a810300030790860398259400f0f54440018856403128030701c1f0b015026071200c010700558042450000344a850401040801c494a00000c9051490305c0312003d039002c020503100044c0b040c0300c4d46646016100c180c0082010307000e440e00280c400d81c0d203070042d40008003e100190a90200341d0780c9004070b030010640040810581c0c0644800d40c0c1a1400000540e80030300c2c044c0015100c00d03481c102058a4140844004840c0c0901603600000c403540c80b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 536233579 1250 536232329 536232341
    0x60b0301080c040507020d0c0f0201260a0c020c0a0b0c0f0d02010209040c0813060e010b1306140d0201080a050a060b0a02061006050a09031b1e14040b0d020105030a0b04 74
    0x503030380050004000b040100710582c0d40040800c421540000744400403141c0c4680f0100c000c6400540c0350034440c10a000490355004001e01e2160380082c83c2c01070b00c0305560b20b0019203102d001c0ca550208003444a804017243c5404034104950307030280c152082030011401d2f85d001400c51040c40c104440480140504a6050070803003061000541d41c0030a24484900305805201c169407100d1400000d64a8a80c15034645280b650b0000f519a030742e41c040e01601c0c40000d60200c0c91068008000e050005000b10754a001b802050050a004030080346a840c160f08000201000c09a4142c458500a5076212248002400001c1480c84610340701e0310700003102d00c4002c004000b10249035015003614581000001c07141310082d4489410060104000701c8000c0d0f20446a4080e03d6000050807061f1080c2000c100d01d07081d10760013031340611000ca034090300c40d200f40000a504494a21141200042020b01003000310748504650ba60406e03240c00707145005600c80e0b0000c40c0c3c4508510317400203103903106002003011252 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 536234829 1250 536233579 536233589
    0x9130603150f0b09070309030e040513170c0c010f0c0b01090207140609030a03020903120d05040302071502030912031b030a120515040504050a050d090f050301021912060b0301 77
    0x306060700840c1140150003041002011028240007400c1124042000400d008001804042d1707500d56460400d072050030407c0891200810600542c20001c802454000c4950300480380c40d1112800921001040700a03a0101e91054016000015a89005441240604a0003002c101c81e00b12008000382c000344410b40030340820030380187c8031503a0786401744041c5640f00608000f91300120801c1092900002110003d41c8a441c1c0541c807a0042c0380801d252a103680c3e0b0b04000c0880201c1c64000010041c1d1000b80302c0c80c001e9003210700c0550303105580400e02140040740401070708204446c9a080c24080c0402500c0c110403005c07680b40c113100c0b42040040e1085441d400784c050708000b4408001c2540260070342440703060358030700708444d00f422042c00c4a083c030801e02040c002c6403500001828042c0500c110404c00d504081920340a00c0b800c0c0001300604002c0c001d41598141d040703004545814144265070f460001f42982d20141d41d6600001d44071101c5201c05200304a13100c040c00304456851034040c5000300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 536236079 1250 536234829 536234843
    0x3120507051c1706090103150f0501030b0405010c09060f2a0c05091b04120c0e100905180a060e010e0d11010c0e1005031905040311060606031b09130603 67
    0xd10000401401e03030428025008500f5009002c6995148030016045039403000c0c01161508140d41118041c8c003144450f00f041d1842c00c0700000910007400c000522441c0714100070001c080c035a01c1c064440e011140580c00016031000b280380b00160007900d059a03442c0c020100443d141c2801e059151100d540c4480031960145200d0003040f80d400c4c242405ca030404220700d905521503142016a030043d002d54480c3c40724a013141003541040c0801c9840da00d02801c030081240f0a9458810a054180422403140a081d145030000041c83c00040e9072102403000b040a0103000802c049880741000360001c2584c462a0755601c28855104002c100302c080048021070f11943c9044e0144509982110f1401c1803078001e100c0c1c06085810b0958510101c00c81c010104d0500a480e03485001c0c2900402508880413030b5000d00e03000c2407005143d0000d1551030801c4030300b41101c800350341302014080680410388240c80040d880300c25010038100340c840a02403080001d411090400120485c20054404560041d1020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 536237329 1250 536236079 536236123
    0x70f030f03050108123f0115020105061c050c030610031518030c051203010902090301230615300903070f0201030b0d0219090f060806010312050705 65
    0xa406001c2c190040214002401c4210b10008800c0c804d803003050110700b00c00b00d44011a83c02e0120700240081c542d0f00d036180b82c520354900544a4a101c401c03e004000c6410000d11032140d0952050044074420031000d0b10f580c0030f070100c0c1d000140d015a04141c1c1181c10780550050083c1c6d945040003890310a12080400145403851404c02440481c807010b07a0004841c20107400e4502c854603032204410155051038141b044440504060f81407420f00c5001d942600400000094a90000d030081e2441000440080001080d64070030303283c040484c5001c039011441290001580c41ca0442c1810b4030000d14441e481d0314009a001d10003c004250504804100180c00c03080c04013150803509055111001d072004514001d155101c980315080000d20003030425882d88641d200603212741c43c0d00c50000d540544071210318141d0503100142d2080c1030003a020f0039464042041482e811030f002d84000c55104102424140c2d0958403000c4103080403001d2030701884420420000010303020040c800941034101d0101d022 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 536238579 1250 536237329 536237357
    0x120120d0605030a0203120f131401030c021b04020a051209030c010e030403051f0f0e0a020112060e0c09010e060a1d0a080322080a031d0315010e0705070f03 69
    0x440c1c80c2500114020750119a00b1001030714001540810aa92821000d454420364615030045100b1001c516844c4140c801c00010f014030b005d51219240c4009880c144085580c000081740c0d034030064040b411000c0031f40c6010f1440344c2440da00820340a601031800d103281500703007000e2030f0f0b0b02c2009a0b10040e45074000561005015020301c0b038645441011030185240c2851a01c85035a00c0c0c081042100d44c082141e02c50318500c4410f58840080650b550a003484846006841551201c8440c101a8007003460149020351031f038031511940c1c040c8c0b50781c0d10881d601602e40c0d281c010599003082c0a1141804142c0d000b003032441c0d841380083c4c8040000e603554111a5515000240740e214000401070307024040f00c41d01030201d8580441031380c045a103c0101400181d40303180c4480c2480405034005241402003000751403c5c181c1c0b1404055041d92502c80803a2030082c050241507661204032190307a400c0c0d01c602e005101000c41f00c90903e400c80750f140342103410206140c4610b1140c00d5401021000b05a4a5440d000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 536239829 1250 536238579 536238581
    0x90603030917210901090509040b1915300f0311030a080a2a020d1803020307050d03030b040f050906181c120507180e010f050120120d 59
    0x740e03056078002d840c105803002e0300e010803d032040742100f01d490008a01a0400d0348030300c0045009200041c4405401e08241c105090212030036215921a0a503107145094001100e014844026400c0000484100c3c906104012944000002030140400222000000c281105402c40400e4018000019000c10501e0003070400c00e500e580c0a0555001400b800d0030741900640e8550744004942004a502d20390200d800700c81080b1014a81d9001c10740e4013000d24030590015459020171091388803240c0301030000f121902d00d1801840025410740c0155004e011a0802c001450341491082c240815040d08580029040d2035035407240301c2510360784004014914908104690f00416024464805a807084007955120507201c1c0c0c1c41c00800b0031400100120a1140380b1010071050004000c208a06084000030005419100208801050041c000c034000c10000c10850480d44001c0c40b00003c54070300801900c3c81c4c98030303151101d42520031003d0115070b010180403406454200400c2550b80e1005585410 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 536241079 1250 536239829 536239859
    0x3120c030e0a0c060f020a0209040f02010e03010509010e0d0801080d031121040b0f040b04080a020a020603040c0f0807060905040b01090b030405060105360a0213060903170306090a150906030309 85
    0x1740c2107503c407102c1c250240e00e409550581107a00412510080349182c001079408001c14040240c02d50700e01400c00c45401d1040d401140b01e0443c071810307250140f203412822141c826081c054006140c010060750361615029034031000e03540e06d850100c0c03400d110600c00d441801900300708184003491441e404100c01c000e01000380650055803600d01c0b002d20b041c48d844550a03844000e1004000410000e104a0f92a000b0020388207420350007005c243d40d901e0180b5141c04030301c141d031080c2102c140f40ca8902196a8001150000c1560a50f40d10b11413282d00d801d00b000040c04010003181c0c140540388501156402c00c04000b0362040380034600802d915403400c020300c92002941c800c2c0d05075802020225455460b0000341a0512190440c01c0180a03101d11b49468001d100b28100602515849800042c486070440108000c9038015519541d4003070f40c2104032001c0e4071003102c00b01d41c00944000003401c402c007a580a0b00105c01c4140184203850b448500c4401141c9a540095000c540b0002003000b00e042910401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 536242329 1250 536241079 536241107
    0x109150f0813030e0909100e210a1d0a0e010303030e0c0609010f080c0d05090f0c0f0d0b0a3804090302060103260301091e060303120c030e0a0c06 64
    0x10b0320b6a00055100100107280c2d61411078842c0c1d5070000800c0c0429020008801c0d025109101000011007160b074242d52100c0c40500703c1c40c3d0f216a00c500f41d1800648030251400700c000d90311340381c4000134515584080310500310100e41c0e00c4411101e0204004c4d00c50020395028511070784001800d402410551407803d0b07840030b980c030311440f002c120750f1606981c89000300042d5425418940c4164070b0310b0741041c000340140c50290025514085c100200f030540080d100d104c01d086030040d2152958030400b0b210040100000983d00700300c4402c101000100c0d512034440d070180080300c0018111422602024004031940308042076006440100029004084071000301e0040032101009140000c0c2e80280d02c8210500c805040a0038111251107c1c1ea030b2302d10000115103168040304c1c0d596844031100c00003040c2a07580c8120f05031210311010505207043c03181c0c1c0300340c9405840e030304800c112020540380980b00d008441c2c0200b42d101c01c843c0b4190107007001540e0b9042d106038819180682801401401a4040041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 536243579 1250 536242329 536242351
    0xd0608010b0a0303120e1e1f050f0c0901050d09032102211f060315120309090b0109030c0b03040203061b07020607020402120a090b06010509090606090109150f08 71
    0x41000081d80268039511710803031503c8041509445281214181800c200c20a0b28416610081c0781c0c900c68041400d12408020810341a08a11050315450840700304507500c03070150340c200d000304841005100140039181014034110b03151016010303000094400e1084100c001c5081d64902c1c5907031082070003d48800c555811821414210036240340320301c8000002d200b2500011010116803548010300308030b61310721200c801d644502e81d0b42e1180180100003080320094000700b000000724441c00c0c145ca1040e41a500f6a417079400321420410f40324001c20000c112103060048800001001524040c00f000040c5404544241c03a0300e0309006141c05e05100800080364008286121501c20705102d042e281410740698180380c4440207840070400901c22441000c4071420080c4c1001500c0c1d0040c0c00000c03083d403189034004156200d1000641e42d40c05801c1001c1e80c002d81e9a00043c0460400d0f801070911404145840c0482c07680e10300001114240e009010b200181c490f4081c1040d1139001520a50440360f8590 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 536244829 1250 536243579 536243599
    0x702061c052505071106040509070810050a08060708060616031211210a060f1202040e01020903030f1804051905010f061223071d0307060804020d03020f030d0608010b 73
    0x50300070441d1203900360003000e0100d00c6514009981b0f03581709403406400c02600301e085d90304045202414020007100c0380600c0e42d000207804a454104104e6603011075042d4070090906480c0c0d05015510744030b00600c40b5800c02018841440314152121042c00c3c25030298503031140da2008a0710810130f0790050601c401d00c02c4010440c91180c40c0c074054114030320400d2180041100c0c1c581c00c4100c0064110399205003d03503c0424030100c1c8150f5130440e40590b03984204e0702005100744482c2118280c1c055442d101380c4c1600107200415003801408000c0008000c940003039030060f500c410001c1e0840e41c0580d41c0c81c20140c19101c80c0b40183e900e6200d041d02501c01c103100b402006240c518024240b1740b152641703646484c2c4038503981c40c00780c0202c1d0030031b05007021020a441451902c01303001820701400c0000d114041c414950340b12010700b00814180300740c03200c590350415a651a07800f4000c0c180d01c016001c0b821880b503540c8070404000c041c409040c940482c03000c045070440c58a0241800e40b070480402031b02c2400700d00c0f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 536246079 1250 536244829 536244901
    0x80712150e0c09102006011724061009050607050c09011202090103080702061603021f06080606010f14040f05040506060a0e10090b04080307121d01050702061c05 71
    0x4c516252200301c02d03d050301c0d0070741080c2c4031600c03c564408600100c602c81c0c00004500c14000008083c4191030310411225010010036800c230b41043d102d10100f0410700301d6008542c00b0704042d4400740740001e45c6d042902040f5912004502d8a0f8803144050b0799940000c40c60342da26103000c08200b40104030590301d440d550b040790380001d080c226041c032004140c088001540c00c110b45840007620011038004540140050850501a480d01d1040301c0d0400340040e40c03040c03510610360a11401d81920710b98002401c95076200340043d41e40c2e0003440204418005074050303030060400b074075000300040e080100d441030040385081c09100035508017a0070540714190500008942550283d000f0b80c01010441d110f510244c01d445040d10041155000561060b50018001c506000004000c2c03540f00d2080b13100c90a11012082d040b24000942c0d40304402d07042616003042c0180d840360300a804910f0000b032a141c506034500c84121801c00342e05481d01e8090751107500b081083c2841d0841c83c6180301e03c000307012042050300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 536247329 1250 536246079 536246089
    0x30b0f0601090f05090402130207120e18010308341b030b0f04110a2c06010807030207110405040303090501200f0f19050c06160807080712150e0c09 65
    0x14044d16024560b8000002d0941d40c41c0c10103104280c3c24144115600e601900b01000c20603109101c4802290302000901000e00380f4001d01404a034000120318803690842d0f80e16202903000341503495a018005c0442c002408039801c031004200d402090450741c034080f41c41c10100588a05015040d80006800104041141e11481540c000b2083c400b648441c0ea40c0d10740036448a10001100350822018000032440e0003c2100d40510340604081242e509a50001403c00400003181c15600180380c80e000304070454001d8015140651042d400d515040b45244081811110215002d5001944489001e01030000070711030301c1485400020030403640c00c81200681401d200c1c00521150342071000904c80407016206061303440303001c0440c41d030040030041d820008002e80c21854511899000c1c490210301d0126400070241564042d0381c450110700e03036609038141ea407082d00521500034400790085412180c10a445800180c1c1e20005041d0421801e10b070120414000c020290301c1011002c0040559a83d10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 536248579 1250 536247329 536247359
    0x3f0d031e150e1f15090e071205010509131704120f020103050f09031b0a050105010308070512160308071e0908071e03020d1e0b0109050c031302010e030f07030b0f060109 74
    0xb401c034400020f2213a0210854003010607901c15000c1800305000d1140c030907842000144920803805007841140d0b03c2c0c2d4100000036030706032520055010240c0e40740d00043c0064503641c4017010704030728031400c12b1740d01c25410b0380e40c4900d51012a01c1000200310f10085603091310441c0e0300001005000016481e019544e140d9a106101140350f020008441c0000d8404d800c00070030411a42c0180244210b5030742c5d1400e9503540e046240f040b42d60340251300241d150380390000c094540203d0200500021582c16407030560381808064020350401016005d085070701c2c0000c110703801da002e0482c0d40b00b21b00249840d00c6a03081c011981c00540d03a40030040c00311071284040b02101020f42c0d8040310100d16000702460820070a19a500f1142045043c400208091100ba64a21412101c5030701e000d0011750b40d8892000c0d11440100d072590b0760010300020100144d4415800301161090248c211452010b41e14005031600103140e0048075010b400804000214401282c00c40d0030060030700306080340d1070030a000241289c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 536249829 1250 536248579 536248589
    0x13051509091b09100911040f0b12010e1005041a01091401020c09071e0309110a050603270a060203040210080c0a0f030204053f0d031e150e1f 62
    0x3c07000d0119500001041c400c0e001081c0b07051041000b00310003038000700e03aa000b81c4074806c080002c6c503030f0000d0b10050030400c4445008031840b681090343e007043c101020201c0054440815807c40c040b000c112520303580705800700940004950300107110000001415400c594018180041907145a0f21160b41c0020302d80d40c01d514100c45450b84e90743d0b00c010803144024605840d080001c2a540d1038032880e500b41c1d1044520500511083c3c0120340c203503041c130050000c944211a00310300d0402c00115195081c1070700302000b0105644880b25005900038a42c6030201443d03064441a600005010441c03074184002c2c1d085c07401d141000701c0a460301070b180308030601441c0500010b0124072409650b80c0d034401d60403200a01001040d01c800301003603034042c510440030003a22168480040c85000c2c40d2a40c55038039801c0d0b28200070000d000403c1b50320800c4010f046c0110310086041c000101028900c00e0740c1c080c20000d009809400f4045a14100c1000025480a8860110115850582e102d42d41302071041c041510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 536251079 1250 536249829 536249839
    0x1808120c09030703030815030105130c060f08070302070f060f1505030705060f0c0c0604030602040e090a0816030e12031903090506010603111b03030702160e0a0b13051509091b 77
    0x80d1f903001280b1565200883c0c0241c1c0b40d4a400c1c2002491214003d40340d000d54059810624040d4403610705407401c0c3c24801c444c0c0e01040200000400040c483e030001c0c44080d05c90700300c00e000c10070399985210554800d0420000d9003501c2c0e01d895445111380c4c1e0307401030080104500425540b49410045021446820143d11a0090004201d015480c00304207001407200054805c0c1e0342c5030760f0b03401c05034000c0d002801017115010480001c501e00c240700188407040560007156a602c0d040684a4040d845908030000314180602802001c40560f185041c0003c101142c001956903045241c0303406891231364440e000d80c00d01d4603095041c0d02103940011828191105410f0014100605640004080c01030b10764059080c60f046071840c45014000c0055405808645c08461260b81c0c03466407554007400d24010141c40c104c81b040003511691080d0031041140320b0140036000c4541451101e00140c6800f142d40c0351140e8088000034949041000c942039010161501401d1724449002000340408800c0990724030038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 536252329 1250 536251079 536251081
    0x50f1b040501032d080705100c0206060f2709250b0414040902040e0d02071a0315210307050d0302030108030d05060103150e06030706020d050d0e011808120c090307030308 75
    0xd112401307000450329400441c03064a541843c07034500da8505031326a078110003504040e00083e046000140c2e05000c1c6e0710091030121004401c030144003207080f80084411b4003484503100e05400100c045220780c080d060000c082c0000429200b4451100c502004860807503000000013000350b0492031094600b0b031120a00d00c1691180c0340800140500305540c0040e5200381b030311000c40030707075140001c00c1013101205400f81e50001e9030f10480c00e0807103503010b05c0b034805855082000130b506107016801224880c078003c150525015889401c4801d10301640c0d45004680e01c0042e0080a001080101e40001d1481d031400354519030502c1a416101d000700e40e401c0c2d002c9a150b4022a1541c1e009800105101c541412516010b45e980c02c02c1d8810b044058444030300a010b00c110220b05a480852100116682c07610342d01e203000c003454a210018000560b10b00110b5590310742e03140c1c000151410306c1035030500400c0e2680c5c603003211140d4a5000c0102414802d1007038010402c1030016240843c01e402143d030075051155403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 536253579 1250 536252329 536252393
    0x8030c120c100c050c0d08072a0803090304031104090f1b0e09010b041103042f04060608070305060a140d02060f030a1b030501030317090a050f1b04050103 68
    0x90b08036240407a400082c02c00791034100c2c050b4010083c08060320084110340000301100c02c20380c1d000c00c0940b5448009400192110444649a1050f1440700a01d0308011013141c40e0342c4429056810075581c0801c9600001000c00603ca00c024501000120455007003102100a0f91400421400d0240040010789038800b003884950b400c85c0080004c01e80c04100345070520304124168000c180b042030030f610035440e00f001100c05000305420b4134851540002290326540081380b81c0c1c02d04070340c0014400c004401211400c201130721107015030801400305465000007401e00700000350995000414032802250905010030260b80d80d401104c00d0b07a40c1c1901c02202c5a003c0d0700119400d4411701f011444400400000c0c00403030480f6a01c03480700b806101d03072900c9520b600d0f258110142c407000e110103000125420251202c488003c20300da07401a014504a510500d40c0d0394a55003400841565942c03036400c15180b185010058580b070190b4107000710340c200f0081d8107640da226462840110b804130300d04c00d1100782c10f074 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 536254829 1250 536253579 536253583
    0x10b0907140c010c030f060e0c0405040b151207030506030c01090b090411041811120402040209060c0a0b0108120f3a050403030f062601290a08030c120c 67
    0x104002e00d0360000d100c2601e0b2207001801500403100342020749480c1000c00202030250350385460081d0501d0100601e00f80c507000c1000054540c0300006d40d846880764480e443c940100000a25420041004103d21803502e5035016044038401045140240c0012611614981c0c0c4050f0700815103040e413003ca900e4190310b201080040030f00c1ca03039144681c00001404104640d21240c0510710480d101410700c6003174080350000c034141c010315001030700840380751021400520701900030b081395070b4020f4542400c3c111551040c91070305060034030607a62456a1401032100c3c2e01d09110a0348441c86000030181340c02e0110580c60454401c2c8150180150f00c010300e000d2100d1105401040351015240741341c0340c0085511074400042c030054400710086882d00c036118181d0101405004200c50b03006034000b0035590030380f02e82519860b50220001c1c042d541c84c041416003c860f150131030081101040250f4890140300c5c01d100074207802c1e0b0403610307441c0e0090041c1d415a403000170b0f40100e10026103414a844a0240721814 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 536256079 1250 536254829 536254837
    0xb0405060306162303090c031c0e130207060510080303090703021207030501021b07050a0f05010837050903070f0f0c08010c0302090117010f1a0918040201020d02010b090714 76
    0x7500c01244c03542481c503001040c40918000c03440c010a4032010150364041540e5070384581c088421016020b400d41034058091040c44600b14005840141e001412880b0310040f81c1c401d100480b100b036556420b0041c00d00c40d15601401404004006600e1820078104044c0d0303408091100920805000c0c4d000d04c56001d05000104c01107174800300942d11070406880c0b80f15190307070100c6002181d00c0340344400100d52800081041c200c03403440204030001402c0c41e004450100c4010012080c0c5111010404c2d0092168100c0e03001720030100d1460b02082d000d03039a4040c15558081c20408055105010070000315284803040740005500443d603401d8aa10f514004106034071581c0011000e510b000d014107052364254006000300345090380c03002140c0401140501c56110213008070400713007483c5d0205008601c00110324584d100d51869000e810f024003000006c00390384144076004090321080b82408110350b0108050501e0070036500080c4811403035800844c03800c50000b042541040400d14a682c03680d00820112 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 536257329 1250 536256079 536256107
    0x60f0f15040f0e0606090705040609030311010216050f16030b0f0613020c0c0a05041e0506030307020409080406090e01030f030804030306080a0b0916060c02040b011701030f060b040506030616 84
    0x248090024000d410b515544c04440080c00790a031213000480c414803030001c40b000e80346542c5940d2441820341e20110340840c8424450602c0c2d40d400c00080c180d000c54402602c400511440c010401002d0141d182802d01c040000c0703d0380300b0b80c5044810f000081c00345415a52042c142010807240d80e4400340001c850820310742c08921810300c000b41d28000c10300c0100d2880c1c00100c3c25240280f07000c2ea18814801260640440100882040e1a116002c01080c6c0c011603042032005040f6424010103800250031910325180c1101c021400280c204581500000000300820b031507c060502c0e0340c034640f900300400031803480040802841d41c0c005000c1502a80c4103d0241207408119604094246004a141c1c402a00c01162604c038a01345800c46801500b400307021350714203076182d42018038558203010290200b60f11003810b10500e2205007150001d4020200d00a600440381c0e00035140b1241010b82c101c0c0d0300c541d4824040c900701810001b007a20001600b40e00b007002200c41c0d1000f0561400308440010008100d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 536258579 1250 536257329 536257331
    0x30221060108010501050705030702090403111006090f02210a060902030103050a052505090901090519200109031b050319020108010914010618080a03030905060f0f15040f 75
    0x1195440405820895209a400ba01c800b00d071641c95000548042c0141100248550300401c41d039401814081e44035030300b192103803c0c030b100e54007003420b0490304040c4948031080e1110740d03400d0100104955806108100301160004518040030f01d00f80c03881820801440108072140c10010a10841099000000800004000719100c2d6100d2400caa22003a9083c015111440740c0100c01c2c07100c615910b1007000b500d50364001508040d10702010b11500c1d0b80000c00c600e803955039640ba6007001c140700340f101042d400d2080343c0a0600030190b142403031b038085050116031904860f81c100c0142603600f10b003c0c04d00703494015450251403c030b01b680362031821407150083d9401d40540822034040200303240d076062005200341c840c0c6d8003e80c0c07039050310001c8914125121603552a031000400c000350091791080001900c4181404031070343c032120762500e480f00300c1c1c404600107680c0b48a030009202d4280000340c1c00a207014003d070528200b16181642181c00076020201228540000d20503a5a0740c0d84001480c13050210 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 536259829 1250 536258579 536258617
    0x30f0c07081306180e0a1a030105150112020a02030f0912070e150607050309040c020a14100c050307020d030c030222090c0804050d0503070c0b091015180c0302 70
    0x59900601e15581c86500f01060207100100c0b45102d100500344141d40f403c6407004620740c0d480c0856405088480110f003d40c001e184207991060b00c0038082c07a44030b185c1c0c4d810101807e44070f070f400044c410302c03414a18080c0e00e40705109010005e41d001c002c58102c901c2041c88903844880c1c090000382c00d600b4480641c00d55100340c103400030f41c0342028600a4884c08118580c0000c584034101131052501c00d1610052094108001c0040c451820303900c00944911144102c41d5015002c1e5241680303507001d03421005080d0700c21620300012480310f0042e1080c901c20307890000d01b981003610001e96140385c1d11007520141a12044c04100281c440da0683d903466003201501c00307441c5030a90246031502102d00ad0310a141e4141841d0040f441d000d203503d1400359510130001c050032044c107001100c140c0c01c085c00c00c00c100a0600420743c00f2075204032034030b0b01403101c88002e44203092400d02c00400720b41d8600541e43c92510848001c00c10918200550545a000050089604661108210001d100da6603c00019003c400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 536261079 1250 536259829 536259847
    0x50c040e0a0b0103180f02040213030b070801081b0d1218060e0307050307030b011a0d060b03090d030c020d050d0e0f0d11120715060302040f09051e03030f0c0708 71
    0x1c1c0001c410b026003a2070400148810301c1ea2692459036404000e460300f03440042e03190060030582d00511100140c140216141500c0b070752811004201503828000160440300140401e0328103008a0383c20400b0b241080380960006004a0303440c9000d1070340505090070310344500138840d0050700b140100100c0d0b080c01040043e100e5130b01402c8081030708441402446030078004621030134001a0007080d80d03040507000100ba8a440141080c10401140302030620300e003806164028512806081e02421300300744074545a24000f801e0034075200c0000c114104243c18a412101d0b0603030003061129011003240f61090f40c0d98408042e05002c0e21f05007040f100e00f03103e00c561072891441e010540c04d031501010780e56000e82e1049640c20f9580e404100d601001c10020810040c800108010b41c5510120031081000c200d490352500042c04036589607444003035850b260010b60b410020240300340d6803400c85030410701620b030340c40c03210381642c80c08000c0243c603801c00f02d48089040c2c40d070070718169000554003003020f5030b0790b032828 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 536262329 1250 536261079 536261081
    0x6090507080d080a020307200a02060d0501060e0f10030b0f0904030806030d1d0f030f250501080103111c0b01030c0f2c0c0702060c0102070b0c120a050c040e0a 70
    0x6030b581c1c00c0020400000f10745142103038001c4074000e200555401150460046030721484600307600464000e4442e09401c2c00040c3c591070050140c00c0c8520b4400141985002009003503024401c643e14030440144802040039925425804400354144ca000140b01c08100041940ba0461850450388403000508200415510bc98028421481a001da80907083c20850955100307400302c071049140240c07003039203a040e81050245400d82e00002011138490305007000005081601110113806518100c1802c6013004c001c040c500c6d0000c24003032030100714961442c2c41d00000c5020100d070b0588116881000c004802034081012207002d9001072030b0342a2940d517868000c2c081c0109102d884940011200005503d04a201e25080c0001c04000395900f030724014240b8009420005080c00e04000050104501507200c5401421400c0e84400005035100414200307950181002070206264070000c000c0f40c0c40c074800d50500590010807540c400b0400b512150010b15244c0205d0300310250441096013000700b43e2501d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 536263579 1250 536262329 536262343
    0x1701050603011b0801030210120203101502160902071b14030c040903080f0405012009090c03061f05190c0303050c0405030a1502190203040e0109150306090609050708 73
    0x104030020070402030b1081c540502c542d078030082c50f00400c00400040001d030406451103400f902a600d01001c0300301809004501320b82003a01d0586c1650703c0098103000e0b8201e88076594181c41090300041a0b501054010ba0721808a1030143c10b071240c2d0042200e0b42041a101c13000000700100300c0351800e2043d2a04061100610044021842446035500c4241c2a081500c58105080e4140d96124015607902c2c2c4600707807448002c0c00031036481d036980240200050420003011a54105200341e10303580c1176481c0402081c0b2401070300440c4d8004d030400a000342940d0304c592800321070080780c03803d0a0315044840b00780c55a0199940990400003400d0b80d00346001e40c0107084a171010300c02d07101045641c54031010461580070b0790003220380540c0180c035500c020401e16819040051a0300001516000c0400c401501c10f03084504c5050150703201040a11400360000c4440780581541c590420440b072110703c3e00364210405210240019540c0c03000e92041c08040e404c10300303030035411400701c0e0645e0741d03565210756541e05 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 536264829 1250 536263579 536263591
    0x41a13090c06120f1a040203100f0b0408060901060e180c060424020f1e0106080f1507020109170708161b0b07020a0501030507020304180c0906030b0a060513170105 72
    0x458800c82c980c41a5082c8246202c041c1050516509010181700788002075001038291900715040d10300001d04544840c0c080c001900650501c103444a10f00000300d85030400141130480e03164140807081c04804001082c0642c056001030080c1200121800024100045400600c0e00030760002004500c0a503090940e03105003040407588940d400c40c203001240c0340d89403c40705d5811500410290341078002c071080b0f0383c1c080d45017000000403100d42d41c0401d0b81c6422040b401d80d11140d000050106284884a46d4071641f09900e0b0000b4031590800d6a146400c2040e4000c0c0140702a0020a011007400101010f448070702c01075146030306100b900e5040516080300d1741c041d040104880c442c0040392401404081c0d4840702d602a0038220468140f0005601501004044030210711060000003203503860340720300450788443c0b0400041c0440300320000420789030040c0c0040003403505083d04a038180e203030785110108947c2c0c2c0307107804c0c0d495200603c0c1015240c103050703120680b80300c20600a6a00140194000c0f40128 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 536266079 1250 536264829 536264831
    0x604120f120f1d011e0506030102040f1202121906021e0a1d0102010212061e090a0c020d080603030a1d030304030309050f0a030b070507060207020604080c010806041a13090c0612 78
    0x404030f84103800d0b903000c4c1d050051000350032018008200180e17000a070b00550010009400c064661040074035200827079100101200e00c5045150079820502002102d070900c800c090085550300d407100c0014412800300041c00b19a000039094210040b04c004000254040c0ca1010743e50300301c036440200f10b262014540303030040c0300f180c0019556600510845291f40e404045810681e40c130a4100801e2081100030007080d081c1c185034111050396280099441091b00b044002001d20070008020b01d40691000352800b40101d90381030001a0ba800026111070251711b1604859404240d1400080300d4490036490780c240c44041000300805401268040c00d0f1030080c1c0700c6544850744241007205014032480054544689040811100b9210b580148400382c01202d001d807a0500c160b01140559106a101d5245a001004151210340e401300c00140c01c0304c1c08a80600c041c10422400c3e225000c05d600003d8803907848414115031902040d00f000c4000d41c1c101120b0101c540e500c61020780b206081b0700c2049502 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 536267329 1250 536266079 536266121
    0x15050d09030e090708150d021f08160c0f060903110d032703090b030405120f04030501050a0b1f11010e060115020313261219020604120f120f 62
    0x314400c50000d0302c41c6d0058041000100a00002d05c142c0306508441030780c0010b02c01807809040e4101c98030030f000c0c804403942d4a0070a880c0140c010341148503a800c2c00400c021002000c640070031800c211039000c040d0052000100c82c900341c40d040e281000f42c40000400360003100c1c449054a074140d4001100c0309844541c15841480440f041d40649003442402030205126060511614404a002d582d001d0300c5101240d800915469000034690050961503149040000f001e00c01c020081c02001d0300801c0f080018000c20003c40002240180107803210a541c404054080e04071034460b98076210401081c400070461413003058182511200c00340542c8a0800c21500091002071001003158548135000050204260402c1075135a42e0700068101c00c1d220010b60f14008a54820078000008548003844543e540c0d49000c08210611841d40c456a070190f4100d041044041040754103147c043e694030f4984407080c020300d92170564a8010070b00d0091501c910f00f006030506802d40fa401101c0d516642285401c031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 536268579 1250 536267329 536267341
    0x904030f0e09010b030c071e060603020f10120b1314060316030f0b1302130f0614031b0105120106030b010915050909250203070b010b0403080415050d09030e09 70
    0x602c00a2003000000c010030400954281400e01c060041b45100d501003262a800002c0d0440000b05116011f440780380c0d40b41410011890441c042040704c10080c0c51925101188120113804542078104401c080c0340c4406410a00747c2d1013840c50700600390b000000708180226200c0c080c11019003241c0d054003a205480342c1000550b841c80c0401e04a81d403099611108034481e0f41c030031046001c00340c2151610301606040f00d00595450005542550503400700145030340104409034181c0300103501980656981011b40c0c1c000f40c4010a5041402c40c4c16404054a106c40800480e080d00c5118250681c0c00e80303010011910990540050154a000342d8910007141d840e00d698281d020035901c2c1d1400491400c000754110750800c0000700d54004170814114a0f1051019000d0345082420341007240141c0000503c0c03810440351307180480c090028184110700b050304686e03622003103210714050944c40880541003032001a2141040f41c0012040c0d480a01c04440f492034050f12079810710101d03510903070130407001400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 536269829 1250 536268579 536268589
    0x102070f0e04060e06010e1302040902060c012301140d02030c2205010b091e01020c0a060e120f0606090a060506040e04030807020109020346020a150c1e020904030f0e 73
    0xc103a81c7e61084100058a030a200842c3c030803a0600100c3c0c00035200d0946c1c20140c0d031114050300f07800c1010710006c0b6110f00e4200e01e00c00170b402d003807009a4911000c0c2c8014840a89166070720242c1442c203580001806403203000003440d2100c190305003540b04228102d03003100c2d83e0381707038081004000070f0080a1000b42d8071503113510110700480400c160000d0b4440610305c01421072200f403031211076041c01541d112000b20400303e10341c50303903d03003040e0b0100e01c0b440740281040c1000040344c0c0d81040100d000e0007100c1e0008521540301e2502402e0f41e0321843e001000706074440455800240182001483d0f16540d642c3c0d20342150f0380b002d0440f025000700da00f420005000d14018010f80d010140c4c0200034040380600b000c01e080c001c0980500f0880404010f04001c0c0c250204903000d0100702d1204202e0980042040c41040b42100807030300552580c5d120b401040b150030f41c01030301d5580e1090b400380582c41c050541102d0185012900c51010750300500d000c051105140d000700030314110044550310340440f00c0c0340e035003404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 536271079 1250 536269829 536269831
    0x406051903050411040f0b031507260408030711010e15010509040506240409061b020a0803062115040c0801270203030408070b03100f150e0102070f0e04060e06 70
    0x5010030211244c5880c00380b9050703200310b9500945040c0000d9401030780001c41d01e01448100280a1010460107009901e0707006440410700c0c80d000c0075a41c1c043c0080c02c501d8a001c1d4000f500c02404071502101059106025000190748500c03003030001c1001c0c080480039550b540c03802d10b1000740440030034800480c2c5401d0800030716125940000040005441e119010b881e4580d81e10508189162070f080185c403240d82d54003d1220450080d034000c98600d10b000c10003a109900211802c0c15540142c0301c0e2400294100203603503000d04210780f96507260700500140c8901d1091500385000e14040c2890507100e194101521500480c05040da00c2c5186840d02495801c0300c0e40c000c23038490090502c0890f00807026242c1107004c42d00740302400352402d10395604c04c01b80c038065940c4c1201c10b440e8400310402036450100110100180418409180b01501d0100300305541800c1d1104e0380200501c8401d00d032000c0e4020004040200a04250303c0c00346503448000350755405042d44d0889074142090402e0111003400a0f1203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 536272329 1250 536271079 536271083
    0x1e06070303091e0f150b041518090209010303140f040801150f0b070b0402120a0b01080d0302040e1306090b0c0c0705040e0c120709180318060806061e04060519030504 73
    0x83c400032074603030700c65050718a003007480d00440580f501b0030702c01035486a020b40100d01211180780102942070101d84424000c00c0404007903001d142629040c00b60f079070140c40a04413901070808000c5107520040081da988100e11220005000010f0002446841540084e20625102461004403a02e6100c58052846240315015444000b0300c038143c049084005c5407504240f0040003258603800c110511400d241040da0255144140d0000401802d80c0902c90001c5142d13030351130114a01070a0002055008802900b0000700480c0c0612440401c00c05a011090319500401c40d03052502c1c1c000c0b5038440a9114a00c005001d0064000020305400c00e80503d182c802e4205004c0c2401c0030f800c506015000644882d855098811000d00003050b10302407007000801c0b100d40301c00d02c0d1484000c0c24050288042410042c0036902c1298040113000d920418084c2c11032011031b2900e6548114040c000b4210611784003840c80c0550010380060695000002400d0408074508501c050301c41c5644154103d420072100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 536273579 1250 536272329 536272343
    0x60807020a02030303180703051c1b0203030403030c051509010c200d03050705040f0303020330011a0702030610091d102711040e07060e1e06070303091e 67
    0x100d00940c6c006450780e400565514102d542c0315551f41c80d01450304000390b0780309a0ba000003040051300c05921501d150300802040c1c001c4004c01109502103640c900c16444041c082000c5030704480c08125092141c1c0c486e644042414010500f00300041500074490815040040765001e5080425031401088000311502080054805840305510547c040e090040c10070f01004404c1001250a100910200010398000e500071521440098070704032500c820a40c5200c0e541c01c642c004030809042c4203c12606480d041e8000c820022407554094200e03000e100c00096250043c44100f01900032044603100031540241c4051000301c900c4040000182900e041180c8590421416002c030701900c0d81248404010140703600b10640c4410011b0043d420b8111400c03200300115102c081407501d0203006007100106041e0290810629000c805003109800012490003406500e0042020b09201d1504905480c40541020364440003490000d00401d884001141c90a500e01c2c004400c4103041000d10180942c4601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 536274829 1250 536273579 536273581
    0x20f010e03070b060f0a14131811060d0905011e09020102061609030b07110106090209280302040203180f07030206040509250e090604140606030c0d1104060807020a02030303 76
    0x3d5000798100c00a09442e00950382c5c591058036a00c81c1440c2000400d400603d00003100301140c204000030304c3c00b800e107843c5642402c0000c12a1a090452018445c1d801400040071004d00030100340140100f05107222401e2600b42401e06100064010080a242d94192290f000000e220b28a0403100c1803031010f0b005030700040015003490a00e8640000081550902004d001d50b00c0d038440e0040041150407030005010741003e000c550000340643c2000c0d04244c1810b500704452800410b003c00003215022411050841601c0d8618411000c1d0300095a0042c10039540c0313107403031440408184030000d6a40c04c1c0b4401c140c020795280002080b8001501d500514607440c0a01d460100080800b02405804508030586003512605410040810643c0d080752500c80b035802880041100104009040c0c500880c106035280e03418a00c030b13803c00343d8080c000301c0e85a9103a44404441e14614011071a040d10b03840e2070314181920125030500580111400ba81d2000500d80e200d80c0c080741c65139402c200080d01580280 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 536276079 1250 536274829 536274833
    0x200315060a030b090a2a12020f0705010c0807140a090b030405011d061605030c0306010c050708011e11361f08060a0f0306050c1c0b01020f010e0307 65
    0x400812001e8910301d00030030340c6280100002c01003030b000e4481004140e035600e040ea514842804581d00b070760403070481c0e000100401441c06004507a0f08814846443c0d800a4071280c450307512410b030b812580e00304000308071104d26144083e210305403d886c1c000105003030b2640d5400c078462000031a0b0100c1b825644410540c1d1401b180d14a003034002078002c407020354984030030720424141d04035551501c0c500f041c000c1c9510b042c0000d10b0210781710010f03160800c000c2c0400c204098800c0c80f0040369044142031905c03403c0308203541407003810058190415040b0317500701101807459070b14103064200110030700d038400c1245111800141e0b1491240b85510740560840384d0482e413a6010b40c2159001440114a44040407403d960019140402645481008a4004609440072030f80a65404c2c0e00440c151400000141807600c80116428a413000030106900c80700040c107a0007100c004e5815405801c1c00e4903099404c00344007480a070020410050040c41050441708500300e050181c5e100048440c00034514011250b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 536277329 1250 536276079 536276089
    0x90e071e1728030302090414041e05190609050312040c0b041202040b040608030a02061f1802030717090a02040e0d091703040302030f150f07140a090810200315 70
    0x25075042d02130660900c11326020361554011441585d480319940d80c0e1614003460280c032184070b924900c588850701842088006a40010708103c0c1e1015040303a1140c15034a440e00e00058005a0380060907400302007402c0340707040b19516450380258030405207440c2c559101c1d4803424003402181b08181401c800d5034410009800c2607800b0001014000d0b0000c01c0861316007903243d00c0c603840a41c88078010790080e4208254090351080c42002c00c5149a10b40b00d09030302c1c0061050402c01040d8143e40c42c6c030f034000b02080703040380103500c070405000d0200c585103410300d001d20000ba01c8003011942640170301d0400c2039200201c3c1002c00e42c05c01061254071010031482c10710031211031a11320048140741c03910040001001603a010030070032810803904002412015500101500b00c910301400c001e049810b500d09124140c3c1d007001c128880f03090f0b01c0080d80e8440d2900390040300c61f04115406500d0714043d12040080c0c0f02c10300d401520041c0302940c0104240400d42007103e10b24401110444880060402660501d20342 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 536278579 1250 536277329 536277403
    0xc0905011112270906010207030201080a020405091003021908191b0f1a040605181f0201050a0b150904150f1e0509060a090e071e17 58
    0x208121840c5507501e07072003088650b106510503c046800c0c8000c1c40c0c01d00c4404802d10550301000e40c0e000a480c1004800030390341d42141e01000303050000c100000b500c203410b1036040e64001c110080000d00941084003000b504d841541c0000d900610300c0e10340d00031040c3d80041c400c000300ca40c3c1000a00720320030280b103840310020b5112021120f8550503082c2c0c454900c241e04044003c1d080484030203d44516000c4807030713481404441200c560010600c02044019000400c0e10100c0d4003011200c02490710610001c2d400f000200c100e4000913403004503548020354154071807441821060070412450f1410010801c004142c40802e082c0130b9001c00407591681083c0e00300740c510600b0324404802d4213848803580c0c0e4001c202604014000c4001158400700701001001c550000c16050b81c82061034107200001c241c8041581c06888092a01d807070394490a10704c100301c1c0b4801060000b400e07001d2001c1c201780c6299506131600c03540910740c200c40d84248a0450210764004c2c0e007880b014201d00142d644011007103c4100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 536279829 1250 536278579 536278607
    0x8071b020111011e02030601020c01091a030a233102040207030314041a151c021309061b0219060c05040302040903260112080c12041d09010c090501 65
    0x140710041c841014101c0d040c02295030311100405070310b1f441c100c0002442c3c40940c109882c10008440030420402c1d0070b20218044240010f60b02d550741e03a507824841c0004d0f241d008508d024101c5140844d03030920480341c0682d8056916014048441103c0d40c4040407180c55880ca02014010341c01105401441c041d070044c41c016120341000310fa01741410361000600c100c02c46040d1a5910501c40507500c1c000385030303543d56101c60010180000c0302c1c02c0c140481d554072081e0301d68100f00b90000200c60155917515a040040150300700d030900c009803e9140100180c005000d20451a4100810010105001040b0b400f101c10800c080a03014024071b498140152222021050030300604000c0840940c0f9280a141d020a000b80c6900d21110070210b000307001c0344224580a0345210440c40103008040d100301d00c001d40d29800c40c40003915100801241030820b80c0e428842645103400140005400700113007288204520650804400343c4e07100a040750aa4590001090025030960424070456000d03034a00e0400003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 536281079 1250 536279829 536279831
    0x1511011b05040807080102031504150519050906040504020d1e120302071a07092903090c0a1403030405041e0e0705030c1912020612010e0708071b02011101 68
    0x440d610008014035000314054800200c00090034040004104416401011998000c52961401da020031810b2128440c0b8140b050b5169482038840e550440f142e5406404010720380c2c204c1d42003401d20340e10100341512819001e4400d090004081d03281902c1910b12540e00500003806503051562000d20400662004440c100000b120341e20203d4500c0710750b801854019100140d854203a0f082035403400348500e285054041501c02008280fa600880c804200c5440c034812419410b01810311224102c0d89000d10f486c0e008000c000c1008a0900180c580b010840a95209100948407400718032592503003c3c82d140c1551003044100050304060303000d0402c4040c00006a1a000e021442e41000e0301d102c0885200d8560100c0018455843c00f4011401e50200c2180c800749198955022100c2070440c501c1050307806140c6008a2040d5100d0b08200c500d079100c158085001580c546040121150050320b03003100145038040003826060142c0e40c01b94006000324042c03c5014855401164042e0744202c04030f0b525 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 536282329 1250 536281079 536281091
    0x10030f02180406052211100917010207020901151704030903050a0506060a05010507020a0902090102210301060f0c0809131503200301060e0112060209090109051f151101 74
    0x1001e080380031401107106801c081900d0130810810981408241154100e003200a0141400140d01210241c01c401040e10084c8070b0388002c22044e2450f400550114040850380c098545400d8019402420000e200300c89500709640ca40c801e05001e0b840e0656080c000c1843e00041801d001848480380e9402031091614148507520307503440303a0800d01001022a1181c2c010b070b0900802d8035000f41c0200140c8002e29160782030002e950005680d50502d1f120304107016600150f2031132640d2082c0400d02081144940c01e1034444001e51031a07900790710903c0b41c5ea0014803091140542184200000d0f0361a0b03400c9558141024820001c201004a40e900311400c880c2da40c542e010041849042450001c60159002d00241540c0d6040707401100f1405540610a07454070b01d050203030400b14600707a819034940320b06404d24041503113040302c028401c119042d40d00100c2603000050741c0800390002c41c0b01d003d1600180c118084c0d160864015102c0c280100140c4103814548030100318410400306410401010002c205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 536283579 1250 536282329 536282359
    0x3161107050612091b15090d0503041203090506070f0b09011d0304060305010b120103030807230a1107030803130309050d0308061203070b070e060c0f03040503100510030f02 76
    0x1581c8a0880011607640e418204031303c1300c0303040c800924800744411020700481c00301e400188828030f07140d041048038100072882007503d8640225481c100b0744d00c00c08882d511604c64021046003c8140d40480000703405510100c0d840c20000c09844141d81c1c400c1c00914644059520110340d22001404000c0c0c0d5940c8160080c0340f64010171444401e0101c1e900030395a01c90400c03000505440701600103124940b4100084402e41014940040c1101d030036280c070001c60380711048100d030400c0c0e110101081541706d0040300c1c0300300c200701002032145414070788900742d1015000d00c40944820703480c440035020348028800100c10409484500200c1e0384a481c2070750b2466110000a91020800c100c00c0d80000c910804215240c00e04601380e0481c2099040210f00305000e41d69100e19640008003000c2c1080420002580307a51121400c0d6016003542c0c00c01d895500090b81c0701d441d903a4004d845594403a22a4902d0814018001e00c6014054064091002000e43c00e43c0c5403401da012803000226001b001080710070715 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 536284829 1250 536283579 536283589
    0x6091803090d03210e0d0206060f0d150c080f220b0601110102070501050406050112170a0519020a11010302040e01050f0604050d0f03140316030c120903090314030316110705 76
    0xd04089081c0001d0317075a081250145007141c242d034010305651002d014007156030303034075090340c03414180c116407070325180c4034601d00b0407082c0e9040340642490b182050301c40c1c50703040c1d08001c4080c032030b40e80c403065611640d4034204009000c3c50058410312044101350841e0012076058841c66070b1152040c1002000c40c48080d01441c22a4844201a01d1ba40d654400344410054203016607801030240d00036501d07113074849031607400d00007000c0720700c6c406482400210b100b1054056020b4442d05a0840103940b1110a009000b03074642a9400c82201d8000e03030075500b40f080c0d40c040d10036035054640150544c62907a0809050100f400483d4602c00d5004000b4000001c1c0d41e41c8070020401903c0c4601a0721141d50070903e0042d01126004501002c401414820080c0c1c0c582070701041d040c50038070b038030b0041348104065506031401245580c0d01458a814401d04505054211000c4800c5910444071848400c0030307040c0701f40d2213010030741d6a910b2070800e02d0750746070b9841c0c85014108030b0440c1c4042a80c0c05203558100107a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 536286079 1250 536284829 536284877
    0x40b060a1e03060c090305030f0903010b0d080304031211040306051b04060f020f011802010e0d020a06031a040b011e12020315040e010e0705010c1e06020306091803090d03 75
    0x1622400e50706509004003c4240240c90080d1554100b100b400c9003542d035520345901440c420300212040102d1a47d03d60b5500350044204010060115035a8607200d041011075940202c809034082850039044040102d80f910644225181548500c1c0c206400c5a039000003401c005000a114003001054801c0301103010001840200100c2c2c50b5620404000c400183c00e0203946044214030340d14003170041721045420a180250180d092a0024108280100094552900c107401035044208440c0c00f14505406070700a40c1c1102c04200d85281c0d80c8480c20401050328480c1441a00143c20107000d0199903610f441e0303814a6290742d00306010480c510403002000c907001190000c0e56200e04902803441c600f01441800381713060004000f8484095035055084d078035415071042c03904000030061404240443c0061b024286201c4080e5031030000d140303040600180d0416104e9a00c2900c01d54040b94802c0b5012039919440070140010b54280500c100422501e0088800160b05124641503500c86070103900d1049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 536287329 1250 536286079 536286119
    0x1060314030a1e0c0b060102031c0632011b050a0b39030711030309060a1401081c0323010e0c1305060703051903090515040803040b060a 60
    0x468958031100ca0040141c035000c01001d008040c0003c414242c03e60000580d400706401c0603504400c2d0301e400c00100c0c0781d4862510040c900c148004494081c0601c240c01c1501169041303046620110004440281c411203141301d140890514800e141c050b55029100e40c4440c40200e910084c8101e1003500d549080140218040302c60b85012003c010005403000120600d21400138068440138001041100e013190b03900790400d90050010001400c4248242d441340c142d0000f08040e2601c80c10410030300381d0740344030035515040b14500300314100351440881901c035070403100c0740e00081000c24580310b01d0031004100d054140041540341d00c0040c5c042644031408841c50b40700d500400e131071585440d200c0201400080c0061a00d00410411080d210b04d13080d1110080d502e0032a40c040d40c5401504d4183d81a119102c0a00e4051140034010611a03400d5030260380010302a40a81e840d000d070081080301e5490007110024034120061000c41c001c22030800c046c07a40581c000d003542e19055281e0710b980356482c000c1d03141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 536288579 1250 536287329 536287333
    0x150518100302120a05060a1a090612100501090c0e061e09061c0b1f050306040617060114060301031e020a0f0b0c1e07150912140d0c111201060314 64
    0x1a44c0030030008210240d070210001004100204440d07407036510300d0910700a164800d425813404262940d562600ca19000d8a80c3e10442c1e81700084041008081c181c00d10458400d5860050f10001103401000561100d480041c0780e01c0c0b40c40c04021a104100c05100c03102c100401d070501c0b8407000c0b503e540700103140e0030340b001503540c0800031664001400d4418000c8104d0140c0c4c0c00040010680c00c1c3d40004181d410b519041c80758490355110b012900802a9510401100e140c00003000b0480a0110319603046c0c640d0b425a40071a40280c505200aa10080c880140790005003200c207403a01d10407408000020384001e000401a544e1f402c240f5900c10b0300740e04401080c000024244140d0001080061600009000c82e1a00342481c1c2903910b450b0202449030628802900d4810007800c2c1c401e40354031004e03010701d0b80400603444c0c0c142402009445516200c1c90f40b4400c21414940d03060281b140c83d404c80e50b00076420041c01d1012018031002074000b04840801d99210343c00400002c2c41c2d03500d0f60a4150380600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 536289829 1250 536288579 536288593
    0xa06080717010c210908160c060809030301060905040209030309040606050406030f11090f0102100924050f07050f0702130e0c12190c1502060a15051810030212 70
    0x9010b007115481c00604080c4003450b044200e901d00c3c00051034004d040c5000c8001007108040c100248140302e0403104e100250340003201da004101c240b18803601501c2c804d0765444e82c1643d030305a1f819038030322080c042c4002142c8943d84c02c11403460986c00511358100098184d07400c0141210201d01500d10680202c0003045020505000741036240c413480c9803a01170b00c0c0f414440c12100704002e403064450400c0c0e0a028541315404170f54164020806107240f6041100100071b100054104066401b540140740762000c0c6030b0074541c2403401014050140620480c60007072416403240942541c003a84000a02601c1e100c06009590140c0c0c1c0e07041021011072198040881c07010a03502c0c03c642081641a207680c402d00081c5640321851000151240190008210560803141c050400425098840e80100d02e2040542c80c0701032030341d501140d414040d489000c414016404401000c1c1a4901c0c5030103460f070020709848964a101c00fa8086681d0041e0b0000c1510000644035004200402202200e41c4038070343c030902e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 536291079 1250 536289829 536289869
    0xd080106020610030f060906140c090f04141503071d091203040816110d03030902010801150509041a03190b0f060906060c120309010c020c0d0b010e0a060807 69
    0x7000469100c40ca0f4916925410308542d2a403e9006000b0f0000c4c028581d80c45103201005015400381c008403010140c240054580940c902189601c680e00b03082c026500600013441c2400c0c03c4c083c04081140114815210b030b900c0e44003480c51255840c0c1c0c0180c0c18450764500103560f205001c414160701e1541200e00d259840c164001c2850022220f840e02204481081088089075568064801ca170400790b5000c050141242000c0500e074124290345640030040002441c20507803d944610b02c1a803007038072409016a624540c450500c400c8240c03c80104004020000f440d203001d078800c800ba000b000d44810501100f600c0803918106400900000b07107a5501c6120052041c052140c990181c81d4084000031840d00d0b00101c0c20042c005060503001d850089010019100b0900a11480e0250b14500d1a00c1e4034004400c7ea004e010b100841c00054000c04400c00c101d803c103c00e1004440d034001c450741c1c0c0719902c0d0031274100403004000c0140064076035800001c0380d410030a2089200030205440e016020071108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 536292329 1250 536291079 536291083
    0x60f1003230403140a0c050d08040b13020f0616060608030417070b0d0e030702190f050418020111120d02070c06050a090302010e270108060c030f01090515030d08010602 74
    0x52840203041e207058604010000f644058000081140190b943e901c0b407a1040c41520b179403030f000c20014228003601031105422036001c80d40c58402c0d8000c11802c90740c2d0300e5201024913203c9203205c0280d0019010b5503801030320f0501400400203a16500100082c2216584681040f031f080e90300161f5490b080003c040244025801244102030071040280555034030344180e0003a94131036010a03804150702e030a10080d000c1e00178829200d040d500038040260395461900003c1d280d410341e004a00c07040c2120036020070142070030302c515410340c82c2600d940f00c10a50180c00540d24815030344802145413156500280c00a60200041c205404a0002c05600c502c010300c0c1c140007140362504080100072040c00b04490055000c0d0300c4508032602070230314190780b22066012071341490301d11110341114900100c0f40301d0395400c6005000d048500c1c0d030041d1501b54684100b0703080c02e03100c00d5920341050702e2440010302c0030f102558840c50b0490301e003500b000d52040c0c0200200303080c90203180e0f8000105a815004100b49501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 536293579 1250 536292329 536292371
    0x1e0d0f0b060f031b090406020d020a020a0615060203031b090a030f061d030304022e0e031006050a0b0306061c02032403030a030e0703020a0308130905040b0c03060f1003 74
    0x20407005070445040800041c034281c40001e902503c509a41e170041740c107000d0703154100c610030312900c0d03019907845d10045c0000e59210b160240881c0e00c40d150840340d00030f80709603400c10002c0c1d4400d680514910307101c416520803200d2042d0806824018204032009841e80d5400041d001184202ca40c011900c0003810310074100c0c0c0802c116400114211036440c032154501100300c9500c69030469480a801a2500102143c1206038000c01c46200940200c003075040d40080794104034901c00c4085400c4001c0101c0450203840b403520440d50010084132040c8046203481d0051a8000c03c0a030486003000220f034500c1840c0364405180083d020f50000503c03205151162040040720030458502c00000d200c1408a6074078443c0d0041001015500c40c0905a6010103220f0b0f4002180c00809090004e503c9061075240d81e404411000b0a80141c0200051824010f008841c440c607000b281d41c00c801c0e0766a1210340d07001e6100a01c03055010031990f40280e09030743d903901c2c4180e00e0001c50350000344902021800c0b0402d040303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 536294829 1250 536293579 536293609
    0x181f090207080a0f170c0c10020f0405010507050f01060f080607030e2d0a03110607030c09060c0510060b0301050307080309030c01030905150c120606091e0d0f0b06 72
    0x4010028400070440b0030085030410480c501d003880340040c610404807405c90340d03540d507030940050310800d0180c80400c4901401c40790312140c2c01d40d1142c2c0040d043c0d240c12440f4500e41401419000d000070406d035801440a00388840c0100b041e681d02c85210201d240c2151806c0d0031854641e41101c4040c0702000d402c1200a07404110382c04c00704120390260044643d5140c00001d5903840e021a0b0b184c00b141010140d003d004401c1e411001c99540c052031340b82c05007641c000c0f06418541803042d5800600c10303d200c0c0c040e0744d8151405440d02509107041c020102d90000308400180d030944941c1c81d1076454507480b4451900200fa190405648035410041018202207860340000129802071145180070754000c500b03020245c0e000d080000c0e14031a81c0ca0801d0400103c4074034003030050380c15020841240e16250052142c8149003001c5082946c40e482040014024800b08507046a44100079403c1280480b00c071000070180200214041e00c0f05135516403481d0701400040302c001d0b10b400240312490034400d11840000b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 536296079 1250 536294829 536294831
    0x501240e01090b0f04080708060a05130807031805030a030210060803041809060603080705030403030207060809060708070207080a031d060c0a110114040e0f0109020c0d0509181f09 79
    0x1161040000c145460070f01808500c003000044408416010808590051414000380d4400540d40c42e1a180c480c802200c140002c0e070b040c100002da0001c08850441e5000707910042c0e0700d0401005490403102d204440d031480074005240b03140030400c0c1d6800c018842c0200d200750700400d80740b07a85610000651300c4551005400b5031080c0001c1c00003c0c4c005140704090400d000c400a0150110306000c0c01808131f41c0d002900b444c10003e80b180501c1340102c01070003524025000c4a2400390ba070041200d042c041126030301d03040e0700f010010401441c41201d905400121a00c119046241c9030b640003801d003212260100e0100d000720000701c20442d540c1188021181003107403010304114502c10b82c02c2d120006554001c0c42d07161035164410045e0302030070010103440601000f0940b80c588071000b185171a80142c0b0411710100c0d090f000028841d0050085500d29448003003c2c008004207020251402c0c1c100446072540041c0c10034601c0c1d001e0080144181c8140c0406210164007591800305008007082500260869 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 536297329 1250 536296079 536296097
    0x405010312030e0606011b050307061404060608060c19030603051002070314030c070209101a0c060901050601020d030b130e0607090f0602120f0705100204051008060a0b0c0a0501050124 81
    0x17607a04030003500070010700c25242c25409045460501e0541c868020000c01e0b00c3d1500288598400c1c050341140e01c181c3c403510b400c02005464007056551100100c510f008004009c01c03e07441d15403141003032900806014180403508540307951325070381444031026103130298660100350031007030680c0103030300c0404d00c03410396170203881c6040c4110600e100e4400d401c8060300603000403010a50307209041069000504410340125038142003c819040c0583c032401c9401600d2040a001c02c054210601c91540181c02c141c0060808900e00441500509140343e07895521032001d030641c90606480d406002100d9541c000a003420380742404005d003850207680c00c1945100641c0401340201900081e8404180c00e2000c065030300c900005904503a03611400c0c0008000b8001d9451042910f81941c000e0425030b441140d465001c540c0040b4100d41c01001200d05660100c00803408000c071022440003442e00c4e000a0081d900300101c191540d60a442080e8400b44074044810303200910b1040c200c00e4422108000d280031026 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 536298579 1250 536297329 536297341
    0x3100f0c091a0d0903050c030c031908060a0e0604060803070b07080112080a0513050d150b01050c070909031707020610270b011209110909030a05040b0304020f0405010312030e06 78
    0x82d900030000c0c1d03062050741da2155a014140280709403002c005c005001c503680c8403900003c6a403241c1040200c0c0d0811501544000300150056581d94801d0102070300089480f460680030f42c411903400b51801d070308196203880120b202c04080c00104040c1d4001d041d11131460500ca0402400710344140c1c00f600e903080030500c0044c0042d10507000c81d00e0341d482600c2c000d41c840f5020750707807218036032560b03800035a001c1485a501c00821035005c01803030442c8448182006034200d890010348062007410010b040c82e4004920500c41c1907400c1c0d1103000c8160291400401c43d0b800e1113130510440e04251101c2026030301c144204254801d10f010000042d10380002070401103460b12039081d243d00d003401c00a80c0340c69113030302c0360f02d0059210341560900520040810310146100c1e0401018142c0c10680190240305a41d00140c1c000000100f00c844042043d6607036403802e03181031100481c5401c064000c80c1c0c00b09046c44001500d940d1409424040d60080c5104604504912000750807103101103100c0205400c60300070840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 536299829 1250 536298579 536298629
    0x60203070b1b070f050d1805010c0c030218011505090a050f0310020406050c0c060702010e10030f0f06080f0c031f02070515060a08070308160203100f0c09 68
    0x85a002441e0101c50325040080c11a6607901c014007980c201000c20804240311604c03d4643d5094002c8041d945000540c0d6011521103054400b028502c4061075001c200d59441290800070090007000c8405600b42c5a500161240700c1c440c6408244800040c0180b1090640440062600702681805850501c5041c0421b0300b80040344a503500c1411603588100310b0b601e05004030320700003181c100304550350358581d000a4569040800c12001610902c000a11315041c2102201c11481c0c058580388004610b00d0708008144961580c03480805449244060b0f10250394000c01021080070180400c1e000d0506507041d03d4001000201001c1c0e40c44003608480300e40340882c0d89102d05032604143c4180036205504203019100307001006055124024403a041d01c2c901400c01d5006040403105100e120342e40311911035131001e1500016200110400040458054100c2000d401d284080c00759094242c0380e011100c110380a000007894415215a07007206400d60083d0080054010903030342032542321400101748 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 536301079 1250 536299829 536299837
    0x40f0204050a350114100f0608010e0a1805010c05030106082203080a1503050d0810060f0503061f09091113050411090a0305070501120608030316180b1206010207060203 74
    0x3103e0f2407071011110045010a4100f00385219100e100480c150170700030300310003000c4001c0c070404404a005c5900030506510807450713141210102c0581c05030b0340d110100394400400d03020b0250f54040d1024041c03000024003e0088611001090310380e26160740c54050080c049607002414400c04940032606500d2190204800c1241c1513098640301080d41c4d100140c080c000d0403c43c0c1a280c03200c0c07601c4400410010300180b03050b010764090b81d444c8040e0315503451010111825014450110302c0da18580302503d440740e4040d40d40003000a0140d01055100c01d98081144805210b00c00003070f081c01d20610100b091800703030a9004002403146480c080d41e801d00c0082c1140d0794010302e84100e484403032041d4030403244415581700040080400324029031b00c0c83c22032383e07070b10b401e11889000c220b030044803290150480c814042180c1010029605c6d503650041c04203040755509c070440040c0201030702c002c80d501f9005403201c00540f559881c004e5441c040590361001d03017200285038a04540c8241c000b4420380d5808000c1e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 536302329 1250 536301079 536301149
    0x60c08061c110d0b01170d08220204050c0c01110a0207050f040906050711060609040f14100e0c01021606020d2d030c11010c0f110c040f0204050a 64
    0x10008100342c03501ca0510b03141d0380000c41c3c1c42002c0302a0b00c1c0a2141c800f00c0c250480740550f008000c00b003080407140703454180e003010085c0440e54901c00101c1503d141400001c4007460822a14003d4a00e5400141101c0b001c1c0e40e01c042910000c03400241c0c80b0401d00c509811520820308050905034440c2001b959110140a858060128074001c0260b5440f00d0b044640c09580c8040144180d18003004000c140001e641e24503400341c03040340c0100d0401d0800606260084c0c0d084a40c3c601010038580f12207001c0142031507801070a220304040200504080c0c4034204c07040401c4c0d00904441061100020b2400c0d50001704402c42c03245401d01007004a4000a0028680803682084407602c0b1509040d00030642d4178110300d800ea4014400d414001d1940b40c1c0c48186d01c106140c54002d83e02007264582800c890310380d60b440022450b0310014210560184406912012100086032044103c140214052b1039203185000a42da40103c0c05004910f4150428405050466628201c1c4030030030665200021300c00d041c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 536303579 1250 536302329 536302369
    0x304061d3007030302070309061103030a020304021c0308092406121204060810090c020c060d0b03070b0a0f0809191502032e060509040c021908030103060c0806 70
    0x381055014401600740e600a481401c80ea00c0c1c1e001428083c01940c00f0200840c0042c0d244980820342c540220001c81c1c0c0101e95600640c155910704039041e00a600107841668080d9030802c020b88202504990024510711a40d5500514200603d0880c50728a1113070f600e80034429040210300080301c200d80b949a001c0d50071281600d61344120307412141428a618041c2c80360500024010540303680102c0c500f402a00a416040304440c0c2e9002030350211a9282d1743d040040c1c009a5290200340341c8040581128400280e00041c9280741c84000b03407a211265220b1108a2000b00e05440020341001622240c00b40c0d03810721014174501040f0342ca8403401810b403110845c4a0545100741804280700c0404d55524144400f10355900340040d207900000c40d445649201c1130f014116818121401300d013208101e49440c0c03580d504212401040001031720001030101d0861050b55405a886114015508601c601407a01c5942e20350460403c3c1042d64100389144d01442101d4003480b03c0c60301c42e200740503907100d550f000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 536304829 1250 536303579 536303623
    0x603060e0111250c09270f150b12010501080c060301030507030f0614010e06040e070f1a0d091406100b0405010503070e04050106030e01051003080405190b030c0304061d 74
    0x141d5400503e41d4000350045981c480082089465581704469420300041c0712401c2c800f92072030403c1a88003801d001010315007805006400580c400f80d58000010b00c500000c20100e8503100450915909100300e050142e446800411605000b030011a100d904144c558030300e10b40c11a125150f80d00c46621000382040c81001814050250f140d118900d11001d00d1142032071944c1d980442e00740301c030050324514800c5103000c0c14030791100360000d50b01c03013181c0c00211150f03503840c6032100c40d01c0c0c02018a8140c40d13481c0000c0040c06030034900342c41082c110602c6840e00d03c0c90401e29480651074030000504101d00d0800f490401d0002400c920252401c640091a11942c5c03542c0390401200c00c584546903071a0418100070001c00e403140c140d0042c69240c0d071a80002c122659543c503400c4091502484054086401040180542c0c1048020402a400440900101c0c543c2e5003560070700d03d51040b0303505100241c0c048144801c025050040c1e030114400c520f941100c04600394001c684a0b0700c204502003c800b19a5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 536306079 1250 536304829 536304877
    0x10f0e0703150e0402010f09060e0609030c0306130c08010c080402040f0f0507080714090906211b1203070b06010815030604060903110d140f07150603060e0111 70
    0x40c00040d00e41291001030400315594150000c0c1c0f4450565049005c140e52181e030b2070741640b00b41032180846044d95207240540d41c00c0c0c03051007080c0e48505a415054050482c00c85000e0303c0400c03c9601403025020900d0005100e400c211052468035040b2000303c2c0d0411156540603a8408001038000d601114005030301d6120f1030a01005042201d8005031070b40c180010064419003003100d25110b10015140c0901c1c0c8140701c0c0f100c00302d902c101440d55a001c00f5000114806041054144016000e1425400551003500e203006162815010400c0400e040c0c0c80e10100545c108030390102e216002e041d0043d03050511503903a40340c4581c0c000300a941003204a000062003030316045c080003200031014003039900e40d003440e04200024100700503059000c108040c2285a64076070001e14100b140c101603484c0490031030940c0c038883c0703190f004c1520140600d405000c01c4020603440c002d910300034000c0c3da40010380145186001e00944011441c40303039060b40350448a06e4521003100444014245003400c1d200710b40520 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 536307329 1250 536306079 536306081
    0xf040308091309050c040506060a1d0409080f0a02070609061b06020f160209060d0305030412140301081e030301050f0d0507083307050403082a030403150203010f0e0703 74
    0xc480d10b14403241c28001241c00340200480c1e581000101030701d081c01241c1c0e448092086a100f1221000d000a139070b2810710030b240308802c0821040040c020000316500613242ca0b1607120741c1141201a415510014500c800d19404000b514001c10441c207000341314500e0817001034812102003040c402c00c0003a0048200401c4410fa04a400720b5903118450350320f401c844000012421440300d030032405a03d4200105140b89000c000c1400d0081c0c0c196100c40c80c590b162303511041c02c40000c00045052180941c10058040c0306003001d10701030055903006000b036100441c8441f400c00260028034030f20390030400041c8056180d12211812080d4241c6007640505101d141c00b603e043c05a40c8150014010400c0101d882912929400700c00038001840c82d1071900800f030031800c204030035108000410001c00c01080050600c401420b9200d4903901491640541c00348a203040910080801e884c5420004003881005024940030162240c42c440c00c60a560401440901d80381707103801740c08c01600000d4005070101c2e100e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 536308579 1250 536307329 536307349
    0x70c05011506090501080a0509030f0706020c0a0f0b0f090d140f030109060302030f06090616030912091a071101181d15120705192c07050f04030809 65
    0x1a9500070400d940e50900070039041050050a002616200204203907080e140291405180803c003c1d42c03414403610421341c002d500007002110764035000c1c40b1a0600000601040c1c1c80c440c05a000b48088075014078202c5d403812001031800541c10f802ca024040c9800b400030b03d400c10301070141402000040030004203105070051407a1007000310070001c000715070214240c000004036842503044603841c0c040b021555854140450311038520b40d01000010720206402c1a59195480e0302d03040020789a0300646982401850045401c00802c3c01003800300301e0b0410b5918244046000d01c00f049003080030943d100101031444940b041d040226541c6243c511300300599482d8002c060b4074901c000701064554020341500c0c02201c1c40905600c40c5c40c052071280c1088207080f030380d00389002c0c042c00c101d60600e001c00101340b60828184501c205107010100790801154085c4181004071078950b03030481d82c8141d10101e641c9005100c0780c00c11030306204504003152032000b95415030303900c07402c05034076090008080341c18842c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 536309829 1250 536308579 536308601
    0x901090305060109021306050f090103050406090203251502030f07080405091021260c030d02030a050105030304060c0605131208090606120703020111030c070807080c010314070c0501 80
    0x11400001801030081d0b00400d088440310161021b003d90790304040d91540120b80e450b00134440100070600c1d80398480e9200591007032181000054640e415000300c1c1c58031004413100b04101140512000c41072013071542c0d00b4010720100010032b10504400200070b440b40a0203054032841d0001141000c1000380500a0f28003810340649a000240b6006d2001000c2c00024402e801e0508022a0b0001c25044401200360126411400c050302d02d00601c0c02400e608e540030003010760041d40c24064040b84040178001409442c4001c0d00250300c0e8246415603208403801030b407140d0301c00d5104000c02c00c581500082501c50058005034001810758a4064420984000e02d80050014504400350481c494000f1000c0340903203204022180b180e9074550502c079942d00c400700d003011164001da008000641c402c0c1015442124500d06490604068000051405a2540146445030045001800f01410130003449403010003d180500196811238111030394400080c010720b007049050003000c001e00209400c040b070222 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 536311079 1250 536309829 536309833
    0x180807120209040c09140f10060801180b06030a0608010501082d0708060412020c0301060323100e0c031b010503130f02090a0c030609060503070b0703110a111c05060c0901090305 78
    0x1070345000d55400035110803190105031f1145000481c408100c01c6041e901035500907110010075034244080d05031210f002103902c002c080e8807609001300c0b944903000034601607042d44170040f5105081055050950b00e058119030b01a5000b00440c584d4064080240002c2510040940e01c0c00002c1303558035410008150040081482140b040c4400c01c800c1002200c0040420780c261000c1c8156070b010982620024031000d44801019510389610160082042c6803a03900001220300d5410a0b4080f4415030304000140c403503076040755a45241d00c0c1400c0c0507080a8550303044852070b00c00b0800001034442e0101a00198010f0100b8141e2010071503038000742034405030020102101031034020314110141102e100b482c00041d00f080030002c0c0c11141c40c011103059420040240103114107041811285811150f0240d00304440240129112a41408070702c008501402c90780001131250018000c050802c8400403403401d2882d1181c4000c142c02241c051b030400b40004080740d441801500494050302c05030000b07000c0d8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 536312329 1250 536311079 536311091
    0x61303150b0916050c010e0708070503010c05070803010902070c030f1b05011404030b0601052a0c0901080a0b0402040e101a060703091403030d0c180807120209040c09 73
    0xc0540c0164003140259289020700150441c103091007800c010a50f812000c100010003103808460040d409020794000c01000020b0005617540b055250541960003407001d9000808140440e043c00c0c040e010030f015043c2081403600705940e8490900e44414880d44034a1640440c040c010040015190002140c110700302514000050904076101000036041c1040560b1101000409501881c0e40742f144000c001a140c2c181803075510364014041c0010101d40c1000000c2210410813007450400610148014022501c207061022440303262189031381c8403131b02c00c0e02504010802c1e05800034180c60700701d5015800403e192180c1c03000c1009001c400290106501640c9015a4040c4066000300c05800010707422104542c00a0280031580c89154000380c0041c88070481408410310540750100c0c03914002c3d0440785041c001894120840c2c22009200000604030160101113030014012030015110080140c082241380c040065128600b00c80d00070f0140100c180043e05011400c00700a00400e0116014001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 536313579 1250 536312329 536312333
    0x1e03031218061505010e0d0204051b0415030e062203020115120c1409131a0a0615090f090f0b151b010b10141b0705010e0102121206061303 61
    0xa4150f10540355086031405400141561113000b8100c000000541b040038402525000c1c0400342c03e00070109141c9010401001c2d140c1105000100f00520046240d100c01e512016001020745254103030072002c03580010148241c200c45c40700c5036584480340d0040100c180c1100d2400381d000d40710840f92856a880c1203c0b000800c01d600c10b03a040c18040c400d00c1481d20041d2100890f00c0c8207070611040e140c1001400c00001da4529003480300c080e12500500840b4a5591108440c00b050a0b00301d4841c02c615460388810000604552041c0c01d00908bd13081070314200741404c200b400164114400c13188180d0315040800c0b03446560780e000c042d01140103091251041c01d00701d01051198401401d001100182c460907100c18001803141c4480084001c2c00d8624444480710100d40f81450402c15800300c8108000d850948410b0354050404035159a0242410506d0304002414140c20020700a065410030310300281092032402c200d03a504141009101400d445680200f401d0b070042000140c1c42d0444600301200f = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 536314829 1250 536313579 536313581
    0x703020c0d060c110a2604030b0703090b0c090108310501021819090b040f0c08010e07030c02070b0c1501080a060b04020703020c0405060f0a0e101e0303121806 70
    0x8010b03403070f0351952420791449510079940c8001c55880500340d40d4101d40c507103807095a002e4040c80d9111a040c80c440c2401d850f51140c1c5415602955204046641c0d17114001c20043c59400307941e444081a4003250a0440c0040003a1518200426940503070045036000301502103205501c28041d402e036074942c0082081483d1550003944441c61030300d8001e04c445040203042c50103440201c4802641d903650422645031440701c50103464503000050b4050b450b0f0050f407003000c90b03a101c0c9034521102036856080c1035150000c0785000c2903002e002c0c501050b007007240441c29a0780005500c0d0885624104a503510824030f82c140c1d00b090a03c82000c441052100000204d01400081400d22240604c904001d540e0862040004910508100401613000002a0791031490260701c92544114060b000c0394503100043c0002d03502c00843d4000f030211040e20000d1000342c02d50102207070041e1141c2203200c0144604c404904030102424070004041200c0d03540a0154030406070031100d000c2840310f090303c0506d0440d2401038 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 536316079 1250 536314829 536314841
    0x80a030e240f1302150304060b040f1508030a09140a08060f090f15040204051b0d060303020606040506010c1b0801110702190e0a0e0a08040b09011d0f060703020c0d06 73
    0x29140c282c9440c0840c410a0034010038007240c6074028404850500f0381d8042e0740ca243c000820585145139034075088100340d1aa409041c40890720f44000017480c0100361401c080003401c540041c030720f0343e00502200b06010340113a400c00c1950030620100c406001c03200d000840044d04d5800124190241c2d2041c02081c1a0480c0190b016400190690b05000d02c480b02c01583c0e8050b9130380b080710080f02ca0700800c01504240d401542c201c44d01444074200c0000d1410085000e038042800b000d01d0030782c0c2d01c800708103056040c4202900900111424490b90070004002001d0107003002016001088003641d100a0980142c0c40b84010984e0310020300182c510034a030603d290f0864030b000e074007483c121204298071403002c000b8042070780d03e8031802c19104d88480c0303135020040500c010524041d2248818080128040f41c02400c000d00c0d001c6e0174145d035680740304001000c02d03010404405070302030b0b94400d03d11507940d032010300343e421081960161340351441c0b0704049203811441c050094101092413400c9007445400d422507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 536317329 1250 536316079 536316091
    0x1002010c08010b070b0f061c03020309040f06030f170c0d090609120b010608100812070c080a05030307080717100504050711031b0a15060906090504080a030e24 70
    0x40c980c1e03a0380c41a0b0301c0d00a1080010007071221402c0750000e6656456810010b40010000d0501e045d25445071150380040400140c098001d0303400800e085071603203000c0c0100f03114800b01480502c41c1c07510390f0b1307610b0070003521b05000100f141410500c0317101d540354010140c0b0344000d54803003281c500c9a010000504031390400d004043c0003c50001000c03a840d8004a400503c0f1503001108401b50381c031f4048211030004000d05005c509070302400d00090780d00341c104032050000c21821180307a6106030901c1c4c1080c1c0d00206600c542d64582011190300d01103040442276950082c1e590400d10441e69a00c0401c90302000034416400780b5105510602c002104134608c2c4a090380c2007582c0405c040c2c1c9403850161889100c191141c1307035981c001c209240806040303281c03d6013030f4036000045416110103581c888006100000f000c0c400340741d5032101084136007001c0c0074010040102240401082c241500c81100714807034203840c41e00385519880050b121540801003040c072609400011005d00d64110411070a2560582d42 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 536318579 1250 536317329 536317337
    0x1c020c120706050a1107110d0503040f0803030a0e0114040318050904030f020f0f070314010221090c0402070305030609190e1f060b031311090c1c050c04091104051002010c 75
    0x5c071480002c940d00440d0101a0886410200d80f280b0104014804490000441e01c1d40000e10000542e030140082000140081501a42e10381ca01074825008071000f2542400c880da041840e4042c0b002030712003440b41c10030340514103410240130b145800710310150b06a208a801021207800c020605510080c104200f15440c0e095070b4115108544460303607041889000300f026004130314100001105595002d203030070640b100160408031111840403850131500054502d6100300000c01c44001c00c00d2182c0f04188000f01c504509041c0607482c02811408024095800341e980c0f1008950b00194003c3c5007104200c0103403092181740742000c511030311002800300c00100c8040c0c014208820a245003e80350544040c18a0765065587e83c00c008501c0b401310080030303540b00c001144069940e445800225100b010000c13803140d5100c02100052411194540302045554038000601c04200f000c28220703021034111001c0030070a0380c4c2c00ea03003802c0184174a9101e56400000c184c00007007201c0d0190404403010350203840d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 536319829 1250 536318579 536318591
    0x3030f18010c2001020c04020a0201060f080105010b090906120d02100b12060408070309080d0207170312010302190b04090e0601150c020d062d060602031c020c120706050a 75
    0x401900c2806884000078030349045840601803e035211061a01c1c0b542052044800c3c0c0407070100424226444080c0f4617005035100c040610024814002101c01031409500030030180d0303d00741900c0390394040e50500c20f1080031780101103000c9070323140351041003040c40c00400d403111161110b0002c0e40e52130748502949002d0707081041941c140c2c6010140010140050006400940d9455030b0342c0081d5030110a0840c1031090b04540400c03e42001c200307603850800b00ba00184415410b0881200c611491091088450f40c8100006c51031030741c501c1c1c020303811030340c3c1960f408051992043d240c4101c6a40c0c0d4118085644020900047e07408482d0000c100840e52801640e6007a42c880b00150740308840ea4880b0004200c1c00701d070050050420440030a01c0c140105070020b0314844200114540305000b4040d15614940102c8044940303040e1b200b044000c1401c0c1c001549800303290084130110310940340c1e1114140f070b40403601000d014014001803103a01004160203550318028a4414020901990f0711507800e85002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 536321079 1250 536319829 536319877
    0x30c211b05070309120609050607030236010c0302070b0f090f0a0303050f09060f030403080a0b010f020c01050d06090c0903060b0f1e03101b0809160b0c0a0203030f 72
    0x700302c9500a0b019901c050381c0c94104456020890f10094040f0f5050355648111b0002c038200b803000314003584066601507070320f00160000780e000d00042c030070440842000e4881303402d03007406004130b5550061082c02c7c00d1162100d18142641420b005a000d1100244005051a0490303c018020075400c40f04456107280d02c0074200c24003a400d0b82c28000100818420060488062000c0018154540b0700400a6140101944144003190400e6504a0100d6051028044203558501480d40b00703071020318108502030b030340030002580c0e8085d4a482d0703414488005a01e0019821540015015100a401c08d008013081c031a0000c1c644901c9110595205180030b03420200b51511183c040c50001004162410000c244070a20404d4201c00710800c0d418404c0c1185031010740c0f06030080d05404000b00b540d80c04a2822104003410340383c0000c0c0820002c2e0820100b244068102038420002e03640303007501d10f644440301d10b014603143c1000b1034406940340c40301044107182184840010015038454900841c4092021 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 536322329 1250 536321079 536321087
    0x10060f021612031115071d0a06030b040f090803150d061b110d05030105010f020a020a1413090f03030b0d0803010e15030c0307050f28170d080106030c211b 68
    0x14802e070078031341da100030541c1d5070710480101711000340307510f44400000d52100004050908c164400400f290321081040a149000d200e14000d4031608a07050081d00100c1d9100502d91100400c02803004146050152454032040421701c0d03543d50080080100c40180e039818200807091540c0440000c4a107204070141240104900400301010380701c40342580d007040015a8003884409059085208110b80c0c40003590361125140001c04180c51071003a02e10711001440550403501c4503414560f8240071240000900c40c0c0400090aa00f5140001d0518558000038602407800362000d4000304011001180c0f0700c0300500d085020b47d10750b40c089000701c0350b0f8074241500ca03c4d25041030f55040d08000d900308101d0819620020b1081c8001700080c0c5110000da11544c0001c0100d014120380e540e10000500c010f00342d40700c4407001c035902c003030082082001c071050091844505001d05010162103412070456507029101d260600706883c04459800346002c0d50000041101120007544031888021207405c032400307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 536323579 1250 536322329 536322343
    0x90207060b06120c09180708092103010e04080403170c100e1c120c050c010b19031202032703070501050f0a0509060c031b010b0910060f0216120311 65
    0x5032406040d5240c0c2c3d15040020f1341e401001c1500e070458070034940745145142c80c07100740e1710038003064032001000c3c00c0c0345d05a2491b00035046607442005c4c103482c80148164905006482c1110703841865007610751340d43d1820741c03103d020300c2c4c2c4002d0041c4080609a0500074100f030144c201c600c041d0003250300040700c40200c2802c2d1981c3c040300c43c0260f0480220040e2032540485510418010303070922074035a08560301315100311130340346803020b001078004144820061401c2c00789017010b500403280070f81c840e00a241021004000d5100c000c0001c40190000c2d618903000b4401d581c540064100c81d400001c035004c1e01c1e07106080b4800d420341d10900030310340302007071960203942a11072017403c4c0c0303003e0f500306a10103000b5143d03680030b0509160300440a101c2404076001c10802008407c4041c071144900e807042035065400c0d20140c40d00180b249407040204440807506103000e400302e4156180c4210b282c0f55107030003079040095007401c01842d51780c405400f0030031011a02003115014443d94400c9080303044840000c0e00d17001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 536324829 1250 536323579 536323597
    0x1406180606130209040e190b15030d2a0b0105130c0503070e040e030a031b0509010203120718030b01080d1701060c0302120408070905090c010f0311090901090207060b06 74
    0x10002d1041c2031044a16405801406800b4000042d070610240070b1070b1900c4100d01401080e541501c100200b08101c2c2e03400103820624090030800700c0c2a80703e001a0701d444801d0307408400c01000044e07640f0807010b40071710040251004210740716545200e003000445450240aa64024009070b40ca200780c2800034464000900e40036a140743c15501d402008803110035010b20199032182d12000d91259002c814402030041008a071000614018804d14400800b42600844024004103001c2e4441598010085840d0348035840c1d180c0c0c100345d0740d551080d204903030034101d030119024403204040f00708003168020301c2c141c51001c0c02315045607061501c03c851005168110803281d0000c90010000320340280101c00c961886401518180071a0ba840043c0c9034000c0e502408056010190400440001d4400c26070801c070b6034405800e818240e403001030320204485038500201076440e0044400d0b11031013401e517091010010042c1884d075944503200c20103504074900c00c0d1280d519255000f0b4891411000300c4102c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 536326079 1250 536324829 536324839
    0x60503070e0f0307080111090901060c03122c0a060609020405060d050709120f0201090b0403050a141908041401090f06031e0e0616030c0e0415031406180606 69
    0x9000c200c2448071a0b01c11902d290b42620441c0e2010546200a02801c07401e003100c0310119072a50001400c20114820690089080c00300c05118880483d500c2410006150146400800c0340320414060103140c0e03040c400c000b5a158986101c0c444489000f003a018440d078014007040c4550758517510340d80101d100d03074442c02e50700c440c08000f0b412000b2026000550b1001701400c0ca00707460365488189410700304e0501400c42e501d030403100c12001191307005003985001d4580e64000c1d505060a5654207982c6508000024040c0c0c0407004806560000c2040b240e0503400c40000081c02c203900520300001181c119004038050604000c4840c400c5500c240344d55411100a2035070354a01c40d00c3d104050b00180030b00b1410807000304080e00c00d550b842c4031900035440400c0e9000010100e9151507000c5000030300d0b801103288105800c0c0006405021703401200c103190303100e04072400281c070400180c048038002029440100f28407000080c2c00d10058001c10711910076001c500102042040801201c0e07111758049410607401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 536327329 1250 536326079 536326097
    0x1c12060f12020d1403070c180902010e0d1103070906170d200a0206120103150908180a0302040507051e04050924090a1b0503090a0206091f0509040606050307 69
    0x2d8a0301039094090701d401000d0700712880781c0901d201400c65104003020741d001c25400e0310400401101800f00d541c3c481000008002c880ea0310f5000801c0529840c04041c070401d42201c020050190401c0007020800d0000d00302c41119a0345d03a403200c05010644280c01007450a4082c0900311200810f0700110003a0319501d01c14503403011811010102c5040060702042d2168002120040e1289070042c000e0017200c00c68024252f146151500303400e9054040405e4941c140504200010803010541e141804c0301c22126990021400c0820014811580701960050910342840382c1d140e040001406200031401545d8101040b00e032901056214500c6180d0704440d51100080c0c00703c4030744104c0e031003c1c80302026032441d0041d08000140d002d01c0a40c0c0d02c86546a40e0103040c030000c154004c1200080c0c840f81419401e5281200c092a202d44984801074006e0000095030302c49542d5401c204642c480c40010020007400884100034074580040b410140114601350002c200d2502400540f0b01c0b0707a030342355201c40c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 536328579 1250 536327329 536327333
    0xb010215041416060e0a120f0b0702030d02031003021c080703031104080307110108180606060703021501120c0e010308190516060b15030106050d0e1c12060f12 70
    0x82030740040703011032480c0074403201c00040511201920307000742101d035070300f0440c4000c4008002c085010380d03100201e10950200301d0f20014690b0403408c00300359000710a84081e0390741c0486c180c0c21131244c10102d041761b506c004204011441484082000c1c0c9000b80d4205001c06507011191181ea5901e2101400c1000b05100160000f84070f90401c41c01a42e040126030f08185d0345590b45403450f0000401201c1a400040e00c02d66596032019910758404e00b4400c00d001e8181c41d1032041a201c400150130680540e50004012081c107008003e400313555140140303144107070340c0d590008408000800b2001c9501c0a00d291000030f13411900303500305058982014003c1d240825003080700c07034800f81022142040c000240401c9021032040d40034001250700807100450400c85500411405002c2d0b183d02c00314049003400140310455110381a540c544514040c0041c0c00c0c032a10420514000144102000c101c0c0c002160b210015484001d14043c00c8524170288841900c0d1955114200500e010307d07901001c05403e0100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 536329829 1250 536328579 536328593
    0x30e010306050303160507050f010834110c0105031b030901150e07020c0d021c141b0f0301090309030f062d050603150601052d0304120201020405180415050a0506040b01021504 77
    0x1c40d03080754080e490786080c265020480c03454331840c140c045904a011a00b0850083c01319a6045d48246841c610314a8030654034440e030182c0281ca858200c81c003000045811100b5030010340c8403140b8000b00c042070740da10304000707c07100780880d800d04c011700075079100b521581000c1e1840c900d041d6000b000c07280744002865071055810300c9010b0503541c1d90191a55401c003140d05000900b00e580380001c0f480ca0725102041406811a0494080e82c000d84c94504280c003c42d602400e05c000b40d039448140103288900508001c00034242d00c100c43c50030200c41341074a00c02c0090707000f50b031800359200b02024482590fa036410541c58010b2000080d2146a4900c001299503104000170800f1002010011081c034501034555103172042c03244171203090201c0c0001400280300303040100003000701252009504d81414803000c0340d074100c50302079004409402140072404000283c2445000300310800c108002030b00e8035a03441006002c00750303101405a0300d440d071046490f51004c2402400c540040c849002d642d16180d840741 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 536330935 1106 536329829 536329861
    0x409210206010e0a02090112060e070e040e07090e12190e030a031b110d050115080c22090c0f03020a170604030e010306050303160507050f0108 63
    0x100f410900c040059103c0001200541c0341e0600c0030040e0351542d286030b4013194081c145480801d5190b0100c003911b2003110155503117100c035148001404102d807000940910690481001405100c400c0d4100c0e07808034202d402102c0a2918a070780101c0030380c104460242c0c4403070100c109241c8099000500c0c42035590101e0140100c5031065401912080fa1110f1488265800038884014060030425001500802a06014250380e5a180031030080c0320414041540c0c00d55403601103410f84001588020703414000e4503071407280444030007800c4281d50b5a804c5081c215110342c0c0040c0016001c1006d00001d0114484290a031800c41c410404000700399008560520380c66824440d002000007202c4d03401c03980506100d40c90701c0480004a028056542100d0340603c80040c1c1c5510501104901c0d503401c9000d42c00365103400b5203800801911801c0d0900f01c0d400200864082000310340112028 = true := by decide +kernel

theorem cover : BRFrame.Cov 536151079 536330935 := by
  have h0 := BRFrame.cov_init 536151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 536151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 536151079 ≤ n) (h2 : n < 536330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
