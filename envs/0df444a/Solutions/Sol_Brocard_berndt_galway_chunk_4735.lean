-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4735
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:34:01.352622+00:00
-- url     : https://prove2.me/submissions/a7a79e27-7e57-49c6-9568-d9c440d70925

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 851438848 ≤ n < 851618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 851440098 1250 851438848 851438851
    0x130c0501051908090a1401020a020f03030103120f0309060203040c0305060c0903190c080d09050a060e0607021005090d03030203010306150501090b07170408030705071710050912040b30 81
    0x640351100d65504d4600d0410703d86120000c0c020b01c0044941c001c1c480002c0150b000c3d003c0c80d20f0070390855000e0540308080948a200a0001416040c2039104005100b800307410080080b401602d0300140903559500d4690407038200341e60443d4403401d400001c1040c80b60800031070780c10100709040207160626540009603a0f51341002e2220103c01104020790501c64103c0f0410000d0242109507000900010001445080c02d406910701c51000104045005841011164031042000d0181464084641c00700201c081d0112030901c208501000019001e0b1104102c0ba000306202c1d0b2000750702c0754113501c1d014081e0761100b44541606000d0100c10803540c0e81c4030841d541110886e200c0281e40d1f8001d400c0c115040462801103141c1d102d00001e00083d107442c000014040180940251080d003070b00c0e4910780000b0041d10801040c1c0e944410131aa402103810750200343c201149004407080d202505110b0070840c5c20950064071040c0c40454401113260346940f04030084600d03c540c19040c80c03900c0d05541943c420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 851441348 1250 851440098 851440147
    0x4050a1202041d100c020c0d1112120903010b241c09030f17090c1203120c0301031403070f080a231b0303010e04060b010512130c050105 60
    0x50048491003903490310303031207040380607810920b4498070394400110541e134404a0100c0f001c07807031a05148085252000c100030b0102000289031010700001911944c00c02c034610001c042e8000000032508400031400c0000031ba0805007079150b9504c07074044500301800c44a442c00a50300480c0a07481c0454580a0b102d050500007410591040e11000108a00761481d07940d4010160b405182c011058241130300500002d04146143d521086140d07508408a80300400548104200394041241012580340c00d80b5040110000042101e05151414110419140d000c0ea1144100d41002005000348005210003024100443e0001c40c44d240281d658040303d60080c00000e8100e01d40803c0582083d44101c0f020500c5850602ca00d88214000084c00c0501358050100885054059219111204000300540c0d0417600980221070301603a542e2a0107000e441b691000360704101040000640b640c0d07484c10182d000c2d0800c0a00100300003868541074241034ac09800060620405014041d42d50301680d070004003584 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 851442598 1250 851441348 851441369
    0x31b070302030d050109021201090b0a030b1803120115050a0503070e011101140f0601020a0c030809040207080c0304080106090b090403200d0503040b100f03170d11070b06010504050a 80
    0x21a00d0038128214001c003e0310500850030f04000242c00c203101d4000c0c0070001010031403800a0390341c402c80802107880941444e5002551201c1c10404548902191a0700007100c80f0007515240c0d03115800c0341160302c496080c0103803a40540c0144011143c0211182d21903803282002491300417240e002074400d000043c92041008010008400340d644a40b182510350404a0b00078000210007411407803102d9400c03a080e03e00703201d03030b540080c94030f41c400100b4401d0942c0101d40120006e08503111b820181d4058550a80c0241d001c0014200140b13000006000e0052444c2c0030703548440c10f00c412282921001c3c1c1c00304200f00d0500d1104204c075902c00d000c05230825414280450629480b03034410b61800c4800001444c0c1d8040c40160b03002c029000b10055100b01e01c100c0640d291aa901c0d2a800f2129181d07004403108514400b0040c4005003503150901c0c960f6410b5107046091000c80c84040d0705680914081290f8200b005c00c0302c404104020542035044002406c2c903a061909040114400c84040e205030042c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 851443848 1250 851442598 851442607
    0x10e0103150b01090506120403020d0503060f0405153102120609130b150a05090f0c1b0a12110c10030207020f1507150c0c060f14070201061703031b 65
    0x241e004c1e00407100140b40103402261035000103410b085000804650a0b00540070b01c6560aa04511940403a445036000910a08035400e8500512000306802041d1802c0040e0f05034200b003160b0b988080d084c9100d0300b920030b90300e40e0411581c40350144000100c501c482e144d0042c4603040e107c241100724143e102c0c81c1521458019516109200c2c8501e42d5104081c0c010329070314040c0803d8a580c21411244460255813241503140e484061101c190001c64042403ca0f150901182d50800300710300401101d07035112a0740188186500c40e0500b0f059030980111580741c140c0e0940301c062030304044010304d20030820f00a4004040300402091002c040c50745803004041d40090007200319681c580415182010152654040346140030010442d03500154081d2001c000141e501c0c2c803046450f00402e020011180c2d01c0180d408810341d038040144c01c45100241101d5241c005c91800039004c102190310aa40641c000300e100703480e05001c898003600300c2603021880e410400400103d00140090164460807500040d41e64 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 851445098 1250 851443848 851443871
    0x3121e0e0405060f13050a1805060a0b0111010f0501090e0606010c080a021218012010022a0607030f0b010e0d080f1303021c150f0f091a010e010315 65
    0x200c100d00d0314081c0d0b2002035003c030002450800e5201c01d11540031480c0030402e521314040210323410454800000e0403035024000203808110310350025111200c043c100300f0074041d01d030b0344258207541d540c0f1030703d4a4050b69500100b06505590064140041100300544298200f0000091401b100701a001e0700b0306900003190690a07208010103001074030714040640c0c031240cdca01c01c88420010268105c03030014444000703103607943e510310401404186482e40284081905052010040d401c03c0d110203044085030f190080e2941c1c13072000c10200d4100b100e4042d1085141159000d8111005101c1000c0c40b82e1602c5403c0c04642d80102e100030700045d044515100d14100c0749454402c6210b520a000d014480101c1c101ba0035022540001099034801c441d5403200035008a070220031541d5020000d48207000900c0e514185503a02c0d4400c01155407019000f21301c10030384182c071000746c0740781c03001c00c8606926900405041459411040d17000d4034850381c2c510301039490364480240300c605000c914480642c2e511a400603 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 851446348 1250 851445098 851445109
    0xa030809040e16090603050c03070810050705070b0a020307090b03060a1202030c1804050106060f050f0a02100c050705060606090d021201060f150e010905010519120603121e0e040506 80
    0x14203211080600d145140c813021001c0160180e0f1108a8052042d03041d80e1480740b0b070105a520580f102c400081c01201a01c990450181002920312400c0c040100440d00100b0100408280b140e00104009a070f1ba0900701c400604d40941580859203254041c011700916075a441600d00c115084007812010b1031110b40006070a11481d404ca13107900407010200f58482598009051307110340d020701c2c000c100c401c0c0d5804050724254000740380e5000003582000f1180c051035101c406071a800c811441102d04000a030301456003194000d40b04a004200081182800c200c02040029807155090396200e04051401700890810110f07050000d03c00c4030180c0180d04030a0f02540044014401c0c0940300c5100c55403580e507840310340060401000020069840e0003107a500481700c4004803201a5511031818100c41c1048074450502807420080204480f1500ca510b0b416000d001d01850090000c400080170440700900090004019a81d08042c110307900d44001d41c100d4591114100255000300f0070344d80d1500000c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 851447598 1250 851446348 851446363
    0x31c0507060b0d210c0b070c05010f050f01090c031413080f030408190c020a0504051b0c07060306050a06080a021608070f0605011d041203020408121201050a030809040e 74
    0x10340281032140d50350240500c040b5040102d101098507204c8100d00214101c2d214240c6040181903883c2e80b50100b00110b101e6998002c24601a10002a00c100a0883e000660741d080d41d1500c0100180001884500d10600c0362a00c10030305d60074108014010141c4103100f003000104030800000c2c80d000c4203001c0c8441030b0102e40c101403000d60026503a00d000e24022a00f81c0105410280f40302003120b00e000014010808069002e40051840e2103241c80c00c42080b000d03100041100c0356024a0034003078800030f01e00e4000b404400034028040c01e02e05003020340c0202143d81035480180b01d0a0328140070001c01d508100d2250b00601c4003035006d640c648140041860071400031000420072840014544148141c20843c0080e4512500080c0410399958220254418201c0c0d55400848900b00c007280000d04064880e440c94030081c2405420706031348800890810000c1010444864000608415140d058101150141400703c0e07211581601319100d0710110b003d46041d103402a40c0e12481201010303020000c40 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 851448848 1250 851447598 851447621
    0x5060d05070308030f06040501030b0a0c0221281407020118170d030c022d061602060a110d020d0603020429030109110d1b150e031c050706 61
    0x10342500d81d0b20714203e40d0701d0340102d0350040383c0440000030422610305400b40364100da41003e14034406403030b012030900c0140440c03502c00c800d520078500807024805105c0035030f248030051046042c0e110444442c1c1010224003080b8002400ca120b02050b071070060300100e0040c0903002046450351078202602c0165401c0d541807009035584056a03200181d08031942c1b4540c41c1c81d0307510800f5101d58501d00d8106405848006041901680206041d21741c2c2440b0b020100168a505182100e10000018806810b00102b5a4444600c100980d41c040300c0c1c540411169030030880d602d0003001100305c0e043e4200382c2c5004e83c41b0712001850300010040f080b41000c1d04150301660b0002c004008810032046a9900c1e0300300084080340d00c055901c201c0146180601c1000b06c1a5000010000203035141360411a40e0100c1c64000c842445502400200e0124508652409844c455050b4040a2006080500003104c01e8001a1003a030011148520610845084c003540c0300190902c00c1d00c95070b0328600b95010703209041c2c0d00c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 851450098 1250 851448848 851448853
    0x21507021002030a0c020c031b01111f090201020d0f080115030b09100503010b1c020f061b0307030809030319150302040f050f0f0f2d04032a03090905060d05 69
    0x2d003c1c206804d80c0c0a4201088240c0031103c03007226010900d0744841c25100c0d648600c00c1c80c15200340c0c180d4020304c10042070052900070340e8a142c504074a900d001007000701d208040303980d03124622800c65804200300c0044905a090028614107038110044c15028140510210700c00002505a14640a80c0000da40e9400041c8070740864038003032501443c92206403040300d219601704442c0c01002d007005100400c1d0803040400050b0300681c59024000868104207038a074000e0010415042902c21440184100980c000e004d0740e541c0185003401408060050b02d80c903c039800c20401e1000c0c0703d164080e8902001400e5a0116941210b0b01c0603000c441d8181d40065046820a80c03100d010301c042d61300031031041d148403800461035294810300401828080f145090840150808118806c0d451441507601030640c9050b006020354106a51303103440303025a000c0300401d00403010b94810a840c500c10500c401a012400c4401034030f11f480040041826100c3d405800b0f030745c1d602180c003545542040000c440d8100e0704 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 851451348 1250 851450098 851450101
    0x6050d2f03010c0e010f050901020a02120c0d0c14042c120d021b060403050d1e1109030c04050c0414120607090e0702070f03060c0c0b071106090a0302150702100203 72
    0xb4040355442d44c4442c0c002851000c1002c0340a0140086e6680010103a004203030310f100c1ca50034082080340c009094001c2d40b24107000d40f2041da443d0030706104c1c000d201e01d0160750190700e400e00582c000c6031440c208a01ca1401c0282d8131a4480c0d511012070070324807103c0160703070740d1a00c2d14010a003009032900d0316004e00c2000140e803440c440c0103500200031412100840d42c48604501400584a1078103641c0100015801c00c495030114125400c50030941e0180750004100c9160b40c200c820441c0d40b04410505805400300e1029000d20f030a10840303074041070645062003942342c030000180551045010304000401e2076140c5130441d1300c07641d444070380590f07a50040751140d00700340030050144442c3e84100d00c01016000b00040103140301159000880303003c40140c04103141980d03582005811604440000c0000a541040100c0e501070702c80c601462560702e803d841c01c205a06080e090180052508495501040c00b00001070790000b8040f803074418021303013042980c9644c002207040c202c035813240e035120728000320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 851452598 1250 851451348 851451371
    0xf060105060f2b14011a070803450703150c0507020d0b041b0b031b0903010f0f0f0603020607030807020f010c02012304031706060d091506050d2f0301 66
    0x910a02513800c0780b0300945880ea0744d40c50504080c807000c400c0070003031350403c1c800c0d1800030f410240519001110085500e920349040c06802c1c0c402000202442401c0c150054881d40707214105d101c4101007032058002d000c45a0450300c916a100c00150401148140c0c1c0b000b06e0004c0c036110b1f5007070711080c5034010010207024949051028800c54107440c1964080450048060405480c084000445482400c000c0c1940d54446000c0e00210140c810003101c3c620410182101d03a400313100e100d559841135000040c0032060400c07548220b8151144000a140c54103c0034405aa5110181c4414982c1850b010300141c3e00c0b40000c034100706e200c1c6d410030019170907c90304075400e9030103421500e01003000303d19500c00f0b550000d80d5610b00a1099601902082030142d041142c0240d800349954400700140440d460222a05900340481e401c1031000c0d0740703139000a42900c8003041c0c64081c6100800c0112a404030101031512010880c1c03d0300e41c0348800d100c00183c11810f00800d50b4000e110f110030000c00030403541c200342 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 851453848 1250 851452598 851452601
    0x13050603250f02100213210b1501050415090b04030c03120e010c0f1e03120f020405100318170a0806060a0f0c020604090e0a03020f060105060f2b 64
    0x40c00426541c15000070404007140c41541c410400780c00b66802002d40c04030f04d003500c90080d0320503000807101c1a100c010110385400121084040b0200f07401c2418600111818900d01207440501719000f1011816502c00041ea8000107440584000300252350800403a1102500c00207210b40c800d1000c0300c00454000f05114a030000e21044034040d202c2048200c840c480100c96900002c9002c501103556603c0080101d0700b88001d281026102e000c04c0c111207040e803984103d640410040c00c90010f420210444041141d50054041c41380004600b581083d05010006100245510203c0d08050b50f82c580c15041ca0031401c504048550407044070351003d2140f040765100b07035110614030000300d500800401e0260070b010046403800c030901e1780c424841c140141d400311036040c403114059901001c2440007091540c0b940c410101041c0780403009200740e0545190183c10a280c04c070150038181c00c110010030154413030500301e40c844404007d0455070740c1c2c55241d41601301002000c1c0359283c4148984044079403e20b5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 851455098 1250 851453848 851453881
    0x6070509211905010b062b0e190507050d02030d210609091a0907181d1f150501032c0705040f02031603270804030b072313050603 57
    0x103d000380289017610b07083c08014131070540395204520b45100124600110f0508856400d01c4203d80410306541e40c5040c01c0c1b811750000c95400785036141030b0194041003070400007070004200656101102c210700b40c000a8681c4034040c650703004d00503028004464a40e20000b5000c075440c400c0000c20a50f910f94000f10010300585408441806800030416150441c0b149100e2007411480d0040403e5402d06034200c1001c81040041000d203a00d8802192041c0380d508a0300031250340040052080e0700c180040090074020303000d95202000e1618101000140284265100381e034030a0a01060400d031a840e03422808142070447e000001070390b070001504810124001c01102c0c3d04590500c1480c000012034012440191443d2100044441d56122034500036041051031064000500f00c0000403180c0c1550b00c615144003c0343c060030300090502c01c0080b40440e40f40c00c4003003450300c800600884042031034911b0b002401c604240d40c0100d0f00c03160328000040c8590190401600850322400e080403022000c005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 851456348 1250 851455098 851455103
    0xb0c03102c0f040507031e02090a05060405180d030c11010504060b010e01180e040204090c03030206190209010e011817010213080c220b04020c0606040e060705092119 73
    0x15100454075034015110b0007409140c00c100504075961a50f5a11407038039580f0340c640d10003020421040070141e038810020504c00c01c03800c403021840d8039003401044102c0324002c0c843d285030805038140d000141c3c000542c0040c812210700f4001407600d6255401d844401c94802c1104071903003007200b04030812240d90031200400e402030b2038030100406142d005507103055601d4002d142d404c0a09404006c482d10b19450715400c98005440044c101c1415111070b450440940c1095001d81d0001c0c0500a06c5201c440000700034601c480001c40c10403070202c00090110f04031000c81030400c211a940c000d4040a0a0441e1000705141000c040f41e550715071480d00e0103034118120500350b080c0b010b100015000004102c0300c500000c000c1081010140c3c24108448018204c20b03041c600c140d82d00001c07026a1158402800707000a114020000da2078180200402e440f000c241100c4160080b00a218840d5003100541780906006c0b02c4903858040c2c507070480800c05032140c10070540d621907150700d07000762807400580020342030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 851457598 1250 851456348 851456429
    0xa03030506010e0105220b0c0d09120b040b07140a1107090e07060c140d050714070302011b02010203070501051807090204050901050d0201030e0111030a0b04090b0c0310 74
    0x15100300056a01910f4400354502007801041501d086241c88264800b024400a003062003403615501000d405401800003842c1542c000004000c48641000385c940007400324565601300010160350340302c1010f6005c1d000400090001001c5007540d4000c02002c00f11910841e403e07501e4031030b01000106840c165281e170303e1160044000102c1d0701c80290259490240b0007170014480981b400004444503100b0800030369070740446680c6400352803c1400306c903003245101e0fa60b050f12150305084c03409007c030449541c104903074803401c02040140d8204903111068000e044000040030820b000507425841510401400c40d4640390800c07800d82d000002c02c000721030410040341d000329200e55114003248114086d4540c0111b40d000100901d1404040d03114055106240101d03107007969101d40760035243d990512448043e404410840f420f9114861038460034412030b82031220144903140c1000c40c03e0040c0c020712590070004000f642415401c01e4520040582c2c0c410010f06441c0d01543c07034165442c1c07a0341b01070680e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 851458848 1250 851457598 851457601
    0x150c030703060806060607020f0a12050c10031b0f0905041107050d05072013050a09020127031407030b160201050f06131d0a030207030213110d0b0a05040c020a030305 73
    0x912000031000d110700005051b40d450400e0b1f540030420f08400c081002c0794494000c2601046144010070801c2c50688900000e02e14285110100700d0300ea140d005640c402c252401c038040f0952240380d010744909802604004100042e003003030032100010715030403058029061140886405014500828580740120246c500c8034445582c215014420341c140902240c41e0301c24503007484400d00b00d0603206000010b1120780040d01c04140e4109581085070501c0c00a41d44980c1201596082201c04803d40003543d60903550980c0c917611740c056600240000380460000540c040d0407074404105200155402800d100000d28100c0c5594904080d180385010040d420a03010502b00102501451300030742c8000c0c941780c40c6501ca201000300038644184051000582c001403180034250074861100c00711300a502420459045006201d80200e1041501c0c3d0300c0d074031308020b002c1004036110a03503106100c406004241040180300250480b040364100e036900c03615240c015564540c00203074800300740b0300ca234405000740e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 851460098 1250 851458848 851458859
    0x1211040801140f0709080601060305070215010305060f280519090503042d0b030a0f0633020309101404091e051504021b061006080c090a050f03150c03070306 69
    0x1150901d101b0721545901c0180140f00d8940250006944003c8520485031074030885803240d01040403c1c0d205aa132a0041070038445c01c28801d5224652001500e04541418045101e481a403c0b192010440625030b440c0081810020401d0882d2005032114205000c00c3c0e5a908005489510910681061003215505680a40c1c80902c04516101c0d0380c0d5a280c1603d4644524041d0a030701c02401940859a18840c204100f903d1303100d0400607181e1820480810210040352821401101008000c800341c80c41c04201007980c00012141194019201c1c7c101c1031803405416034041f650318458902c00000401d02003040c400c1c0d54407603800c45215a032102481d000c807010040480d041035810388038500300c440300b1703e800b401c082d0000e108644802c6204100003480140c100e0805034241c5641da003c182244c0200587c40c0c1c00040e0030340000d20305943c5c610300035500b030001d2040f000340d01c81d6501030855200864200d03a0140903401c0150100300c503e0a1910b465400c00d802580111110004607103081c0b408540c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 851461348 1250 851460098 851460107
    0x4050a0f0302060d020a0c12050c0d02010212011202012c040b040903020a0303020313060f0504030809060106120c030f0905012013050d020616030806090f06011211040801140f07 78
    0x440b40c015001030315080c940440c1002a60104409030184003600401800244d144074040400f505550344080c6c4403039081d80590f08001882e00c005003160700501c01d915401881000190440340113200e4036062444607c01039404071400e1683c801c0c0369450b1004090782080e1951580d075844001c51382004036120390801c100854651940240040e0712010701c0c0400240a42e00840c0c01c448840b007015021000c80d5146002e4500140b03007450700a40b00c0342440201504143c0860b00600700320007034080740d07050000040c65070540300010558961280d01c00092140258042600c2021128062007086010306006028004400170340c5000104038580f050190009825281c0c84040d807080e02c0a080e20708010003002458608003668002c00070064040720392101e001900d5050300c65152401607240000c10000503843c0103002c1d6000d50344090401040da0b902428000030350080f00c070000382151035445c009286000d560070084245d131815030810f0540c00d1300c400d01485200001c00c0c1e900c00d650f03038010454 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 851462598 1250 851461348 851461379
    0x50703050901180503010c02030904060b1608031003020901080c031b0f06071502131502070b0304082218060816030311121222080d090807140304050a 66
    0x600294052040151542c070401c180b42c1006541d883c0020601d40342c00001e421644481c0e50140907034000500034005080c1742c01040d00400100004908214180c1c14a280340445a80020304090b40000069044581d03250014041c6401810031030b03030f543e10b0f402655542c0e80409800e510900c140542403504000c1d0b1508051260300140504036008030600501c0342580000100f22a40070100002c03203218241352003c2d0910340345003c40340b80441c4c5481d440d41948540907021400b1501f080005000c85061002100e800940c4070381c2c03503039880d440c2d1100b6118541e074100a0a00f8010f0710400020711150850100c07002105000040006e5503a500304640e65051881100440d620b404600b040820300801480c0c2c80090080291180c0e120000c40032011507100800c1081490003030024000d13100505c1101c0c02c0c40e030350400400550380d07c10b501c038110107004942500300c5044c1c913106220104144001900e54441d4829801082c0340084941c403502c030b800c58080c0c0c5000b048081c000046950f134000110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 851463848 1250 851462598 851462603
    0x2030c040507090501111015060906020303090c210604080c010b01020a150e03161a060103020a1211042301080601390212160906080c061810020c100507 67
    0x81203213004019984007042c40c0495402e406440a41040e07801e841c040e044039400c8080c00107400c18206000581018895080201150b02c1403003001018500054813074100303c0c00300d91101d0300100e00358284107194060902408140202d10a110400230000050b01007415640001d200c03028040d00126500c125070381018040703000301c041e000086038441e0300a942141407a41524501032003a45000758030500c1c19001c9a0311a1008100180074034403410b41900f1042c2440c1c2035107000e00780103004040107030a40351042904d070384e0301b0807002e0310000c50100d44c020407900e04c0341143c28084900c1c031101c011041c05409d002c600c500c400550990f20941c00948280c08181d403003031019414030700044445040c480c205684420749620b1401507a5400340d03c1e0f030859030a400500b011520448482c0c0c07000300950003115980e05200701881a900c010480d4030b04c0e18416078019468000d042c82c21b00318160701200c601c0e004004141d2281d181c03980170030301c400400c0041d50700315001c07610104111000e126400b400f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 851465098 1250 851463848 851463857
    0x81c0501051009120609170a0201050106080903031807120303020904050604020405091f0b0706050a0b040b010c150204030f080406110307030c030f120f0204060809030a2f0703030c02030c040507 85
    0x184036007202e134448a03c60714060b001c0040e81010640da1010704072100507280c2c0d4902d10100708044200d609004440c00b4010601c4e005215003480d1414940c0c0b0300000e82400c15614161007032001039541000144002c1c141c05c41040140146070070041c0c001e40c000c0041c54082d40c20b1000050310b500b018002c903000c444010300002c080d55603202400181009004103c410b9800600c0001401100d0001410b1803500031000010a8203103040800c085820380034505d0b000b00e0034040c03a6034250384c00c52950a90190070011500e01c5080d003d2900000f84901c2c0c100401709000c1c4d40a180522031802c01402c10b5822a480700880c0d110240f10b410743e28003070a640240000c1c500020100028480c000102030751480b0306081e003049402c030111030151074421410400080c0e0101e01084540d44c48010180c00c0500030018525065002ca8018a1000d1000d44910504203000102854071180407281080481010a540c441c0340c480c42d000303000072070b125410b9100b0700c41da000520742c40c43d291140d603015402c5501d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 851466348 1250 851465098 851465117
    0xf06030106140c030409020301090c030f200d0b030601080d08070c0c0b09040e01050a0c020d0806090f09101b1403090d030f150f0e0c130b090607081c05010510 70
    0x301c29003d500140b50485280414080060f80000d81e0010b58060710001030081882120b0880040c11201c40c0040c1c408440c2c208030304208000b01060402d100c200c2c81107141c6942d0300349401d0b200d028085007009281c142c410200001400000400c180d18060780a9072454000c0e1510001119a4840a04081d2482d00110410030001c41d140e0014084401c0181c400305d48030f6400c604003803c5803400c0f20403148150b1126407441266030705001e2402c4c181c02c2130400900b20308050011070390000c4000d002210f140000e4001c19018002004080c250b000d03042d8050041c4140d0ba01d42c612000071843d444000300d0304140c04000d12a0b910350030f80f0320030204100203004140d42180220040c100310081c0103c004e649035004240c50518800f030602134448581c14101451800304960f89003900200014000803003031001c43c82d00741d040d0307035194111410207001d01d4481190a0006800b445407071001040900001142c03244150041100340c0d1201c00c1305001c0009aa03a1014080324850001c50315002804880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 851467598 1250 851466348 851466377
    0x80313091a0d0309090e0307030c021e03030c0109030f05072a1706090c030c06040e040218151207060c0206210c0408060a0c1706120610050f06030106 66
    0x1405010600320300885a00c1000340080491403001c0703011003d07800510143d606001c04411801800c1480c190b00e002145412035988000380056841d00c8020b02c1050046400d0b0f140034041c640245190300c00405803030f078a904000801d03000f0080b0b4601100816035507045241e801e40900c080d600c8007500003103100c03020b00544084034040d109000d55035803201144240403032141e00035010504d04c4003224009041c94142500070340d18002d5200b030a984a50b025594022550312404260b4007141d0000c0e4881d0b00d5034a4a00c00a0107500c0d008081d0030b224001e0030108418058103405200c2c420000381e42070405904110b070708940350291405020045060030040c030005043c01c80c02003040d20300300c80090000c02106590500c01003016210600840700c042001e010704076040c44400e030400e00f000000c001c1500c400601408140840d400090441c6600000680d00e4a803010a41e51403046241921a145405100101c40c00d60b1070040b24011105422204500d040c00030443e03040c0c420701d0710354135030404509 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 851468848 1250 851467598 851467601
    0x11103071808010c09080601050307030804151e0c0b13081e0904020406050c060703020c0a030e0148080f0c030c1009020f030d200c0d120908031309 65
    0x1014440d040408640700000c19001c00c0c0b154130a072140c0c564880100c0c42c94640110b02e8004180c210500c82c1c0c02c5601d0410000c1ca440341200d0440b03000c003032055103a109210050300c0001e02c1744100d4000e413a07142d40030400c2d550310800c200f00c5644a84074001141d102c10901207504522140014841c200c100039102100d8000f10b1124070302000c45161615058441021800707a800c240e02003400f00d0340c0850320b600d1405040c8869a031254003460b04508100d0030f500c02c10f56170b802862000d001d00c80c2c07030301400da2a0391180131001120401c80201c0048030080018604014030740320015000ba41404d210b821800c14442110031116801c941820b080c886250704035070032944403915040f41880300f00102840ca01c02444100c803980c1d010318000031002840e0041c05080701411031007034407035000304400507040d6401c01c00032480810007101c448803210152410a00c0c20003091100c0d03501038044240001041045607440c04545041d0b07076204945980d561020380c0e079000f803020b58003404941210902c2070000e075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 851470098 1250 851468848 851468867
    0x70f080a0e01060807030c0807150c03030b04060b130611030c0615010e03060405030a0305010617041506120804140a060206180a0c080d020c010504050d02040207050309090c0a0305010801110307 85
    0x41c000003615a03891051900d40541a8021a0141e9508000700480103040c0f010000800c0c100c40181c0d4800401c4000520f03030650040300401380b56542c01c040e03010351501c1c2d000d600a440500003003651001050810089241c151041c04001081800281c034200030200c107980c0d580d41c0c00c800400280d12220407040056451000160420480061102850764100301c0d0341c0c0a81d0056001e1030741c90180c0d500040a565050b0070060603c03030710000c1865035400841e905980075800c40030f036038410300100100da070240c0360942c008140c50001548050138401c1d0400100f084484030444c00e44000810020301c00d0b10810303440750030b0144c2c110718002602c07542c070302c800c5842400218080c1d420402407540c915150103803d4028060540c0007411003140700d0380402840c01e00d54000d00b04181401e150800107110300d43d004a000f4095a00894540f0401c2410004d40e000e0290060a0500500e400c901d540c50701e0b0481c10f4070100081c00c00d0b000041c3c0600c1880f4581e444160590714174a166503040064401411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 851471348 1250 851470098 851470121
    0x221180d0903061406090c1b0f010c02160518070c02061303021207081207050c04050703050417030108030a0806061303030504080f071202011103041d0f070f080a 71
    0x540295214448140a08984101962150070711182141404001c4070b00301544022030540309002e03c281c0d661040c03001d984c40690500000d0b0369508202a101c108604405580a140710782a2401c86482d0103401c45070303c904490342204d041209665060f10b58403410b100b62600700d66101d0700c18100c0652052000d030b0045c0b550a1000c07600325268017294095011181556074103070850428030461070051030001200e14041c0c010130b0403900780030301b00d034407041c070f950103101a07600002e9504100031081c403034043d28540c010300812042c500740c2d1018014090488088580c080d5000c089061f0314441010741c1d0607107030000b005504098003c2029901d030540a415940d01107014088096115105c00042014502ca5a601c03034440d840c200b0510302c3c01d8880034034107030141c114200a11520100040d44101c49409203000c1c1c031005a281406400d51160790080d40c1c005013000c40d012020624441c00710301415014a150060307035aa0802166440c01080ea48000170301100c0104400d10590380146171402c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 851472598 1250 851471348 851471371
    0xd110309064312020303071d0d06050f010602010606110606090c1c061a0405030c060304062915091c11030304171e030d020c120307030207020406090221 67
    0x445620040c115001110460b10740d010300350003100704000790800884401d0000c2d0004505505000c07401070b081d8007404100e036407120700719130194400750344854610b41d05603009102000365051100c00c0c1404d642090207024055800c114000600900c1941080c40400582001d021140c881d07808100b44100080c040025000b014031482076003071100301070100c044407080d10010f140780c64013075078401e510800c09012040700c909220402c25030314041003901d03d40008442e825501da590b4035212000b0249030508080800900c50a0401c4a1050f072403030b400440116450686034a0300c0102600a22410314000d40182c812006590591358003c005101c1510a84030f00d803070b461a8202003891904250300c441e0105581001080c0004014001c4407440180f4a61340e41c9010b44044c000ca0f80c2c0d10030b0b00c8212840a03400902d4049050050220303400900c4904541ca90fa0700300100010041c1d00a50b530142d1265242900c000b0364901c05108031002244072080c180101015070380c405040010007031401c003ca5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 851473848 1250 851472598 851472667
    0x209010b0901051b0c0f010306080706210e1b0607080d0b01120219140a0905090403020c04110306130e070504150b0a090f090501051f1806020d11030906 67
    0x625185198100700c021000003403185e1a2031404201041045100c500d052510b44007082c447c1800200d600b1080c2e03205030800b4110f6182032085184440c5960845810041c540a44500c6001e4049500031427441e0306a118029a1030074801c229080c407034244000c000010802c000303030444565070045001020141000f030300c0340e031006402000740ea0002c2081014003003012441c2a1058000060741d98000700101c4d1241071040c0c0e64409032485010740034083c82200f80308001420107100300001801010b01600c184151002d24250b08810341043d50040e02c60090210200b80844041c41900140340d4044000d00b1074501d84005d200c01401842c105d003c5180070202c000c00e04401082c01882c41d401e80381d454001d02803a00e50608144413072030b004031410b6070818004000a1b5500140758110f5902070301c0300c0341103a4a41c6000ea90850fa0700b2038441800b09071080c002482070300030501c2c0790001c0315600c0e9015074002041030f464981c0b10300c1c0b0500340e00c84c2c418801d4802c0c220404104006c0c03500312000c88605c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 851475098 1250 851473848 851473867
    0x90504051603060b040c0201180204020f041d150102060f06090c0d02120108070e040f08090d02030109031101060918061104120507030317220c0b0a081005030a0209010b090105 77
    0x71000c090b08150348082e01c5140780c04640c240307407152980940d428802049810044480d8244600700504060311498010506105000121040714010130001114900740c1440c480300c449540030440e4802c40500c645020700901c1e500124500b48a4021450030b4a0259100e0782084200100907101502c0360a050010110a0f05c5c1440107011000c80740d80f400701150315000f11b15142c440986c000c450300700d08440501000030f4081d104400030301e601000d0320341c0700c02c030b407030041000c00606010203581503003884848024035800c501ba902c6419510030080c40880d03100d28500043e20642c4607115030b090505084440070807960b612590900700000703d91441c01d0340d01d1030100d41d04540c018065a031900401010420140c0155000441032140ca410a0a924024034544018294030740c4c2c801ca40307440307901d51200700541c0484400141000320069520b4402400000742005001c480c0791816840041000c50315240002e80b0403034043d4002e180307080507801c0503000c031410f800c402c0d604e60603c4014804c0c0542c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 851476348 1250 851475098 851475133
    0x812032206180b040b0703090b0a0504030e0a09090b0a1b200d05030910060e060f040605090705070506100302090601110a0213090b16020d0f1403090718110409050405 73
    0x142280100840f00090404d07051060811070b01400c44800e00d0b20300800b240016400c2400b580c1e0209100c1400265590380f400c059440d15070b0480d1544c2c1c42140080042603082c0c3e07030790261240900540c00051580e9450681e031080350b5181381010132011340418a401e2251294105071800b0041c2e00c9002801228a504c03945040c0c03010640c0804208040100300e00c0c05001c000c3c0000d09903090800b07110f500c0c54601c190720250740203003019000300001c400d081d1031501c035600042c0c000c0030050083c210f00e1030222002440384d008118100c0c0c55009200125080c0c5071500c482405880d0010256403407511003100649044000009620160003440c071400b0160360340d4042c008101303195082c0465000100d2500b030301d401e240100f507a5540d00039200d0707459000d6400a419483c81180b410308007030f01d80c0114000d480d0126000b80054807824000104041c1507004904101120f2480b5461603208440e00f500d802510610503001c50740c01c5003407104000c0d41000b81c10190b0080d0242d401e0382d14096481000751f4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 851477598 1250 851476348 851476391
    0x1e0b0a0509090a0902100806010c0b0106050c15150d0c03060c2f120a1101243003090312020a030e030706050d0c030b100206010812032206 61
    0x8003280010401450740d041445403140d0001e9003410401984000341e0010f10041e2035030401d2020041003100240850740030344140038102d0340081c403031091907940300c100404907400074041304128040c0c004120481e091001c2414090400100c41c8185034180a00707200c60340b900c6600940b101c400c0304400001003101445040e00700659903850f654002c9004d41d139402c0d187e030070001542c0381030300c03411101c040f4031000704105071109440e055a03665185a0142250481c10300410241d1a500e06407600002031003042c800642403400c80c00301901c1690721004078541d807403014002e550141400300a502c0303042160082c018024440d041403404d464507911403162140036501c3c0000546e00c401c010500385a004030a01c071098200314001c140b60b0741012801002809203091a04000c0e40304d421428405000390002c60351030b04040d1501c0700742c4031200d40081d50344100384541e410078040c026003c60b9510508084030720400b100c280e404042180c120360800f5003c176201d41980d10702da60304800c41c3d140c0c06002c0500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 851478848 1250 851477598 851477617
    0x6120108060a0b090606180307091104170d02070b091f03050603011401150e04110703020a03080a0204060e060304230d170921070c0312030b01020d091e0b 68
    0x30071061401528010458105140091140c1c00d00d20030400c0a540b16811540c0c900101c0021010084000c00807a181144135044108402d040501610008001038007900c08c0703075059000c07400c140c0c1032021210745643c5460001d000580120f08284501c0004500070644642d003d0201e45000c0c0008044602c0c200310418000000f0f6142e13020702c8068078090003000b02000b1040000000c07540f4280001c8043d030810007102041c4440b140c242040d5550f240d1025401c024240100c40d0780b481d080c40c00a40301c0700404012401b0460403008650b008c100340c401d44081e665161517410183c0d07011810003060707820083c01120340c2c3ca02c0802241c3c54001c0600040300c41038005006203481e03044044003605400c0202000603198401100300240e1410000d00c1541d0540402001103404920b5900d240700c9103d4000003803d2140c007400d00004000c2c154603418181700d80c0da5401c00929444c5001240c03a9104420143c00003003820380d061214440704819603400700d15402c040841c080d51141035003866040310048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 851480098 1250 851478848 851478853
    0x1b040b040f09200307121d03220e0f15030a05010b0f09040807020d0c210c0b070c0603050a09020d0501060e0106050c0304090203041416082103010902070206120108 72
    0x30000d0385202e00400d032014506000701000d0b401034a5041d0f02030f000042000040103400c0c0108180e0302d425900454045c081d0400d80d0300b10207401409a03542c0e52103c0c40110070680c00b0080d42040b0b00790844044169080000307904d0342c42d210150b000c3c0c1908409030208a283c403c3c0e085820b00c80c0e60400c03d2030f260b244141c00101e41c1100c0581040138a00c0c00340507660040140000b000000740d041e904031008580c0c121080d943c0f400e55810101d14502e4180c0042d8155026100b0480161241c501844031140c0315200030300b505a16026030001c10b00940600504050400400703100c0240250401a0700441401c0000f414400d03c0d0001001c03c0d42c8248151050f0759608411b0240f065a0b1030b00501410036810304626011425615564070300c5140300da180500d034084045020002622001100c2003003100454030780410690147e00c1a040c0c0e0b10802005115520038814106061010182300c41c46076441d460450307182a1136017020394048030049138040b404104d011000b2003243c24280c043e0000e40d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 851481348 1250 851480098 851480129
    0xf060403080c090105040306111e190e0f040b041e05010f0f030507030305090a120b060a0e0601231608031603020f0a0f030b03030c0a0512121b040b04 66
    0x140900300e200081c00c8801d001c2d00800412030310766040720883d0300300e9a101e0700005a070703441515181524022070b640d8004450300800d400900955445c040c04100f10074210851001701804402d0b40c480b24240d40954000024084a82c03161800e82c1c01520015001340000c9400320016215144d249001d0b101c105c0510f680700b0050126402a0071a02c0140c401720f035042c03030102d04540f11160ba4510230701c0024100640001c8003400740d268901c0302402810b520640d08501e500c145171600d6901e00440e1190302503001000006110019000c545000c0c5c4010385400c0703050141c04d42448014801070060b00a0840200204640b5405402c03000d94441c1c029a0755035128140101000c804040c10540e040806006200c0d4221010000301200c00b0701000341402030008110301403e40c007038442c00748004d81c103000226203101d030807101252140001c1d206000f5569010701140320b03034125000d020b1204207a10700030000208004418401c120300094400c036190300345541d038000c4d404160b200e03806c410402c116046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 851482598 1250 851481348 851481353
    0x90c090c020d0905030114011205030c060a0f0c08040305180609181e061e031009261603030c200a0c0e071403071b0503120f0415020a09080f0604 64
    0x43d40300081c2004600a0080c0303290101048903140c418010702d84110001021a020031504004813200282100140c41c000e203007202841006100580c0c0c0341542609200d8503582e02031040f0b168a1043d589500c40c2810614180c40f480031080c40321400907001701080000d0f043c1130f50b8803100910410808060f41d2800d07d0a160381c40382512000703031540140103500050041d159036403046800c25807818035080740341880702030004e45408501e15040704802c5ca00301c0503034144000c07040000070304003086075038604040d05100c0201e101d10410291109407101d40340d081b40000e209410400460b6260b01e4204401e180d080200240c0184444005259502c0380c1100c0042109008004004004c41110352080d450000c40c05007404658054541901ca00000001c03a03403805103401d00b0b40d9201c0310380c3d004842a102c0ca015542e80c0d01050181c81e800011800203138079008001100c500c1180c0c030000c41100311a82c030b10608040c0d040703015828180b0134004030110300c0e21010030a00c0b420b040d442008001c80e007401e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 851483848 1250 851482598 851482607
    0xf0311030118080711012a0318050a090513080c03070b0604021c0b06130305012c0703060c0e061908090601080a0f05010207050f0303071106150103090c090c020d 71
    0x9010003100c0302c1d48024800841c0003c800d0391306264102c1144a41c001c00a00101c076850b0b50308000e200a120300182c0402c80000480901c40403d210b92034504003010103425a03401c154151080c1036101008001c01e00c01020b45801490304964901000400c601e030541c1c45a6040d0490301c0c4070b0180d40c0c40401c0e07210030b1049403650141c01a809560840c5011004099001c151414840c1d2038900d6072281c20910325600e07002c04072a401061109403040300307500c91070124007174606103a006c41e028085007030b4a11401c0c0070918110506032080001e04001e880e607035812020705490340109c420b00548400b240150389405004102c080030b01c0079440d0441684001c0a4940000642248450791207040140920700300020046400380e013104140c1d894440525100b406403046840c004e140b17008405d5051062000003001d035005560366103c92540884094010b84e80c2d074000c03903150300c2511025a0540c40d55019522441946010741914290207071031344d80000c140c501c210038010050380144440d000e801c0d800f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 851485098 1250 851483848 851483861
    0x30f020c0612040b041401050a0c03050609070c03270306020705011802030d050f0c0f060103020108090109031e0c020928061211030f06040b2410050a02070f03110301 73
    0x440701035041030903942111881d084000c00080032080c880012406100d4282c00f90302031110000000e00c660711f4900100c1028002c40320b01003000c41c0c14100401d0440c034049040c00d21592207a0350340001c0162684080f01c13011172016010880c0c5180e40420307030308150110800d0000c0c500400b405a070b142e405107406421690020303005144258048180740040c1d8010890240300240c504d88280c89407420410b80071780b8850118201030034030900640c20202240466058100c134000d0300e41c00042e9550003900c6003640e4045030002d00044403a00e0041e01c02039000001d500304406864103410140c0c0c180d002c2200210151188400f000c58041c04c05000141c0c001b0441140b501c0682c1401030324030300440c035003104d801d0980c01094075050484d03010042d10108550b801c0d0705040e07005c58405080908080310840c02c280c0701c052004450f0340380d1040001131104d18041c403000c042c10b5107141082280d42200c0d02c0d088090003108500684100041c1e80210307052450196001c0c407404400c1444550408d400c4072a03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 851486348 1250 851485098 851485123
    0x703091a071a150402030a0b010f050c0a0314070b041406010821030a02090303040e0108010c0f1b061b0203030603011a030706030e012310050405011a070c050d030f02 73
    0x2010070980000403240014001811220030124480c2d40f6240b10030340814244201c0950414070100c2003022098590300150794600c021303202c901c0d080304410400c55651064840c4011a0b03440b003514540000d100f004500494140c46800038202611551030028040054130143d0300010f004140d030280c1c1a043c0300b05070042889000400344480c0341c0d008201c1aa00d001a112490140400080c0c0b8000c00354040b1011500010160b039a11500c440c2c88818602003030286400720f62a01119191141c00740040205090143c0c0300e01c3c0030400010111403032007485401c101d070138070745501c00701007508100e032400d12494402c0c0e005992203160400900d403c40e40d01d00b002c01c54006009119504a460105203201170b50100e10300070841901031461b2074094000900b080b10b0480c08440024042d01514403041d0103a81c002070355803001c070358800400007034940030301640c0010300c4004d42c0da1940c00d00d88030080810030305c5000200c0c0b61981c0d84000443d00e81c18010150081044c85e80d07182c1d20703d070b4184203171584c003030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 851487598 1250 851486348 851486399
    0x9120304080703030819111e16060f0e03030114270c0a0504051c03180b0901050a0e18040c0906120f02010c02131e02030f2208070309 59
    0x3498004840e50301d00030742c407001c2e007031184140105035001c421007030500c100301908109200c0d010b80480840b00c0350380285012a840340b86640c00c038020800e500c4c09c0b90074400b42c42180400400c00d50b01c0d007a00600d00d59140c01245075030b58001c180c2da10720a101940c02800c54049101c00302c22607805000c110318605444880c01c01061200781121080c180c0031a8200c00c220115580356160244140c5261040d90800e80c3e211070084628524078094102d06c543d0a4466900e5005540c080d0310500583e505501442d40000d1080c4100403495102e50060480081145000c001c1103200501183e1744901800348003203107458140800052104800c41c560080400314020040c8074a081d2047d0355900084074000c04d10640d440e0340c0f01c19a84152602e00e4040c2e00101051140149080840004c102848130201203840616610f5404082032080c0da10868038200607803036030354401864556641c01c403a080041c3c02c040e5148200030900d144054180c013032003525011002810801501028818854038000c000b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 851488848 1250 851487598 851487607
    0x2150c07120804060e06040b041e0b0a080601140d09080703020d021603020607060212180d020705010503010509060301021b0109020306130503090108071e0e040b010903020a14010201020405040908091203 89
    0x50b4039102114110344e420314001d04c040742d080000580c984034641c00f21240c00c002080100c0c045c1007000303000e54160060a842240b4030f980e88101002c5024015010340401c10701310021300c0c90b5003d001443e00840341c00300700368901071500d01c0d040103c521035203080d00d80503804140d850405404000c01d54400d00315000420341c0254150714246089003074000240501d0300030804c20200421501900d4194100d00030480071442c0c80c5410b41c2c507040220121001c1c070310404035500d0405001207004800d50304183e482c0b0703156a0800c800e224518502624003a010b40d401c100070410743d8100d071407000c9003640042c00410703001c0044c01094a0304001805400c101200b19161400084d00042212a22442030070080c10550b01c00c0c0c0242c80c19400e005469401300e410804078031801d1741c40642c0300700408084070100f103101c60020046807424102e01000390403055001d03040c0440507544980508075041403002620340b17600c800202d07040da80d0b001c1c000c40302d040c0040340f584200e1400e40c040d18081c02c4c1020056041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 851490098 1250 851488848 851488853
    0x3060604060c0201051207020a3e030c0d03090311030309010804140703140a02010305150f1c1b36020901140a0915080112030809010902150c0712 64
    0x1144210300c0307280c090107a1420641e04590044040d940c6c0c0313400d0f031140c0f40746078988200080e48078849070908880c003003d0b0f041c610042800240701100c8028420f200340140200980f44070440e0300034603004960510a07400401c0c0169140c50b0344c1c441d4180b1070764a28803400d03d1898805421880c2500c003070b2203500103100e03034411030740d0281e40a80d005410880000f0380543c141032207400c1058940020b4090542090303c4980c80400041c810b00e414404e9808014544d15401c0304007000044c091501d92000210107104600d10f0855410041c88041048118080100741d40e5598000000e0001c0080c1d403940071010400d2010000241714a00c5400c40094403800c01814548031803055440701c1d50000c0d41c08920145c983c1d2103049501c4d4004002e1400e0343d610ba480020183c02848280300c1d056910080074050710001c0d200b44400d074103c0d0040c140d03142012106d60750a4540c168000e003070341980d641e03420f603075400750743c5c0c2428551880c84041d81a654584980310003030300303100c215000389400c8011055140300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 851491348 1250 851490098 851490109
    0x10b030613080a0318020a14011106060f091806010806100504022d070501110d0b031b010503220f020405070c1e03022104140a080307060b03030c010f05090d050306 72
    0x1042040c1e440c0005068000d1444001417807101180690400d845000120f44c0701040b002c08035811200742c0396a008216448001c9698420841e0100c0e0040d000c01084140d5092003540981c1100507901a11451105130861901e0f18000760701c07506465114405001c0040f41502c5400041c2c80c094600f540790402d00b103010200c90b4004910301c0003c0a420204c000418031041c180c1b580c8030b920a0090000ea4456030981e08180c1154803004601458401080791614001403c00803201d0b2130b00d00a0140c9843c2d400558040d00005c240d02008610924a18103c04050104407186032080b03014907a1083e40b801400304988000300f6000038060b0a0300420041200b510594214150b609041c0f1542401440c0403400e0148251281c17010650040320210b0140441000c2c0c4150b60104018607000c031180c004010912101c0d2060f400c0c16002017002c039001c184c1c41d800c11144040080d085900c0d1081c0c015a150031076058059032000a651039080c01440602406030f1400320703a06d481c1040c118101a800160f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 851492598 1250 851491348 851491357
    0x60509011d16051c0506040b0405130803040c150f08010b180d111908010b03011a01032a0f0e152506050f22050c0f120a05010b03061308 60
    0xb1072072406110500946110300101c91881202c1c20310204280c6220092801601c010b0350304510440c03d02e40d210320142403038401c643c403c00b4244000e401e1044245c1b900400e43d40040c0050320b52100b802e0000c103e21007213080088421081e5034890001000d100c400070800c0308103822811081e0003c000c030354500014101840150b5100b00e41d400102c214918260302c810066850803a01310529484c030214600b00c0058200403510707444000c0c45502c07038010800d801c0303504003e8910b0380690204542917465200340d000d00310b0740e402079249a9400d910030300a07140c0c035050155030100049001c1074a140040c2d00c5005848c0d4802c0a0355901401c140340d451441503801100348042000c402c1c0c003403094500014210110007250407a60070071240c181010700c20042c00c011190a4051150740140211000380990502c44558101018201010b680c4003085603000e0002c5031503038403009032040506049001d120051101d0b209200026075039400406150030840000c12242015a90404020210380280300300d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 851493848 1250 851492598 851492611
    0x20f0d1a10050903030403050d18081204090504050a020312031504110703050c03130602070906061b060509070815060102060627100810060801050a110415020f0a06060509011d 77
    0x40c1c0c0f9030b80c561022a2035406a83d1025000384a0f5440d10041c1c0c0390420b566552013900d0510800c0501e07203880483e65130784035526105c1c01c0da8034200000c01140c4d0544e8001c3d50010711420a54160301401d40001c1c0c80c0c40b01c000580c41042a0001c1888a0b03200401882c09148005030340900c100105090310408030300401401605101c0001140c2e2240c420604c112201b5071030300d00721820000d0301e4543c025034580541c05080201e13031400b003010071284d01585041e2094000b003001c1030744441c07540d03031618042c0078080e1000c50305204200011410103424003107206d18111580c1c10340c0881c42c255000924146010340300340d000c0d120700d2440000801040450094011110000501e680c0701d40b0308000d040c12040c0d010400d075000340100031031074004641201003190300d50030081c000c0d512480d4070503017115001c0320307040c260703a004200c2040b036601c501c024071980900d07a0041d10004040002a28201307021420102c442036640c20003404140f401ca40352078054010010749103807000701c841b41c0100c2101c024245 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 851495098 1250 851493848 851493857
    0xf060f0a020102040806011805150906010e01030e0111131d0705130f03050f10020406020703020d0602041a0318030a051b0c1002100b041a13090501020f0d1a10 70
    0x848440c0c41c000d404460003848980d040f1082981d65035000454011810a26100141003602048054020305171400c1c03072400017484102241c031803c0064174111052034119050540714006503915441c2071140c00701d21220991425542c0103070480316131501c4c1490308010042138408041c0c4a40c1a6030010165104806007046660750290f80e920f42104030342036011891280c00340401000700080070502d4800c0c419481c00f15000006011081800c1c2d000b10b0040d540189d200100c10070251905072030201d40a40203035001446e054982500b008500c0c00122904400703140041401140c1007510702e40503501c420751010b54101015100c000f007a92182144a85900414042103091000240b040d1196a48001e0142c0d00d8194903000294490800100d030000b41c42c135040e00d5103028202401081c84000f4981c140c000b00d60101810000042905041c0503961a55030201c0c4000450910050a00342c5501140c962503028640c41d030420354114402d040c11010501d400b00c0910f844036210704003800300c10f091 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 851496348 1250 851495098 851495107
    0x105070905190902030411120703050616120501122001050405100509030d0e0a05030a17030702030d11032d04080f07020901032d03210905060906010609050f060f 71
    0x8145610b40c103941c111268080c400024003003006182541010424001c0d1607405410842c04003007501c0391110b03c000744c681e0b009a80021400038201603a1041005603040c0044544000445042200e8098004440b01c10f4003401c10000e10a034070100d60f640414422031038022491490000784180031314880d80d800b4600071210203030154050000e4503007141016046034000000550002c0890078116010f40c02035440c1c150100e050b050100c0c0031500c45404c03d44074031000c11900d40e031511540c80180349600314003050211883c28541400b40020f560600500691603080512428013417100c107070102d03845da614a0a4080c50303414401d4803140d10a8018800c907840e40c0041200c00c01e94418400e0083d071081c80d0b1000030007006501880040f82865006050180d0503084c0d241040e0070100d94009404502c0825240e4112030310000c0325006a58580c00200341d03480c00e075648170701d4010300743c0c2e07003014a170003000040c008654008441c20086c142101c0c802426000000820840c0c032070340940006610300001d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 851497598 1250 851496348 851496379
    0x501140403090f080a0813030b1e180a0f03090308030c0d0c050403111210020705060f0117100e030409020301090f0b04020f0a140f040f0315051005010f2109060b030105070905 77
    0x46090000c49e00b090384160785160040010148007842c03850003100711f00e08002304e11114a01503006032030070468002881c01d00010b48400d40c242c1742c3c20000700d0420881e650040005030600001c0c500584000c42d010762554070b0382c0c11090030340d0b032b82080440801005102c20401b0801d070007100504404141c9a40b0240240c403014542007581c40c042080d1840d00010b00c2008101e4000365013445000b92a10401d501e0740c0381e9420001c00e070684001d1285560001c0021100041a40d209081060301c1c28100c0b45441d030781d42c9401003660001d80c0607011066499096080a2480303000e200042c1c0011541146042e500c1c41c2c1e40d141600803181c00c0c9040001e0384040300342c1d00b0210001c4070400c5811840c150345440d92440d015081003a02d000886840c03482000c03003080d00b620340c0610750040740c52042120320306050100448950100d842c000040040c444a801c44240006100204091038002d010428907000e05082068580c5414418081c0e890401000061743d403001104e004c0d58001c540b024405901d14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 851498848 1250 851497598 851497627
    0x4090f03030f1b02150105040b0607080d0902040c110c0a060203030115030e2509021809090a120305070f022b0c0605010902030a11070302070506160501140403090f080a08 75
    0x10302a0f0211180303407095002c041d8001841ca0002c40150410302400da88075002c0c00180c0d141c0c050b00c5504900f040c8007002c00600038002600c04620302100019a4801c2600094142c03650b40120344041448015086007002042c001d02c06c070f210098a001004500c0c000e4029503911051203000140c240044c2c481c4a40da2007500110030501d40f8904442501c0601082458144041e5160000083c84460700040d8019580250340311281558035920b4404011024001038100050804c90940a00411440000c1004d00c5d090760355072140c0d030b0000c0c0e035141c09032019201540c0c500c814030035580100345180c880a44041c2c100043d4201d0903072044580d01c4040d09442030300c1881d1000b000641810004503c070340240e80514414440404148190000c0b900c0c04180c07482100c8000e001078120f0081440b0300c0c207000d401042a1456411084848559500c031039085400c48070700049005241010f00060681c0500311501038561548600100c61030300710100c0d80e03910010300040c080840070942d0074404124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 851500098 1250 851498848 851498861
    0x1b0e0315070e03070e010e06010c050c0f181509010b120411060c0d03020c120403030e0108040816031e03050106020d270e041403040501090515091002060a0b04090f03030f 75
    0x203022500d003607807958605c840c1608240155080f03030129900050707456100340d0000d03174115088000781420031080c605100300007880d42c810b075810000551040d803003000920303120783c8500a01d024a42c403840d4030320100075564406034800d86400d54144180742c2aa00e01d0354042d07400650190341a03104400780d001103080da02031000d50b04014000d85201928a980580040854150800c19a03d080b128050b4840301e90040740005000210140040a0300394080e80310715030400d01640741c15092070300841c4448295809100c00b280040c5001080c104501407801c626031100310f00d0309050003a90705105000350f640e16045046020459402c04d42d00c003803c9080108a00018206c407155556502c41d5040c02c450a003e80b411140480c070200e100c2c1c06d5940110903036085e0750f41691040b40c01460402013100358074030b20040704000541086000e040d940c035041003038001c90464001c1d01583c6841171030311088070805080c007405141401c000000062101c0b0702e00c00c2199141c18000f0341444800e52040041c204c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 851501348 1250 851500098 851500127
    0x60b0703020d03050709060c1401060807080705040f050f130813170c030601150c1403030f07090807050307051e03011a03010f1515051c1b0e031507 65
    0x1406100341503010451240d10a60742d201440035499042c0300700c0310221203100ea90005540c861070840016100e514180c88580e40d580007007403440d1220b83e0241003e000c0d0b8410f07282913104000030405401e00b80600b03015072640000400c41840e00d03414040d8880401000003042d5030030a00900308011902003901c500c0d0008066204916840b98089401404004c1080d0f40071311421f4041c001601c0d00080e4035060350300d0300c546150440d150590036100c20602da4002c070380c040e024200070300603041c04002842c03044203d6010074859041000c800380084100d0b03040a18140c003c84e5040c405901c0c0029440101c070310566044071342a800d0000740c48100b00c4140e030360b5415400c100e0184448001550341008044007200204500036415001100b02d442c0b640c01c51b9020360909008025510b040c40c40c0c03079001c11860a090b403402c03070070a2412010300c1c0c0101200240395915042000d25403a034986882480350241055981d100103000001e94031010034140c01d04a440040016468503c034010580e0b4208 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 851502598 1250 851501348 851501369
    0xe150907030803090102070605060301151e03060f1b0906051c0e0109030309061112011406040b040605031b070f0b04060b0a030f02031506090a0203071b060c020c06090112050a06 78
    0x4d0400e5414040d40c00ba0f181544c0300c6041c0400705803c0d00c0c040c4500d4100341c2c101c40d00030782c0715450103035030382202c024004c0c01401414013440008042001806246c0d0010488040001e100030004000c00000038107a94100801c40c044509111054100088413081e00e64807811442c031003017000000f0082d04c1051028042942481c05250400d501178000ca0480380c030480081c031499646030312101050141040980a00303d0160042128481c941c03041102d902c0c001d4201c40c54503896244003c403c1c3d0050380210001100001002502d1030311003240e01512855404161074100075440e01c0c24091040e03034003c4d01d03510140c004030701040f54a510000c0e160801400c1d0800480d030300e047c100350070032070090241d01902415010040135540d5003446881207030020041c0d503a5440c1c01504100075000101303460184036208d8000380c4020859820003482d81e00c104d1022131080e0303426200a00303002120b4540f80c051a0140100003042e038004121100380d40112400062540e580c02a5602820b0b00d940f1105151 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 851503848 1250 851502598 851502601
    0x114060a08251139030c0402130e0a150512160b1b030702010215040f0605010b0d360501110f0301081504050c0405040218070807120e150907030803 65
    0x2540c100000070103c101c0141607408000c8448100401061420084009a030001c0c2c54041140780010140c03682d040e010701280c2115058001060499010500007100c070241e076007080000344540054a64850b92180c01404045030529000032141501e0103206c0c428888036850394a002d40801c5200410b007140c903440311000d6501c01005c60241d11920100c50b6005000d010980b00c0c4000000301d0384000ea06038020016444040051010000b0250045412030003110342600810b05601500d80a009004410740c2d5030b0301155080c80845069000d0302c03503645540020802c80b082c0080028035204086c9078404404181803400c2e50060111000405098502043d02c0781c50320500c20295041c2c400b0740d030446002c42c0c2d00000c1c0c040342e034808440040840d4080c0c03011903181c0c1015002150020300c090803800c030700c1d030601303c0c004500c02c03085440c0d8000640d014108451598042a0210144800002000801c1140302d0751500d0780043c4d1050b5050401202c0824200f00d01081010300446e00f150545849 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 851505098 1250 851503848 851503921
    0x3090302100e040f060504150315051f03080a0314040512090102030f0d091e1205091f03090b0a0e0723060c010e1b0f040c0909150801050114060a08 65
    0x1000d40b4012240954500800b000c4401d440d23250010549400803411106000700010036006018000c043c1d041751038042d0192400009003400c5880514410340c00c958565030b840c200201240c507551541c40b1290720810910000c6000440c1c5200103c81c00503003659a4008100140d103107205260b01c0440420000072442104507541d40064162071041c01c44a000f24a01490002e0006541e6000343c014602c408595103003c1c0120028404000090280350500824403001500c0c0c841c0350900101081e00c0d01031030001c002c1d1207142c03c0c1c0d00081032001000b50a0421807090780c1e90f0014003070325003600350441007501ca01c402280801850701c401031045070340c2e10300301c1d036200c1c0a0034620010555a11a08c9801d0803070120200058111b800d004c0d16000280f000d0504010141c00e800421030180070105001103080015409404068205450307180511480c00348401d08450050b809034901000d4019020bc00c0e60310f5200300c49104c241850700c1c55140c0c550207002c0104161525818100b0314100300c01105 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 851506348 1250 851505098 851505101
    0x4020f0d0302010e10020408030d0b0409060204080d140a050d0f090f031116380f0403022b02010c0327061803052503060626030703090302100e040f 65
    0x9002e5084801c0e503122042404c174101c143d01590007880c00d185c00038041c1400e0304540703520014400d10f0060020680b04103035225481241d10940040c2c101d50401a48141c07203e8020001a084001c041c20040ca082c20f2120000c000b400360500040d134031500c078035001003002082e40000240c2c2c0e4204c201c042140c8a686000f070a05a000101c3d1222070141303005106032040303c00f9004c001ca4030200500c643c6101d02c0e461010700e0000d080c04140e030782c1e00030071807001c1c581071160054444081104080783d03903281140100b111a48191406004200c2c1000c04045460890035908000560a09001040e00100d24042d00c507081c100b54039005802c05c048141c0c0b600004520580d0440e860354580f00549401107021003c904000d0002900e83d5103c0c4c9904034008485010b40a5408150204280d2142e200c1c6c1c0c811055404562018005104140a1642e41507022500741c1d6251801d0300114607004940d50003800880b01c0e171001034859a0552401d1040717a004410607400c011000380208030705000c0c1d02d4401d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 851507598 1250 851506348 851506361
    0x1f0e01170c041509060206010b1621020c060309030901110a06020703030b040e0a020f12010b0307030c1d01030b061011011407030608071a030705040f060804020126040b04020f0d030201 81
    0x10343c461842030480f0103240a107044c2c00643d01c442e4050002c580c2406140950381d03004501c6021020b030202c201601290119400a042c040351001040d19900d0b05500203181218507005948942d8003002800382030200001102c01107202820005108500d000c03200e03040c0090880f01612079800052550101949680140321000c003c8908000100c030b070b00071480d130f1030b0340c00701d4000d401000d404581400d0745815a85040c052801c5000803e138460f024012078200000703540219a00c101000c81400303030201307440c105d500c946030030801082998515140c0300b6100001811107400b039412101c84200c850300c0b413442040c0289100d8000e01450100403105085a441103c41a0000b0b1405401060816002ca404001c0740d988102040c030300c00020040010f181e00c060b00340001d20104000001e054800c222655000b000243c0750b00006103824000500321150401010807258030020350130031640c0c0d442a140742c200c2c1d00300200030216504c3e44040381100d000b0200566008140500c42030800d64150400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 851508848 1250 851507598 851507609
    0x1090317070c140d110616050717030a0801061103040b160501050105060306060906030a14040c09060b0306060a051812100e0109030207050111240609061f0e01170c04 73
    0x303900b0555110084005102c5002681c3c0d0701c00d64243c03a0402040207020420b6045000800b550702d400b40b408600d044c072030000d1008a03041c3e040b91104019580c0000008102c84809001661410b100010300600d1007a050140381c050202c0a03110404007042003050302d01030066502201c0c0e0f03074500c654030b0226801e4003903400c0340d00f503003000300102d1141050000d81e030150314050503071741c00c10845404101442c4c00003001c030000c0603600c250003030f0810f0a0f150003600541c001c400c0e010455040c05030740000d40d8426089a400140c080060204549442d003c80341d036a4020700c0c0454031821502c03c00010209924842c0f5031100e2402900000414081021040505680020010414109089401d0316039105015001d03800140c5c0400c501e5003e681145200b4518200361080d030040350030318052280071455001d8459205804200c1c85040115159402250480e41c802d04808119244c000c5040c104030392608000c2c00c2490000564010380300514009801e0601400f640b4022280c07005030781061044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 851510098 1250 851508848 851508863
    0x6040c0605130f0608011707080304120203190605070f0e010210020309100608030a18050f060c120d0b0901050f090426160b0c0c03092101140118060819020109031707 73
    0x1f9110b10401c0040c3c4807045460301d00166042c1440c2a0b20300b01840214201071341c150080e1031201402444844d51082c54621131140044d02d130600000046c0b180746005a14014003000d400d08807056070f000030700395404491020006da0313280c0d1219185800e0a000645045829041641c003080c1b07488081302800310a40f180c2d5410040c0500d600c3c0340e00501a1903c107a507009260b03a07008100d5030801030010100c040800023214106040c110885c0c04a40c448075035054459035032680182030f0724040c80100d00404e421070b003002c0140d00d8200090b1890b90040c04c000c202411150358003440050742e480712001c141002854684844041d600f01446c440e84513022100c1c01002000500065200b6050700c4482c07680500441c10188003400340440d02400e010b8061901910040d080244c0009004035000d004645448070440c4d49410303068a0a418030281c110782860509100303000140000843d800d204110100100ea02607181c001030310001515080501510501c98003960074100300d400500196125144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 851511348 1250 851510098 851510129
    0x4060912120f0b09060d03110a1a1b0a0c032708060105011416080702130b0a05090903070201360f0815010e0604110307030f05060306040c0605130f060801 68
    0x4102e00f15221001c8003540180003002103001401c03c2c0100c1ca52552003402d0080d54498040e4880e49402c401d07100031a0801000350501c0c0c160800e04048581040e20406840d0b840d0045806415a5000f800510010007408881c90380030306104081e80c12110302410000403c0001c548091181d01c00f10f4004e01f50300c0c0c27280c000009495442a41c440c035116224081140c00e0201e5070030b9000b030b40031a078041075600000520000c000740e0340d624540e100042a030240090120b8014040c00781a00703171035000d6031065010008010351210003004482c0c5080d42440d100c0c1e108048008013200840004d041000c4a002180c1100c03210b4803442c5030310782911404a804000d0950b01c482d070301d60b43d40c1c40a052040003020741004101003030703c248189400180003403001c03c8482610b4054a0380d03401c02ca0f1007c001949411300300c030002d00381c0e2180b16004903003a000740089103005e454801f921003052042c8020404001060341c0f10414050310701c800351072110842e840035076940c00002e08400085c003a89070134044245 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 851512598 1250 851511348 851511371
    0x10033012050f0c07020607060615030c020c010206040803010b13030b1503120c07090e0c2d0607050d0503040807140d0906021606030b060d050a090b01080d0210050406091212 76
    0x410540f20b245440c0e80c02d490f24001c0c1e4240310709a00020002c0342c41c6c60b01c1c0c3d14041404092400145030b10a005d035400213802c1100b6000a10744010310380413034195049030091102095100086038151800445030315540c40c1c440512303402c032a141e580054414a003000901c14a407000c1c0c100c2040300710b8102e0890340700740c8001d041e040700c62251070003da80035400110100301d600d485800640e090010f5400390340e0026000303004121244018000c0051078945200415901400410f01450702c1d501030328a60708090702c80c0c0d216039036880000f080f0802e008020000500300714100007200d805640c82458441074a2801c1c003160303503c0d1391903070186022a91301c1c2800b18002d4030010704500c114040382c48001000d40341c420107600506042d03030744907080708081141c07030100070721402800c1c02a04040070000b5020b484d8280003980c030304181c10400d015045038010b0507190740e0000b1200f00f0200c15010029440e21fa51610400034601000020180c0c0600c00e8442003250f0040080080740d0000300c030a005001056 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 851513848 1250 851512598 851512621
    0xd020f030a05160e040f0b03030c07060f110a0605150d08071203050603060403030b060d0603080301051e0604030b060a17060f0a2f040803040e1603051003301205 71
    0xa0044000154980485100d00e14140d0000c006d4041c4070100014030030300032408241540d00c60700200145070312030031040150903440300301c09548903c14503004041c0203200d5134a6889212172403015100e80e48400118089040508030000000c400410480c0c64a21528008045410402c0151017402500e40f052807000c0c0030b402041e10a00c1c008002e400c40743e40d103550980c021304492074800e130032034018800c101403e41c880c032856024500884025840e903141c1410000d060031940c2c00043d007004c3e811624096a100d03c402d80341502d500c2100d01c1c10320754906000c103040c07064a034004240c60b00c1c15280f0413014032000c51254000c900c02806400a81d82e883d000700c041c3c5078440e040f078a84032000d101d0952409404142230b45490381d869102460107030b8810382c480c03a541250300690100300304282401540ba1500ca00c0e000c1200c400e0600b40114680341c40c040701000150712001d00012210106448036a5500854185020045040c00d8079900c0d4803c005108400110b241c0040130f19040104074521400e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 851515098 1250 851513848 851513881
    0x102270a031109280603050c15030f07051e0a080a0e060a0207020d1b050306160e060f090405010905180f0a12110105151e0904060c050d020f030a05 65
    0x34000c0010303814030341d040c000f00000c014028603080390302c8208030760b00c80c801001256001841113004130b1060b041d41095421300d03005428031791040041451801d261b00380c00007542e900000100210703001d0740c0c032100141c4491003101c42104d212000c4140c4000c4c000c005401070030f101a00c0da80d0f141c0c0d1680e0761442c058110340c12540b242d41d095100000041d00780481d078004188803440071385400f007850502d640e0400b04022008140e140401403042c02d2000e03080c1042151351080c4100250710054a502c0300181c22001c081c0d904a014400c0018540249100d0008440304e03140040c0040040750382d40d01400e002410140da0009140c500365040c500300b06000102005196584405803426140559510410104140420042c0b244540d180443c1d90020b1003518800d0141c1460200402c0b020340c20445500b07031001e48054041410415014a6169106400d50265120308009515031000b0015a058004c201c2010b81450001910040702d281c10805107000b210603c50600c10317900d991888a9841d0300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 851516348 1250 851515098 851515103
    0x1608070f06031e021e030901020c060f0c0a0f14030f070305010807080c0f1813051014062101061421030f070c0e0901020a090e0106121109030102270a03 67
    0x481c90192030a640168001d180c07117460100381c05034180c0d08641c4210185c00880e210b0b041a507010411600c0f0210601c075565011003001041480c074980500840f00d203000d151419010003003030303103c805105030007604a840c0e00c10504548984034980f958a4017100b0108507058400242010300015050200144540c1070b00c000b4005407045141440a0040100385400044c1d440501d201c0706100000c40d014100380a80d090310710ba1114904181020352610b070702c948616101a04d400b1207000100e07850400c003500860216100d049100d01d00c0000742269400308203c00d029442c2170320008001e21110083e2100e210140c0d0003500748600300008200b01c4604c000311a850707401c200400440344a0038002056290b1140c441a40525101d400c00c040c0284102c504100913035000445140464110989030028500c0380d1883ea041d42c100078006181c2030080104905054680301a010490280410b03680c820348090021900d07800c0c04080146074007164655601400c107007046051250420003546d000f500d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 851517598 1250 851516348 851516381
    0x2041103100e090a02040903080a11091509040f0218010215010e0c1c0c03140907150c020a030b0705041a1204080a050706090c140405090c0609031608070f0603 70
    0x1480c00750b11180220340140074800c0c0c0d015141504005030344500c00c0c4071140b4002e82d24100c0c2403900c561a0300c05c0783c4200d00b40e040d807803a0500408070180d0b542c810300f20316014840543e68941e034900c4003090142019a002508803400410480328524490070480a210000d1b400c031910b004a12040c602c0c500f200703004000d03240c070341240061001138110000340b142c13807134044a61800130035881202048801c1d84208800180e202c0803c1180e2846101d0841c0e0008031031b0ac040c0108078541482030703a00036030101807a0280410300e0300010a5541d0005032074011500200035640078944064010450741c0a8060140510341d043c032008150340264080c0c40c140c1b02c0703452240741c2e503443d1501c8480040e005135000c0b4003007210800111001441c03034021840e40a00c2208503c201c00d00308034103039a015a880712128011807410042080300080080c7c5c1c0805100191000b59881e06104042400c1c19481c100302e00450110280003d040d400005540003103510142c044158541c0340c00085060f1b80fa000f0500c4c1104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 851518848 1250 851517598 851517631
    0xe3d140601031508010f050708060f130c03090f05060412020f0601030f062c2104140f0307120b1803120718121115040e0a0b09040f02041103 62
    0x9502981c040c03e4914802001124400e81d41d010003400d5416410541c51059115410b01080a80041d50944c0181d0201d4442c00710b140844045000d0a0100a0300c142d642e8075003104030f010500a9004010030f0f42c109082100051580c00c10550b5150b058504450001010280350003ca00c0451201121a5400085c3c02281d00e1340d00d0f945002c00410384203a0300c40f81d64049100d0302c403c1c44912004001c840c2011503007042800407002e8101420554040b440c0c80340ca404151328015200100e034182d41100c2040400840a0404a488050340d80241078151103040f0001c82c1d11404409040c05041c440d02c0f05001c81c0d42c842029000d0b503085242c1072249913005000308400d049603078400503032108803840c00308158104852000310b418029409036010741070200c220700500202611000c03007000d0944d40410001c1106610152511445c401c02101c016054003040e02c88401c1d0304440d68440d4024402c1e100303410141018175802d0500881240300f00e1614040301c10340100c00b41900d101e04003081645425 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 851520098 1250 851518848 851518861
    0x11070c0f0e09070311010314040b06090714270a0b0d051005062a1b01080f06010804150603051029030c010309050f03042903190e3d14 59
    0x5c01c440ca0304014181030703d881c1c80c1001c0c6141c1c010b0080c81940108818902070074101c060003c2e1510180130081008900202480d0b00c42610080307943e03e107440c200810000620b0203030640407218103051903134400c4072007200040c48a04100540032456807940100019201c40c100c60f035040b40644540c5030441814818102c0c0c040740c06e40e80c0503c80c3d94071006040542c00f040141400d24960404e00300c0603c1507060b243d002c0d940d002411540c4882440b45144090601000181c049a8000d0004080710f42c1c840101700c10b051560006001140e00a00f16070508000c0401a8094aa0303500a080b0781c19071000c4461106002815601c81d03210040e02400220503094011400740601003000c1d1071a02c19030081030010030007000144004c041c03000e29554010b400048081583c3c4a07812400f9031204244103104c410030590680350b02c442040c0200240d09080c4090072070804928038080b0741921082084000d184a048a8010500401c5090505081c200504003030071202d8160140d041c050760782c00012803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 851521348 1250 851520098 851520113
    0x40503070e040318030302070801110c0c0904030c050d030605010e0f010f080c13091b090f09090c150306080606060a120902040b0916030c0f02031c11070c0f0e090703 73
    0x200b040c06032410303a0b44040107180311300003043c1d15442240180d00400d0f0803c826031080c8143c00c1807080031407401d03143c003245040d0303a551900040496072081c401500070408150180f100107005070303440010b68000300305d008000703801032049115541c00b01c1c0c2040c03032600c140d241c910650418034005860f05030700481c00460489480c000140701381108502001562485d01010001600905101c103011406e58030032043d90508100c80c8140409100707004005001c90b80c400e480d06020385009500004107400766041c20f11500403c4c0d4800c400c1d203411036040d035a4080d41600203a040d250030500302c1d00030740c9400040c800c3e10700c150414a400902204000c00c88280130fa0000103110b4002807010400904030400200341d030030706959006c80d00761114100c140003030701802401d480c09014200001d144603402001f07526442405070110b03601608031414290010b903a480070806222141450b0348800442c0781060703210030b031405070b504024907044001968880c0001e13054490840c01c4091f10065103955100300c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 851522598 1250 851521348 851521351
    0xa2405040b040305070512030f0418020d050117060f060a0501200316060c0201060506071407180905060f160804082205010e0102340b030a050601090b040503070e 71
    0x10080200400507000d040710000c0c10195018001414440c0d2a2078108412801900540034040c1c1050018030080607240041d81e04482c0b4502c6036161081000e18850b000b440f403070000b200200d1400001084c480001801d603040285220100e410a4503039581c80000380354202e41c001c0c3d00040020003800603500c54000300078400c0c134031030040d4429400703010303240c0c10768120040303000c21240d6860401061105601515245620b80d0008111f00c81c10040444c4452241c1c07800608a810000200280c2c03040400540c00240315401c049804504079652000240c03240c0481035440b032080c2c001052081030241da800b0700a02c1040c0004190101e40801540c2c00c22000f00f0a40340c40300140311001b010080b510107208920003601c10208103038145000903040c05008844903045600003040d07807090165001d58404048803001035a410100f03100d5042c12240c40c2500304c00c000440100a2040c07220481e08081d010780000d882d0590501e48482000d51a80141e100e060381c5644442000c0040181058000c0d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 851523848 1250 851522598 851522669
    0x1b150e03010e010f0c090f03030801060c0f02090f06031b0a0e100801060801061a07020922021201140106080708011e0b0c0d1404080c060a02011506080f060a 69
    0x200d9402e41107190300b030860b03072070801440c48140c843d048030101540c0582800b01829691a6a0f240c0d40d0446c3c45c0204202d805004020900020100c038806200901041c0f840d81030f4004c0819a643c507000d074815420410640314036001e8490700864030282c8005400e80c104001c0c001d08100315084c54a50314004004d8064405125810103c50208d0058070030f000310005408140c001060040c41c0400081e0707040d58540440f11000c1007803100c00c0060752034145003604851080000540143e80707040c5101108001e2100942c452020161040c003810b040d003103807541201c50601c68400f6a62502c0039607407050100d031510f00003540100103110002a1000c000410007542509108840d11104403100c2544400460405940122505030300e007640840b0106c1701070f403c1e207038107800c05143c8030304241c1d40d460301ea284500c280d001040c0400708610035400501d1503030300e0715406005165200d501400c0c440b42555006001038550002802a003001c408040071199641691446000510b4400030b100000540c80c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 851525098 1250 851523848 851523851
    0x909200105040f15080705190309210e030105061807050313020a18050108030f040501120f0615030b0904110906120d03020d05101512021c0203041b150e0301 69
    0x81141885000000f019004c03244440000c54100100034015003002400c6d4001c1001c2000001c0c1c5a646154000c1c4604510382000708003403041740b51221803d40710345d541c2c4076000e200c0c01c1d156018943c011040b0780d050038160001c024a44500c0c09220800b4904298524441101004102100c0c410f20086a22444901029285103010760016031041c1d41d0f540700890b03075201c6c0300300840010703805e100c2c41e07005044c40c0008610f0020521103181c840d01551041c00e05200c240d2103000c6240700d194200f02076038070b10403800704000c9490360091119994108d640c200043c3c9004840203103030800404050003260820549410071070104100040c0c2c150050401e604600440744030358418000700715030781c00b442070380e1000358481d9030141c602001c44400070802c02d200d8086450800881c00d01070881c00c001c0002c2d00c1c10b2a454603c25408801034403440d900507868840500440450418541c06107001c1c51264288002700040070400d914100e800c0c1c040c0201002e0b01c0914020070358000c241d0040c080502900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 851526348 1250 851525098 851525107
    0x91905391e07120c02040c0c1110030f05040f0b0a05070e0d050c10020106080c0d02060d2d0504110108060f090a0e0102030420011403010e0403052701090909200105 72
    0x8540310300741002c40f90840460005111601185442e0040c034204641a1070042c1c401300c03240c0c541e00400038034a00d885002c0c0d02c64400643c402c40c4603070801101c00d440d40380c0901c0282014541141c407a041a20203a5080c0a00e101180b0910141e00405005c2c039416076581603e1000141001225600c1c00404c44040c4101d05d080c03901d81c2c44002d02c0c3c400c0d584141e000081c40070b10f090b00d4142041d401e200064850316501c02c0c030200590b80d04082d130320305d00604c082c00aa202119041d031442146034040c080106140201044c0701803035680c00c03492041d44661441c0d1000c1601800545400744e042e01c896911656004120502e0301303180c5a65540304200c0207011503500190501c480c01c80c4e10646040e501700322200000c2c0540600200440d00c40b01003860562880d68450506445500040c050440214142008142490b2240c1e01303440b00d40741400c1c241002d0301244203035034200b04900c541140c089107040310001002caa03944221130009402c91410a4103942c3c001004690078090341009044c49001e21 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 851527598 1250 851526348 851526353
    0xc080c0405040f14070e09071407080903010e0a0507151419140708071a0705030703050c120903030a0c3f020406051804050114091905391e07 62
    0x3014174050602a11500148041c41d0148090440020000c40a2240341882c022500030f54034203c03040c0a8201006585452000c00044c0c094201d803000d0201c503105c0c3d40004000d20902080308002c450510907506560100840d05444104081980011118041c8090b8600d0194904080d90160b641c0c03408644980a144481410744c000710802d44d0702190124601007000b0308101442148841c01c2410103542c07408084c01026444001c0455041544580c0854107109024040d45c200f0f801030704078180d1620707005442c03d940e074108035038480c401030800e0741600302c00c3d00030b4004500307140001007032484102500903800c5000080d80070401004c40c0015100c00e04030200e10140c8042c0105a40e0995200d4080043c94071003601c034260705114502d4140104855003162820922964080e80d6114040e507513900521702e251441301c030f0401d041e03040c4020401c041d0000070700c0072682c0c580c2600094890145e441c002d920852442c0050075401e02c02c0014440d2030342e005c00f400c0d181c0300e10018041c0c074218855 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 851528848 1250 851527598 851527631
    0x3020c1203072c0d1415040605060424061d030a030806100e240d090311210406140708040f0317070c06050f040503060f040201030c080c0405040f 64
    0xb15006070000303115104060515400303894581c0340780c0c01c0e1241a106600040005074101c084c400300103040400d01281c0041030601401940d403440303034403000b007203161800d070500c040030f880100c0b8143e1081c1e14040190303e00380c0d4151042920110040c200c03001060501c08156a81080000a0f40070410340d007500303444564042044090f40c611036910000f20b803c02c00140481515042d100702c00b1b0003d00110200c0c26110b40d10030380d0640305180e80122846900d502c00b1025481141a019501424802c5103420f15800003021030324850510202d0701c00c2c80701c001007251504100000454010230400040050503c00d1001c803142070200d540701d5180c009242e480d2042d41d40282c0c0300080c0c00c410040b0800500201644220300c00c01c11041551410b02240e0b80c0340100004c1c0d00485051110208665209044034000d51300617042c003a044a2550502203581925100d04403012070029013884e20840c1c11038880c414560140381a400080e0610307082c40700b00310280040c2613941780c26980d120425210b0007000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 851530098 1250 851528848 851528851
    0x71d0406030b010f0305010b0121050a02160c0608090d0c0b10172b050d1505040e0307061508060403140d050c1c020f040302120102090d24050f040303020c1203 70
    0xb107408552015203503242c407d09468140c100581400041c1c0619600b4001d8a026980d00032540c000008031540c4141d01d105c02400743d4040d040205120600d000200710081403500140c40c0c043d22803c0083d80c0e241d25640cae80d0401c6208080c001055001c1c081c0c0004c00c1030050542004d54026103c80d06501c2d0048181545180c1c0315845290b40300010404d1002c91030100882a9400900d840054061b0703144003074802d200d007041e402040c50f5135040c3c41e000c01c552130054601401008005001901614000940d41c5d0000042520740e1851301d1a40c81d494440c17220407030704035001140a4401c503555a00c00f9626007413210310800b5400c0c000c02c02c4000d615458403900740b00b607090085caa511079421804180d15000c2002c00c84001e10720402000d5890b400310000d0764102c07a41120040e0701010090300841c0a80542d43c820790b040802c41390820204481070080559203e45804d01004084034070440c60140e50080e11449103a100c420b01041c042482038000f410440000d80841d411040c4103100044240e00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 851531348 1250 851530098 851530109
    0x30605040c0614070b0403080a0906060b070303061403070510020114040b010e09011e11090612240603070c030c021503090f0303090d0e010c0c031b080105071d0406030b01 75
    0x18001c80901040f90424280c2000d040050002ca080c80c106603119000143d01a101a05002c2100005001800c00ea000348001c0340d4450018020196030b03110405a9400620045010a041c2075012640407483c0032383e8020000018011710303405181c20103022a03100c0c0069000110b5407680c031001c04040c110310300799001c2c40c0720b8a0450301a6140681c07a4040c044098401e032400c0e414100d480d030080d410310303541c0d501d94000d01e0070000d41d9036070034642c101c280e02ca105000c64100002007903280c60070b003502a6407442001c5038169051859209000c56500c5224074141613401841400403441c19407007040c00c00d810612038200001441d00c0c42d0005404003041429400d828400081082003d00060218950b912a940011802c50800d84c00315a260300e0b03141d1100c0100a807814014030030341e109070543c0350b0098110303850000145d00c1e4284150100f804e1040a2036110180340e0000e1101ca0512856201c0d01065a403880742e080d44061040410140e44906a030240e140e00c00800854060304800f4000d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 851532598 1250 851531348 851531363
    0x1e04090207050a0b06221505090f060f100807050304030c05030712021204030f0b09160b0406030b010507052109030708100e010603080d020a140a020c030723120703060504 75
    0x9003c3d1070200c0302840d000700141e000301400c0203080701c00c000220031102e002d10340c100080703010380d0f68010744115460241c3c45075500c404900c05000354103841284060150605448581d0043e242c0c90503c24006c182c50000030001d020000010540c40c0714402a541141c42840c0c11100210719845207403540d00701c41020b031031820240b0328a05a054041000b5030f400407010f00384d6401c0c2840d5807100406060310000c045c1459040100050441505200c0340d030a000000d210202280d031222a0340d4101d030050f018041c042450b0005145640d8000c60681c0c0201341d000e8001c1404950080a1030f90b40030108a00030586a028011041c81d560b0501154000d80b0701e0303030002d050f40e4160201040588140c41130300396481c2d150800c1800800c1440e070441c3d100300403050026a0710050300404a0f030013950003240614000d0b003c00c110328016408a030b90040b401045048481403500c82c18071404824200c00b00d80d50f040c02d940b182421a043c01b0303040c0702d90702105000f0380350303a296039071100004c1d10710481d0200c1da080c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 851533848 1250 851532598 851532613
    0xc15090b0423120a02060306040f05040f1a0c030a0c030905060c120a0506011e0c0512040e0a0b0303160305070821161d030f251a1e0409020705 63
    0x4601503600340d82d000004448254803140701d1030005486500200020340204800000101c003901c59800c000c01003240d8a40c104403901d498102428144440c8070110782c0c4000c43d140080c0c6603102941103c1c001d4804501c4145141c440207004070082640d5248201450f03200e15904011540600141d4480c504012405658100601100c403403c400203000100c2075241109206c5140d07406030701c0c0180040100244035a400401509990800c44040700a28038410000c1c68400841c1d46c0001d00103d8400b540c40c1503480d1500e03280ca0007a81c0c43c1030086a09a44184481d0f420942007000c0d403107140d402410810700d000d50303075112140543d00034a14809120503154a5410354062015420383c48014079491a400400003003000b0400c11100880d5080c107100c40800025507503042c440d111070481d0a1044a130400d041440c10701d5103064184480002402c4109c0026040c1c1e61117007145040d900c07150b5100e14000001121003141a60b01c2207800da86041484042403076a0030b4401401e80074051401000c0c0b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 851535098 1250 851533848 851533889
    0x20324010e1917011505100c2009070e15030a270212150c13090504030315050a060203030c0703020304050a081006050109050f040c02031c0b030f03070c15090b04 71
    0x34050350741020503507817409441082a0191580e68001d0b610200c8090719140001030080b82e2100160344040c0110402401710085261800d400e8240003d098a10120755902d1500c15110983c40090030f607044280440c6145002200c80025640180003400005004081c101002c807003800c500c0d0000c2002c0c240e06040019840c1c61a81010f1440d03401c00102110800c4d00416140a000a000800c02d01d0700400e8400c0d004142c091130340090f000c807220421407031400b828014054070500c2d0447c000440b545001248504244504000340c8400e50000d61541c2c68041104507954462002039046000034003010510b552a20420002840540020704c2c180c041c90b401c1d042128215449941406029001007100307403141d210001c00a00d0407038000500703a46038502030b4214400e22070540c20180c5499a5500011595030010301e0034201a000c86074148030102d00700c2c0d500d10500101a00d121001c24042000e8030031408001461115454040c1c41c4507a5040a400e4a40142d00000e000b2080c2400c100300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 851536348 1250 851535098 851535119
    0xe100b030609010213060c0206040e130b0f0709170f1603060e010219030f0906050711060105030102030c0f0a0306180509060f01050a17010902060d02040612020324010e19 75
    0x1040030b10345008510b0722441d51040201c1c42240d00c145030500c05034a03840425581e5a5058800501d0082c80d50f06403403400c140010304a003c494800c84142c9a60000f080150003020180e900c074070b40da516042d940504004110b5640300030306104042301e101c5c40a80c451914001d2040d0103240060040030440305042d8906441039070792221141a8076841481001c900820701001d2498841990500180001030a040749000d05807070640a00300600304810311507526405041005d0011074001a581c640c3d17280c40406090f071000b9905022028002d02c440031b043d42001c8002c049440341d505002070b8442d903a1903107108041c07890703414401d802e94038810002911000d210081d40944142d00000480d07041000240100003140125282d4824001525000801c02d500075203100360000c0c03070240c44000034190700000c3c0d4494000e01e40014226420701880000034000c0e0790103920946001205802c1407141071032203090441d0407604003c0351400301140c0e0b450301c440c00c24003054048140760340c4504140300d04d00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 851537598 1250 851536348 851536351
    0xd060b0a060e1f1707110d08070e011b08130807030b07300c0201060503010603110a080a0b1303090b07120908030a02060c2803140112050a0311010e100b0306 69
    0xa50703440540942c1c3c9121039100c40f0300b0b2085026010142c1841c2c40b844422039560006100300109480b9a4075868145500245880d20580f0f03c0e56412101040c104011520094084030f0f01c0910740342e1910b4400001e060b0000342581505004000700143e0b40d034081c261810056502c25906051628180038610350f00100c100f860920384c454443d161540078914211400d0030342c2108481e19070365541c03041e6041c0700b0b410410080030000d000b0302800c0d480707003042e070b03100e405030362140e0f1240e0080200040c1400001c030f250440c0942040b0705da802b41d680d12007003c2c840701c568001241000181d003004501902110080c1c02200d00071031517880d10f000e80140c050084034258000c5002648240015010725034000351142d80181c607044d400340c581b009203e0262a202810084040004e00384c0f0700408000d5240d4440072000c020b082e04a100769a88004d56401d081040c18042d0103034001c41c0c205000f20340180c82016236004080000140c030070301c0615090600d04004000303000a03848841e10b0f44140b80400c00c45 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 851538848 1250 851537598 851537629
    0x1509020f041e0507121e0516081f030c0e06101d06130e010308030910020f18010c2306061206060907020a0b010e0906071d0d060b0a060e 60
    0x20003840c2c4448070040c2440b401891042c8045444000055149114010303034601c000d5505001e01843c211203079402d46150541c4081040145440001031a12007010f8030700342c00c82c4260310b401035651600c41010018024801003941c2000600c0b50000014007060b15400040c4600c801601250402404100c1c41505034004442003000705004840750403450b65000c000c140040380d0070740d60f0344800c1d90307610102da685034807010925211000000c288981d510041d44641106410b5034031901c000e0b01c0e810101e00402c0c41100c0003038014040184c82c0715005050700154941414030b542d1004040d174850024a10400d10340c08403c1d02d1070440c034040710b401c02486801003003c403900c4032484140301000781d450400a10280c0b0070002c03400810f006900911a101080d40c001c62400240d6071100b90080d400307681a59400c5040c414200010080b41c4101d60000d0750050702c00d03042c0900c0d040581009201d00e2400c0080c0c68090b0780c2d045010070303940d071588144002c1825032a03c400c840390038020409202d0410340c18 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 851540098 1250 851538848 851538851
    0xc0206010f06180506030c070209070201090c09091505010303020c040f062301050c030d09140a120302090f0402190201140c0403020d03170420011713050a1509020f04 73
    0x601c90491180c1404003a01c407145441c04000c0c4050542c0303800310301180c0c049500306200000307100e0a10b0421008040042c001c0c0e544506c2c035207961303404038201e40c81e84101401444a003d014009505690070640e00e031401080001003e1145060300703c01c607a02a441100541c1c0440413160b00c50410380218203c111410308200b0100340380c003e24102340ba107400c1300c40707001c6031301949180c00b503a020364141e40e0582c1c03682046030384480c264014040106200c1c0b0b400c0d501d40b000303070111405a1034000b50072156150710041c1404006000d10099019402c64030003154080c9000280c09e0198803a4405400c1000309020541c03000c0c13510000190840c3c9403400994071303900c00365040152005d00d040494084a17810740e82303148892000d003030407241100214280c03035000c103010301400180500089504000c0d0b1134402d217110701c40d60320401582d25400030000c2c000d600c0110030008551501e022009116203004409940109a903035481d030400a1003241d134404c100d955942e20000b54240380100718640e100c00e580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 851541348 1250 851540098 851540101
    0x100906060311030c0706110f0c120427060b070b190204061b0201051c05060109050105030603210d2306061c2f0717130303050d20030108010c0206 64
    0xd00d1494840144403800310b200002d005d50410000303034000107215000300b1405072246140ca070203c0c2598400605404144102c0a9403040800300000b21421140191244241c45800c0210280001c1d1100a04944203564000000e10703200c1050007000d185208000524441c6804003544180d8261031050031401417060105100558010458000300d404181401d80c4000c01440101c8131441601041d2814030b4a0392102c5c920241580c002e540202801d807282d50129031500c0044139140012034007254140c2c000307403140543d400007048040c4901d003d482c4440c035051120f51400141c0354500d442d180003540c082c9102030000c685482060700500100e40041c40c02c0c00f842c229008000800c2c000000c50b0361795081041c80640d1018004071256006009030703d00844241c20703030640350410a0300b41d5591b003040c031001080124090440b00c1001d4102c103041e0200d8151780f0f045409411850200c2c03000c0e0303610f2110b148041c0f2901640c020803c4d41412a41d520340c1003180c0c2c1c5007550000c4007080151b502150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 851542598 1250 851541348 851541371
    0x608060105010c03080a24090b030a030509060d063c0b07060b1f020705010201140903030112020303070f0c15230a0c08072003160311040906051009060603 68
    0x40421155509031610440c44d407200d1b00500f000303016007490030f4100003250385000d52030f90b6858151030803281400d400f0446000c5403414076880c1c0c1d0151500800003072042061174070340d241000207400100e0511000007421070701d904060820049050800100d18a880c00c00a100c80384140d140001e00b11002e001c4400c0740c40d20702c1071444c0e8001d00380002c100d2511031103c8460780e200d03801c5000122621503124480210768000c080e44480300c81c05010300650078041c0603040c1d190050b00d42401484a000214074580ca0407450754100800b1107802c0381c1c180020458100880c9104454118150044500b0100d8510780308000d08406440303075020050001ea01c030b00d40610020b03411444641e403030b0442415594265003208407441000d00c140103201020124503002440b90311022203a9010700d0110a0101c1c1605c00d08044da1240c075a0746584c04000300000c02e0000a003441203109409001410204000c000341d900d80040c0c880459084441040d541d20030040c2e040b00b80500c034001c0c900e41c1800c01903946401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 851543848 1250 851542598 851542607
    0x3010f0f1401030c0c1212050606090f040e03070213150603140a09020a050a080f16050a09090303111603030b09100b0f07050717010f061206091a1504060806010501 72
    0x1c490309041c1543e907044455114011049011043d80c4072003400603e9584034005448058100851901c40345041d0006825007001001c5a202560080113071107207249a00820014180300001e008050005001071801a11649100d0000303160310358010800c4d4034148054a40e5040d6980958109400c05040d40e001d4843c0310355090f08620100703408140200240003051203000c0030b030f001a403c0b031682c180004219402003003030b2010035412802e0310516010381034201031140b254000c080c2d0060007047c0400c1070341074950007202410f03c682004200360511021940c0b8680111035010b10005419415400301356052203441070808003254000320341c0c00c0200006401c05c82c180604c00307100c14000b03000841e07a01e0400c117964401d5441000c076418181c8600b0f003100410522900100c05e90300345103c51030100514052541a10345001c603ca400c0b603c0c2da1a0000504100803058428004c15500c04007103070520400103215000c1c007003a001c080700c0040244008c0704d0284d881205650003110060100f683d00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 851545098 1250 851543848 851543879
    0x20307120c020109091812020c041103090d1107050a0b0d14330a080a1a010303230c0601060801380f0d090b0403090623160203010204030803010f0f 65
    0x3581400201000408000007810360010300181011f111115420281580012004074100042d0b90910400d0a01e40301c0e0001800182d4181c2030743d4100304440240b051250090408503400902290070856032000810700c1c0d1035954100300d42d40180080c100301010300c140144044000000c00010aa00d441c00802e010324000a20407154421401840c41c480700200072107900381500182207200c0c4ca80d54900260744c5000940f401c403414503c103401000031402c5104094100d030303090340f6184442149220001010320100391400c40950052000102a040030440b050107400741d07440d0080e6550500083e0120b03101d000e182161900450861420004a07250480e400f5515181c501625028643c00c0c0100c2c0c0c2c0100c0b500c20a00ca80750074064414000b64008260056009841d07071040b950700c44030200c1d04080c508a640040003001d416404028580400900150220280b08495000305030b002900b660700c2584103a813401e101000621100c602e1100c520300512084101842192400110412a000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 851546348 1250 851545098 851545109
    0xc07031202030d050108031b0319141c1a04060501050904200c010c08160e120f0f1e06160813080a0c06050105300708030a020307120c020109 62
    0x41030304030008128000c1054912030490350500b0310403503840e0b8041d1641c23500840125183e045042e0441d000f1608080101d03000042000c50184e4495000c220949246904865445403902d0402207005500a00c07504151080801d003004180419401d840c00250700000b2440c92040c0e280400c02c000c981e0b00202100c96043c4141d40101d4a00950402113a00c451b031180004c29850002840403211241984416410103050b1103135030300c03521080308d100700c480392058041002c41c4140c3d01c83d06c52441d1103040f090350030041904032213803002445055410002c8501144c061903000030031003004c2c1c0107800c2194003104400c8004004c60700d0014030b0314202c4103941c0b5100d001c1c003103218046424012480807400b002034000303016036540c80200000515900008506071034691800001040745c1c5028240c4199144603140d0156511610316110843c1845802c0840e50724820b08000141c40032083c00640041035040e00599161145401c0c042c1550340c45050000401c60301050f030700c0040c0c1e0041e6680081c1c54 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 851547598 1250 851546348 851546363
    0x50f060c0a170a0b0a0806010f0e040804350a26040510110a1a090a111c0f0c030b0c030f0103030f18090b04180506070c0f1703070806060c0703 63
    0x3229020303008001e0101c0d03d0005c1e04001c0c96040407607454000a43e10381240d40c415210038059503240d610451404054034018100300e41084200042c60b21040005d101910039002104400c0201d00e9151075808240052070054010803408010b0011012000e0202e400c0045000010051402d01b00641d2249000300792144108400311a070f1a03205e07446082d402d0710240100c1d00c0b044c0950800d108001c0508403807409821324000068074803000490001c00c00b0b54003440340d0f03034898082d07420800c070004500312600084440901c40c0303010901c00000c81c0c200074020302e200540c1c6415414070703820080c030050000306083d000700144541922101007050440c0d0301880c107080c44040802d81183d03010782c4607004410304101050702140d00c81556010f100c011000f2102007203000c0c41c00c40410759099031a0005851030300310b403000a00340b50045a07480016480b90201071f00110140d503901e0340c4075261030740e242c2c1c0c1040d0100810003039540003160190400d00455400c0d0915113013100b6140e4468aa000043c0b512 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 851548848 1250 851547598 851547601
    0x1204060c110102070803060f010e012a0b0c0304022b020d08040b03072c030703020d020d140d02061012170c100207060b0a0609090504110d050f060c0a17 67
    0x1d10955903050180c641c1d0000350f54a622500340f070002504103580180c03040f000b0306501000c540c000c00c0f58000f0000d060710388094042e01c801e050380d0541c2000c10809000900d4041c090300041c1e02d410010300c1802c080320003a40f203003814014440c6540001d0b07c1100351b1503112050705040308405d019480322640c1100d90703221512151811000fa030040c0e51001c41c4000f00031061010701070300000e8129094a001e81c2460400c80729000a1000d52411010361743c02d40c102c1d040030300140c1040e06281c10003d00150118440285982d1100300c81030324a0384d048442c2c0c1004c8909408140d0600c0499000f010390390100c0b2085003805010181c038044518020000d0b019500b10109008035442030303038410350b80381064408220140c010100079500c8080b0413a0f030340340781001c980700754600016400e007078418a40c0e03a507407454109003a032401080064025203c01c80721300c00d280b820740e13217500c000c3c66a82c1c4524050114420b03035500c0c00303180600191043c0e049440a0081100580d400b0010050f8000001503540c0103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 851550098 1250 851548848 851548871
    0xc070e070203160b070e0306010b09040b12070626040c060f030b10050c2b050c0f0102131d0415020901111e1015052808010e0c0402120406 61
    0x25407042e51224103c81645034544001c1c800d010704510710581440e00c07098440700d0030780100741c1c403458240035588104201b44414901c1e41030540c081d06503000054400250031540718103075403600180d54884000103d510105280c1c1411460117070401d01c010120318980c0381459a6080030080d024010442041108072290281c584203400402030b400300649138101100c29400000c10360760080c2e2000c0c85134803400c00f490004401c0b0048201c0b0b01c20507021014207000110400b200c1303039882840100018072403801203102d4650284010320641c0b800c415581003403450080310610740c0c0000109501e011800a041102040301c00c0c0c01181041700c5c1130070050362021000f0041e2600504855000c0d41ca1080c0482c49542890010000300c203011410100e9072142c210081c2d54098941e88807030704800c003604c0700703081000c0d0509a62104500f1001ca8410301107000804016010408a92004425039120504030708881c0050110411510040d83c06516000858800f045002006000280400e647d200306000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 851551348 1250 851550098 851550103
    0x6050d09020904050705100509030d081308040e01031502070201020d180f0b030411030a0f06110903061611010b18060406170f07050111150601020304080a060e120c070e0702 76
    0x60340203007070444a0801e0b080c2196920551300444d4060b047d20b003003203c61980900107941a0440080c000e10825490b4501125001005030002400001c440500710000c0d0704507029001a00d082130640c03d0541c03650400c2d07440d00075840304d9001c80601c100706100141c0d901046600c0d400015080405034403101072100c4800f0b909552050001c658041d0b00811820000c20045000d2030042140d151075801c24020103885a010803001418241d80000b400300284003600903030070514041d0455400c0002440200e8281442103031a0081c0980a40c494410303150483c01c08600d0b28001002040500300700c0c1d0110f8190030301500310b0103d0030040030010303a0640d51500010064000c3c58058060704920000440d5100301d09002c0540b603010b003e10101e4103511606291080e80c000c040104048003807000b061080f540064070450460000308400302c0e04140400542c080184102d600041c0c0f940301d07600790360900c2d00e07005040801d51b404000b801e03c800d10000b071500c2900c880400101c3c840d100e00006a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 851552598 1250 851551348 851551361
    0xd11090a06020102220503100c02100c020a03121a0d02130216120806060304060c090b031f140f01050315040609090204200d0b011206080610090b060406050d 69
    0x103610084061012039440da040d00a03180e201c81806403039044542c10515001e00785540c1c0a440d405030301c21800c0c40615a981c1d0040130140380d80e8010f41c2d0011034690020310584900707980942c00342c4c0c02426186c5c10903a02c802622424803080004200140c01d01d003450300c000d04021080303849508408400010f540d5801080403055002c404110342e0344001548400b4000000c2c0010380703490103011014400c0c640109070b01741c42000028082440d5503126981c8000400100c818841045000e800100740800d0700d0001358050354007140d02e00300d511408800032030748001c3c0b900009104079840002448581740c0c1400c0540c8280c0c2401d0a0703880c3e07601c0f00b242042c0100e0b041e030f10704e078010300300303000044d401e04180d0029007264001e440912000509403000d4079003d00ca9500318401c160104041409902070f0741c090007001d0300514154001c4a04103820318240d903815000068107400c031100340321004017004298001890301c000d060050040d4107000911901952042206104000a414824502640c440c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 851553848 1250 851552598 851552617
    0xa0b0108191116051504050d0302070f0c061206090b061b0f06070903030e090f04020402030a090b0f0105033307030906090c080706110601051521070f03060b0d11 71
    0x2540c4a140e86416000d410f03080c080181d950703000380080d094a81c40d00131400c504ca0b540000082902c0852801c4c200d000354003410003039801049500508002a44107451000107160a55030103000c0e421840d5060102c41081d8032045801d4500f40790399801d9110340056503c1b5250030b22080c11840100d00200741481446080301d19540200000c010906400c00c5400382600d02a03565800128000d00610505007c01d40b0021004d10700c100000d00146012f070001d540c059036076807011442e2500f40d540c296080805507400c00c0e100d00303030342d0060025081c100700141c0d8842e41c080c01210035100c0e040741062091050101e000801005000140784d00f4083e8004290096000758208100c24250400b0394501e410b500541c040d9000f0b9500000707070070b48a440344480703000368076010300001c0e441c10041240c8048844840240d81e0014840c4446e9512300b156110b640003480b18a15900d4980701e54014440c00d003000c80a01071501d01841400450710300029a0000380c201d4600103503107440482860564010385504 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 851555098 1250 851553848 851553881
    0x905130f080a120507021e071a041a03010e0a0f09020a09140105100f0518060c070602010605040510030b04140609030904150305150c04081603020102060a0b010819 72
    0x10040141800081c1125003040d0740342595042c410020f107007503420030381d0740000607880600100850343c2000e0740001c0100c0b0002c200c030516569400d90075a1103000e1441c0c4001c400000c0f030100b115001c180590150007111507151072030740d030401c1068400341001805103100310396200360403003131035140c4d910503100a1f4004250b449103d507100c004201a11404041800105038013000048605060040b14501301c1a41ca070142040b400358001c880c0c81e0062034200d0802004015841c030340341c480b4801405c48503001c101829000b03050803000b90a540c400c7d4880c6004d42d28140401c00100341780320030441926442000b031011510b65041202ca07014010705255410301801040c814083c0c000402044011400c0e1402d0045400c071045950300d0910703d220140c059000381e20503500410f02c081721150300c02e001011f00d034107240d181d5074007a10305110041101a4801106001d00540d038040240603031198500c042880140c83d500700081580c440034000d105000c4050348800b454031400d40020046c010711804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 851556348 1250 851555098 851555123
    0x5030106051c14040317060a1814070e01020d050403021509121c180e0127090503120627070521010f0806041205031e070e010809030c0601090513 64
    0x40d2054a906503021404100034007803040ba0b00c1c1141048512400000f00092500e515001c0b0b0275402c4404400710245e15655010310804120b0348161490003440031759224209a5009000603141205d001c4002c0c0078040140010001a55652900d001e0101c018000036161840d44000c100690b144a81c0c20f030841c060b0303440341e181448600100300041111552501400310703000d4445220440c45020320307039010701c0c00c400502040000121000010401a03620f2001d5440b070034008045a12004044445800c0040e1000718500d40d581d10580160084172000d40b09280c0c289200b13901c00c07802031740c8203080d09588002140240a1015942550052008440c80801c8806860a8043c09009041d2894115100032403a074000068081c49942c0c0b24a4a040700040b00000f5a07035604010000d4080700303941014003039010f00054410780502166100d10310362034600c01c0058201c060003004504a9403040c00202e40c80a0000384841c112080042d0004450310750100c81302100804180c0a44281c0e011741 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 851557598 1250 851556348 851556371
    0x20408100b03070906061d030a1b03030801170a02090901150e09060c031905091c050a111906020906070506010e0403020c03030304020d14070f060f090b04030305030106051c 76
    0x410801d903150003141900c580c1600c88040c4001c44499005800005060740402407510445100208840780024100e07202c0c4d41c010b50f41d051400001603041c03409400311680c2002090b400c003060601402501300708905607400300c04c8440e612039090304003074880c800d4440030404150007944010b00c081564825100d004d80c0703400d611641c82c82c0a8031961024030900c0c00241200c1911401d403805650260703007103850120391020000c0a4480505400102e005450b0801010860052051200300e42c58544640321b107515103028022200c4001031440c070b03801c16075040d25003080040d040c2c2c100c0359100340700580724100c00d00802c68034055144014010310035079001040c0d1800c19080c20348210702c644e080b286810850414142c40303010607100203400207440302e00540011420302d94406c0c24002c1e903045891007175480c20081c1e00b580695000c0404102140150009603a00c18030b10005041080f041ea441d2910359900180343c0e11052003103d042203404600070f018110303181c10505036104104400d001503128007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 851558848 1250 851557598 851557601
    0x90102070302060a060b030f0403050405030105070e0f0f01021f0609090b101a07020d02010c0f0b1f03080f0c120a080f0a05090c01141213030212130b0a0302040810 72
    0xc04141c0140c031946000603e1303100180599815903050000060a507103480b1400744604402400480c1413100500012400780c40900c19103206855561f02c0c40d8034615810107000c060210f06c0c94490188036000c40d0f4010ba40d0300081c2641c5a0305100317002c50801c4803c3e180940080590f87c1001708a282041a004140440c95842c6405411083d5211a0007550303980c4100a9100d00d0b01010741507681480040e0251902e1010f03450014010304004044028a9135400840280c181d000c48411012809020340d2030b41005d0400c3c1d410041c10b1000f20008d00f1521101d02901410080c1502c80d2000691404a0b20051000140ca503801854098542450400c0581803020884405204100d65800114a0f0007640501350249401c180a003038403401103130046580c02da142c50656040d1004103d50800070510700207483c0324030101600c0d5104420300d403034001d0400e0722540b01265100001d1004484141ca4600818102c5019140c0d8907a190344104064000e070240c1d030b100781a01c0c0540c0eaa803081c071180c0c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 851560098 1250 851558848 851558857
    0x21e0a0b0409050c0c1b13090506010311030c010215061f02031e182b050a1104051608063d111e010f0231150f0e09090102 54
    0xb20b040500c015955140c1e80c1c10769018000c940b0340742d9400282145d003440440c8800c01101c4202034054031100081d203548106441682e0011a00d95000d1001001400381c02483c0c6002107500718040c0c01640c1c071810000703603102c0e1035038505580ca00c08900443e20543d26507500c140028514610400c1c1004a014080d460fa00107071001c1460301416a00e103208040020100e80400c64000308003581d41d140841071140c20040c0401010920301c1c603124030741c02d4107840c010310450548118010600c184041c6440d5291030081ca103024040c1d0704107414020340c01a0700d2921000500a81fa2100251391000005070912401080d2099180380c041080450780040c01801c4051403c00360b81d64060081412040300c0d040401c0f0181091034001c03c0301c60501c404000803078822002c0d24400810f90007954101901280c0c022a10310310540c1c00c64035100c00032404003103400c3ca4280344101a40d103407840d1280c0e4020030380000070010100417070b29035070707046442c002d29415000c0d1401420b406d9a41c0780407450700e4003d600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 851561348 1250 851560098 851560109
    0x2103040b010f0b07060b01020a050f0d0909060e0133030c110f07050f060c060a06030c0f03032f06010e07090e1b0a050c10021c0c0c021e0a0b04 63
    0x80c00000070521000d10a0300104894006410601d00101034031810020203e40180c18110b0190070000c0c400319400f00038190403851010050a500041c1d94400303406038083d41e0000c0c54803410b003903040000240d00419a0b044404505149c102101c10401e21101d000c4040f90003001820380e04c440c80c80c2d80342d142e40004a801055141d042403801321300d208079a0340c0d140f5000c004095000c140240b0140c00d102c3ca8440d00060080c00041c20104050441802d105c0119000d8070440d41d5100200140b00d100c2075664014800214207004490854400501c4281055554202d00e140320420741014580d2110041201c0200401d8408658480d809120381030000e80e130703080020700050400300d45140b810308403602441c00313078000d0510713040030013030403582e94220700c502900f031103000d2110380403101045c0701c001100d1803284001030f0340e681403c601d01c0500c400c113010213803640d1038140c20803c0c0c26040405044140c2c4c040390300c00c0c0a40c00140f682500c00740b5101109411050404001800c0791451018009551 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 851562598 1250 851561348 851561363
    0x2d140606210d1107050402042d030803041709030613021009050120070806180d030203010506030f0a020c0102070605240604030609260d0f0510030212210304 69
    0x2920703942a001d440c81a00841c000701c0c1c1026081e6400c0d0b600035100340c0c48800c0020207607a151a03070351000400b05d8001d0b502202ea420240c00100b04411031701d8010005034686400f007017100301d0031741d200c600082c0030045c401800800301c2c2c02a298504001c0003683c412803c01412a2040c2c80d100b081840c01c441c500c01c049000300f2204203055a00740c0510b050000381c44040e0b44686c8c0700c8050038040c80100c1104001940350b4050312402003200c880500c0154410281070360400454500448502c0c549036203105408101841800107220381c0d590304c000c681c1c0294040301c1271409500c90140440007403061401650180d8400200c0500b040060b030481d520038400303a251580c601c030118180415000368045465484102000103200042280c0d12640c2d8030750081000110060400c51800400c50403000120280e003800301f03440410003141e0191903c12a200542840b05007031101d090710402e5400c0c00000d1042e0700d01c4a13404081201005490201c00490741c400d03034160484261101e03568414ac40659061 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 851563848 1250 851562598 851562619
    0x210703110114041532030c070c17060a14070c022e08090609060103140705040c0504090c11060105010e0112060b070b09010c0c080d0b0a06030e0c010305042d140606 72
    0x130030300c06443c00e03000c80014030042103400602e100c5c0440d40c0000e0484540c2c1c582840140007182c1e040982002908030940420341e0034044418003494501d0040100c2c2044d41006904403c401e00034620b90341040303150034103000380e002a100140c2c1d42081c090f40c14259020010011508402c0e12403242914401d580720101d094462840d002c0d03c503041119404050352004004000050038103512400851210040c0d5070496150000a07007900c9400030b0501c006030303022a00b0300c640c44851052131100b0049040048413102c00d014002d8a030700d0144541d07410301c40042075140050740955440002c58100d2841040741d581ca59400300e003660842c500070758249003401c0004030101e0051140c22903884841e203550390490000c0c0d03a0b24055500c2002a4540d4130b0300c4259100785034075030004500c00380c05140c03004601c400008074810316200750310720540c0c101030420341032101041b081daa00d1003020005042102c3c0c141c8a8403810020751f803c650700141105003146040d14801c0002c50b1040c051042258400c045 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 851565098 1250 851563848 851563877
    0x151104060908030c06133008180606060306120102190e0109320d0501051816050409170310060201110306061210080d0309022107031101140415 63
    0x8134001d065008a03158050004608074402c1c006052805a100d040e200c0180e00d04464800e03003201f49904c0004191202007d641e60305504a50340e01e034002000311100005c40b01d4500e8540e40c1d208060900e50045400201280e6541c6401081110800c8070000965a882a6441445000207102c9a25001444d88510440158460000401140c01e134000b0084140300141d6003466011010034107203102200d84164440a450f400d0040041da40120000904c51600c403908001c401d0854200c181035801c00b09001074000c012212103801d50340c0c1902c00007103840301850089001e901121550b40d50800210400918071071808026090b40d0107980207001080d401800c0300d040c5d0009440310380c1d01401c14410881c184003102c08842e0700514001c40d1080e0700d0703940c1c5007050909440210303ca002940300da00010550820600007410081c800e41404040c4005500c00b41d103880b10340c04000d210050325400c503055a0b2159003c0098209420040303030b52169201050441110380b00c1b403910201d804540705410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 851566348 1250 851565098 851565103
    0x70b04030302070e0703060e150a0b090d0b0a06080a0f1a2e1512060f05010525170304050c030708030f0a0215040516170c0d151104060908 61
    0x3103039070507001064502d090500022200000400150406940714070008100320f0008015001c7d8440c139071040ca100070030303209000d801515074009280700581041640b8050710b900f20000041c580040010501d92290641c032409004194000012031142000c02d03828400c0c0801062100342c8290361103200311071004d90341001d030f075011030700000304044268603d1300c035190320411520151807402c812091303503803142d200b8503100901020410001d451000c00c6441d00840b0701c00c3e540a4000c510903154410700d441c000800728410316020b4002070b0080c11030340320300c0200d81800300c82e0305500620707804000080451889964200301d50940303da1260051003201410046045000d441c0c680c4043c40c6851000746040d0120b522501441085110780c0c6045240d2221510125010314400c50141c43c04682d4200c02c0303031021403c1d80040c2c800301008405207481c08000500d95400000c03c3da0b40030030030069030a1114203801e1140307100f220035051150306c1d03c0e152107400c028800d0380c18030340342d0a84c2a5103401ca141d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 851567598 1250 851566348 851566357
    0x1d0d0905010f21050a061403030304020d020613080706020a020405070f0f26090109110105030709120809090a05090d1b1103010e031908060f0315151908070b 69
    0x5000c5440d4102c1c00700500d100d03942c42c000451810419600350114020741c001118011101d02100d6030342d60b0400d101c1905080d0940c10000c800710b00860460500740c0003d4005140d07441c0c000e00c183c00c001000541c0f6025a400000102454130503945034503a01e56001e500d07410000c00481c4507500d000001040b840c09408080045000360781c0e0100c2e804440b002c25076103001d40c40b0500b480c00030f420752030030f25400400e01d185105030000d00000c070b0984880d2600c4035808100f03480c250b042c000107204100d03890783c0c0003c0310300495a0800ea40035240a0134144040c05203c0c18010b04e4000001d0030802c0103281030340c1c01040c061040d0f401281c1d0661107101080380c0011010b40d01c1e1142c2000c090604010807050313440d07281d201c00001e00018084444d194810700d10341c400d10144070000e4202c400d990455030400c00d00c0b0342c42401036902c0100c3c111003100081c2c1320580214100c01c030188050104004140070b01800c036074103001a007140c1b01280155480048000c031171242c050140300700355020800c2c41c009001d44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 851568848 1250 851567598 851567609
    0xa0809091e16020f010606110607080115030c090308030703051506030c0f09032e14061012091520070201090324150e07030605010f03020d0b041d0d09 66
    0x101c2494499180c021440205258190114883d070b41001520301c00a1244500074441505c440d441d070804201c0d085c0c06c00c40300a1000f400e10089034010800420b10017103180c03503440d0341d240000d440d502070b10058072101030b1a00003078500003001c000c00c08020341582c40103005400b00b0380288902604d0401b0000d25200460702009030701c009001984501c2c2040c03003d4a40103200074190390820342980451f91442a140c074a45403081c0001503148071f4411107124910024034050110303142c0b8034120021800c4000f0381101c600c1000340c240f980f07148180b01644101103056120060000505140031356102401502c1140c00410080c410820701c14410602160075869040c0c42d0032040b1842c584500c0012400900721105503200c0e2628845001c070a8801c841d25841c1c03c240145006040c10f041c01c20b03100000741440300f49440c14005000740d031f8203c4020840d1000030710307000d40e4580c0000030150103030a010f0b51140c0c1041c1040d00c800602501101440207001a4030101c500d600422035044805002600c0344 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 851570098 1250 851568848 851568901
    0x13140406050a05060d091203240803070f060b0316210c030b04020d0f0602130602030307140d11071511070b060409082505120c1002070606080a080909 66
    0x7000f01e82841000791034682550000028010ba003501d941012a840c45180c1d400280d403503c3c00c2d02100341a411221516203080180041d85050090041da00d00c07038004040c004c10200e820328420080560000104c000c070142c10358569a94031300a8041084003409003845580740c0c00c200250024140c0d060009840e0012009101d4a180d034883c4102a07c1c09402642c05c462284480804900300c1200282150301c41c0341e005a480c40540d40d0701c1c1031103065070401011074004006225109500100004203566140030046c2d40d890006d0032007008000c40107000300485c070046021018032005400308180d10740d800005000c0030354124000c1e070a0b449902002814a00020042112402d00350305c09200c06120b0a0300a00d04619840c00140490b141d80884030300c00100010201040001d21481c004403c030452228241b003402c091441d1608140c0d004028443d501241000902501d5044000140199801c1d00c003060b00a003040d00080c1c0c4041d0741140101450300214081d001710300b910003041a0703003080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851571348 1250 851570098 851570119
    0x9140a120206090c1e061611030610030b07270308130b03060a03060203270105060109091a0f3c01091503200f0a0305060d030c14121314040605 63
    0x1701e500c1283c1070004085d420a2050005400c616900c507030310300b442c9001d01070003c00381090104041c50303c080180b0450f50101e4154040000418800640c0d41022440c1416070140c0403802040010500c0701d58442c2d020480e800000052002c0b0000400c000080151a8600c007030710f07040c14952134072080c1d0710290480c858003010000300e10316074051138009901c946a100d402e0300008035902444e01c206080361050755a4414841d603581c200250100400794100140030146c0ca011501292400080c603060041c1a241d004c9622030740e0303699031014410503221410207030620403070002614081210000c800c604000224400c10340c0250215412983c011211142c3c03003017281002c4000d410780354030840040718140034103500c01e000000900221040e12604680381c17100340030020b05071000500b1050040e660040d40d800403a078000340d0581d0168100c82c4445140b030f0042c1680785440703422200700c02803250215660a10741800301203142180d004804140b2a61101ca0406c0308484041c030030b090340140c2001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 851572598 1250 851571348 851571379
    0x7050606030a1a07171009050604051909020f040c02071a030402031b0409060908030702010609090503040927060605090c27010504030b0426030f010909140a120206090c 74
    0x141d40540c404110305c0c080c00000c54280886550389401d4466058003e007410301400803940c980304259006004803000e101c07604142040d007400b29929000000b00799221107a05e825501e07000c08002050380d01420030842e031807a00d18000e4440260b030061406010220b100c80c030300740c00c40e030060340e0040c0d030018003400e103a03030210301c410412600c0344001680240d182d1020b040418541d1180f101001d010b078403030726900c0c5001c440013401c4400d070b9044001c185180c290f00707202284000094400b6140860b400281b080d400b6600f142c6500702a40d589801116000b544904200090700306200301c401c280c13113190a80e16150300c1c02c515800366450700210607214014070007143c0394010006280ca030341810a640390a880c0e485444d00f03801d045400341ca0041142d03510240e5040c49100305218804054a8a421030920041707420312094180b240b148013544a001e01018000400350440701000342800322034408c102ea14102c0302500003041914054006c2100081c003859000c038131495543c0c001000c4190486040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 851573848 1250 851572598 851572643
    0xb030f06100c0305030705030601200607090f12020906150c010605040c050901081f0801020706060812070203070315060906080a050d0e0a030b040c090623010c0b0c0d0f060b07050606030a 82
    0x3010f03241040800ba0605020707610002f96550b0700c503810009461203190141d40902540c0d201d500c56800c01004040810204e08482c0894400740d0b41204d00c103000b40c554000003107540c0e40e88d1100d82d020400000301031084140c1584010120355054800780714030740d807400c1c0035109405003242d0329010982590000d54000c2542d10265503051544110108041e1a40c5503d42281c020038000c6905a41d904400d00c0381c000200003811119035950356440c070384413955001c6916180780c2d2100604c0c0401002d00d103c14a007080d008900680121402080f46990760700e0f080b40e032014015411345560059001014124bc800c2c551035004072006003009064524603503504004a000400584540107a0380000c0f9030a900c900407080100b94503001c02d140010b0040415204000490782c0760b05001d90303900948000341c2e03550201c5a002c00403000068803610801403a201602d50f265002e000c0d02d19010020032446500801b038504140104200e582650360070341459a6140e8100303000d070504058074a02407003006403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 851575098 1250 851573848 851573851
    0x50a08340207273c060f061709030903031c0b0f100507050a0203010608012a080c03071e020303012108030627010e0f0f060a05120102040b030f06100c030503070503 72
    0xc1c2940100c80000325011242c5141900e002d4210a415000301c082080003940a01701c00b80420f04242e02500e46440d801412140750300440340800c150308000602c2220301841520302d4040c000c2d0030f0701da89440d1040c041045025500c441c1007024a03140d640c803183e041442c074013580c0d02e9014140c41e64840300d40c0010703a0541c0000104842a00c1000140c81c0161000e0062000070400c0c071001250440412801c20134418260400801801c0ca07143c1c0821710030783c400c0b00590070030a0001816585e03100c1d40710458602c102704d100e150044580307514860880c1e50020086040300c0180d11903000e04c030410700b2602e14880068801901859040c80860070502d4110b503a00ba98410750784d4641c02050740c0b07202080031113030300341c0c40b0881c0d5800000801044046d0350b05900d030b000e68042e070740c0c0b0407510f445800105501c40d0380c00f03802d01428180141c038200304402d504a40c080c1000ca41c203680c507407800c1c4e00134082e2810f0846000d400303240420300d0300c0300950080418140701581038450604541c0c98880840c1d90340c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 851576348 1250 851575098 851575121
    0x12010611162d030c1410020a0219080f060703110403080f0a030209090117010c0e031e240a0606050306060703050d02090607030302130510050a0834020727 68
    0x1040c0000803072444010a0200254130540255000303e28209944e40b20411154071540101d45440c2d1050340700b640407035054a11941202c01e05030720381e20f05070310265540098011080e28421288407861888001414511484030380d80c0501402000c0e070342000c068011840014002d00c0c1c01e21115a4640c02c0001510408155150050501804d0000144490401e034000503c0158101056085083c00c1c080c4500900c41e90805080d00d61a0801280d41c030f61010311840200400321040c4640104148400444240b040100d0490800c3c3c1c03880c02c00d5030b06c8099403001c4089190007000903186000f1003d4a201c0d0740000d20050030070f48a0344040d141c50b07000301d5044031707071590800c40310b5141d582c1c203030140c00258003070703a401a00c0312407003031001e84035100b15080b080c03045004080042d400c0e607010046074103c280504c3e00384d045880381601c1c00080309211081d8080e45141c3d589003070f4040f42c4c3c0300095848540c19400c0310800d0740c0d1402c1a8a03050108030003420400751014042c0312400306908100200321 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 851577598 1250 851576348 851576399
    0x309011d040f060609231f0c0b150a0f08060712091b030218061507020402092722022803030513050909190c08031201061116 55
    0x4296141c1070220b83c140c0e0050408140b5840080c131651800c01c02c1c00c0200d0a00403080103951105000048019030140702400e00d010303141080c06580c1e4030500300c42d811342c1ea00224500c003c1c10b0000d0080c034030222003402075003d03001d80c20002488c1c40704030210341c0850b040343e409001c407525042821036401302c040104404032600c4070040f03400507900090340a0708050040400319454154410000b100c1c200a02540c04034544000388034890f0345160700c070b801e50140014400d50b01c0c0310034400704019004bc07004088d4006000042d0440c0d40c4070f684242c44040c0e84100d800c801580d2444102c0324418200743c0200000c44540214500500305040030780e0a03c3c4105000c0001001c030895000034411054004400291000c1407059001441e074070b004000c2d100c205c0b2207450601e04001404ea44901d0780c02c0a214602c55000844140a440307042c1c0e0020f0100c540079640d0354465805016190002841000300150341c214090000b0000410041e82d1502e0b941a0141e08620300500b00d43d0038420b56085141c80fa = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 851578848 1250 851577598 851577611
    0xd09050f06010602100515030705091503060a020721020c090a1e09050706050408060609060607050d05130504050103030c0311030405030a060e0c01030c0c060903020a1707050d020309011d04 83
    0x503204015a900070503d99000b4038803094007840038820795801038140004012850b10070941541e0101d60002500c200b580c41d060503a032418541d591480b8030002190b0140510010321801d045075800402c8010f014070107079114001e800e09070000651014a1050041c1c100c4100d0b00854a00503041c1a0800c2000d41c011551404054090001003c441c0006e048582d4130352006040200603c0b11100510550402f14101444d20010310f0f290b4000400541c483e8181400150990f0ba400090b1038076503420030115810031100001c003501980c4013070541507031100c1c00c035000503080c645806414141da40c180d0f2210f4a007017003a134003901c0b00ba1004c440421580014040480d06840410141b49558040c90021400b2205069144e04150041c88070303d0415080015001440c0c0d00f01c100108010313440040002d000045040c00c0741041180b203c010544401c84400c1041e03070b080c400191100d0b50046040d100e203410045004da81d2886842051408281110b590003401211030440e9543d5034000b0f000410700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 851580098 1250 851578848 851578873
    0x3020c1e100b042a0f2a0f0614070915050f09210307021e060403030c030c1e12030603020f010c020406081006031e0f02091909150b090c0d0905 63
    0x1030b0f10300098080300301090356481d14550f0b5071041507038402510b14200400090000080d1550302d00720481e40f243c0404071b500c0071804219801c0d4560b500b083e08680704010303001518101c2c2082c1c0100b51020702c005034400b030021500c1b00c2451041001d5000303030748030705280c12524100b55800f5000300c1075141d402241c1c584441404e041c520600c00d1403010090145a6480c0144108035900200038403424612565121000098a8500c201c2e0f05603070b00343c00c1c200a203195500e01220105540300004001e0524110a20881c2c1403500149071360074858100013060f8090805c0440440f5128440039510042c0554002041c0d401000240d8189001400c0419040d442d251078070302e8080c1d40e22000303141503a10b000030002c3c011541c0702c1c02c0303802855103010035011400c0e4880d5201e500010388007901c542d02801c04115510240700e030301c9103090404c0c00c0500000b01c6500740083d003201c1e80c0308406809814415035030340c07903d0415810340c1b040031034440060501702c43c1949035009098282c01111240b14400a0f410b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 851581348 1250 851580098 851580131
    0x1e180609030509041109150c0703060c020309040e03160204021617090306130b010303211d010c0f0503150604030213050601090b0f1801090b070303020c1e100b04 71
    0x60310300a885003a42c030b242c2201440210340c0181d00900103051706222030840d5a03951403501c8041d4012158107511a11080259400c148042d4002007180380b810076410300303954000c0044d007400c200840703040015031084001181c43e4400e07551032210540e060b490a1005140540c06014000c9000b1741d101c1c0340b0502e90b540c0388041c43d00448041c1d254000407404840c286002c021155000442940207011400c49640d003444031749040c000101440030544a044006064200e100082c0b2071781a001e001804d400290740500c0401d90b40364030075650801c15402016406420f91400082c102c0da034151031a561040545454168408020303406a0200030020140c1e4a0610744507120000000009a038201100090111b100ed9403190003088814801d4003240c1c080d550a807160416540c0a100e0b081c540480100c40d41f03440703a00700d032448040100c0c1c11000d055060303007d84050b24401d0112014648030460f09000c0c0c08011300c64400b503510000e010050f0b400c0303942107461406000392002c05c0c0e0003002005a0b1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 851582598 1250 851581348 851581361
    0x20309030d120506030f1203040812041415100b0d0e0102041d06030c010f03051e091510050d0807030512010e0708060f0105250c0e060307091e1806 65
    0x40c001a20a540e0307601c032100310b20490360007640480040c0624882d114011f511044a401061307c16007021000500744190f01c01195414204416807135903910f0241761030b110f43c082d4541c071500e0b140b081180035001010308001d450b004881048005010b140340180d040d190307a00c0003000d80d010030707152906086201d130f090020b0005402015446101a16108407003088030f00c0003802c40d8070952210005c0d102c0d50341c014020312040c54032403074040703001c0c1d8400180d1100019a4003699407048009010003a0006012a804071020590808200152105590081d1850b00d43c005c1c1e0340c1c8004010044000560801c005241284c800e0800e2800e16114904008408078244c0c484000300e4240010498142e40c0494902e038031032001c481e121600c0310038000081c018001c1c1070030200c02000e103090810100001d00c80f10107c0a9102000c1d00b1800d4892600f056900c4060351030364041d02c203190010800a8a80c001c0c0100710b80c002080c130080c0f4581d084110301502a84488240c501d00c4c840d4171002150b11800f901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 851583848 1250 851582598 851582623
    0x6210903031605091332060a06020c0a0e101502030909010b0715020d06030f0c0314070321050705010212040c0603270809060a0e03062401080702030903 67
    0x840c0c07207103801200940e42500349401c920403c03008109405607070b680c446074100d00581100001a9241201201c00c904801d0300e8a407905621840034011130032100c8080c04c500c24603090b0340c1c100f8050b03941c01c070690380e40500c08400c43d0300200380c15061201c02050020903901080c0c481300c908000c0d1f40c7d002d080ca90111104103210060304000b0700030410b4100b11103428010448018024a80880354031001000001e00d60912006900001c15802110240d04190061134108401118400e124a41070150070540c1c4001c84142c00401c1c8040c21040300070941c90100c9130011072002071014006940011421900304240c2070110601c90340011400901c06000d2000411401102600782420403d410107040e600001c100b50400303035503282001072510401460304d07800c1244030b81082d4915000d1154040c01d0200d9800c240003099400566900420040b00d200040d000c0e038070241c0300e41c62046072144140c41e90841c203d4075019031a5055100d9040035900c41040d1050300d08015401c40000c2c1072100601c0764 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 851585098 1250 851583848 851583853
    0x60402071a100f080303240a0f090c0c150207050a081911070b040902030925030b01080d0f200102040602101a0d120c060f020c240105062109 62
    0x1003020b55840e501c601e50140c000c41ca415009207240a260315601d11009001c1b161160705080c03000d0200a041a910302e900c00010203110410b51141000280d41c641da00c02c2c0c1880c6818401c808a825000350303550355040790880c4040d0780ea16104402400039500c100702c1113442c0d00c00e409004012401c444081e0298003d85071940b10880304804009000c400e00100d680056007103801e0801021054008a82c116aa40c0d0340150f1030b81c0d680030342c0038280480200a40c0080204040100000205860502c181d911849513040503903200d8040d1640c3e119040303c40008102e18a840544c9240612130340a80c8603824003144a0b418840301c0110709903001507000e800903030300040c001c8207402168025a40721162106601440d00301000008803d0202400c014200f050341e00380c0340741028800d270b450302000d980001050000315500000742c0029402a24541d000b8000c94224682454060001001c40e2441c4010480940d00307040400000343d111500f50000040008d0a07200401c600b00c154511402c4540f01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 851586348 1250 851585098 851585101
    0x50402240915031e0f070f0201060f030501020c070801020a1409040207051509010c170a110f040f03110108060a0612021323060310090b0103090501020c0606010e0d08040e060402071a 80
    0x101340c04d505281c006032940b582d000040001c8180501c0300c4503400071842c0b8120061480007070051340144042e03042421486d2517a0004004c1c00f00c150010103132191040200e601099446072407500b00d01a03100e107040000c040c034004801004c1d01c68040c00706240020b00040c82e08000340c4d1440d180c041c85034050f2000080101c1000b2801900307200300c1e08018614102003041d00001e030505035040c513009054494550380c40010808407503489054840c4180c000400e1a903498442c61008458106031000301e5140540800118039940704802c428000c01001e4003032040c40d410702d101611403443c486241320b001c1d90300740300c1001c10ad9501c900043c0100107481600844c441e404818031003150380700c2c1c9818010b05080040c00119440b00c0c1c0302c10100c0d0400100010900c5980e40100c000c0d01c0303501d01c041c0c02507002150707000c034070305000c141d01e402094242c0b01c49406240d80e005010907418020005041d1110510003000f030044030b02c4145034410002800107140081540c0e910401ca0f200705130380d10119100d40d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 851587598 1250 851586348 851586361
    0x160f120b030a034806110309010911010e011b0213110d0f02030403120903020c12060a050601091203140c0708030307080603030304120e0a03060c120f05040224091503 73
    0x24440714102080700700301001001507106001150f03404d50300082484a980e00d14042c01400c2d13000d01c01c450804558203039170f410640366090181c03800b500d0660300f0b1200d0400188441d802460756030511003040e1540074043c42a0302010602c10744500c4203036009444152a41c1c203451030b610441507101c0c0040030254540f11001002c50444440910b10212503104009000220360810710900044039513140c046601e403941d01c0e0490511618003000d41e00708003d880c4e868000d9401042862040001c42010031156840c20011106018940b18000c2031002c40213084011900c40c003040c500c00a40d0204c06890036020765011480c20f22282c0c0b281403540c001109121900b640022895045a0f04400860850074161600d040050b00c425141e42842401628080c290b00c900e03c016004641294040001c2c00e0800006481c840c6680f506805461402940310070062403403207441d00070b40c0c0160113425020b00d00c80c3c1c903c0d40c3d0605010f01d41d08050040c003c00500f80d030b450380d01d1406009299060b030340ba0700307100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 851588848 1250 851587598 851587637
    0x203120f07080402120c15040302010318080d0c05041e051905060406030e1501030c050f1210050c07050d020a0c0909120503060d050f0312160f120b030a03 68
    0x290039010304400460500105540c4100069003181d01142c04840d044900b140341e51400300c0200309030750404003580c00c01c000b00c410040a0300440e4003e80b000e01048440d820080074241c41840c000f04420320520440c4c1160505500641c1401c1c55810308501e41a115a142c4050f500f4100c40302c040c04031124010300c15814420902524050f00c203600a058030306140c0010001d0145001e20403c040d601c1103500c0d00301c102000041c0441d144400c803000301e96181d040c44024100f9170b0042c41c0c0195a480000016411f08510703d509000d2554050500890403451000143c070024012110f610402c0c0107500c003248041c895101c10070004d800610b40340c02d0381e10303020411700490380c040d48000b80340c692000041004005070440b044540c0c5070680c0d680e17036400001541c680c542100030300b40c3d1041c203a41e1204a1070010041058036502c9411304581da48540038040d800060802e098001248403a40c03100060080900e09014000c0710404183c140c00d1402091900812000079030001d240f000c1010b00e9071544 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 851590098 1250 851588848 851588851
    0x801020301170715030b01030618090519080d0b0604082505060405100e150a2115030f0c150c060b0603010f030311070e1807050a060903020d060e0d020312 68
    0x4140103440044e140250640c03064080c1c40d10340b000d0503141c070081001c0c2e03842070b4000d40c007038110510314928810b00c6035000002021025002c8800c0d06c10401a0710448401d465000070460b409003a0610301041c046e000e0004e007900d0b0302010340000c010311000c01d108100384036407120402210610301d50740d010344081e030032049420703070005002d41c2c4104030620032622400c1100b099950305042c402010008480811200c6440e202e0090301007502280480402c4e91180e07004021a04414040c0d8000c501c1e01201c0d4104c88951204030809410010704200042c1039038920316406010300a80e0040943d10510b001c080705000d8205c02c009880513038010204003140c4545207050780203540c21411581890003c1140c1c3c42203010240500c021107a4500c0e1400040120802030040b0440504ca00d00b17000080240072200c1241202c2e25000c0c000d404034480c1801850302e01214000c2d43c0301e18449103143c003800070020500f4404e4500c55282e803d040d002500030421000803801d41e5008507512142c040b41813824060 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 851591348 1250 851590098 851590139
    0x622090c020319050906032212020115091506120b030105070816030903020c0418150b120303150103020705030721170c0a0f1704080301090b0603040f26040801020301 73
    0x1301070010b43c100e62100c0c0c00b50381c1d00948829078003a9605454070020252205400c0c014140f03068030218500040d41034100014184034040c0201c0b00075103442d8880e099a054602800e0520f42c10141001401d00c108040240000c50782c1d0002070320185640400c0c00d4400456054021600c0e80080c400020003221089515001600d01040350081660b40207441d200c90411b064850b80c0c482079140d11400181c4208502d50384e0001c581410500c1c1865440c0c0500245018588604084001d132140640301204481c4102400c5500d040f40140010056000307402410042d1258401030151030000380343d00003001c0c080c1c4400c58034003a440085040040441c012131440e04901c00200e07050094002d050704c140c90595000b410700080410781c24a00b210480085140e460b2401c8001040c84180443c010040d03058500c4074006002901d80d81060059034070013070b0340c01090f0038000d11703945001c1410340b2605a101c884a00400b03400c1b50341c50015040d2504260030968803650300000400c003120400444040541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 851592598 1250 851591348 851591357
    0x6060d02030c070308181507120f0b010306120f030c0c08160311030a171605060f061008070f11070b1c05011e060f03023009010501050622090c020319 66
    0x20244106d9444a5401c1c22001c50605244041802e29000703583c10340007021000410050855546003440140507901802030100b80b030000007094a03e28102c0c21000a608060000070402c0b5540d01224103003010700c415100e21010b4580403542401c1400825141c1d0f080541c02a6400d0550800c03e03030354851021036600ca42d11a800d80c0000a0404085006100d011a00a5152a1801182d080d401c1d015440208107010710010090503050501d00b55005180c00e81e04a030450100701b41c1520b11440540e00c150109035126400d04082d84035981441030380345840c0c16100741d15500d100f40350094000034441c40ca250300c0d00000c40031020b418402e19005003810800001d089085851a262011031401030004000032180200300c400e0098040b10042a03130220425542c071419030444c005400399016010903003079840f012030440da105014190582e48010030b814070388800c40003a0340c40d0000c684641c000a032070b511800601d1950340c9c841c032011a9029000780d41d135101c0e140508030b410016030f40c1000500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 851593848 1250 851592598 851592631
    0x30b12012405030c0d020f04231b0d2309010f0b06032e0e0c04030203150912070618031812051b1c060204060f020105190506060d02030c070308 63
    0x1650f0029a0302c0d12640191303100b5a1030503140c0007083c0031584a502d0640c010342421000003901404d41c2044444903180100c819064954010341c0d042e80c4071a16940380d02440c24009074500e41000c0c0c0c040303c105004070a50200c01070200ca084002503804070384d2005165581c010292401d1014001d14000e80c004452491542c9000c220641c00c0006080135400403082c101c20002c13205001f0160a0003414080301c9280c138600d4600c0e000301280c3d0250008a00034000c4855000504000040c0e07940600040b5001d8a82c04c404031900041039045807000303540d02d54503200180708803e19108100302c1c05000c0d586031540380740e000010241d0003404c1da02801c0d001d58540032842c04a0070101e1016580e0301078541c2c034528041c0700703000907589441c4d101c064074008000c96070b820204012170340148200c5510741c40d902290744040300f00303908841c011150b49009003900c03030a0800c0b9441030f0f8001980301d180140b801307003032649100d510000c0b130f0400c50320440300c000c000601109254010b18000d60050241903030360611b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 851595098 1250 851593848 851593859
    0xf010e0c010e010903081206120f010506040f090b2a121f030b04110a091b121a0d03090e070c0510061410030b03010c020618210a030b120124 62
    0x40d440303031240710210b07d4403000c0854a5a0f036104c0c079020510005100700c0e100710492510b6a4000e100a840c058071580c604a18010740f4500c500840030300f00c0d0801d86900c000e503034013940021748882e04580341c1c1021802c1c07898104038070722620240540010824a54085241510007030300c1e0075084004a0b030f40e69401d000200b00103030540109592080d40403000009640d05400460000709464100201060400000d00c040400d41510072a10788071540e41e181102d20700d14501c00c22034250300c081140c078003e814605846818107461414159109107001982c5660308c1180807094001076660030000382d0444129818032400700000c80a011510f0700c20002c091400700001d04103001c5102c210300502040c4030090505000e684551480d02010303000340f10340f00714900020f4403814221506011982c6a10030316011280004501100b002803144003000c42e00b480c1d181d01c00e9900004000d00c101a110300841c19a41c89038800c400c480c3d031180d1b0003c941034400d01c4800140c00102d44143e0350403600c10504111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 851596348 1250 851595098 851595113
    0x1051302070c0b07020301110d0b010e0907020705040b2b032303060d0309050406090902040e070b0f0c0705101101050f3903041b090c02030901110f010e0c010e010903 73
    0x440e000c0f9500950303a10b00c98404a80074044450f80000c0c0d03900045030303403d110703429500f1110120000760b9480c1d800c0c104220402c00c04610076103412005030703c0110144075508044d4804111880c0042c00c2c0350b00c0720a00791f00d40c0a40b80c480900f000c045856200d11300100340d0040359200351080c0051056060058420540e0032074040102418410080c014098003410302030710b000d001070840900240146901c030351810028240540f822400f075403510010006940d000700b208000e44090007a018a042d264045850054120003019107075800380250006244d5245440c079010710a050719440010848050198211000188001c5400c0e18481c1040301a504a80384d0010000300c081d0b010081c003501a81074413409040141000c0a0308002092000340031100d81103400490070754040d0100c071f64503002d504040c0c2b2802c80c0b060026034014402e80d0340540c098200320102764496821240e0015010400070309659480c2d1443d103158224949090140d40e1004170500a0002800e01514103440c43c1e84510303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 851597598 1250 851596348 851596373
    0xa05210322060e010e160b0f0307030e0708030c060f070807020606090703020408011118030307080f0711190f080c0a03140f0d0816030504320a06050105130207 70
    0x54504840000404020a60b0f2103c41c2d1095090020000000008810b650368004800040d400400c48600060001c00100881d085041c0c095003150444c6c41d1000294054403401111a1082c055681d0209001204102424050303609400401c81e40c1800340505084010191244013040740c1c910400039180d400060352038200a054030651034607a101c1341700f14024059038200c10615402c2c1100001c00f09401d0014004003103118449004500c1c01b64101070b6a4840c40134000c0c07030f40405010828000c40c01c1c002401603240600c0c801d010300c2803210005203a03502013110010b2031044031107003400717031110350803040f4007801c60800142070004d60310b80000e604006501c40100041100f41e040260554180f00c6000c00f00102401c45000aa1018010381034034030442e003042000d502d4100205155110303003e0030780200c2e0081c18401e4002c144012000040d8810030103140c4180880301c0348040404100a2000640d000d490000b41303a5040c0300800007090203032988101114010700160b00031030350603a002c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 851598848 1250 851597598 851597641
    0xb0c2a0616051603020319080f0a110d0c0c050607080702100b032d0d02011523060301080a1703040305400602300a0507050a052103 58
    0x2003040514031204980b584194042c0d498600c1042d00b40c6800c0680001c0600403480f156107207180c1d1501b000c0780483c1c03113501c03c80d16001600050004500300320032541c007a55440440c0c0d01c000b840d003400c1074603038811744820f220a080000c421504180500c8014800c40760091004c0ca01003000d418100c00095491908010103445103989982c4400d01c1c1e83c0400242592101e03c0c01c8003d030135145000058080b0700201f02d090791324000c0028032245a031040c415184a1490444004105420030003494000e001414410f007560040b048a1400380d42d484000d14000d02524000303001c040d14529207041c2c0c50b0046d103200c62840728103200340300c00a50044156518440306a204a002070354000481e0042092080c80000c00400790091041003040c020665081d50026000c035030400707085000c10125010030403040b424500f021203258003441c26900050400c0002440d045007420001d0700c3d035034244041c0c2c1100b00c071190b004007051040051b0844234016280101c1100c1411850038498903c08180c40700010f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 851600098 1250 851598848 851598871
    0x20c030604050c040b04181a0a050403050d0e030c060a0b01020d05040f1223160519060f020a17040303090b1207030207020616140c0409080d0e01090b0c2a06 69
    0x102ca905d512190700080001e9122400f51440301da5509124410701c590b8100d81e035030380400d1000150b03522024042c141c081c81d8545d681a2400c2e4404038603100400040b425001540010003a0b07400b00e0001300640c1d402818002800034401070031900191030011400940341c01d002d014001000241051503400040301c1d840010400140824030380720b802c030341c40b20748140c4c102030300d040744520b80f004005403c0440d4446001983c2085495408010150122080c3e03000132982800702400441d1051940e0a0707410040d00403182007680070340e181c403110709007550030b080c82800c041010414583c1c4120044001d00e103140380f0628140b0280e10380f08201400400a0060640008820045441b61403c0b034450341c20380300205a4401c0c15203801e400e040885e850481441c030038056040401e1400d4481c2024965028080300d1801412208100140c038036001c4100b03041d540c590010000c0b50300e00c4070b91880307070781d081d02d04c560b44403d0544a00034243c40110030010905a4a050801743c0380b000400c50303045010080d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 851601348 1250 851600098 851600111
    0x10f0e0a090905072309100b03042a0b030a06050f010c0609020d020a0b0d0609022104020d0b040b0906090c06040b0310090c050a020c090603070b0a02010e1606020c030604050c04 78
    0x3e00d00d14000c0c103030b4800e40140c5850b41c094100b0441c803a0303400e88090812184603007580c407201c40700c00300c0580f14021005901c2c82080450001900c1c2c92004140c001020b00c8048640c0060900712040700d05540040300c608000410002c4005e0284911006000c00301c03450210441e040c80000c12014501c54002d058507680e680320004d658a004048036541c0e4001c0c80030002c141c5031583d14516070040d0a030000c0c81c40c1842000300d0310107030307600a40c3c81010504440b10320140403000c0b06e4002150250040c0c3e084801d0703014103004171341582252440343e80a200c0981e4141400340000b840c1c080001c2c07001405d604001d40214165507100d0407201150301c518030301616501c1e51007001e04090281ea0101103864038084100c01c00c00e41050140808607415001c3c2c1d031080d8000c03814030001c14800c45000340d040d0003440d0b06205401e20a0007400003011103100000e03400c40182d0280d484d0803142903a640325200c8000c0304200d03443d810006100000020740103024141420ba861030f07030781c2c2514010541302d5170300d895 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 851602598 1250 851601348 851601353
    0x20120d0b0402040b07060e010b1302161208060102060106080c1c1d160e16111002031e090109051b01020a1e060509120d05040804120b0105010f0e0a0909 67
    0x400000031124014000c560341c40c0d651000c400960700200d41200c60301d00f08200181c11240c188580400400f001e0320707010b100301e540c2960900951180a8641c014503003a500030008c03426041d840011200c55866810381e178181540003a11f0f200c0140e00800400213034904208414002c81d0a85001d240e64070082c81c01c1030000c90600c030207005071401d4010508490316428610030b00025148a00c00d580c529880309883d1144002002c125089482c0b208208008030045241440b0300c03002800524239400b590440d181c0070742d901050380d00661b1a103581180380340c10792103541d1810503aa40c011005800030816003015a55075910740c40d6181c010600058039006008141c1d009001520501e44d2000b0104061001c1c1c01c991081403402e944265059850a80010308000000500d500c540903844407450a1450340a5004064070009108444583c0140030014007503240318502c00d115031043c14005000c1d81070000040000e01c0c2061910100100c1441c20720041d110601440242c030003031140406e00c0705150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 851603848 1250 851602598 851602601
    0x130b040609020315190c140304051906020c070506030411150f070515130b0c070204110301150806060310050d0501150f0f0504150b0c0a05061620120d 66
    0x800c042e4041c060041c1c1d814402400b030350311350310421100085201a003002d00c0700d642141e0941580401255040443c800c0001c0d0b428042c5038030900c52401c455440b40c0710182d640141e40090700c201d510540106459601c0b035020300910002d09400e49405080d07140548440cad9074421300508240c0515058641d1440300045807049841c001700210540350b8888413440d00550354040d4038040c08601016002041c460614141203070480c83d04140c08480c0f5071203010051115502400c1d040b41d010341e980701014a49035042c0003650081405003840d0000101040011700030507401080701d44603510800800040a0080219406a0300295104100c80c1120720b0201c0c010b00d104403403001e90759004e40300018030510000d400d1b400c2d10200700d08020070b03e82c0c4600b4001034034441440040c0038070004605001030403c40c405010030300b01c487c08990959140b46c480034142031040d0703000012181103030200010150404840c12000e400003404281c038041d42c0401503210740c80c000207103003004400940c0030b20702c0d20315 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 851605098 1250 851603848 851603861
    0x406051003050115031103060f1609121202010f1b0f030f0614150310091107060e160e01030b0115110615040608010216080f0f13031a130b0406 63
    0x30100030000d1304110604414040010f100850384014840020456410301080f06802402d510171145501c4d1144031085e101507002415200030848a40c0340021290039001c95180014040c10b140300954a17540b40003404e58154220f4901030030300b44120050141c0303004403110b40b009160715010759000d01829040b03010303020b10245007607072a0500c08082141c500032040003244d0780048030b9240c910416040f03d8890f500003100c0312064005030010812540c065900300003040306e401c1d501c0915042071540e45030115201d10489044640c804031460f5000700750a125480500030940c80031140c0d6145513500b600856050040000394401445c0c081106400703032141e024096558400e480c154900749120b000701d1201c8801c0309100d9030a200300018959010b100700d900c003007191500c1c1005402507865034001684402110035401004000100e502c45859010300f580302c1c410188a80a00c0c44d5080900c0d43d402c2c018100e825003030003279003842030601d90400e9510000381e0044484505a0b45c0341440c3c0c004008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 851606348 1250 851605098 851605103
    0x40f02061c050a020a030e12030112020a03081809010b070215090d0c0909031e0f0804150c020106030c060509030601090f060504020301030506061009120221030a020a05010606050a080406051003 85
    0x1442e040c84116079098003d0006042560740c03c02c400d003041000583d560007201d038a1814400108018441314034112542c0350034900280600b03001c0c990700c0c0d981e50181e03404104d01860803101002c01030294035241410900508440030b0050400890340c0024828403d84445081c25000000e1041d1a030b4070b408900111483d080140e04112580e10f05c01c90b8068081444110000340c0c140c100440a0008440075120004495943e4403100c0183d03401554010130150094545050100110422100500801203400426030000c1801031a52604111050300b58000000b807010030310000740c068030009038250441381080004164030403e07008503401011990096908180000008070a0010005000b4050311042c0c0715000c088000c400200d03901ca500d0b004200048440f00c1491002d4500301ea61000f440408a1008a048120304405491603101e00d0032900540c01124621050060a1058400502090a0407454003070300e0100105010700003040104410764400104289208000d101070145a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 851607598 1250 851606348 851606351
    0x60a0503150a170c010915080414100c08090d0509060d06030b041112070501050901030c020309090411010f021902060706180606050a0929030a1205041805040f02061c 73
    0x76182c5400700e000c000101e00c3c4003080d20a101c90b00f520780d4460450141168100340c980c01070100c0a110866200384050400d0741c1100400e40800d40c0d1060074092110311050003100040c1010b069900540903601c0104054100d82201104811417a00002113400b00c10003110b00a6403154141050001401c180d000a09119880401c110401064402d0010304c104111a944e207944039500313441c0e644400d94080c0a00140c402d00180c5550b5001fa0808a90b04025006890418070000082401541d048400380c4a50304600004421560012101e00c0025410f02c0076098082a11091a114282149000340946000140103051282e170703501120381c894a40e026440c080c0800d04065024040c070703010f5141306414410300000d0740d540c036200300f007420103001031f0070f5030307008050076607105110801c0c02599050b01542c02004000352984240c4082c1e032200e5120b09444a0410803c1220016007494042d0810b00c0d020074080403402e01400f966074258110b0f59a650b84c10200011840c1c004191041d0705410b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 851608848 1250 851607598 851607619
    0x301030b1f0605091516060b0d0609150e0a03300e0d11030909041502040e0906041208190c050d06081f0902010815010c081602010f0e060a050315 64
    0x180d070b00400030000902d08440b6021641a00003019500744240b500000203468400c0c1c001b00081c0c4260401e04154500400d250300c8000705484945c251085a8000c460790400c80c40d6285150703100384503440c100042c8c800240040c0040740d4000d414942140c94034003040e844070006d031040d420710700181e62126250207414042c00c00c00740d8038540d662424940348804145d041c45402180980041a18064040104110300c0d030340b00d40c0c0768110895079881c12542119002c000100d031504a112016000341405030080040740b45c071f400c1006507504007043c071101700140401400f11407030000142c0a880e4240c48400107018001020680d01807103031015444100781461000940303004c012901003010f0003484100002c4030a80100001100c1c2c0018001703010820742000300702c0096a01119140e825818103010020001d541c0310a0050303000200703400710010615542d0004c40d64042da01c104251910b0a1124030344a44c2800074030240112000d0504005000c000500401d000c0301948031784007009813401d0642c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 851610098 1250 851608848 851608859
    0xa020f0a0c15090516060305091216022d040207031d03150709030c08070e010303050a0215180c040e0606010c06200403050d05040302030714033c0f030301030b1f 71
    0x116050b29034200c1d116a11710400207842402401000d100b140518080c09101040200c005d419400c441c86e26080803a00c00d5856006840b0b4101450044100404a003440d40c00404081240143d80c4a814007441c0140704600001e5046289290443c0b100e82d584000c80c80150082031a10602014402d0155640000e100b25680c10034008410340c1c0c000da0303000e55010340300c442469460003e8403840c09412144030041011901c6003001d030240c6002413064030500046900c1414008506448803aa00030704000e100280d00010480c00c003680d08150b900303010307040c00f0442c042e880e51030060155040c054207038101d600b08841680101104e000060407561141d01503086c55010390030a000c01c0b01e6a01c100d4260402481c0210f00340c5044a500500606425040c07900036000c9014068800b90148100240d5108202002d41c40d1540c82c07040382c44a00d942c20114031006040d50055803600b8258100150180b202070010040301d0540740c0120803d1403030380b0384100000b217600e404080c0190034005c049000c9903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 851611348 1250 851610098 851610103
    0x110d03030b210c120c120a05030408011a010e010215220b040c0e251707120b01031107020d2405010303020c093702070b01030b0a020f0a0c150905 64
    0x40007000401210b020f000007030309001a07003080e210089000c1e030201c80c445800d0b01d042c1b02841d001007001c000f0381c1c40300d6507039a5605240d03800c02d4002d400d40341d4552844402d150540000940050801d1801e80710540e240070000c0e407121010300004101c442040002100220516a0580c03444031100d41c5290314074090401307014155094030101d440b0f0b01d458800040c084085060b1a00a8615029036540d4a66a170341704490f104880020314184440b40905403d10324031000b89038400c8205403a030b03030f400d180e4030740a0108a4007034608560603d482c03d0b015a40f451100d10a0300c02056043d10300782c080c1e1405042a91054241c1290f030f00d0710191641c40141031050740d400180c101c9220307400700c4001c18011420000c0e0030000701c031040c0341d0800e070503e01ea0044042d0007810102200402c036203129104004210130690344903d00682d440d00d40ca00c010004c0104402d42190301c07a502400c00c50410125003001100c5100b0004544108103617592140248090090b10f0400e000b1004010802c3c00241e103411034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 851612598 1250 851611348 851611399
    0x1e0e15060f0f120a02070201050f03060307050a0303050903010518071e0b04031506091e0906061509060801080d02190c09150524030a110d060e22110d03030b 69
    0x800ca04441c0b01040f00320b2498005c4d036000700d47c141c45007070038140a4400b658043c0c00003880550b00d4401c00c040081c00c0e4444030030500c040c40c00b07a0383e2603546200c19001e160956102510b44420241c0300d4800b180402e001060301410b9510380c1205072a0104041109401c080b003076005104103100000c0d000007080300d040000c60142003104028803e10395205905c41c115070048440c0004521a06003200c012a042d0b400b0000386445800f00103002071310380518902d40c0a5103000700c408641c40c0311003030140e40e421108039801040d03154002c0c4003503590a10700944410001c40c07000d22480861030004108054980400060140d417201080309500100391000c0907400c500c5282c0c0203910402900f2400d040303240c0c03107001c000c9424841c180b031a1035100848009044d4200641001901070040c03c100880500505004100c0042c0c3c424103030411150608811045456144214030342c0c402c1c01d000640c21481e002e840040842d0340700c042d28660309042d00682860200c1d240d100d00701422820700384c820412101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 851613848 1250 851612598 851612617
    0x30312090d140301050d0204091509060c180f092705011b0f0c11040902060f0d3e0409020a0908060a0e100209120f071e0e15060f0f 58
    0x400203254180d00702d010340d110a0086940107105041c2c03000260030035400501e90305124145a1105100c1c0f00040d60850b181c0080864645846038400300050303078060301135000181080840a541850a840341000b99182e100d901292a02c6505040d4203d23083c1103100c0181865220854920b982480d029000341021482c01d07108100941d0440f80c054400d21000d05850307444c0c0c0700d2109039413864845014004032a200598015115544400140c9404002d4024043c0c00f03103405841d988a6180c031001c0d190305a401070a00c00c4244072019411070f84900940c02c229002040d4500d50300c21002c1490b041c030960700300030070242c00010341000907980a4403010031240c0c81c8060b104244c071180c1c203180603104400044180c9510480c0d9080d164003041c0d0050042c01c1009140000880102072240e0400034074244082564011180401c0000010001e1036500314003646544040d9007403a1800c080e1400107441c010500d142441f1071070098891400b01c40396084007044d500d0b101d10120000c18959805102070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 851615098 1250 851613848 851613857
    0x9050d0218090a0516061b05010e0d05072003060c0313080406020a05010f0b030709050a060e010e010611010b01080f04020a0b1308010e010e031c02090901180c0804051b030312090d 79
    0x81c401c0081c5000090050306c800f541c42809032092034a410916001500c005c0e41c603075680d80088603d40130b040014405440080d105c894484105003841c44e80b8212109039000c800c1c204510319407280d0380c046005a80300a40245c042d440e0303100e00903044812160b02100800050f400140070503003d40018000440d24031413002070124040000036541590030030000250180d002c00b03014481c000d1150491580500402e01c002003090303450103039802d9000e00380d03c04919140d400d0014800c6950020160090050700ca00a010940304000001c0850f0001010450310703010740004602199100c956400003007601c145400e8582111030741241820036207101d02c0f4403a601e010103120380c1c00c0c4e040c05034610804100d80030b14100300042540040480318060030442c000d0b1b0801420f40165134032151305002e840704060280352020064002c10460b009502a0001c0c40080c0c001c00002800004039030407040c1c90140d4806005160f10301180c558003400300440e408544020800c20301c1e14000030384001c1900513584 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 851616348 1250 851615098 851615113
    0xc08030d27020307121403030109060f08030304030804020f011b030e010216080a060209190f030201142b0e07120b07090b1204030504050303360109050d0218090a05 72
    0x1c0c901034030080180007501a08003020810803065010f0f000107140c0d00800c213020305984210712590455109800081d0680c3ea01c44007070250b04a500c444002410008000f50701e18145500d01400b41c2400602c028810740701d162117540c10340d100301c00d1341c0000e2141142c9042075041030b241c090b10a40300075a11500512a22218200111003900c0c681e007250b00d00c102900304141c142c4c03107180182d0311120b912904842124030384c00024200402e81c03002000d141a8828059042d440010590000f4102007031448c1010300210401a0210886035042c3c51064030302c4000380844a040e002400e03501c80e90b03180502038000002840c01e00d1030f043c040c811b4400c8040d840325686800003a2050707480d0b80540c03405e400301400800c1440300710455042d0007502a0030214105651180001e1950307214000110504152000f90200d1441c0b204030341d210551171a040a861000a80c002401c0b024188581d03403048010f14002c5080d5101c00788100c40c8828014040039040c605024102c2d519606c04030200c41c070b44105e40303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 851617598 1250 851616348 851616401
    0x11010b0d030e040f0e06010b04090f0c0e040507031d060a050c07231c110d030c140f09120303091207030e0910080304090e150c04060503040c08030d 65
    0x80e10044166058a40385180200324041c80014640e0403481682c842c1d07110b012101449041182c0c900070842c00320340a595034280480e40c0184d50341c50950f00c00d480d05040c91170075215006030b40c0b004070010641c1c00203243e0b9260790703007103016104a44a03190304800d13490f15174110000100312540300d605441800c1c0315684441c0d8400307456200d0018050305003101c1c00c40c0c1e840390729a80c180010784140014115244a031090a01c1900b0503003440392000400c0060501c41d011003014001240740700c0031418104540032001202610f519001c111680b0300500008080d110b101082c0281c070021580500110b01280052100340e40d41c3e0700c2620845010f00c41c41108600f1400240111450564141c0d1400746d40c480400070710560300d902905030030744d840310140c001c511190b040019200400301c1c180040340190741c4410442c10080ca0401e4002450341000411001407a14411102290410b00e03100e903803503a4a04141406070b80da500041654080050130000002084d00a09050240907652410b00f40811 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 851618705 1107 851617598 851617609
    0x30b070906021504081c0204080d0509030622110616111005030903030708040206070b010608010315020a090e1905040f05010e120d0b13050711010b 65
    0x800020003203180c0c100410b403820041800303c48464141622402c40600c51241c24400820003000c018840181c40c0c1d040340c0043c20a00143d07080001e44c03250040090f0300c0103040520034400e00300404c40f9040210004042e16401c0600b020840355981d4030104034035180d0022541c450000d0000140d00102e03960005852072258400440d1254000c040084140e0a520100d04000b400d00801244c158004100d0b9003044031400c0030001c80c0e03954400540d40c0e100751203008048140e03540c00055016000350416050380e108220410b940072211110908034000c0b130f40c1d000d00041804604026411008001c01d80000810031541014040c5405003001d03100191000c640f84010020604140b240c00e00c03034400c3c0c10030180003806503075011401007000e40c01020b2018200e1550740342859442da03905441401385032445c160502482c984141c000d840320030807a02080702e550038000c00940c9807600 = true := by decide +kernel

theorem cover : BRFrame.Cov 851438848 851618705 := by
  have h0 := BRFrame.cov_init 851438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 851438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 851438848 ≤ n) (h2 : n < 851618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
