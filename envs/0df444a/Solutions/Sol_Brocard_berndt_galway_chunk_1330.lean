-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1330
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:24:43.441249+00:00
-- url     : https://prove2.me/submissions/59f22677-cc6a-4140-be03-ddaab8c19c14

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 239028776 ≤ n < 239208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 239030026 1250 239028776 239028809
    0x170a090f0801091109040f08031302060d05090606100203091c080f0901022803051c111903151413020309010b011b050601170c0a08010c080f0c030103060203040606 72
    0x7600800811004035448498084442c50f00d16060301c455200329800300c11a500c001c0242d49100e915000509940c4550003548881e10041c2d4802010300210801c2e0080018186000f034491031500718003814950003240c2e0301d2012031030290b010003100c40030402903030b4030203802034005441103c0c0c00400002601c503101c0860303038a41c000703080743c028843c490099080700e008030542c00901038052814805024444084030f40d00000a005901802e1450780904804240c0003464404100f40d4080d00349066800a00081e12552544081000d00c0000b80a1070304100d500d8603a0102c0050010314014201c1a0100c1000c03100d2998803414045044000121300790344a00f00748410754040e081c1c5000c3c1502185044901d607108249204441049a07004070050513a41d180201224900461300c0b0340c41454064504030400944800855800501c4220000036030b65a003110b0044c07200d94080c10381080902100107220303203000d00c50706880c196078211400517501c0c0c42c0d5181c044024104c1340d00c109000301180c0c50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 239031276 1250 239030026 239030039
    0xf1106160c0608010b040602060720030d0e0106060c05030d02090f030d11070b0304030f0c05010213030807020a0e0f0c0f07020d03110106140105070320031c0c020307170a090f 77
    0x10740000c480c2a92038600160b600d606111300719010300d02500c0700580c01a00054001c030311644158980c2c1d0407014604480c0504005c041d42180c0c0700c814040c46642c1c1b00d00d446802c1c61750034443c0400401c49450014890005941c59075100d100d008002182c580d004644a4011f6070307010103003105807000034111000c0c0701c2040c2d0094860fa242105c400c0d030724000ca0500240c5101c680044038403682d07040d0f6034001d400130070220030307141404441400e0b2410b640c2030161807003071180900350344080c500842029440d903c951041003194125500001030b0a412082808003030942aa00f051700710403224050303a1581108040c224441c00f40200196000c8400c1c0c20020500d500884001240a000c400a02c082c0317441d482d0302d001c081c1d541c480075130004104001500200e4410f208910201911403807a0f00c0f11340d100c2d000c951035500514002000084500c15a0300488641c1c811007100342e1560020f1401c260142e19a501c400300300c4495005d0320f01c0001100c1f001c1c140b082e11100d0183c400b02200740440f40d2140d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 239032526 1250 239031276 239031293
    0x105031e16020712030905092a040503010e030405030601050d110607030f11010501032301020d050a061706060303160809090109023402010c080d090602250f110616 72
    0x41d0440054000c5070720115045808480041140d0b406481d110303101450702d0144103144000602c1c05501d01d01d00390307217a4020104890034071070400040c503d06480e98100801c02d421074440401002503640100000c1149403004190903044a02c1190184418000383c10036410768428040340c08d9001c000012202c04050304100c1511101d40c2d66038444621182d102c026500f00c0f00203010140a2007008408003402001403051840d514680c54009820215843c0e83c1c0401d5a406035206000f46440f07950030310035034090060240720707151108000d143c075080910100c0e840e4482c20240c1c00200014010b8001440b0104040380c1d2140030140036402150303500c504a47c0290000342c00d60035464201c0300c115040c14014100640320340c0e0300014600b00b203c025401950300c00107640c0c01b15854001800024500341103441608555030240301d0141c1e0f01e180b142850360045484510302110030b821038001402140300311401044081c1d01500c00c1c50101101c0380090001e00660901e82256803a00a0b858200311921 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 239033776 1250 239032526 239032561
    0x807050d0608072c0c0f1209240106081b0702060c060103060e0d0e0402031806012d1224060306020c0601120b040f06060e090d1106150105031e 63
    0x2032481c0810380f02e00c9022298806500413280082d5202c2ca0b01003011144440014404c000c041411646081d024101e0707820781c1c800455407075009802400140c0440600c00341c500d140e000201c00c98200c1903040400182010002900300e050542c4c214400712014076185c2c0464114540007854241c03122054650300d0b80d101c82c240001c507411801c003c42c02c81c0306100000d50451420454071007a0310816240140f01c0290401040100c0176480300300b445034103031800d000e403e010300038501d0b141b60080c017880c0b013854540d81140064080f10490345c000b000f110148610307860000d035201c2c0014540140442000201030031a800351030001e442c1007400403c01c002c0c0d60092010700f0701203080c0c4040381e0381c9807542450b00b282114060000d060100000d400948000e540c42c100b54459440041da164550750200e000900c105c1c2c07500c061340c0c0070842e825600707034000300c01c03644201c4014018403240c03518400501d00800f81002c0759051040100100340d00f00440c501e4030a03481c114044080c1c00f0300d001c10882a00d00d210 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 239035026 1250 239033776 239033789
    0x106020f21041d090d030e10051e070507060506030312010308090312040603090512070f080706060e0c07020102010e060403050a11030c0105040807020108010b0702010e0d060e120405040e1501060807050d060807 92
    0x2403142c4498024045e00651200340300303d01c043c0502c2c000303c0c50080080c0c88020b001010502440500c140358000c89040e42d80610a41d40d51a520de0402e0f00d400d408803080941000d1080d8000d01c8101550038841042e40d0540e54409041c03600c8002100103e407600c0075410115480342e90100e00803801c280c0c164000d019445c000c0044400034a2103c4d100c5400c0d10031650090720203503508a07500007003800741004141c090700c100800201d03e550303000b644111000c02e031040c26001c00005848415076030b0900458569025481c050800c03420165000741c854410903030320074203000759506400e140603801c1c401d0364081072414000348000d18003460406520307031040d0307c2207000c20180b4001083c02c02c20581610085541a10b818060301554010081c0001040004450701783e201c0d0990001c1c0d510a10810f8422680c000d0801e490b00c3c14101000180c0e43e00e084104ce16a202036071040b192142d8401e50f070704442c41814200300c1510b540c1003ca51510684650107025810003100041031035002a9032000c0700c0e203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 239036276 1250 239035026 239035033
    0x1c03080907090623010908010e1b0306090c040b04090b010b04050406150203160c08010c0c020a0503030703050306040b0102070509040c1d04030e19090e0f01050106020f21041d09 78
    0x8407a5002070460f2100e0003618010070780000f11141514103c1001e0207030802c14180303d81441d94640b415400c4d503030703408004041a0088488200381030f54148110107104030440181106240c00090241d4904400180d03034811926070340e1200c0300d41ca85034002c039009600402c000d00150303103803c45003091381e1003445220300840c5018400075003c22841021480c140b405e501452030300301000401c545094032500b066030035009d80d40c000580301e04240714596443d589525400c42c502c14500400204240a41c8504c0c040c0d0020400d010000354024112a444001203c0014a910300d40e40105d140410603040755401200c400e0600003405030b00d42d40c580403541d40c1009081c140c04122400703034105a090364020041450829001d1561520340b1052000c03075180c0e030414034070558480c80e58050b40c0b400b010241007600800365102c4840e1082c052903000d403031306000901c881409000040d0342c43d100b011352520740056200001310300010b000102d030020040c105c2400f540684c100e8a0340010314060303e16050621 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 239037526 1250 239036276 239036279
    0x30603110414010b0307031b030b0a0611072105060708180a080301290d09060506060a0c02061e0a030b011805012106050d111c020d0201030b1c03080907 67
    0x15007401010b00012404403114640d91800b000300d9100d400140009050541340e20710707108500100203582580c2d241a60b0040790420324882802500025a007020341005440103615011a82c0040e008003217942a54450422a56000002402214052005029009040c1802142075000ca4030303034003910842c00341d082045840c0203501e9030b580306800300a100321014401080038452100644078048811001d0b10743d00103581145070001e501c40f890300d00121307030f5642a00b0140049445803d510140640d11a846c00300e08500280039100c1ea41e200a02c1181e0010301207014541c2e1920620702c0c003090700300064481c84000c4024020700100b280c07490000c3c80d0b480c200090818080d494004848041c0c482c2071307006401c0c4d5400d0000c0c01b10020700c03000c4103440303000024103512580c07074251303105004006a40c3d007040c0080070008400e90706c1121800e100404040c01700903079a400c11050740e0a40c24240015506002000300d450020b07040356510140e48200100c0040c95000445c803817041c2501d9055641c484d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 239038776 1250 239037526 239037529
    0x2010c08100e01090f0b100503190209030a08072d060b01050306100807020c0901032108041a040c1d060a06031104151107080d030b120d0c17040603060311 68
    0x207072040c0700d602a4421040010420024280d11103005c0301000c101c00301d110340ca01c20101c2d900303100c652000c00c0043e03000000c111120740c0c1c010103542d00051181040d0326114592000a50751401c088028014490001d81481000201c03081020a0b4200c105e2075102040052499042040100d5090740c60b5410100c51901c10342c81402120311070113006245548207100001d0449111030f00400e1241540f04100340000d40781e89007280a402944100c404880050b0403440c1c2d48014200141090180f0500c0c0c02480300007a941044034800741c403100200c10300f940c0e0300c2c02c00000840d0a03038071050030501a103a002e40505040707117055202d0402030780c1d4242340e190b42d00c03001c4044442c1001c43d405031482c2480288039007080d04400350210440c924040740c07251000e203021402d100c80b691016686601032440c0070303405500f500034040c00340802c49030310f070008041247c03441e01e074850b4245030000c020581c044034003008111450010368064444005441d40d49414028009240d0f40c00181c0e0241180103a06149 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 239040026 1250 239038776 239038801
    0x807081b12102d0e1905070605072102030c12030114041e0507020303070306060f05030c0a11240a020c0d0c0611191101090b2403010c02010c08 63
    0x41029040040403068502da2800d4010b081c04400ca0004045943c05400302c00080c03000c400c101000c1d6180003d5422a07038015528100041201034041140c82642101051010070b40d60121030483c20b0240e500e03000da2400300c4070614400c883e60300d50f0049003c5841041d40c00409406c5180d6036204542142c150b04000c011180801d01c40c1620240351410f0b03203038081c1000d40001c0d80d240d00c0980c07017002d00c41c003007610541960703421150b02005900110410003c65418002e020042269092400c25001e038100700408074400104100d5032a00c2c0020501c54140c071031040303000c01d61031101c10f50307400400010402c1310751035101c5104c0c2d00722103108021600304900b5208407400300034000020050710f44800d5054454070100003054480390340d0b8601e400720014a036402840000d00380f80d002c05403a1800701000d0020312200a0440d62603152805410001d44003964050b00500a02002a00d40407410140b102007600c070301d0f4103034145d401c2c40f02044e890340e0150001400304001d03031602c0441c1e5035000b4803101c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 239041276 1250 239040026 239040049
    0x60e040c1e050c0118030e130504020114090d050a0506010f0b032a04031407150305090601030605060d150b090612030403021003020d0903110606040e15100807081b 72
    0x84403410a5080c85601070b2009240c0010b107140085004c20740010315404805036084140c0104000b2640d04919240c0300c40e03d10350115021004205030f04054000800203e1745894040390780100140408596540c05003214850358000215082d04506140181c0c44a01c2803180110711407120a01003408290b42e800d0768440c0014120344004641e9443c0404807019100300242c0710351070f0400c804408598412509000124141c0c0204059880c000b01003108005c1921980d0030103240c002400b2540001141e8541140c2c0c010201044648441e000910740c1740c4040b40080103040c0380702e0001030542242d04498080401211290a03942d01d000a00000c1c2c60222600c0350640c100b00320030b00040c0703014150700030019000d150060500d0803110300c032021a64820003d90116841c1800303d103420400f0400140d0040003600d040c88401d240101c0290380d40149501c41700c1482d130700740016030100e40c80d00118004024080442c0d07030265507081182e444000c000c05140b9260380b1070044c1200d80c18910403080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 239042526 1250 239041276 239041307
    0x150203090c0a05011d0d060b0306070309050c100e0f0103020c03070303050117070e07030f090f0f020f01050c03070b0901090b070807110a03081305010b150d060906060c121701060e040c 81
    0x80c078280c800313810400406c0c04100110b80f85603903400d100040384c1701044110310482d05900c4c0080c0c80342d218101289410f001ca101c9610500503240040c0c0890780c00981c464441c881940d60086c0c5410090069000c0d003d883caa800540c4000304080c2c040c983c2c1904168103e8203118440300f052541030081702e0322400c1d640151000c2c90810004150780c00e05c02c3d031000107101c807008000144854203980d02d600ca41d0008000703481d42804101c8400035031402250603c001902404c00d06c0c030b40005110302e0303512402890b1000c0c10464041d400a04a11020b4101c0c1c00c41d0341e03000d81c0d01ca900703141c02030010b00200000e848000018034200d150680013580041c1e130625050300350701c40c41a103681d0b83e0968510390314048001c0740d5a5485050400880d120714459035a05d00d00c002d0700b20340300c00c0c4a01c4040211000d07079001d406c010742401da0810030345401c03440a8465541100c0d4000fa80444141c0c191808501500c40c6064014601d000081403503020050496107441142c0500120200c404111640c440085008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 239043776 1250 239042526 239042567
    0x110d020702120d1b05240f0a200a0504050d2d05060126120307030e010204030b0a021308070909060e010b0f011b0512070c21030804150203090c0a0501 66
    0x80000c46200e00700706404d24800d00c201c2c3c11140a844083e92907500b244841064450303403400340491110080c5185034016034403407003048410005035803440c86503122880c194859400003941040d4034881c03800c0350013031300700581389041200c0a13160102e801900f20010345030a0208144040070210980780d0b54950540140007881240d0030040d1840100c0d009505a500034603841880c1146a0801c3c04201c2907811140707402902ca01e414900502640c8030002ea4a40c580d01c100014000541e1010070b01d9003080d140400103071140c8140e458084030907142c0c4c10200340c80c4980d480005201c2c125402200000784100001d00070305900000460aa41030015850b41c0500400100329a951142040b0984120f40100d259040740b180c1d15114100030041c0e00320000d0b4200020a00c062010401d03000005240341003400d41050a20b29034070b00c4c84c0300541002002c010660021900b8881d00c04682298442c99240071996410003000f4256a030700d140c80994050406038400042c01d60184586819088000307110 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 239045026 1250 239043776 239043797
    0x7051303150608060907030308090a0b0c0d0209060d1a0402090904061e0e07052103030c09011814040509070501020304120804030f0302070f0b1303030f03110d020702120d 75
    0x380140c80c0300e002076208415075100b80019005100300070260103462000003409000d811410700034071a6100520100480d8031552444000a107440d0816074084407403102d6546131810030260001078442d03070007030a600c400e02003004035041c907465000da69081c400c2080310b1064641641440300703a01460070003507400300d0301f100001c001c209560040608503000400400401800020a0040b81d00410a0981c41d500985082c0518100315003240c44101c16101035034500010501416070b40e201c0181490408000402c081840d130f40241c0182c905d002012091856541c7c46001014601e605100554419030801d0049007680c42c020441e070050320b5040e8055894503061080d009800700000c5c4045492080410000010490345811100740c1340c401d90140404038940902e06080c121181c014120b1060100604610013003c2290039003280d502d070a2500002a0b4514281c1c028085514222400b02c0700058041e1414510b80c000c000080c8219144602c22050940c01d69650a15490000106034000fa1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 239046276 1250 239045026 239045033
    0x60c0201030923030a09050f062208101e0908030a090807020402030702060115080f070c030c060e0d0f08091e030f0c0c090703050402010e101815020607051303 70
    0x2c40c04085020f0044162844007100e02d8042d0607940d10554403260300085840181250300540d803500401044682524030001000002c40910407180004222100351400c4034800d610221410020601101500c0310b0284001c0400017030010341901c21080c01c8009294074140403684101c2015580040c8840c1c25992407407031800040c4019034094903004403d000303040040e5114002184128156405005203514114500da480c1d0801410a01800081e00810032110074615049601c0012450709216803001810182d030f04080317161019100b039060002e03482c0703040000240074051402642d00c07014480300d400d50480d00d0300016102e5000d02d4204605241d80007282c140c0a07d01030580340240d038980550909080b0080d8001c040380215038201d40380206031072500c40b522076805034007400e081c04240340c69030000f46019201c481c080d20070403003454482002ca100380d0ba481003410360700042595064641c0c41c4081500e092009030270051280030000b031311840c0b0690549a4145040c400110560304598 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 239047526 1250 239046276 239046281
    0x2306041e0c06050a02011107060b101e080406110711031c0206010e060f030f06070311070201021e07080a0305120c0a08010b07020411030c071a070e04050a0e0307051b0307060c020103 80
    0x914410856403a0384a154034403051f0801030a0f2203205644c0014000320040178031941c5441c91151106008140a080c000d50030030950440d02000e46160982ea0b6594524009005000fa152920350915000c80c000741005070300600c641d0040c00843c02ca40c004850302211801c0803d000c100c0d4001a004200100101e804642c10182c111500400082d5148041c20229280060f4130005480d01d601070740520035110b170140300308801c0500840501345048001d1300003079a903c000a5090092404015050086000521020014110080540c0c4103d42c080c240101260007500002c40003907191000308012801d42c0f000c446040c5515160301e02c15070b01c0c05066502580041c00213907001602d481801400c818003400551141003407504c0c00e61218494248080d0800c00003202320342130034609040c04400b0780c00184009202c14101c0d00807c26544280444000d8411070070303d40050301c40820000700704000481c0e058a82010710b082000f5111300c0104040e076509007071098a001c5144070144401551007034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 239048776 1250 239047526 239047537
    0xa0501062711120403080106030b041109090a0b190305120c0706230a090305011b0503180a1709130504150914100e0c0103060b12042306041e0c0605 65
    0x2c9882608001c84501c00001494086904400054410b801403140c1d07900752044415000b000d6030f04101d10000855203c461f803103070803101c03803081c95410001804800c1540000300c0c1510041c040310790000580306020b1619206000484090155070040c440c1070000a003500c688150040c01084404d2400005a441e41d981040440419002c100161314070081c100080c00540c0d11940c601e0300c00c5245040183c2160946d04a00b080b482003121864451944801545e800240c0508206014044402624503119a503203005000001c0342c03c0c1e289040381d000c0003a060a5101341e4550003032100350414072040b90f000712030040181c040301c0e00240ba501a40e6000c00100344c82400d0020400711300d1581d45161131a500e6950b11855290750710441100002c0c06100c3c8214000e00703041c010f40c0c0c2418014201800744a0326040160078480000d420300c0503113502c8240703100c10b042e400205000d140c403100d038660f901110141c50020030040124548101100c4554400760000c401d04032050404408071021307800b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 239050026 1250 239048776 239048801
    0x50c070b160f29190e0c090903030601030b030706020a030c020f19320d260306030c010903020612060118091b030e030a03020904090b090a05010627 65
    0x8000201000811040001012500400e9919a00f10751190a929103418510003038440440f04030078000b48980c691103d01c02c4e0708240070003084101356610800e151180d907030007640d4005403501c1071001210020004600646007a42d003806000c45031010f060b5104601c0c0304410043c1d0080f5002d2010030b203e604003041481c0b0040c40c8011032500e000014400302c1101441001c5a9a4a18100100c100c210388041030031525140f204401d907180e140b90610480c504543d00d0094031400410320410070010300801079407a04c00306240503403040b031a0010340e5400440710f86005c3d00c00c00d00c03078001d02e60181e000181102d03401044580703400f14001184400c410080c0245040c081841092106080d0042c003403000741c112000c00085201202c0c104051213010786400c2c20903d4507110040140c0b18000c000c0392080c0c0402e080140c2e0720b04012000c0380040c01c04441c040c000320b000c6401c0c80414640440c07102c2da01801000240324080d143c20050708641455050381c810501e04030310400001c11349030001c41d0344018 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 239051276 1250 239050026 239050057
    0x10140a0513030525080307080a15050f0910080312090706030908030c090a150302070501230c0c0705030303010f0611061005120f03030406020901140906040e060d060c02010c030c050c070b 82
    0x1403030703503e1205c40d030000d444040208100004020344020107208444159079400d58441e652881c02011600c0c000e50809010b0050101d40700007600742518500c26030003012107c08072507640b19514020008008142c520900350b00440c07400042c650311a000b0f0800094000c02100d1840e104c052000070142c0c042132420390480c84c90003001402d401401c41d1b00011401719100940d0f211928600103084881407040754800703040d034240c0000070061409090350700c146401c009550b41c41c2407940842c82c0604982c410741d4548000000800d040c00800034400c1200c00388d8440809000a01c4c158944501c801ca41400101c20305500c104814035006050011401c200c10079101e06801c645149421544100c4058868580000300191503580c02104500002c04088505040c01d9035840050310a210300d01c0b5950441c590000803c080350340d500e04052020344d00034800c004280020078060f0181102400f1403000c6440d0081011045000328200c030442c209100c068684281090504660f0703800c0380040090090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 239052526 1250 239051276 239051347
    0x14041a030a0b090702100f05090705040c1806050406080a020a021b0105040b040306060807050306070c0809010e18070206060402040609120f140705040605120307060c0210140a05130305 81
    0x40350b451115002d01071170740c06442802444036161082c4c4d00f1440c5110361030b0780742100b041241000856040180c030800c441c0490042101d42d030844400003100c0b000c540d0814580400103850341c10070000d10440d4100c0d1606207140d5180310105049000340b109080158208944050b000704442aa00d8030310081410030320300306911064503040c0c640207a00100e40950780c030582400300010420840004120443c02000c880c504113400601c407040e020b00041c40180c002c01c1940390b0384e02030005080510b80241145da0012602908085660b206450a0003d40180c8001c20264101802160709644a0b510b07685025480d014900c80b19112900090b02c110f20311322014070029100d201c2481c40320701c0c000300604640e4100307020401120070079840113200c0e90185402001e041d001100360356800760480c81c00030380c407148100140d042c01d00b40f01090791024075280074217440b500507000640c020846440100015515100582c1049801650150100d003040c88140201442403141c3d101c080da02880c2c0c1020311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 239053776 1250 239052526 239052529
    0xf09040212030f0c011802010f03111b060601030b04201c02160b070206151306090507121401030f0b0a060b070803011409040c050103020a03020906030703060614041a030a0b 76
    0x54100b0051980080c20004e84a50010b609000f03414400600c02c107150401280e550003e40002c1d100a101e0090580381c1c50803540400041c0c003a591010360003458101103641c800d01107a12404202c4070280030034504815407440e410544545801c245180124484001d84c2c2084100960400001c0f0b03444e84001e43c54841c80306501d0b00251080d0366491581c2141c2000620349581a400300a04078011035108404008034030742c7c00e4945201c45082a601c100050703a407103a511000d411160400030340300781042c0070b21415035844100c107500012100800c10504503500750104d2400d00138440540095480b29458001c0340720120119000360110800180c902c0d51026940781a810007102640c0302c0d1804030040003003640d440e170354095903241180c000301545003564a044509817a0700507030b41050780c0400c9003c02e5a001ea41140d40803000208002e490746803001e8010040e1003980600c40014941003102d0101c01500420385040d1020785d5000e849010006221000340e41006142c03076041030b12251900e01d40d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 239055026 1250 239053776 239053783
    0x60c07090615020f0c0a060c1a010303110c0a05090c0c1504060903122c010209040915060b0a0804061806141b0a02070e041a01060e030d0306050f09040212 68
    0x1c2050300d100240c0c0741582c00d0080d08111208076458203942209550700380941d02d0440350019640e041c10600011000c50070200d6a03000001441d254400c0c1c0a0008006c0c50381100562200304145c01c129407034140000180b04400c1c0c56071003240c0d041701048000c1000950a10080d00e00d030440d01c03080b506031420340d500c52808410306580964101d07a035000c1000506521900340444042e00410611166501c52640304101720701d01d5011201214030a5500070705082074040b03030480d12008000f48130744c00850406001007001c200c07912032410302c0c10000040000f07158040e80c682d03083d107880c0e00300f0030341c3c968460388048e24518101c0915100c1d08071040340001d2a6114626500400100d04401480c00492017a000d26030010700d504a01e00500000d065164005140c00685219130840444d03504c4520740f0000003145402044800c0c800380d800400c1d210762000c1c450041080072011039851898584040d0101d40c281d02a882d0080900200c1d2074650074000c03841a0400e02c003524201480c21092103aa04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 239056276 1250 239055026 239055029
    0x9120c0201120c020604120201110414040c0c031407052107021806101107080319031a09071d0a0f0608090d05090d030e03010f0f1b050306060c070906 66
    0x106441011980035540e004540541081015504101020021002030755651008000602c22801c40300d840e040c1900c01c0d0032000c50700c0c1c1c4542565841d16100d0059000c82e0540185c168041c03850141c0e40104244208520002c007501174440c140c42d580d4401010410b44e200c80000c0d5040d205e83c0c42c0306503040c22a174400c07201ca441c64580c3c4603201c2a25104016811843c005901800d40e001c100384072040d91a081c800c2c9a2000509140641440580e29941000925417004206020220b80c2c025a4440120003406000c61907a04006034012800440130916001102941110400f000100d50700d000d020810f0080003c000004000181c0c00c00103006861190044805002112410408541c110301000e82184901002e064060b2503008003c0c21801442502803043e0050814070060601440c032101c41844054020300c450515030440c003024200041d011810316107082f0706003c603044003030070750f032000060303560b4451854440404000654100306003582907402003000c00208006c05105440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 239057526 1250 239056276 239056313
    0xa1e080c0d090b0a05061c05030313020103091403040f0b03040510020a0215091b011d0108100305010203041a07020f060c0d020d061205160e0f1810051014061602030109 74
    0x3440d1b01c4d1030814440c81070071402000004801903000030f40007860202c2900e07403003225044102e078002e2103800100d016100100740984031070b054581017185001c010001f401a01c0c482c4100c65481d6654001081c02844100e401804907004000083c070000002c0d00200b071040c0035403045420f40703480c0f0354140d05902003e40707407009070341d101711801d00c0107075500c440419035201c09003401d2207103084402086120314041c120050400c07800e603000500006100620718081d5070000021500c0f0300e86071525582421482d40e2011990304154001801a0300c009120070607440308002822490f00c84480c1c43d600354008046c0401d002e030f005d02c80760304400d21500c40c0da8002c010b620810102c814440c146581004482c02c024031000054007000d02c00000c1001100e5082118446c40107215564a0801c100000142c94001c0460060810915000c030103500031501400407042a00c00c3c0e5030303454000603141400341c00b003141c0000c018800454000c00340c83c060841107002070000f00e001e00d103030303612880e182c2081d40155 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 239058776 1250 239057526 239057531
    0x607061b020a0c1208040506070201020307140a02010206060f1e031e07090b010c08040e190608010510051f030917030c1e03040807060903090314030a1e080c0d090b0a 73
    0x20300556000f000b00a003500030403000368030400c0d02c403000f180c4a1401124010500044d81c0c03011648204200c494554000d5101d402190b04400440d48031428840140d006100725130204515203020042e100c40303840c0050091510761102400b500c1d0515080c0095640740c0120000b90842a90314007003c10500c0c02d01011b48031050400c50107030200c5806e030807841d04224507040350100043c40d03074044a06503000c8417840c80d519074503600c100103141811082600e0050500307200060080301500f015025903000c0840307000480d1100188030551018840c08040061080b182e001fa203400703a40941d41c1240107446ca241401c0d440400140140e00680c5c0070300300b1440004800702c20106035080f0142e500b22000f000d45c40c0d400c1c16107402045019104010b0183d0350f485403120300301400342d0a0a00119400300900000c64100d12540351603420070110440030403480650503a501d61881c014034070034422503d41800fa0380b00c0f0542d00b0f0780360300500d600c00310003680d41d0f1811000c0384032100302c2d61041c00c003030101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 239060026 1250 239058776 239058793
    0x61e0806010b0304021011010207060f09120206101406120106020f0f0d050405100302090d14010b03010203160f21020a030c02061509090a020a080c040608070e060607061b02 76
    0x115454000c05911010081e1824000e1100590780c2c00c0c07005000190310702c0d00e41d01c07071004030031018028441e00704c008004624102180b40c1036403041e040510103d0182c84190705c22483e0f250144e031500002c4900d0100860f0748031041c0a400248208130304030f001c001c3c003024184500c41500d510022001c1e0410000b6030b000100c044040481007007036681442641c4081e14044600e4030015281303001c2c40c01441d102c1c102460000500c030784242d060b1800194000c0040128210f18101700c410b49007400031095955007841d8125603a410140201e0b809041e40c0b01c0111503030b15680d007046a51031400d040410030014401d42c600b00b40c000007032000341c80c4420507000590300c40c950507001c0d007242c008507504010364002d10200250300301d10821030190943c0c10f460400d665541d00c0240c3c0e0503c030f181c440c001d50102500c2c1c40428113940008003441c1000064604211194480001e03035903e0589200780b050b040c0301c400010f442410142e0113020702c184110340115141c0d03421405122111080c00040006a000185 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 239061276 1250 239060026 239060039
    0x17091f060509010b07200111031801020118020f06032d100f06050a081008031309060b030c0a0e04181a0106030c0e01051c0204060903122606010201061e 67
    0x19682c1c0140003450b0510b00d01040f643c5d484854021060f1b10803a00340c03184544a4450340240c641051451740d03601600d0781c2c2d600c810284001c0d07403641c81c00a401503281401c280c024640382401030380541e03001070105401e121540c040020315440144000d0032203042050f05004814030000c000d406400110800805203084503207594aa017065004500c102140c00b01041047e4004080b0390305d113100c03803503c40081e80c0c1d900302c0c40511480a900110035072000107007155030341c0e800b070012606840201806100d034580c0d460902c43c040c081a81d0705a4411010891407114502410400e0a101d20191003c6140e04a42440320100032100600351011500d01d80c28100e4645034108941c05000c4504042101c16105240200003e40b120180d6052040000c0c03103c0e4442c2c3ea800030781b108000710704000e540e1746440d500001d01030f014502c000c40e8071015000b000c0c180c040c020101103500320003842e0180301840f0b11645504d001c203070180525065550310400841c0c0031003203600100c041030001e10030f40d005624107030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 239062526 1250 239061276 239061289
    0x1030b0106080a05100302090612100e0c030f07061b0c0b0405011106070e01050708190201020a022b2006091608010608060711030f070c140d0317091f0605 68
    0x2042c480f0b485180c142000036a066034810340d415a44c0603507c903400c5170784290215103d2042801c074180a44619041503e180c0d11030741002302c20904e110240c0b440c06034800203141e0b40c0c491558107124183c02a2009204080c0310300000030f00c100c405241030b0144115501c0e0384402c440c07250014004c3c15000101400b07296080003004c031904140100601640c540040010035100b0004011810007400240460a00c5800c00c1034542074911041c20348034510748103174003034000d50000e48500054007440d1030112000c003003041a0741741c02e5043c80c0d10000fa0b0b0b01da110222441d2001c0b68403002944281010144004802c1003507600c140180300c000d20780c0d00f06003090609102919802195568100306090000383c0c80800d426411649600b00b50026039031000400742907008841303245c0b5008001180140074010400766140403910021810349620071018203001030b9051024014001c901c2070001900b440d1440d40943d0303400342880090b0f851400c1e03802c02d0788010002d00c4500c150b45546500003804545443e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 239063776 1250 239062526 239062531
    0x60b011e0f0e180a0b01172403060c04050d03050d090c1a09060f0a030b0d03020601030b0a02180f06040803070b0402040606020d0f080403090f0905040b0906101202060f0301030b010608 81
    0x210385010803143c8058420344902802800b441c841c03600c07488100c51305e9003e1041443c0300b507485800c0703aa262509140ba00580d403000760150842101ca034441c0a0075040216482c2e029041040c105890203081009214000703000450031020480c041028264001080c400d1603560381c03058000881680c580300600e02d0031000c03d906144c030817a08000400e2256110021a60300c058440c1c4100d40300e81300210103034000c0c24440a01d582100000c605402010b6001c00c0d06c42c1641c0c41030b100310300951208440882240074079896402a005105001d00603071500c402c0c0d83c440e0440c0100120710303080d2a28605801c5401c05501102c0d41c0307142c6410311085207002e0082c20007902480c0b00034040819290f1004161402c1c0c1e00108052012900200301450b200305241000b40c01440c03070070b441955031031710508010182182d05561042c4e405000c6412150b001c0b41d001d004040c1c03003105425903030500200d420000007501049070321001c10850f47d041d40a07040040c500943c0a0303000a2215854200301600c0390100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 239065026 1250 239063776 239063779
    0x151e17070306080705010e0d1403030a0c080402010c0f06201b010507021518010908030405010b010c02030607120612081e04050904140307170a0306080c0a03060b011e0f0e 75
    0xd00b601444060f20014050303088507000d2a146072001800c802140d00b00e20240c501030038000d6994038a107048603002000318050940810100201440c643c02150121000e0320000d00280c0f0f0704002c84041280c52a00c0058070340248030004480107452503844021044a2808880c0308010a0400341090f03c100d0071a5026100d40007403004c1d15100c071009442c5d070070440c07030903820954181c081106280000105010104000c000300103120782824143e4594108071001c855944c2000c14010980d40700f540d01440459000c0d00400090700c0f140020346041c80101940c1d2030643c0c1c0c0310400a40da40d05024220051030043c0001c580e11013942e020408252803100784050f01c1c407804c0004020540302d50100c41d52203500203d09580e5143c000e61858214402c0e070130060141c4401407009031200212400504800c0d141d502c081000c030303981e100f05540354000c2c0020543d0000e841038003040420741c00d0300b040504080500d480303403421481c4201010301c10307049600040000c0c0031083ca40c810369005451045032100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 239066276 1250 239065026 239065031
    0x5010e1510060f0c0b07021501090c0806120a021c03030c02190602091807030e100c020c040b040b06040803030702072166151e170703 59
    0x300302900c1038141e0342030321030b540800091000c0380f000d55110308100c40c80d2642c801701026450405143c02517544420804094031012184000280ca0440784180301180806840e001c020740d80719001c00c83e1400f5020500513881c021902c01e0001603823a07030040d8400050b201d100740d4042c00b2a060003021501032b44610401d40d4030003402f0040e400242d9200b81e40c42c43c3d1244c0c01580da04c00e07040104410640c0e041d404403e850000050010f0160907410482c1150040b9003200c82c03080f150201d40c01034034901e140603809600000c481b00c501e030400303401040b45050050804980b20031440045804d0382c1c415880219180c20100030302012030783c1803103a40300a0001282e54034119104103410b50700d00102a90040c2a58081c0703650b001410307503440c001c2680c045080410550816080481124100754002c10000b5056101c2d041c1100b803000e9240c50070045154803020100c0303007840c02001202c201072003c401440f201c4109034900102034030f000b00520f072060381c9180403490a01e03041c820744030018102d003080c1070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 239067526 1250 239066276 239066281
    0x50604050934080d1403070c061125030206070801050a0e04060b0a0f090b06040b0319020403051009060c0c02091b04030203070303050703080c04080307062705010e15 73
    0x400001d44400e01c401aa440c0d01d55044110001009450700c50105030300b150601c82c0020b808440441c135604002c80a0b21407803410b0b40364240d040320a101c02c688410110340e006041801083c40b41d03200c101042c800700850351802550001c00d004c0280040300740504601c400504008041d4117201d00742e00451b4030700f40011103504110004420000c14010108032820354400641486001d030409065010040e20120046490745250001444140141d81080307090880350f2180b030919004540071503954410302c504686500040c5400c0342c100c8007140303c91903002d000c0840030070405d00582c90f402041e0741d00003641e0a030038036091064618005c0c2131428446000300c5100541c507002034256001c0c40e411810700450314070070304202490050303400c060b4252041080200415030050024181c460107501e4485560b611703c02036007014419805400c1860700281310040000b4407582200e1000890360f480541e041610040d02c64068480c42c07000d4449279100c062890f031900b03007407000d0740b820900032011340c0052 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 239068776 1250 239067526 239067541
    0xf080a050703030507030216030308100e011a0703021510051503090a0b0601031508151003030e060703030209042a0f0215041b06090e0c07020d061a030f03070605060405 74
    0x250020b20001d01481400206074040610074030480c00c0e02d42c1d924100441c49516410000d214200846010440b20750210380801c551800c0084c0d241280e5580c010740c0030482d40085078031030355040404210117501c2050300702c1c05111614550288140c0740b05001c00c4100707143c482081030000e031202014030070346802c1080c8030030340300c6c00300d000111150810a486070b152201d0004800814044004050b9034a0b410004100c1b88000724403008008910000d01940d80c8a480c24407103122201d20008000c61700420210040782045c0001d00180c07402800d0040c10f00d20074802040981d50800c0c811540100d1481c1001c00c200c403004484008103c45181c001080c98450401030351790413014181242d54102d5800281c104888040d43d0210074024030b40351b08005a448030060826001e6003c1c28151020707080014404400d40790644080035001868032001d00303119182d100040008190141c0040b0860424101941b800c021294400100a00441d0790303a105080070411914060311051089081c40180002e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 239070026 1250 239068776 239068783
    0x9082205041e1104050d03030207121704060f021219060801061d04080904090503030702070501020a080f03090726011103060607141005040f0201121e1805160f080a05 73
    0x441d03502c100002002500500742c0342c101d000301e5214a9000d04005e203910105949038018003c564400c103e941c20207820820103a07420306c0d14246205c403500380c40c8001408140d182c0c1040e0154440b440c030061401c003005180b900a03460440f0b00080206807419a10021085440b403d001449840020480541412905078402d44421801304041c1208000324061100c00800c03509070600c014400c108404262a0068598108980410142c000d11500003003c4d4008142d80310b000b036010b000585000b65903000c213603103504090101c44a0b4801c80380003048641c070840d120030640904040c09041c0e100030951050a60b60202c4228a0044091041c49069110001500c403030b20382c40740c21240c0840848411624010070440310048142c18442440b0902050b1540384220354000e9039050a42c1c3c40000c800c405a07007501c45188040c46100d080710b105680741c2d038001c140410900094040d00e50558075031505e050313034403103020340c500400301020040000030014800040c8000c9003c6e0582c0e1006442d400c0d00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 239071276 1250 239070026 239070071
    0x601050f09010e0402073c020103020a020f0708010509070504020705070501032313020406090203060a14060702040608010e16150c1109102c130201030908220504 71
    0x3092402003124503107a0300a031855041c1c5140904115194000d038100072130305464980566903c9044010299180c1612040105000048000700300c000304117a8011002903000000300b40171801b030300991000000c424031400c0006c0c52100000714050510b0301e0300c0d40c203014007540910b20580c4108110301c0019004601002100c0090130000b480070900c102c4040510308906c0b5203e08001d03854101300c1070074030a4500002c01c0c1d009071000c01c1542c0c1c49412010480c4000e841042d407011030a003040100800304507d0f1104500c010f0040c0381011019804201510030540040d056a5121044041c58001c10450303141c12046d00ba07413186480b4a01150240080c041030116010081540815814029208074440d01080042c05508031890040c0180701d000506010728a104c0030340c030307010703610f42c0c19004040c0091a5007525020040d40301d801c8042c05e841e1402000320b042c16161a00d800c04901c2c000050041d824181c907421480c140f16840d42040c110072600b00c60f10403072604020340c1210092240009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 239072526 1250 239071276 239071297
    0x11a030616110f0114010e190c031d030c0d0e0a1701061a03060a0e151e0306040b1e041505070c0c06020703020406241d0406030b010e0f060105 63
    0x80c00d04581d8904460480440c0e224240724441c040d00c4242810b03055118040e9003200405040540e600c800c190400ca250542d11401018002040145006002d070b1200800040c507090000d20300130340030010f054120a8007820340c2030b50400b240d0740f42e5400d010b10190a03132482e075103003445011400c0c40000744008442d01848101801011203208031140c2540500c01403c0704400c04032081071901e80e0003002c0e40c006c03039900e402108000000503e07842ca10f00000e00030301100440c3c42000c107000044c02480c0381900d02c50315100403071004501042d1030511601e40500e000d180c1400301450560031110710f00e10455202c48040040100304800300c1c00608200841452106020a60b62903549040b2410700011501903c260f41d03201d000074409800007035503c1102d109031014804140d44449100301203c0c3c1d0310200c0c040b0603402c2c162a5086215050701c2418501301040ca81c81038200601180480d800b58004803100924440144034442c4d61008240d80406007003900100e40c47c0c130800003005070150701303002d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 239073776 1250 239072526 239072551
    0x61804080705120316020c150a050a02030f030103050a05121303030f0e04060b040f091b050f070501021c050609130b060307031a16020601030c03021e0909060603011a0306 75
    0x30740402909000b550000c0100340605034480c03c01643e004c503190759001150000d8495031070f10f04807909140c0c1400c0005004201c0c014105041c900d070903141540164944c6085010412a40d40300100b1035019501940c01400108800d1681d071604925000e1100c82c0f802c0d03020410b102d070102502e154120401030340c0d414900098000c034126000d0b110031342c000113010f0344241018000304d030541071100030700211030b90707111014905513550742000c00b120600c0d000c124000303034000a0700402d41e018a008110b510390b41400035103044050717200d590894300b09488030305040005048001800b02c5500070321703800650444081e0f41c207007400707840705000c2080c0312001050004c2900008515a03010f100a00003150400010252003104101e0800744a50031503914152902000c50f034070200707200184040c10b9079440800440b5841c1140c08201041c4000b006030680c81ca08500e241d21141c41d031a03011070103404c030a0000c0080e424004105806c0d2607452482c01c8625a6001084440785e0b8000382c065002440302998 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 239075026 1250 239073776 239073787
    0x801270501152316080d0516030605010924110703060203060f06030c07110303220f150815220b1503060310090602070605041b0906053007061706180408 67
    0x1907a240c3c090607405986c40741c580410040c0030000300703681102d0b11202d69401c01501d51502c0056510700c000d80211030750744215a00328802e030b400c4200145220302081c02c3c4a115104000c18961520300d507a001101c1998020060000c54240100c0c120392a0004440c40350442c034002c02c40c46c0c418010000003a002d079006502d992816201030080381c1901c40641d0340040e01888034a0034440710b421512a0900c421044000040c5040400c080618984190342c1c0b01d0080362110001c2c003d03547c1d20f04d83e1990307010882c00000100d980e0900180311080c4c4081c240420704410200800c408140080c0002e14003240c104208800b44d0303008128a405412a404001200d45840c02c0000082c020300740c005090750718007400e0000b0b00040c2a07103220b02c6c154010400c03072005e80701c1349140141d600c140b240170742000c403400b41c0140c025a52514000b669150242c1d20030445421611149004071603808200440e000b601685c2ca120f8040c81420b86c800d1090350700c1d240e40d0f80c0140c1301d0b01041d03100910203080c4000101e80e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 239076276 1250 239075026 239075033
    0x1a061c03270f060813030c0b09030412032d0210090807020402030709030209070c0b0708190c03021b060f010b0715020d0506040c0804030801270501152316 68
    0x801c99a03000d0503280031850551204100c41a00c000341c007402d000320f0012400100017841c0c840a90406552660f2104601c860b19aa404514076000e0f10b0f0030b03481d00041c080403d1030500044141000c034001d581d600c55411817000c3e030204501c2882d40540c02207440040b40501d07150006044101d41618001c0002c41c5140c604210646e80100880298841d00010900c080c55501000d0001502e0080f1034551283d00c8000096070303001c6000d0310007000d5003206000110a2802061400d9100b1401c204d001c40f0b4200040c440800c4601c214100d0003c43c4d404222118041400e1411098061114004000d1828101c07540395202005200d2400c1c0b910300096410100701d03420f085440b000d11902ca0075511071052504210103048200c070b0544c09245464030b5030070550700c0380039114040c54140d00d5403c460790034090341e60781400c407070240300842c04880c0c0c050070a90451880ac042c028041d403601010a0031400c48002d20001d80402d04100000c00400b5200c0060400800c580200d000940b03c3e2914410524 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 239077526 1250 239076276 239076317
    0x30d0c1b120605060102060606031b0307030b030a030305010311030d2c0a0602100515010c020d051e07080609030f040b0d0f090b0411060c030909040c050d1a061c03 72
    0x200411540106407420004002407034100ca4011202602560b40681d00c00c420b0000c02c1c08103d80030010180c40d0305191000b04980402590001d581e403802007500c80d0440d0100345002074211044001070f03503803801002401000840741c40f103014120040c156520030784200800d556401d00c40c9042c40150803848204084a040e000d400b0264050202c0b16117a94171600a5140d40741c40300b00c0d03203034103041c100050403000c924201101d0f0344005071120715200d0041d400f40103c1640105007102d40e07110306c411420804508903c0010340c170403000c0c0100861801d0050079410104040d1210701158414003240c02c03c0d01000d4184d50a0f12856001c035070700c4075090b80104d405450b0003002d090616241880050900090a0200d440f45006800e940d100c0e6800700c0a108240c80b07071248001ea15003060120214519014039080c1d0405d019091003076100341c80307000045005109007030480e0005405151218980e400b0080d00b940541c0855490a412003966202103210340d0300b02000b03040001000f800b0f040c951004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 239078776 1250 239077526 239077529
    0x30f040e06132405010302040501050a0302160b01080c1206060f12150c090f0a050f12030f040e1f080309040c03020c0d02070501030e0a020d08032701020405010905030d0c1b 76
    0x480060201800c1c90703c10142040b009224a64400190302021845500030300840302281c0040c1d40b901c0c5480b401d144110003e40004049040b140c4000308a800030400519105000e0851203010305545c450701c00070880242d041201d01d203210b0700311004010b501d9452a840c1c240c29102966500c0410260048580c28448403040c00c01c8000241003e04c2249000d8030060004010251242840b01c1d00c1c0d0b40402029500b203105880c0d002240101445050510b0342c01400c0e00c41c10601180c3c05c00c481c2648070142600300e40c004011b40100d0004200f1400e601c52028600d0f80040d9400c482554101582c0302c1d164810203180c1ca0013280c0f6005012041c0d807182d41120702021400e029100b01d504485002512828540300d1540024104003010348400d5002c54807070201503004010110101c0030b0b42d100403068000602c42c5500710a0a40ca0601801c54407581400d07040100d000140e9450401c00090403880c8203800c01406648440d8044600e070b5001084584030f190014405803085000d1a2114040d8809 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 239080026 1250 239078776 239078809
    0x305040506040b04020105130305071401031a2704080909010b070c0605130e0f0402130c200102041a0712080601020a111c03090f060810033c0b0108030f040e06 70
    0x44230000000e0010125030001501c0301c4c1c060110500c0800c1c0c0c01103090303d41803d0302008803940340c401c1c00341625252a94895456000c03501e080b194070134141e40310341901c0403a0301307540c441e6001400300001e14001044501600404d60500c0c1030841c07a0729008102e4003a4040c001c03d00100013000151201c0e0a00e1890007400c81c0c020701b131244c0c43c00303210400d2242002e0300d08900400210344812886209400f9102c03003074150759500f4500d14019403c80c1c1c0348000300410005255030802010410001500c1d12904035001c0410140c0c0e038112a20380800468a000403800c00c01c0a00c0060014503079000c42c0801805400c0754408a9070744c003900003e4080b001c1c5101081410b550f16420004064120580d24115203c05452180580d503521060740e03402011101e10070a11407005d020300c002030f4461000c95016441c456080b503105d4008891070305840032080811117155024940404000c004440b46000d8200c0f07030050741c00c04400f0003840d0220301640c02548030b40802c520004400e40c44841150000619 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 239081276 1250 239080026 239080057
    0x18020f030103140f03090d03050d060b03090a050c06121f05040f090b10050105070210090803030c09030d020c090c091201151a0a0504140402070c031b060305040506040b04020105 78
    0x203403480c2030b400350b645450300007001d402280c06030025080c000c802d40306c0345080a0904500080ca61790b0846150f23128046150000f039941d2800b20313016028601a500c0740f04641300a184424160500d00e03d8000f100c10114444c5004020035001d682040e4951508a20181c0d807580000207440c1d4aa510b01c2c0c8682c1149800a191070b40d0605000e000f0f802200e40c080c0141c91243c410b0b110741c200c91428281c94002c160100714108034031001070410308026460a646468080c40c81a1075120240c1180c6c070a495010714418049642c0015160601004004040d20b0000340b10b03044849012822103200103241e800800c801284107a2079480341c0804429140598008004000844801e86103103445805000783c040140081341c001042603500712400c50945032545410b0524007a014a1401841d46801c0d4102c0e03000d01110340090002c07c100300c055446a90040d610801042c8445000c480c1580800c00301803c10041c0302c0403034030110340c80703803c0340d0043e4044a0654440c00141c8452082034111240d81c00b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 239082526 1250 239081276 239081279
    0xa081302090708150303072d05010c05040501110f1c02030f030426070b0a050709030506090706030b012f010b06041502070608040203030a0c0c170303010e0a02120118020f0301 77
    0x5901001c1d95100759404203d840105051314103050760380c02400d00080029240341c4007003150358140e900003000e1840c03411240456801c1c542c2c6140c03d40d1554900d0300041140850180300341c0d0780100c00300d90b084605100130282192003251240d941e06004803c1a9039032140340e504a102c6200303100300c40b00d07030f00792220040c0d032802d16152441443e6118240b0904289002d50070391903007541c2000700d4800640240520440c0c0d190300c058070000b040e000d00f104d0b0078408403900000020780117011484c82901e01801401c40145400b4001c0c0aa0300c450060b10b04011410a9468102c9000c01038000090f806c1c03a084500c1114560303003140145490700c0000d0780080049000aa00501040c901c0350300b10035642a510310740d540c0d6030b05890700001510001d40c5900140103d070240b511842240d0b40e2203025901ca4008540c0d80c040301541c002c812441c005003a00000010301038a401c030f12a040d0040c201d54400c52800707d1000d2000c1484006000c0e0081e085010ba51b45801c0c10400d805881219000492241d0faa5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 239083776 1250 239082526 239082541
    0x1060b04060c1203050108060a020315040c02010902010806100f03020f0d0207050304080f0d050d022d0a02070f030209071d13091211030f0c0f0105040311070b030c0a08130209 77
    0x40c58800f02c0750000c88402c220030061080c00380d9412905810001c04040d2585001c620183d00004c005540e90a0140d404a00c0c503502e03030252003550019034000080c178101034000104100030051080e805150b516504080307890b886020598029043d160040c0c88003000c0615525601c44d03603000d1007040d800810300b0f206202012008004940007001220040c030004425aa12034214a0f00900414800e10034650b03d15516001888036014100d502400103001c3c200c2c80740540000c5031007001c15640450038029454040065170003826050302d01420b103501e140d0008a074000c00408820401c041829040300940c1005800c0014010041c03614802581086500c00202000d00090380c0c180c101d040c1082410380501c40700c1d2030000c03066015600d41f40180407034403400d501c00074525145200e106a810084e0700b00b84901d90180b84030f03a03075000c240d8555011140ca0720180d80c2084400140400520056103031040c21a8401d0030581000b11303142e40c0e03010340d968000900000107508017031810100804d1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 239085026 1250 239083776 239083787
    0x5010f06030e01020c0a0524060f060a0e030a030909360203070b0c0a030f051804181b14100f0f09080303041101020d05040e04061a030a060c1713020d030201060b0406 73
    0x50000e0201b2580c262444059001e10441041d56440c4d0003c0000ac04607104e420207400518081029003400000c558881021a1504011400c2640000d12020060082c05041d0182091480d00e590b000740c200c0c05040034078218804013985980300c940c150035050046460500c070f15401014182c0d10340c0e0310740d194458080e441c3d040d6400c04900007031485085001c0b90340200c0c151074070410440c4d1840000f03411a414800148040c4d0382e0025500e621240030b400080b0b5180415840196400d01d01042c5842c00002808101c0c020030320300d102d02c4047c890342100d04c1d40b29248010702c00052829440f425018407040d2103490f01500501b82c10b00000080006100c0c400c030021300100030a0b8220b1326400103400c4112170a0003a402980503c0c8210700210340400c0f0300b038000400741043c10050040010944000a06c2c11348030000c1160001c0d2180250308145030011a18884c030501c0010008443c6007005222802d880e41000003841080b03200005000d05100358000405001c0128000e0765071501c441c0003404 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 239086276 1250 239085026 239085043
    0x70f0807060e060a09050303060904031b03020109020a08030a080c0f040308070f1703091005150a060f020c010c0b241c0c080d0f1101110307080f060405010f06030e01020c0a05 77
    0x309110f0080800d02000ca2403065154080d00301c8013079401d5454110400201410103002070301088005800d104400b0142412904050710035000098507801500c18021070b0300182d401007455030002c3c00b400e40a180c0190031181e101d0b41040b04a83e07240700c603051001560256402c06400442c000c0f65490400001d0401e800d0480c0c01003860344180703810010700340c0203440704441c4200300c0d401c43c1c602605540d45a402050f0880903640c1c9126140c1125404074681d4000e075444040060030b15040084010703010300c0f0f500c10810003841d000c1c0102041d0340312450070704e0014242c078159420b0301c22500500c000a01001c541c00c2c0000300020340d8844401008880422440da058078207880407000083c1c07aa00c00229803410380c04980f50304401d024030030310036100808800c80c44040c075500c8480e49030000030303180c000714820340301511078080a0400c036151100544000301a14019031403d00148031400e1a030203035504440c01d9150108100e0b80e0800103501901031201c12010b00c0c070800350324004100b03001c00c4009 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 239087526 1250 239086276 239086301
    0x2190b010513060501200c0d08031006030e0c0d1a0906010501030c020303060f0d0512130906051905060d021b0f15011202090a0204031b140a06020c0402070f080706 72
    0x160085241042c440c12a10280f10701d501150a05411512140c903000441e4040811882070b1004400030201049100044402c21541c180d0004204840c1048504900000d0205403404004074a0800f6000342e5428018420500c186000c5541c2d900300010b0061944080c82110700d441c0140c103001c88030a035206030a020f0303640481c1c00d01003031034883c0d840002540d201d80401800100300440c40c506100381c185075400259010f000742c2400742002d0610b01d0051441c3d032136115400314030302d2030841c0c11001c444458002500c2902083d01c00b18400307070180c071110181c40f0300b215056951000364030002d000784140710031031400301c403120380a0200810125980069008030025107000c44414031821a100009014284028486006000160030b15007a07150f0300a20061005203804d45070b8a07131110382000d201030341078101c1401d2030a0019410005066080603010b544060703c42d410000d0103521406003003680c5003d50b41c041090024407075880d1081810b04d4120642c1942c580741403d0000c013500149080c81c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 239088776 1250 239087526 239087539
    0x60801061208070f0804120506090111030c070605060f10030b03010b0a05030d03020702011403092d0c0405040f02040903080a0522080703020c1507020a0f050d030c0302190b0105 78
    0x150500d110301d610a00a510648880c42c203443d542d1215070b0640c001c8001da0307a20f4414017001c502603c0940c40c020000340214014020b601d81720100070700391650411080111801031040c0641780c0f01040648240c550701100100b0343da544c4c10b000c074011010383e07404a60b100c2c02d80070805200300d0b090351000072aa2000d4000b8042034058109004451b00c40b031241e01c0d05640294040740031540f0039405031111a00c1450000b007120b0000b420303a42c940d0001c1d0384401c000d8010004580401c0a07202200740b0340340c0510301207408045401e0307800f0344035030316004414011601c1d41d000408222502828141180c3d00502c1000341c03090608008001c11000c480c2d000c0118603040214400001c880c01401c8030b2819078540c09030560f500d0b030701c1e0103454004510881c00d621441a00c0c0100303650b00ca00105600b6002c60040f82c41d1030481c01017011002056009101f5141c0619080c0300f65101c041110381c1490f05402c007250380318564a003c0345041000e03d14400c2c000da14045200422000381216412208100c5e41c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 239090026 1250 239088776 239088779
    0x110a1d0f031203070903081201051315060e01020703080c01020a09061b02060f090d0308150a030c06180e010f0f080613060e010209090103230601060912060204090f06080106 76
    0xa200c0012804102140e0691000922410329003440004590114452401103030581e52076072090a2500040140c0141040700401801181840c203182a01010b048009106441010200c4010b045d01c50045400f0407418181041c0c26900802c401d40c01198814081a9038003d0701d500c0c24000d4000c14240c1c40001d0314101e000400620a1030b02c10303482031030070419145a80c600d1b03080041343d0348415003913121100284080381c00c90343c035516850101070082c1c6500c80740789081502290042031007010580300c0c1050050500200e11010041400e503141400d1881e25044081000a0800d07125402a01ca1616100000c10080300c03103070981c001c8840382080b22034101d8a812016498034011560504411504210759000c200381d50001c000040245000514000380d1402013800d0103c240c00540f04070703011a032254803180f1a000c0d00c81065988030041c10155040c01380091582e00ca0380719880c030103091000400144503450b0b044400038940b40104000a40540001030080c101c148100001540ba0050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 239091276 1250 239090026 239090029
    0x1090c0503040309140f1809061e0c0306030a02060c01140a06030b0a0b0604050a030323091c1a0906040b010b0a090b0d02130f030c080a030f0c06110a1d 67
    0x2a00d02855168859544250070861690f04008046400d50780c40850031032003e2050321442500003068a121b0031303914140c5409507504c1c1c500540a00f071503d01c405280b01d400b12b00b50303400700080d400c2081c06810790b66030340b15071001130718002488001a6004100040b00c814801c0d05600c107112100403561a002c1d15551841c2d1001100c00a00c00034080c0d000d00800140042e0a541c418120710b800240002d050035241c2e0040b80780140b50740c00031008205869244031030411044500080155000e11242c1707012020408605018103a912021041015082140070021141e80300091440100d40e081c00520386424a21390301d003800e0700e054420444140001c070301c180710030084440e2505181c580b80c1d000303443c00d07401681540c010b03402c11100507804e00c0391a10780303450b403c6050300500320781e80c0c040b0b006411420a0b090015a40d4040020750b806010200c0019420004404511001307042c0030401c0d0480e401c140b800f40102c44414240c0d5080001c809040c0d58102100c85500d440b250035a01c030f4000140d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 239092526 1250 239091276 239091287
    0x1090b0c0403030e0411180109090f061e0b07030c0c08060f0610030510050d0606150302130806092d060106030f0c11030d0c020f0106090204050913030e0f0301140f01090c 75
    0x80001c00d003101d003040b1f03d126031400954041d903820010325103040160390f540450000c4441030311107500041e072640410042006180656030590000420b8600040c0c5040c0e0300c181d1a00c10304400400f404400301c62142403102c164042001401070409070f841034604001100d0ba1410300700c800318494a4440c101c1060140306e8490140f1425070f011044039110b060408000070460340341000c44070103464a40c0890440c0069151a0510a40340c40150700c0c2d0031515560012083c0c0c2d50400e009950001c02000445480018400c40400800c10f524109080007609840441213114852080c1c0c4150400090a0342e4594017000c04021500c0d0100801c0360701c0c1a045580108052a1004641c81801350140c1c004c46940500307081980e9004079080c1c4070080060a00f5640664046010f1070f601180400580c00d00c4200d43d9440300844115a020400700e44e070141c48401c210740c84602800c00c148155889441c2540700700e0310700300e400102941500c2c0501c80c400e040e4809004031f1038658201303070f4528000c5001da07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 239093776 1250 239092526 239092541
    0x106030e0a1509081b0c01140a030504110603070e040509160311041d0a0c0905072c0607060905010b090702060c0705120403050d030605030607020a060e01090b0c0403030e04 76
    0x4a0107051161920b4603206a510506980d80c2056a070b07074214640000c0000000b010112210407900801d00c401d044081c2c1000c0403042520706214400c1450312031308103488c2c11a03140c0402030138001001d07181ca0a2a080340c0040d00312071604554008103000045404c4404103c0c1c2d40b404843c140210f60f154103285848140c03841da50811000014024030004150484500c0042d0000d0000502c1c0f5000201d0030b104417884407419401a0410302002c028080f03d001c0c960041c008840c1c05010505044c034003717000403aa8041000702103403c40b48860800c1c1c09510441007000c1c01425951a8040360905000401c4d101d1320442d000d40c03800080140500300108203521651140d0090b110641c1d8020101d02b0580c00380c201101d1a00400d5880c00020980d85e020303201441c001c1000301018800035101508982c44d542016110354170403020025000d0740082c50810311580400003007540c494882c90903014080c800780c01484481d8880411202c010320001400450b40641e4400d803542492205000c03c45400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 239095026 1250 239093776 239093801
    0x105070303090f15291e12060c0703030b0307030b01120609120e01032a14040302030304060e101d12031204050a0510090c030f0f021e12070f1e030f0602030f010603 72
    0x1450452404105601b00c601030a50040d0825180c807402204060611800726018407002c88041035090515030b251181126104084d001040118255140c601407140c0510901920740540200308003007010640210b49901d40c0300e60340500e2a40700c0100a400500740030301c0c9070b0010b031500e02104a148070000d403a1000b00c400c0410686c9034050181c1c00c544e0710701e07052018800040c00304800801038030104020300061006075500c102d40414031701042640d80c200c40c103005c10001e006900c2200043c0d895000c0c40100c0c401c035032010081900d10102410b500419031920303800c10b900b8080200f84040031850a1001d8440e40544400700b110402c1c3c001142c00a9001505100b503a0009100041881980410850140d15001703089421175001a11003d0450b090611090308143c2031426401c00704401e0a0101080001e8002c59040c800c0f0f41d10019880c0c450030b440d824850744d107508800301c01030001002d90740001d0b5a440214407400c000d0043d40c025074a00d0500c2c0000e41c00001c096100b88154810490f8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 239096276 1250 239095026 239095039
    0xc020c0414160306230105041e030303050105040b210106091b08090601080a0318120f0b060604180c110f0312010504111b031b070801050604020304020105070303090f1529 75
    0x100020008171003900b92a540d0602004100c0812000180303403041d44248240c0c0100b00c242d604629004080e0380d8180d114600881c141181d1103101d41c0d5002e5213a50020240f044a480f01a011403158094141035208d45940b40ca00800070300c081203070084217481c801c01c0d0b8584050310b803187d008065a0703d0007440b0702c10340e0741c000c502040d0000b407081e0a25000c01049042c1501d0300b83d261100c270214020000005c0750060340400404040041103100700764412000c58041d81054542003c03000280011304c0e014070080c0d41c421400240c0c1e4000c010b80c541c0c00805200302c50307152500e05119580d83e44180010015908203800000e22890a8011424012042e443c01c43c240f00301c20105145107400c00c45081f00324003003489031482064540040c0d020075141c1d9002401510302e0310320305a0031102c01074515401a40100100000b40c0d070003004841010741c0c5460300040601321424212880410304a0040603040c0c141c4001c00480710680224000803890740e030008143e4035000350000540403880407290000d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 239097526 1250 239096276 239096309
    0x10605041503170a09090614191a03090f07080609480301050a0b040f0203072001140a050702010506010c031d0a05190810020405130c020c0414160306 66
    0x281202c01074180740140b0b003008400c1588440001c015580203030000d0482c088c05180320319491820b4405030486004540d003450030281850040c3d44542201030301010940c9000000c115804820040300030f00360245401c0d1803e05031100e010985644083c2c441c0039a6100703149030280340c9440141050320144000e00c0ca071440d10301109205400da13109024021482c0e0007445c03440c889803070a02805208144040340002c20403901e0003040100d441c80d00d8449a00d910500421600d0340d00a5a001c802c06911030001d0040c00070882540d014140d84101800070301d02c1e04080c0300b00310b01250030417070044103e60000c8c4500e640e060011200d1841d1060090002075100a074a4144800300400703010aa5029040c80091a210340206003030f41807180000c5240d01e9840d00810408105000c4048010030780d20341507180920b0840051076136a1805030027941c495480b2a17600c03216000704152425414040d00900000c14401911076001c0000c440316607071105480801c1944501c02e200c0c6100360f4609500350290034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 239098776 1250 239097526 239097563
    0x30605060a0b0f0414060c010c050c0f010219270905010320010e06160507080a030e061602010e0f0d050a03080a142d04080406030b220b0a0504020a02010605041503 72
    0x4074000c185e0305800c85010006011882c2003030049040441072502c81070340d40c0c803002300c480c1e00d003001e480740003801a4414410030a90010007014044190401c0c5007041da0140445c0c084084280e00c6c0007000c908121b400b400180400c42604400d04903030040996400407484035000407000c0318004442e5001410003d03180b0114a0079101501c3c1c50012040e4483c0860b0880c0d41d15841d0064a4015911719440710b45664101a80f2119417020352900f0f480b190b04010b140304607009040d0a00b10002c0c14030400c100d40300c00b5612180c0c0700154a00004007868040340c05403c1850f1115a0742c14190001401ca00028003203040c07070300400941c644501c1014486540d0a0700807907444d110005101900c3d4075107201c0382148442c0c6140a80a1401211210399491a1202c0501210182d040b041d007d1003007061071042403565a030380300c662181ca0f650003140c9040703844c00048010f40b0b20f4021360350051001c1001c1d00110b50561046040e0b5006440810915900b0103158840b0103141c48007c03d481902032840d030f00c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 239100026 1250 239098776 239098799
    0x121303120c050922090b0604050703060305060c03150607110405010918140708030a080a060f0509041407080f0a0308010504090809100e060a2d1e1404030605060a0b0f04 74
    0x540c66036072001010b0a2411030010113950213045c003960a038141c0342c180540c6252520803160040e0f05810100881446c46d0346942c0c1383c480c01420f140300080c001c00040e144040c0404803440700e410007018580c0d0313840d04d89000d0325002c0f62007075450b0050346858000720300030311280300790400ba0b08142d03940c0010400c1ca5549107100d044806440d1042e0064000008200d0420800b0b4200109035440f004c200385003c84120044501d164024500ba104052040203640c44484055070060740007002c3c1141d0041c00143c0a24040c5180d0040c01c082c0300b44900f041c2c0410001ca8078001d901e102e50796196443c0d0fa5502004242d071149540a41500c00401c4519014501750f03210b07020a0f00c25041c0380f1002c03003070a000a18150015104c40f40400e5000b0490201174560401e4000680c1c0074400c0480031105400006101480c2c2c0740c440c0d000c415098640081d401e005911804807030000c800d006a271503071a80317000000f078070007540c140b4040c071001c03500850510b00403800d891280d0824515a0700340713450802c06088 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 239101276 1250 239100026 239100049
    0xd08010b04051c060612050d020304121e0b0a0c02150907290f040905060607030807030c0504090504060c020d050c0c0904020f0d0b04050d0c020a051005121303120c0509 74
    0xa079000085001800a0054004c0d2030041101c407010716000c0c6c01e07074240b071410f000c0e5015203441150410803042c0240c196417034411090079041002ca031980000301c410301c1184c850608014000070202c50801c021800e054100c10102c2c1c080f5402c0c0d4500100d0f11035001651001580c3c1c0069a030050f41d014000f4202000e200a00c074504800c42c50316040098620304115030001d0308203014620001828841e00085001d05900508260745040c40c2500c1d44c2c44c01060310340702411210405860307420f00d4008520682c1518040c05000104021038145464090002c1c140550400007501a080d41010864064410340340403100396005801c2608500b402c01441a400800403a44690b03582d85031100f45e10f07a03000210708544211381200d80307030606040040c0390980c1417441100b0172000030b050b00010f840d0101800d0445000390340a000c8a041c117101035407140108030166842e02d0b801e0041054054480c24030a00180c080d1302d50a100d004103001c2c02003500d0000b40750102041040100440b2401c240e00706a0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 239102526 1250 239101276 239101309
    0x271204030f080f03040c0f0b071109090c130e06010e161413030f11090912070614091e03040e011202030a0501020c070f1d04020603090c100504080d08010b0405 70
    0x502e401c1030078a000f00315410a03074080d2a0181510340901401c4a129000e85c080c003d04d10800f410050307a980d500280d4000081607a004d443c6c0100418900b172820860441520401407030340c0c19030219580e0200040c0500c40d0b0b01480e6128100c00003503080901010b01740903104411880b45466094041a5448903001c58a804903800070008a0702c007041e44190310303000d140700b181d0351804101a800c0031400c092800200da807240c2e1101c0140404104001030313030302d0300000300f90415031a4916400c001d4010401c8840400a03030600f501000f00c40d80010400b03003002d80324150401e0342d81108042c1c4a079680114011000800301107401072161035112199581040e00c02001c494a50f0310701d541d401d00f179030010011002c0b60b80c8014002c2c080005a0040030000d491602e10503000005424400c86003550042d201074002c03100040850049a020300010112100c00b801e070101c0c1d8a039184008040794000e210b002941c0c000c0d03803d10030240784600c400c103040b541410790050030507040604100030300d03c00303c400c2c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 239103776 1250 239102526 239102543
    0x10b120a120c1b060e030c13150f1712030601020606010309050f0a051c17010303050a090e0106050712020a0201020606090901090b0c030411120304120204060e271204030f 75
    0x1140001c1034200c1c0c807403d800c880c1c5203865095151880140c9080b0b046112544a0341042104070200d440b008840d401207002c0c4403000c501244021030406032522150055161400c3c1c2400102d01103040190941c401034070401194503045650b080501036000540350700d030060700110042480c87d03201c0d40240c4080f60165090b103a4102c1014141c51806c454401c0480d204c3c3c10002c0c5040b80d030500c041c024a000106410000002441002e0038440c1c0401400014144240410b4505095104041400151000c110a1a040d585071a409041a008130a04803401c0000b0700581d0801803000c69100c01d0940d068000b4410307504e69104000383c82c0801000002c07107650b5015000c0101c0d4145400a00840700e800703817503030baa0609040ca4000034880c1d21100b40242d1012403110380410700081250b00329950548201c2c012200c520002d000340c0744503030246080c51500011300806000c940380718921010410b1403110040d5000294644803128030700c070f06500f810240010008100e982046100c0a0301c6041c80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 239105026 1250 239103776 239103797
    0x12050408010f06050f010e0d062706020c0105060609100f18030c05030d020f19020f0607060f0f060b04090203040f0506040318090b1e040e01061403010b120a12 70
    0x1001e084840d0032010301d856a8490004010f0780c140314650f407041388020301e00f490720f0500c50400b06e90510ba07101d9008007038603600d50001000c14041c1080501c04021868030055800c05810020041d412140403215594a0725010502510784035040b00d04d281780250a4a144010440c1d060790340b41e400f001c030320060241b803004034148101c1c5610a94041e40c42460f0194000d8104000d05281c401255640000e540c0300e0340c2082602d08000890712828800d943c1c0030540c070040d510201e80c8501d58880d0300c035044100810b0050420069401c010340581a600080100c02244190380003501e00a01c030721300902004110600000e51039400a56005020b254120901c030704958515140c0301d4101c41c190005404c50420503110342560b4a940c00802c06003100b0f00c01e10010300001090f09041d2440c51a001c40c540c14801d2403500c0300c3c0c0180d1000d042d640c008002580c0c1e0340c01442040044814018880d502c1c00c0013811441c504070300b00c4802c5c1049400201b910030601d6580910003103044100d0340070b00c910381e000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 239106276 1250 239105026 239105039
    0x203130c08010603050601050f1c0305070c03060c0806010e090a02180a09020a1407050d2106080303092a04050408071205120f1e150406120b090a03050403120504 71
    0x80c00248101e034000a001403030340c14000c0c101141a000b4510a030f4204401d80032580c0e52440880701c40420303102940b14805c4500d0150b1391403050200c000c09001418200000744035050344200c041d0302d00c03900d503031100303580320801101d1042030030b0040c1e588042020003249442c071043e030142241941e00341e0511a40ca003d040000e4112285a12800040340c000400c1480154071148a501c900c803200c10250504016030740d07072622585132021400c2040361011611880200640c0940780c7c80e4030102d01081074948a180711a00ea50048641d880240310340740c0402070843d2050305290100c060011090700340002901008040d1074064010740f400380040c01035401080e03440c121842c1194181d21030954a089041003003c0c040070090a0601028056003041091048208030b00c090050412188605503160440451043c400c1190303240c000d4500a8003052010b100138007440d03c6030143c0300e072204603a80c440145544466124008001590038081000041d201040d80892101c2c5410440e040548440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 239107526 1250 239106276 239106293
    0x708010204090c170903032d070f0912030203030a02030703140f1009020c03030a0f06090603050303060910150c03020102210f0603190308090c0904031e0306120303020313 75
    0x400c25001180c0e42c0d610648920340042c2d90203601801611320889034a0040d080d50740b680001014220101c640d1071071148904052209156640e02d1510016014201030304010810003000207460042400514007050014405000d03d241e030364194011451359980d80d150303602035003000d0041b00c10b054580c2c800ea0304110440d2203062203a0300010b00040c05145c152118154003080e98032019000d4410019284a0381c0d000c001c99921401c9141c01281803c518030080004280c60f03030200318402d20b08035000c000c000020000f03502602d0b04650308421707a150810141d0b85a0390342c2c802c0026140c03858030300c050500d010b520322600d0a030090000501340345064480740001d841d4032140c42a4080c107042000035915016003c10740010090300203014520301003011601c440192880074042c852000c00003494090b08000c1d490318110058003050450915180103040c20a101850152040c0d100240c6e0070200d11a116100c1180e4075007001c10512026030b1001d60080d4070180410b07161a0b0480d441c40c01044401c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 239108776 1250 239107526 239107529
    0xa1a090a1d100e010b13030605010810110c1e0709020f0c011d03041e120b0f0108010c080112030e040c0207090c0e0a0b1312080409060e0405060f07020708010204 71
    0x7a440142800c1800d03a908194140080540310915410700090102d6500344082a041d0351204000319520400a20040e1a240e86940700510b098200800030410b100c0c046400ca40b0780a041c038050103810201c6107003640900506501e0080c1d9440102082d008018012000f01d0120021042d0381c02c80ea01c0e807900c00240e0340107084251186400240c41e0039501c10034401d235543c440140d0050010700d03040741d00c010b40b40e12442c42003040d0f8104e240c28180b1034072320140022004200c1c0d4124035000c1002807806041600b0308403030b4a200740c0740607000040d1410042c0580a011400c0750786070141c6a0a01500c0031000031f00c1c400680400c0140c10310b40582d0b48417881103103070703420483c1c0082103220300c0c06c00d61405640c8034040800800411300071a80203a119050307034a0079504040702d107a8440100854200464500754031a036111f840c25407074031043c821a00002c00542c3d151250a0000d1074407000c075003800c00c9080d50010441d5010000180030f40c0f5120360b515800030f2561042d502c48030b984815081c2a030b00b06 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 239110026 1250 239108776 239108789
    0xc0c010504050714120606120102120103150e030c0d050d0b030d0903022110020a020309130203090105060108070203221d010915050d0303020f120f0403030e0c0a1a090a 74
    0x34824020759402512000719a44211902e0081040780705d1265120000500801d02038001810344076000f8800307406886414010000800c5150303500e00b004405030110f1850211901d1a02c24051f88401000c070031102c0e0141405c0040050b1412610222285e42c03105045400030350f50b41040c48620f541c1803121003424034042c2e45070125103045004004000c3c0c151541201c2c1d6104815008501d5200403803007911401001000580b10401040141d00b9031103450f0485912080760b0414007440d07101580510700501d5620005c0100d41c1d00c0c6001035918030303416540d100140e07000307120500310508004065040c946508614000032640c03200d800c4185030010990480c102d43d440014007078404907101d40d8519540c4140c00700c1e917480c903083c041800422107200160400d6000101c0c042d0340d511000072142e48100d2003414a0f43c43c9820707402414481c5c801c0d1802c90000e800c107601150480d0000501050102008045003250341c40e064a00500e01e5146602503140503043c0400300156507000b8161004086 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 239111276 1250 239110026 239110033
    0x204030512071b090b100f09030b130c0b13090204050a030f0c081b0f03120a0807091220040911060c01060302060c010b0108070f02070311131b030c03020309150c0c01050405 76
    0x2808001740c8006044024041020750864403032020340c03107230b40401243d41111543e402034595140600d600d02e01c1d107201070405a00b11600184031280c0e24020181800c0b0034805804041d180d40325001a4400c0d40300703a0381e20209402003400800e06044000b03480c1403042010307001e125900d9072081d0038001c1c0a20a10070070b800d6680402c0c424280032000301c2c0080c00460190000a8607918860700741e0007240d0781e24003000920000224a24007a00601c0050032140980d119000c800e80313462600c5500d1380c4102c0d40300b58001c820b10f00c0da60070180251000143d1050288100140e003406001040d081059246c00329034850600002603101c8900034200040711100202e01c60420a00140c4034000c05005002085019200350843ca40c0c00f00b10201960340c40b0300030f0242d0f2505032000030400d4441b80d00006080e86050707050086248901602c03074600d0300c11b072004e01514183d003205404a000440f001c0c02c1a07006400e200e90302200910400d90b00c0a141095507082c4200781b51140e0843e00100c604948c0743d0b0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 239112526 1250 239111276 239111291
    0xc0c0604030206071202040b0d1e090c0306061509031101050409090f170705060c030a061502010516030207020a0509100b030c13090c0f140c12040f090204030512071b09 74
    0x140d00200c1171510303100c00e0740305514117840c200c40c400d00c500c140c030346008216907941c141c1e030400702c81c0510190400b404258280108005030901c004d10451500c000c55415103070801c00581079446001e10300c0c688026450701c0d0741c2030740355444103180080c0c514440c0d810071800b000040380712801c900c03512840d2809007401c01c034000c5040c60009045642c5020080d40820f01744a010006580001c170300343c1c0840322141c3c03213460342c9654103480081d2600da04803004040e111290368010f00c2c1d05521091240d90300c2d5000c00851580c1c188150101d10400e2030183d000504a41700f8444c2d8248009141c0c2c020100790076480e05581d0314015180140c0003a00c0c88012050009021040300000241d40000b511040d00304100012040d4405048804d12202203000d12400da12420a020166820780c2c050071413070307010788081c0f0088800c2044149d01c00d010f10888a01d040c0808100e0b4a41442510306aa902c42c0082084d4400146041040c3e004070400b154615003050000b1a4075046100300c00041107084408144513 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 239113776 1250 239112526 239112541
    0xf0d050a0b0603010e01180207021e010f080108120c10091b09050106081603090209102102030a15110403030306030605060904170c12070302150115090501080c0c0604030206 76
    0x101d15078121588190000c1c0010711141c0f0000c0e01403411100700c08403c034031042d4084486000b88c00b881c000654404600c421203901540c2031034a00024034400d076100080c001c1a0103007503660000a01540101d50311080c80002848485c000034880e8051144c215100e06d5451903452003650880d01003110541064a2804c82044442c001c1402402d03076140e09100b9507040050041540c0402070a005130300080031582c2912078042d03841541c0390303074000c2c22200e110320b040116400c00300e01a02c92804034403050b1351071282c2d6505102115103003036801006003031012901c0d19286c203c2c1d41050703100460b071a610003208560b4500c41004000561181d10041242c9103103003060380443d00024040c03401031280e0b0003048001500b140040070006889203081382c60b41c840b5409545400c111446d03842420fa4001501c40615800250007d8841d603440c1001a090380c03640c6080503507079030144110f4085080042e080c000c40d030060b050f1380e038031585041506060032005903000f440c12030155800c2d005a041741c1c05000d110b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 239115026 1250 239113776 239113781
    0x50117061b0307030b061c050115030b150c070e0a0c030c0309020109030210050915071e150504080c03130609090b0102032d0316080f0f041202030f0d050a 68
    0x40111072035020a6150215446001880300034000d908055592203903401d00d588010a07520a1041101461410350703048076404000c110a0080c025004135202008071503601c01e0103850001000941150b4880049151700c988a4101150300b01c201c1c09a004c01040400141d03520794841c5100300c40c003051218560740d010341106c1c1e41c00c01400c1010b040c440c508003d40d8218123480c088990603580c0704800d240440d011104d6003d260481c69000b40d0746444058000b0b1144060300f890707401203400c0518840b01841000e0b542503501e0b8010302c0113042c41b0269510841e03030741c025548103009800803842d020b1041d050f241035034809903010991000c10318003840b401e41e002c40468041d00a000c0200b100c20038800000c3e60303030b02030440f00e81e220b503204650401c03601c40c041e40481e40d0751000000240e10303030914500800400c1c001c0340d6990001102c100c006101621100308643c000c020031403a40242c1d0700d40d42c8a2034000785460544009511003044211f2500c03100200800481032090000100703410045151000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 239116276 1250 239115026 239115031
    0x30f070b0f0136091506050303070b1504110703030203090105011e0b0903030415090315090c03110d0b011e050a03030503160908061311100509210105011706 69
    0x4181c103800d0041c004016412a9042c10b0b4030308451004025500c108010120300a5a00f006250303070074620804104550b04a03580a000740009041c010742d0b88513003c3c183c0c0d9008050010341101d0110001c0380d00e160f0a0480030500940c00360001c02c43c0b00c00100c18450a900c083e03001c1780000c3d4004100002c0c0d0f4070030700c603550260500d50500300c0d40010701600e40d401e9400c2802600c1010400090024050341d04108031401001d44251540000c481103c0c0a0130f64a1784c2d00c404e6910071101d2242d0342c8083c5984c030031396603160360104001e8881c40c00c1d40c80e1a4220302c07202c81b400d6001207618032080d0100d118400d41034020f01c09100f03a6400b194015400c6084424243d0086003c0c1151801c00e000107078104007920350000d9042400c200740304100008482c484a076520030340181c040d40303090140742080501400780444c06074046102928400050090900401288800042c02405146803900e083d252041081c1d8841c030490242c4038180c0021403c50303100fa484406ea0102b91400850250340a028842d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 239117526 1250 239116276 239116291
    0x70219150201060b1b070513090311030a1b031b0b0105040b0f03070608130c1d0610020d03020a09080f0d02010c021b060d140f19020c030f03100503030f070b 69
    0x2540c0391128491290203465100349140740a1404017552407405c1029000070800103059010180c0ca1120082c024003200e00103a0010b03010302c00d528a429000000c48035400c0175035407440c0c001d03001d501901107100e40c605012010011440c07001a21444000c030011811400b5540140a65240108001c11a4000c46142c0d0051564094420150b6404101141200c80c035007071241d00d5588083e81e124081c44a40802041100d01c8500030a082a1402c105800d013401903c0307924664070386004121685000c1180c201c01a0700506254600c18440e4000e42942111030600c0c41c0c0700e54a03100080d0618000d4802d905840d401440d1080c400d5509004010111034a4005400c582101d5005981102603e103002400703000d0000300f0001075080b41c1d100505821102d424000e85050075002101074050076501004503150f00385203400104964402caa944502c0e84004502d000300c0420141040e4000070304400240403600300016030342e00d050000307000928084e000710fa901c411900c0c1114071080c0240030030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 239118776 1250 239117526 239117531
    0x3070507181a040b011b05030c0d141801050c0f160902040503030f1e0403050a0b0f010807091d03071518080a030207111c020102060a0b030606060a020102070219150201 74
    0x32000442c50321040c1d48403201c160b6000c100701c00c59000684900038602c0d01c0c038042c0104982d00301c5c24020080058032540602d041030301c0c6e0b05580c015040b24440b00289500c501d0b80d8040160920f00000d80350102800d00d010b0500d1810095030307a4049040c11b1803072108101c5a00f02060301e14890b260050700c10050803e0b5001142040d0404000c00c0d904c0c0245421a400100001070310490440320141c4040b00f024840034803962151030b450160340310400300404643c2c0c1d005101c049401c84190f07001e102c0c140c035040340050100c0c0b481c12003d08007420403c1051082e010700110740c160b102c0000c1c0001e110441c0100b081118001008041c03000325956410100c2e0001352600c81d40000601131000c4801480340c030f10f4096120071040c01c0c4044c481251008407640100c1d40c0c480010144454011004994001d130292030a03503a9151001c81070b5801031200c10b62603040600040c8651602c8005000d8000d4580300050402425501242207075000b40821f490f0f2008402040160720400c0a440c4410402403009 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 239120026 1250 239118776 239118791
    0x1002151006020c0a08030724020d1b020f21120705030609090102041d042a050f030a05070b0f0409050702101805060403120906060902090103051006020a080d06080307050718 76
    0x20341c40e40100d00c40141030202c485640d0701114004802c234402060704000440d91181c8806191000382040a58212103120030389058a0150020540c1e00c0240d480034007510785608070202070107100469094141a00d6002e02049d148064a0094140b06040c0b5071600c981d01c1c01d02000700301c0d000500510b40e00d19a030040006001217042c0d001e01d21a59400300358650001c5c0c07a0f82c68107145480b480e00c0701501ea4140c0340b180d00c40031191124100c1c222842606c82026103801e500505440d45d0040308060300075400b07840100100c4002c40c000b0311158204065190038940c03030740c10780c0f000d842c01a980040141c0c0000e10201099410b0310890380c000603041040b20800c01d80b0b1382ea181d1901d10081014080c0300c41c54007007500d40d18280c1c0000c1d20395540b201e030400c03403e41c948107902d000303400c540d400d80d000914160000d254200414001c0381500c81c6034000340403140055640c003107154030110640c40d0f960b8454500040120041010741040c034030820140c030a240c10214048507103925005070050290802c41c1703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 239121276 1250 239120026 239120039
    0x40e0102070b0c0301050a082b050c1609110403020a050f0d050304060201090b16080a0902041d01150f03080304061104170a0204110301151803120908070509040308061002151006020c0a 81
    0xb801c640482c04028480c50259028405550b203000d903000d01080e50152803860703003103e04543348010035500e00d0355003040408903030b481145140c000c9000080d000001d40d0014420742c0342c20401207800b007200606d5212a50340669809040d60410340c400005030391104200b030100030307114021551241400c203021703410b021101002000e007040504042c070407640e11440c15003035440e40d070005409989100c0d0705411420503640790600910400c030310b06143c4a00380402242d4091548082000c480d0032040e06811500c40d40c03119070050915180c0300c458000104800149a030328010300004181c51003024004d070040500620066032044c0c006861800020401403702992001d02c2c00e05200252504100203076820000610380703c00c0d60030180a40d88145846030f0880d0f07000c031312407054600d06000da401c0c1a03594400d00205504c01d59005000c220203d00140980c1450161314410844078412103600303a050a5011186520a413150454542c2c02c240078040143c0402c50051107002c11789556413980e28090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 239122526 1250 239121276 239121313
    0x31b090209010e0f03250e18060118020c0a0305070b06180112050f06100f0e01120213150314010b0109050607020d0c0806010b18010f0e040e0102070b0c0301050a08 72
    0x103809520500010340003034440c0d2001c00c030190440c2e2003001ea84030700f00300a5402c0304c030b928154070400311000d04200006035241010014454080d090000801c822b90814007034241c810001403003600301d80e0f405c0c0608410b46004000203580c40d0b00940343d041c0e60350201d04024070707481c000412013802148000e044180c810410280c00381100c1e1841c0a4244104203460480c0c01c2241c0510038841503c82c0105100350040002c0314041200d8155940c08001581d40c14441c420316006d100c0d000c0320500c07908031803015082c800f4018030706186c140b10011340404180040688080241c105680c1032124003102140d4003024840e001110308c090824010091815000070b82501c9102c10090103242888091401c1006071a41c5d1405006070506503601503848100441e5140c22a0411040180e4455450304e640d50040d0000010030340560780707a81465000038240000340c00387e889860f18640d400c1040c000440c2103814002d000b1001103003807075520351400c01085003450594004030100d410071390000d0b003102540d9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 239123776 1250 239122526 239122547
    0x20306060906030a0506011403060f010b04060806011b2d2301020c06040b071403060108062809060e0702011b0f020703020a09020c0d03060501020c010522031b09020901 74
    0x49907800220340e00d500103e400c0071158107004210744a2140042560418001c980382030640070f6046904541d41c02c04688410f40c0f00b84070b014521501080180704e070900c00c802c0183e111030103040c521640e081c508c22440c0c1100108a040d988c40303103000c003140b20303810060745100302d103200101b103c10090b071081d00d586100c030032003103404000a0f20000840174410340030b406881004090205680291609003400010100c003140e00b44002007607041415150441c48094a000c0e0006a54041e0705076610000d000780b800b03540d43c2040e681861490503004240385d0003007460252402c41c1d800300d84c1519081501c0c0340c291018242c0401c0da410090107081024a5907210f130219885880c005044196440c020307400d00607035403c0603400600f040d40c00b1410340380540083c082c10000d4030032030721401c041010031801c5900c14040c00d0b0050b00101078840e040d43c0b28001805a20500000e5003100300c90003e8000d019141590081f6506500c0c0c02e043c0c20030402040c5224001c050240d0f0651401c40314400090814004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 239125026 1250 239123776 239123779
    0x619020910050d090605040b16021513060906110d061203020a0f110315090d0e1c17070303060810050c09120f0607021614090c0f0f040e150d02030606 66
    0x110b09283d010f001608101051034022900b01310310700309400c004441102c200c031402c4e005c007000260541100e1000a010500c07000c3c8021041c400c0d181c0300c0500c0b51540500034141c6010f9101c0c00c01c0d0002c11807610400c0c2082501c60455992404900341c03d40955032a5400b8480d10640c4000d00c20111f60042440300c462940132060a03420202c03844d02c0c03000301c1c03038011f00d5070b4151091a0b04000e50340407503030625008003126422101115903002d8215480c000d00602190464035400809510b0075000200d51000c42c400e6065200d0180c40c03540159003078000003025000251241c0c01041610014011740b00703044d58060051099281003824941b140c0703c0c030600300e401081c1c49190124492002e106199003606250283d40e424204040c00a5960301c1d1600d00001e042c055910020b064600c6549500400c440034040d0f00007651030004c0c0400e00d0b041821201c3c0b11100802408102031072000040c0040c0410000f034100c50304100304088001c01c20301141600405042c07640d540980e90006095500030340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 239126276 1250 239125026 239125037
    0x50c010c05071502070306110a0c1104020d050405032d0313060b130605030c040207020f1e091602010c03060305031b1e011406030a08070f020105040b0403050619020910 74
    0x3058589149007800b158040340f640d804041100d07010a07030219054045a02a000500804800003c000380728491100d508001c207600f9042c580008881315480001581c0080005041a070300d9420407060312070469003100c0170b410010b00c2840381c03081d20400080c0d9400201c1c02c0328100d10074500340304d99440301a11450079507000070146010030220f0340014004040c041c001a02003540d50217400c01a00803400760a00c20f0080c1c2e03c2d0b20143d82080d100ba19601d0350001d00683c00740c00603e0a0044a494140c40c0034440a0301c05481d0b445c2c0e48506081034081c5200e61900b09105140220007421076041002e500c0400d810000c0c1007010981c00001c0e01c00d00d04051542600d002140c0704c1003031602000c0391400d04080450300c0b00c01c41c2c030078042d1301521791140c00d200002010740c1c0308000c16441d052803c2006100c17841c107000300e4022652121f404540f9502c103040c814507198554099002a422951084a156100408100c0303400212102c481d0882000c1c1000d6041000210001d95180510901c1c0010440c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 239127526 1250 239126276 239126297
    0x106050309031b0604050c03010b030c1504050612161d130b1504080f0c180c0c060f0402031902130e010b0d0f020a0f0f06050307120608010506120307050c01 69
    0x303505000329118071070030310200380c2c0242408028035121131080b1020f80741402503410b5007605003818081c0c0fa101d140014050140350204508000500401e181840c2415500380b2020495803038103070080100d1140d11104441525104081c0b050540b8200300b01c4c402c00080c030388101c1806118030354090403030307204403221540036415081900c021320b000d0340102e80c030030304043ca0381da00d20003440007d00a07100d40c80161140c0780c00501c025640d561410410030340140b1810844844072490008150f00850188503207880c0000404a10745411800d542030040c03042c1500500c0110b16003000943c90b80340d20480b030314044040300e80000b00904040c102256519444055101306001c0a6000e5203003050018000ca03040c0300399041108a104880c80102c0c09100c0c0c1d8100820003c003200070f070740c040381c4000b4031052016041150880d51500054481010320034100055501d00d84140075480181441000008003450b00c0e000300b0201a40005080c2c5090700300700840d6000c9500410b4480e2040d00a08100c903110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 239128776 1250 239127526 239127541
    0x3031407030c0f08220f05060f04080706080a0b1e010f031404050102030a0506010804080a180e090a03030507050a1b080c0d08070f031e05040201141303050d03060e01060503 76
    0x4540300b400c014944618a080803040100c00d501134480c050641e1003507042d4901318907031424201100d009440310f5030f510740400c020500d00719009241404010044c10304242c2d590315128074050150b0440004600034070108500c10b4a04d01c030300001008200c0e4007890702150400d1849a80c800e4011250401000300c00310001240241c1001d40c40035a15400c05006117002d081c5207000790016501170f01d041c1d0416003c110700d9071203102c419012700d40111307106290265522040d100132562840d4210140c0d04a4030000b030092040c1c040b28440ea4500c4080d048003a920f00d001000c40798020003440520100740404000c041d80703c0d41c0480c00da00d24010050749090b86040c803001b103003c1c8141c1c0d02035a00c034280034004000c5d4000c0030343c4d0140d00640c81d140003084804205074103440d209130a4050095501c03203d502e2085070303030700101c2e0400d00604014001c1c426070300e4100709560110103e0b01d80085000810005c100c020000c04060100700d1604010542c01c0515013013203400103200c0c050030400f0110101e00300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 239130026 1250 239128776 239128787
    0xc030501060c11060c0a0501090b1810050901150312080105010203160204150816170c0112021318140f10060503040501020c0105070e100201061a0c0a0807111201060303140703 77
    0x20076071714800c13540b9804035481e2290180002e56400c031144074440d13010a0030248800d4051130400d41102c007a22036030384d103c010391004140c020041807a540d03c0d64400e0755002c04401e21300c4042c1d8004d4070f43c648c107001ea047e8064440700041e40031354110f500401c10004003c001d0142d4031009981101e000c198a440d10064040143e02c2d900241004c4c02221495558140c00044043c2201c18a41d00094840c082885035070f2510202c2a0040c0455151046c0380c030308840359401041600b1b04020310f450080d80300d076070000300e0703000b05940b21040c1030740d40c14204002902e041c81240d00000311088002140743c5400b514581038240d120380014000e020003c2820440e082d0150f0700243c145000810030383c640750200414020842c5009801801480c50041c1d49901c180143c1c0c0079650811900d041120300c0074039103d00d1b80d11900403410180150b0617410000386000700240201401014074a0b030486154003040b90107134a40c0c50a0003140e00d08181000044e411400c00412020076500300ca840d410300e0b0606461 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 239131276 1250 239130026 239130037
    0x160506090420182b1101030e070306050108071410050703020a0602030a021e190e0a0801140702010c0f1e0c0b09010507080c160b0901060f0602010f0c030501060c1106 73
    0x740000800c6680103a03401200c80100d003c021140d04030301402d0300e140c8440d81c040513035118041510b003681c4040410458100c80da01d8031010300d0000340c90b0b0000c50a040c10140aa0400c45a00c1e13118001045001c00800222025084902900e4170803e4648000f0305030344401c02c006c00c2402404500f00c1c1c281802403200c41d203400d8100c4001c0d0365a14114010300000c1d409619800258050743d1144000401004180d88101c064054940c2c2d1b040c480340400d0320020130401e0010340c4030385000070220340c440e000e014400701e14031a1526402c850900740400307425100d48441c0301c410000c0e003c0024001c0c030b42c0460700b07019011105124441e40b220b0301000301c902d001c1030798004d44001c0048040c00440d440561040c0d1044400344d03210f1034944c4036202060180d11034181c4140040451114050100300d0103102c09400c102404c000140d031560720340c2001c21440d52035100e480941d554440030031640c521406070341407609151804001c25030508001500c1207149100140c000700c00007140540300d4440000f02c2c0c1303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 239132526 1250 239131276 239131331
    0x609070f051011030703050702042007020f040b031504050c0f22020d0c0e04050601030527010b030f070e0109090b01060f0e04061806050d030f08040503160f051605060904 75
    0x1703540c1d01203810b010302581c2c442481203018500e00b250100ca0300d4010800c000420010b441d80c90b1401c4119000c000c200d0701c860520b0380d4060f030750320900e16480e5000c00c44008583e491140c0b00b846881c00f0b040060408810409503801001160843d215503a2140d02e00d1403001014501f5100c0e038040045041c00a005000380b20341d00501e0180440350321508811411800b02080340d0502460fa100c0c2c00440548a00781c800030f1103040d002d000049000100c580000245800c80c00020311114194006031a004200b1030070405034000c8a01441400101c154040c007504a090050120900c41e98440510320014424207082090540781200c401c1d2107081d8042c46030307100030801d00405898007409802020906c006442243c502031000402e07080c00081c0a80032901600d50110020303070940c060351101d034000c104551078081049211024961101502100c1380103800c40c2c6d050910707a01e03009103400d0441009021094040f03030204140e50700d0100700c0f8240c003400d032070124613105801c0540c40703004010b4100383d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 239133776 1250 239132526 239132533
    0x5010c02011b120c060e1b040e0a020405010b070b0702120a0c02130f0b01030b18010e10030605010b122a090109030803131205070803060103020702150a110609070f051011 75
    0x540405600502c0124902c0c003c0000300801c10080c15a07958501c0b0182180318034500340c108031f48840c030b45a8040c0c100c104030b010981d0004c801c00d9000030120303032090300301140741d0782d002c9120003d01514010046d81308415000511034414440103488247c05910402c00411608400560854954410310190401040d5080c0710034001920718070080d158040810380003031302c0c01148000510780304000c0f40e038010f0001d55548152742003440340380f45110000c1c9074164443e4100d80000004116100d5030340200b00404015031200001d880c01c001202024251180366007020b121004200e01e107903821107140840324402a50ba07000b100040c0d4ac410f170558406000c1c10404804c01c02081d03521420050050310a14004002e041e8140058034035000d2014040d101900c02d00c00107003194000e500420000b400142111502c04010759030700700e00e52041c008100000d5000101c0a00d54400700b00c003d8000c181c60380034060450608291005100d841c3c0b049500c186180e0b0040c0341c0160046000a01e0300e840388054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 239135026 1250 239133776 239133803
    0x4020109030206030f04020909070b1207020c03070b040f061e030515030d0c050d0807090e1005060a05090909010c020a0312020d0507020d02150115030e16060905091005010c02011b 79
    0x200c1201030380c06c0382d06074051280c00d40021580e6601103175130303030a48080301d507080d0034001e07040f8808009160040c9080158812000c0e056242d036820082d110007050b040181c3c0350f40394104100c1c0580c401c00355003c441806040c218480c0707407008200c42c0804070301c500d280c0018182d031100c070711609146a420849425014036980d8990080d444803074001c10358080c000300c803071864046c901207900b04c00c102d803d10001040010103200f0540c042d1000750700101c044401d41c1e2443c0e102c0001540c0c9078004c034070b101301003080040d109465040c0300c0d1020b1ba1042d5400c00801c0070302c3c1142000b0b5103c1c1913081004003048000e0b01c84403103074407456048c1e805e2034400038400c02c6246000e01002e5503070118090090050702c40c0e0000d4074004030154003504e041c0da502d6400c4107800800c1d55401e402600c41990381c0d421728090301e82da204100f04800308241c000c00d0716a0341e010201c1e18080a004c10b00c1e1001d002840142c0780040c0911940e40c0040c3c07011442c550a18141c81d0a01d0803106114201c16100001071450048621 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 239136276 1250 239135026 239135041
    0x3080d0902130c032301031e0c0e0a1b05030a0c050f07060506190518070c1a01090e0c15030c0408010f090b011401090603020a0905090a06060807140904050402010903020603 76
    0x11084809141c400704185150710802c06805c0710988092031160818000500002c5c4080840960300e070f40120440101c10665951003003002d10fa50000d0250542050030410204c0050241c442408041881300050962081c80286280300c0109201030b1217441c3c03111142d2041c03241d01100c0384541d0304031450b51145110b26040d0090b10040d0781c114460b414408020a40020b4240c0401c01c441e00141614158050003071812010300009110000740150003040d580403450030241188090f02c0505500e0300da43c14071400b90304580041c40e48540a074000f80925080d906c0703038031540c03181c000c40c0d0003040d40380c1e50307094441d40c4240300755017092000b5404d02d041c884204106800920f42c151003035502490580e00e40761251078962008038600c0c0083c0208008000381c9020790700904003401c4510b0540d00264036000031030640b042c16601039400030b030b443c00c0c10810654401c1401e60000f9052400c2030b10030340c25000c000c00c6809122003d0348500c1e03413034022030116070145035801c0c02542d01901c0340361240303056030303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 239137526 1250 239136276 239136281
    0x315010302030105010e130605060d021e0109080706081b041805060427061e0903120c0504060f05131508040c0503071d0405012003011805010f03080d090213 69
    0x4001c80c0a58241030010804207400c80c41540302e803041b80000d017010301075619030380060440a020703250052000819074015071034550341084440504940303080c001c1c4d40740c0001400c0c0d10132540480034a0300a948240086a4410714141d00b0601c2111030500c918403607803d14580e07209a60091649904101c421703000c0740c1807a00406d2042001729420000260400700a0f06843c1000042c07024581b032109581d000100641d000a102c02c6d084242d044900e4119030b030642c2110000c603001c1d004541c1c445002c2c0c518034554001c210301c0480070b00c0c000d818145084070107060100100300302020701201203021441082003c68284c001c1c005009070a6101c15030743c8020341910b40c02e0f10151907005202d207010405060004015040307401294002e81c20800d000f200c41010040680100c3e0f155403102d581e40e9103001d503c10700c0008503441030311180e603c0d40360180000351403007480c0c2696041401d0100400c00c00c501010a032084030b420466880d0740c1c2101441543c010100e21000a50145481c0038044000f81140d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 239138776 1250 239137526 239137529
    0xf0301050129070201091809061e18021c03020a0506010f0501021b010f05160503180901170703060c0512010609050f0f1507031103160b0c0316030506030a02031501 72
    0x2540b20740d0141c00e9445801c012881800d4000c2c0c0812055541002202d00c8000c2c0300301c804418000015013030a1f03950b0350b032050702d12201801440420a0404c0842d0345520f10940089a1081500c1c0308060fa0b258045842d601c1c200812404020303485000c102418024030071460031a034800151600c4e980c485034a044101002e004550043c030030300b1020382c00002000161308821105071a8019401302140040740d050340510782100100d00a85000c1c000074808102034644d00c460000c044990100e00f00c140304a409059220090119400440e68800c582c00303d01d03201503a4000c04045a030302c903040c2c41a9602c1c4a8202d42882168846000151140e8404000070503107104880800c40144013a0402c07650344840204594444142071000913001c8154009003010f0b44a41885000400240380d030a0542d04581c85411004408201000c200008003030380c03a90282d05a070782d113402d504014000300701c0d0041e40c205503002d02d540d400115107107660801c4080040359008003180c2d00007400701841c46804400703 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 239140026 1250 239138776 239138819
    0xc03121005040c0206180a060207121803030903030e0a21030212091c0c08060408030402040609052511030a0203040305060603010506010c03050a030b04051501140a0912020f03010501 80
    0x54030011070549441e0080460b001030303a5000705515155a00e02800c1489500807000c6075110340080000090a1800541441030045460920313840c245c40c400b500301010700c40d2200c00c90000460500001b0b41003140542078035054a070418800d14540f0200c1c40099490300319504c81b801c403d1100440038421401085460700c26130070380e0b2410f43d003c00c16420038000c024107560710001c41500e10502d07680301c00d01759a605015002000e031240e90350780001d00b0f00c071050750141c811741030000c100310039401d19010342c100918030f03110f042200789060303100d042d2102080c00d03104d01209848500020000d00c10840d12030f07141c0800096076652001c192010390b803907100b0300c000c176001d000b1540040d08a26040c03150760700ca000181c5030309649481a40d012102c59008908003410716603240c10f001d42a032214890f1a00c20302020740800c0c0c1d6522000700141503600b903424681e803401d5003000010000c940c007100f0b0004480b80105950503a070503a1000804c80010707000c0300f0360950304e04800060186045c2d081503501048 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 239141276 1250 239140026 239140051
    0xd06090903021216082d0c0f0714041a10031a0a06140c1005191a010e04150506130302010908120406050a020f12040f0608010e0a09080c0312 62
    0x1a0600101c0705028016840c400881d0504910000c02c0184006100f40da4076000b1a41c01d94070300c00404403040321b2080e058150100041a84031010b03404219104008203540020302c1e401c0d01c3d2100c0c85100b04000800d16000d2030310396400c40c0280b11a58201d030100100180004015841d441c1c0c001c00a045d20b1300c03071040307003616114a078020b400c044104805403041a07a54941017640030b8030311030141d440b0b03c0c18000e05200740402c9842c6c402b030520071980214200f00100042440c48a00c0758203840c1c00744c03031005040d218041e880c0111707030f044080e82e41c21103c25a400306130200b00c8801e80c402040c90b6400719030084000200d901131519400341880903a8801d880b54218103071206000350341c41d21104151401031104010034050180030380094988502c5c1071040315018110340c90a41c0c2005041c204200340c0490101cac09019101d000d48505018000d2460880c42c698500044c030524650042c18207042c0c43e548035044424004034000700c0c4e80074010802182d40e15180784032142c15803802101c0300c9654030b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 239142526 1250 239141276 239141293
    0xf070f0510140408070204091a0906070f030b0d231b0909030403050303130f14070306050c130909080909010e0108121602041119080109050106110a0b06060d0609090302 74
    0x52459010b64050358112009509148095003400002d100705070003699024210b41807000c140014542e0fa5110311407940c058815810400400b0704a4440307c0f542800345410980465403e03103072480c100c03203003d03008400e42401c031004020f40d00d10103034407069001c2d46000c0c1e80b0b0b0807150300d58582085550014295a1403900742d0701e440045840c1e0007a400000d00e15082000452000c00c00243c00d1482e03d1f004130750400c0040c2d5107981c1c50000906414000d502d03078220340e000f0001c0c41164450301d0f03408100380740100d28121110081d0000866030b4011400e03859500d0507024180015082a101003101c040c19003402075031a01e40c0307010352440034416212141b0440521801215410040c0c45041907600e43e1038001003c40d0f82040302500da0b0755050000a201407200f81c0c07400081400c1c6c40034100154640c0d50312541000813210030303100160071000910040c9504444d080000107041040341c0d030402c1c0300b1140740c0c031044001252403140c005400f01550030300e54041940303030f030b076500803803015101e9000c441200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 239143776 1250 239142526 239142551
    0xc1d1216150309020a06030209061603030504050105010e010b2703010507051e0f0f0d1b0e011106040201050304120309020d1101021011032202040608060105091008120f070f0510 78
    0x102e04000f002900a900450100151400782d0050070903144000d0403036007000f5000e42248000361100303200f80d00080e2903900340000d020702841030601400d026030519001e581030a0080f100e07846040d00076015080105111076a92102c3c4146154148004000384500e0801e240028459001450000b0249040e40c42c4854100c07001c0e8202c407500c41d1300542150911003150988070741600506d90300340489442d0a140740340810b0202600c5070340034135a211107003411010340006040201c1880021002c0e4400c00c01c0c000582c1e000301c192540181e2000c2c4000100c210707000d04901412005600a4212103c1515842008003224946240090070303800c85200780f003000d402e0010b8071640e08150500b11010030100d0151081a1040d00c0d01d00001454004141040d502050844500d0360080210340c00020051080340b403c0910755810034000c040c503940c41070414141c5926600c1501207101200703800501546100880810707145c1c410707000381d00c44414141c6420410344a150f8120211480b42c80c2c0078480995 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 239145026 1250 239143776 239143781
    0xd0627050106020c040b0325080c010c0b0606030402010c05030403150e03090d0305130f142404050d03110619151202040b040219020c03060a0c1d12161503 68
    0x12540702d907004000816800c0180002031210302034440d018010348084884241d148441d00000383c03084184094414a0b105400341082e48401d0101c0c104052070f1500300210310810071890f084802240e643c2d690f612a82b0050b16054050071000f440c9000101d0004107000801c1d01e5400c45440d2983c0c10b01c038848901101b47c0c0c480c803030568010350000c256030a60010a204001030020840e8905006403035646809a401e048032032548080824081c000030094542030215141d1484451145460412303d000a0a41c01502a0b401401d002d034014103503440c2890321492103100c80801c024155030260900012801c3c985480b8040c2d00c4140e1b00306400054807130020a501000c8607006d8000e11004481e603800c20002c0c1c0074480710701303078040c5e000d0103007098881c0f00c11401c2c00c100301c043c0c0080081c00e40500c185030900d070000f0301383c40840e40703040c19101030990070005081040241d41c18100f8521961030001e810f11540c0102074825114034003075103000b03240c4c0b280c506c0c0903202901100d0402200f201021000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 239146276 1250 239145026 239145029
    0xc0f0a050a030e0a030506040f060b04110405100923011707031515020d140405060f191704030807142b0e03120a230402091e0601050f0d06270501 64
    0x141e507c02c400183c0418030001071080c80a10039000840e0500c580030004080c1d80e9801c00e8204201d400040820a0385000c1111041680c031034104440424038004416800c850b40c1c5030710020000c00400205c400da0310070b00046022003c040401e4076142030001000b0000d003920700c1062804010803101007a0b42090704400c040c4200380354018200d41c80307903510456031190b45c0c40d01050744502c1030001041aa41e1702e4080c001f1707819011743d1a500c41701e021105854100448400c0004d004480c0c528000c3c0c1110305500b6548035806040032141501c40031004c54044c0c2240c0c819012803000070602c08512120488210300d140031208031190780381a2003040c0c60481d013201134a0401d507401005030860000402c1c90240d440501a9400902e4901402c000c500e145884250700882c105443c0801c0218a8450750454114032040d04200038189071220b10a104d44020700303010b040c00710211b03c002c0c42c1c0c0d41d0b02d0300b110132220308002c06104407030b81c85d0801c4547c4500b400018288004101d141c0c01d40d900355108090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 239147526 1250 239146276 239146283
    0x3070c021014251401020a17010302030a0305071a0a050a0b090f07080705040f03050d0306081606050306040e0f01020a020139120e0606040f200c0f0a050a030e0a03 72
    0x900d0440c083d600142c03091440d81041043d103808003079110105020b04001d0352610351801c005039940030918801406403012000200d03200c10041d0060001d43c0b0700180d00700c80681c0c1420300565905140c00d040d20540c4840d0030480798609050204081c002481d00018040c00510200b40207404101c010003803145011254143c12200c014001000c5d1807003a44d6407500000c550034118980b6854000003d12a0010340003039070640e0280c00050401e6900d441440010400000900415410940c01c0740480742c55104081c01c10a000c400305a60790780e41e90001c210000030104a8074a42411105e5501030340100c0e900310055442d04200901d411518007101e031184010f1404082c4d101c04141e1080f00302c414407078903041044511010105461428405c80f282101080c004110a14000041000340c032026042006a1030070076107922000703011168200001c1c1008034070345403581811507029203000d0000000148034821a03850780d061040109007003403201c0c069a51031001c40009c0c1c050199203800d074803005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 239148776 1250 239147526 239147567
    0x60506031b0d08040b03040c0e06222a02010f0b0108010503120d0f05070c0506101406091504060906030506150405040218040c210c021e1203070c0210 66
    0x540300d0345007822818185920860f111400c0030b032030320840d081ca9081103804840441c42010700b4010640c8038140e0325441002140d604515090801e405800591445400c600701d6803a040d8100d805445852908017100040f640e5400350303030010000034080d11071000910401440c000c80d01d0555440703100d00301d05942002d0001c0c81c100e54000c21641c2281d0100070b040384016510030340752010904034090540120030300d5503008180c1000382070060501402410305004c400c0350a104010b821119020764003502d004494040d120b540c06404a0003061702d007442903100007800580403c420b43c00090703170070682d072507030b0303020016076442009015114685481c000380000c400c0c00100035030f2519400502540ea01c5000541c0d20019020200d402c0c1c03403030611800007240a005441c1100d107181c40d00c14128144030107041c07200b401000b0010752600002c40d5501d0b0343c80000d6402d590100020401d102c1c50040760140c1e681e45e032a181400409414000b4001ca01c1804c0c03102149001500c1600f2402d54200500d1f200f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 239150026 1250 239148776 239148823
    0xe0619061418090102090a03080403020f03060609060409031106010e01150302040b07020f0d170408010e0601050d0311031905090406230913020402270306100603020f0c03030702070306050603 84
    0x507415000000307040703c0075903400308078904494031140381200007140b040c00c10039150381c1103104103e110901c0c02942402503200d8000c006c030540e108803903503412220941c2c0000c1c0a070307034a0908644c881e00c0032036501c05901c615000025074070541443c9504941112000581b07013805007504409a1040307101d00c0c0c2d2034690901050b809441c20740414000001b00030440204030485903210b40d00740034980d42940b2026004101081007800c07e002d64064070403000c015059030340c1810001a2a240040b2001d0100099401280e401d2601001111510310b0000c0c0c40008550700c0400003841540702e006018082c03401e00300c000072103c9884801d2554103030442180c210300c00c882c206000e14a2710060607002d00c1140f80c8044005030b1a28401005180c00b00b46c00c0484400b50f640041c0b001c41d00c2c1c004910701951040d0b0811610000c40c0c00c50805990726890b000d40e4544e4012562075850250b00c0b1041400c2c000081402045600019200d0441c1d1240e2801d0140341d0701c0f2410184c480c0c0c10880c1785889032039681c50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 239151276 1250 239150026 239150059
    0x4030209091515061c0b03060c0f0f1e03101d16030906060b040f03110a05100c03030b040c0e0301060e01270905070e04050601090504030e0402030a0e06190614 70
    0x100da090300f4040e000390b080c1200b00c02c0311a60101d1341e521380b0182a95584501506040601c500341d80710940c0040146001d001401d08003007407281000b81c00f004000843c0c401c80c950724090307410004221400c600d546901b0103502122107001148030f0003561860001d04074140401d00d500040c42010490f001c51541c56854005030050700d42d502040714070640e240030108002003450041c3c00503142c84100c0a04060561a2441d0b100031000d401074032404269000700401c0d0f5980844818080036407030004503200e00380c40c05070003402d0514051980f003030800300d04002c2c4074cd00c034001c10305000088009100c00d56407111a20f10814081c000c1d0f09030310545240030590b00c00d100610010341c0d510007170002400c20b002c0c0c8407e1304007445c0340c0000801e194003c0030f1000f80041008928054444003004110506007681e000d01022203c2e16624008c5070084000707590308000754820001582e4080070f40c1c0c100d18045550802224a004410300c0b91071900c600800c2031048058880c08201d0042c0c1103000b4540c0031078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 239152526 1250 239151276 239151301
    0x120818010e091f030b070306060e031c0c14060f060f010c050c060703050d050907031406070206010302040e0c0d03020d02070e01140919020a0314010b07210c0209040503040302090915 80
    0x5000a14003d0f01c00000400200025842c5110300c1031039a001509505040f001040040d00410f660300c80ea1184040514001c21914076083d100b0045c2841c214582c0649404207a0400c02c03d045820390084000f004112407000d81c48911900048074a84052400000191010401c1030806030103a4410700302c4400c0d03414110028101c2c24040d040c06400d082c465003490341620310885100082d0f41000c5d20070401c0241c031940907039044500d82d010300f5240ca0312039402996001c2c1407002a1003141c8440784100384c19014809400c500d400508160b566682c6ca0401035550090401d41000511403e90001241098050801d059030940b00c1e19102d18400041000030000b07001d4140b0200880e4052404141000c42c03004003640740c840d40303007c038501c0000d0503c0c0d43c000301c05a010010b2408101708900c009400d02c6002000b0403000100060246041c00e81210070048925009402100036014030080c854008068400c80344219401255030341c2e01c80707183c0e407290045610f01c200100c16501107500c695515 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 239153776 1250 239152526 239152561
    0x7050601090f1512020109061d09070915020c12070302060702060327060103021305090c010f111005010f0803040501120e0109020d0f03030e03090609041104120818010e09 75
    0x2d840c04503080fa0003020310544864a94443c00c40c60324010382075411940c0005621000f00404d0410702c100000c41c0075046100320307540e129503101e90041c000186d40e2a003e071310b820f40a80080003c140c000b020070030001e50f44400e40b01800c1d1007409807001c140780c0bd1600194603020340741d01505107410007001380d00703008003a040509200c048100404002d40c54407909042182d804251000804041d450340c01131014030840c411010300950300344010440c403400c000441c3c030340c00700e001e1810750400d0850341d004840781030b03c2501d245a14011222404c4808001d50803141c142d44207544088400c59440403d150f0742d10546c400c050220340c0c540a20510141d10340d01886075804080c0000c5034503005c0364000b03211100ba000d0120788941c620007071141855410b22aa03081d90480e03000543c42e101007a4009401b40c010f45074001c0c4a6916014098012406031054030024410010590b0644140789084021900019660b01001c100800c0e8003c580d841651903010182019003a04c00c59200c02c03540603441c9030036 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 239155026 1250 239153776 239153801
    0x7020f280c24110a030e090405011113090e011406090c07050109060518070311040e01061a09030d03020702061209010b090711011406030607112a04060b0705060109 72
    0x19000001d00c9892240318244014508185544000401c2c2e0b000e0b08142c5119505030071a44440e0b03000c000aa000713001c8003560362003114025030698440c50040e000d0044450a41601e840124510000507800c003800415928401001d0010700407152210703080f00c107540f0201c01e802c080d090214841e07003401d184083e08103c0c03a008480c40d21019843d03040c2074601003003080b610560f4420410030904450f0b0030440c4100d000034040e148552a5450711150300b03100b150b4081c40fa5540702110b11902f20254000c40042c4005a10469541500c500058098200c1000503010380170f00c9503050606840f0b8402c03a0341c5940e0090442d800c00c1e00c44c0d200402c200d1070051040031030350750310306007803055903038107190144a0000e60750f0b91202203441820407401e5a21000440d00849100c40c01e108080c0d40119005070b00c407202d4079000304401000c403442e80c541100c0d81081007051540b844070301c40c0c2031b150b1049000744e00c4059034180030440d41e480f040b040d54031440310050302c1d81c0c1200005007d10b08494102c0c5117080c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 239156276 1250 239155026 239155043
    0x602010e12130312090f0905060a2607180c020f0a11060706090b09010b0a050f13060509191b020d081b0f13050301020304031b05030415030507020f28 66
    0x3c0781c0d91441c103203110b021480b41c0401c200c210104101c000d1400003202500e0032443c20f02490602c10f006c1500040036010728883e0040080074201d038001140801c0103840068003c031110300b82da42e0464842c0148060781a0307240c5007000312015a042c0005480021340d0079a00040c0303841480c2da00d0340c3c587d001440000c0c0784e10000030001c0340040742c081e000350f48440c0c3c007030380400d10241810040380f0b0071104a003031441d00522010001700403e580b5101c41045040068904a0104607107190321001881c440c6c00203a4070944040c1403189c1c140911340102040103c54104200820b00d0700d0b1800ca004c040e41c4442c80040c1c4c0030481820240d4428102e0f6034001c1c0c102c20703208002260500d16074907981c110040703a5458500229a81200e03074801004ca000800d410303002140346050945008181460b0f0422002200c0c032018a90010000c04200715001000400c10000c60412440d200402070401a1070350001845118140c84040034080b421203403030ba4502c1000b1040d10365500d030030700c04416008000e4030003d2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 239157526 1250 239156276 239156279
    0x306010611070308030106050309101a090c0d060b0a1710291605071202010c140a050102070c090b031501090b0102070521060708010509011404090f05070f0602010e1213 74
    0x401810165007e00815201e440e168502024014601014052000140c5041420807607180b15240b170301b140a40819101d5a450381e1322450701c08014400d03181443c00c810305e4044001042c0c2583c401a080360501030744d490440c0381581d40c00264500c0f05461a408140c0018001c2101c00c013021a48440c48103032100d0040081c00341180e00d8411b80003001e0583c081103070095000c040000502001c0d02920710f903002240d11088a0b000244080c0340c0131402086604801075403106407100300041014190301000a40d82c034015442c10905120440c0308480465017003040740d9904d8600480c111200f1071000c0c850b00039036880c0880302c20203040014652415400784402c0171407251140000a98101110601515400b43e1100714900c1d05000a10410800c0480c078014000da90314500c2c000e04451030b040d4540350800055000400411845100915604207103c02c501003103004910740e01100d0400303a02042813a950300090f826500c1c5030320901c00c542c00200b0300944c0e9a40c0d0b00c016021480f00c06d0070411559 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 239158776 1250 239157526 239157533
    0xa030207110d080307200601060509031f090b0c03040f0201030f06030b09060708060627060d09051f1802090c1b1b04020c03030a050705160b06030d0201050603060106110703 76
    0x200b030880c054401d020008200901141c100d100d682c00d0016081d0089101c03030200d1300c041e8403100103014907070801000003000c10715a071341002035031411070b0302019811141c00305100c841c005040a041c1212002d507000001000005071400350780c0308607004840c90440b51000e9004500800039440f200c8150381d990b40000c4003080c0e02d02d24551041c21028000e1113281400203018260703400c02884544144c00400000005107076940d02c54142c4442c0000050307055803c100002c0d40307402000004800f852512014500303004002030b0300e880c8650032036071a4149506401d10303c020b41d440f08081c1007080012407524801030a101400544c8100c0c01d0a9107420f09544050310800450100c103001c1d1390f40e203c0c8007494403000109202090781c46080700c0c21031608119600c1c0b1074a80c040284403072061030743c502c0084c41c43d5000d24111401084490084d1034034917920f18000f07205000907543c1034040d05c00c1791403000b075941c014420580141801002440b42d0780c81c1130001c8803112030651080100340035a000c0080003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 239160026 1250 239158776 239158789
    0x903040911030402030c04153003020d09080105060d080304050c1008070f020616030e0a0204061806091505060a0e0d0c03120c030f0507170a050307080f0c0a03020711 73
    0x18040d070364409640303081500401d8540f5100d8922544198544110b40c10380d03c0d0a08000402c65621500c0312541c0d0745c0340f183e1958042480030000e55042140414482010b5010038090b101005613228008030307607101e2000f01e0890b2012a0f94a8005186c65040b4000c95024800303190321510910844900c214004d000c103010b9043c40c4d4804020920400c140300311075070802d41200c40200c0e03178802000140b501c603440c1340c10320b030b00b500018003810b940c5c011500c0c0c6c2070f009219151111fa0060f10038403156549090550000f004403038002d40c1945440d202081020b81801590304071603031000c0c1c0340d0005003810100480c0b40d0021290900744400500c213003502e5100d0780002d260060182c10007070916855401e220460144a0101d40108200f58100f1400250403200a4069051614090f0f4541300b40d807034000341904441c1542402d202c40132038924842c50307010b0011485a070042e500c6910a8603501680b030040f002c00d880340c045040c020701c4400f881074800e074080c090b0140030b0a00354514299050104a8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 239161276 1250 239160026 239160041
    0x61b09040c050c0d030e060c09010309050703200904020f060a0c06060801061403010504120f020a02030105010e09120a020c011206050603161d090103081b030a09060909020f07030809030409 83
    0x214001091603001000c0031302c02404031070002d09090010b0103055014613102d2100602c0007044070008030310b01082e64425880940059408011900c1c2c043d207071704040306504a16200d10f5034003000f1401320111814403c0e041401a54082c04038441c2c107541c01c0c200501c98001c90300e5001000340150440010840d14040d00e00140f4420000052076410030140c0300d89100c41d6084940242e04000c04d0100040a01e9895507481c0580d140001d0280c504410890501e18408400303035040d82040300128602040100aa0259a444c411122944106131103941c2078020306641c0300140c0c00101c851025940140c403180c94410301c441000503c00c4d199000119245c005450103040914450300c0003131080c0e00b100d455160b08058518144001d04490006550100140401400404049820580c00c0d980800d082104c812240c04e0302e880f40c403500f02c0100084214070034200052418140040c042140d8400c4609281e032042d00390b0700e014180d440589035400c01070f291040500c000c12001800c1c0c00584200d45 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 239162526 1250 239161276 239161301
    0x20d0f06060215062b140c1c0f05100e03031005030f0601030611070609050f0d03060b07020d0501151203080601030c0f08070908030a0203040f0906080304060c1b14031e061b0904 78
    0x1482c042c1c11b540c80d1428108511450141645400884007a030b107020ba10300940703a01c0178603030b1510300309450700a042403d10100c42003a80e00305001548603034004400380d841841c141140c10700c820f540704209681c9107a03030552091942c114500500c00b1403025042540d8003100600e01c40c5c41c001d805e9440f03004075100070500f40d4264222070340c6000043d4040c0011500e00c0c4030f62030705009040c100b802c07200c09886000c200920401c010301a050420100390004680da5041d0140d60002690b03404007050700302c082400c100c00180c003100c0011a558024810a0302c0204513a444800709011821706550103a0003924000a00c507030a540000c694408000820b80300d91941e002d10384980c0751400090f19407600f40c00400307841d1b0518400f44102c100c0007043d1070848583d4035200c5025809800c29519180c0c18811030b1407542c8113010042024500ca40304505200820b400704e5140c00900f18543d00680884884802281c10000224400c08540780c0c107600f81c1885206858500f0303203080300103000c0780c2010074003d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 239163776 1250 239162526 239162543
    0x50706090801051f0512010f020f0703080c16030305090307020d0804050112060803030a240306050402090703020c06040809060d06120201030c0906020a0204050a0e01020d0f06060215062b 82
    0x40c05004003e015242d000b85800000d80703900c070420310941c540507040e4003a1034041d04040b040a80520f000750401e13001c501d01243c007150340e2108004007046980c0012026000300c2c1c03c08004c2401850243c048910111040d0449101c2d101c0175a401c801500c00502144003912003071240c0380142e51207481003035045201d120100e41ea2450030300090220018000a82080c03481c1c1102048508408400c0b01c3d400f8018450004482c4c002d0001c007041c0d0703481c0b1319020040c150b00c100c0c080104100c903400b85000ba4022141aa4580c0e1403c0048060b403103000c0701c0e002582c04c21004600042c8940010f807103070102c010320142c10030760100c0041003140c075503034400c0d403180f8010226642556014410303600d4003185031030540010750620030083d50340c1d20340240080c0559550800601300202c81d03400600c00919010081d540c0380300e18501000503101c44a40000b03054076111002401d28000240c5400766040d40a65510a130307244400c01050550341001084065211034091001001200e0410850f070b1148801 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 239165026 1250 239163776 239163779
    0x20105011a040f0e090106120c1a090609010e01030e0a03081005010804051209010507060504030e010917100207050a0b07080901050c030c0d0213090203100315060e160c05070609 78
    0x15000746019007001e103810650108000d1010301c014044880c1076603900070031103080f034851920789401402c040d441a50507203644100401000500b807000c404072400d0704050700111103a0400c1e00c80c80e100d40b8904580c440e40c00c00c054120780d4041d0f00c400020341c2c014140021b0800390390380720382d0502507079407400c0340000c42140c00c01c5000c4c41c0021060001d03040c2071800d040c880ca00742e0b6509170707075401c0060340080c2100b001c140c55905070b2046084403003541e132041d0140801e003000e00c0c015200c40540c4400d140840d0100c80049403040001c5141003428006500510030b00541854217402980a5102617500b40150715408004c9818660450f0145120b13aaa030039003032800c55203980c02c4a401070060210350790200180b0101c00c2d20001a40c040c40412040143d503041142580c901412a0358411102c9900200c208411280000c010008403400750b40e290400440756100c14007202e8a40c0585d4211701655004203041a10640c9003c140c107111341440303401c442e1580c5071103107403403041c2e0f00050014281800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 239166276 1250 239165026 239165039
    0x21204080d11030c0a030804050a0203070f08010b15030604240305030909180601060503281a0d02150309120d0203061c02010206041203110c01060e010e010b040b0d0e0d02010501 78
    0x88140c440c40c003030b8010714241004903046984680000002070f04100141010a041c07180c00d02c03442641a60080c200c070b614668503441d841d903010261040d81800c1d440d240c103011042c100250b02c0c403200c3c1200b4000c0c0f89075584800030000144460544240d20800c100501000745044219a50195004800444d11242d8020401c42208070040034080e0080003a80001c2584100042e81d5054400703a0034281e481f561403002c198a002c1d16104440e0801188002178481c2407100d0744404940032840389025a51000030f02800707012850044003d4006521040040c10289600c01854202c95500300b40c4851004804102502c1d410003c03c0c3d1040d0340e8004144a44d500c0c01a002c84c00007143c4282c030040303480b141e0300003030b4031030000400142000012300d4511711910320036844002c0c220700061040e030b05d5a030400003030b0303009040030b0080d5180c50359881700101e2050b00d100040c034100d07484090101d203000d00748100c50a803070304559140f07400e09484142e072014480085c850825a455541d00000707456142c000c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 239167526 1250 239166276 239166287
    0x308090a060c0b07031a090703090c08012d0b09040605100e060d0209040201050d060f050405070305010509010303031a0a14040605060906250f0b07030c03060b040e0601021204080d 79
    0x9006900b4030500d00201e1000810301d03299150302070040d08000a4024400980c1d1030020142030381075610400500402a94507010b40c000562540200542d4407455180d8003480e007202c41d00d4068890076000d19184200061940d0004095021000c00c003094984420002c181388010a540450b0000d850300100021803201140c2500204801c20703d2440034205400030030443342101d54081e00440c0c0c140300050039a40260120740c0c0075000c216040041c5555022500b01000150040310b210703d04042c00304065a20a004107030503558010480e98507a46140e8051b8020000e04564944480c0c00c1c141c0c0d5030240c0d4604c805400241072040304100700000b424200022140355400c0705104040901c407800240c1c6402d020307151107040e0303110408000e83c640342c110441c40454480c0284882d9a9584001c104511001d00030b0107004c06880c240600c007900b00065003522000d0040c2050040c0030300040152544603990035421045c10700685071035070001d601442060703016411481170f90740030707100c40502680e022 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 239168776 1250 239167526 239167529
    0x1b080606030a0803221e06052401180b03011520070501120902150a021c0c02040203040317150f03010203010b030a050c0c0a030824030a080f0d02040308090a 69
    0x11800340042c1d900c65550000c05000180c484110140c103d1814150004800c40c0c0c10f0502d600207101d800b402d0003400544a0020045108503040d50a24020400d000404140352034400601590000300400d88001103c125003443c000c40581c0b01044000661b5002010045001c1c00d1182483d43c1d201421354400747c880b842c181681a50241151041c0d024000302140c0c84040e6142480c00900280520300824003030a1040e00c007071b511500503004c1040c54034180b0020161141da90b02074802d0403401244580d1750b022950416008140c603034034240d005290950040d139000b03220707042c4948516006407924030307910f008a0703400d07070710008844140d4203a240200c24418001c004070020351640d0b0500402e200e05000c003802800e032403a161808504002c48480c2580c1390b152604048400c4200c0e42d0500412140041c0c0e112034201e4204601402c0c207100034030785c54024103000343c0105008111503841d01300d19030050b20340d000c21007024407800404a020340001c00c0198000d0700c006485d45007080c108200740c84103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 239170026 1250 239168776 239168779
    0x3070818120d02100b060f0d0605010813030c0b0c12040c170c150901090506130510080c03070807090f0e0f0709030f03050310170a05060a0b0a050405131b080606 71
    0x2c89641515660001c0c0b54008410b815201090490880002c581c0c5030003101d0075503420180210f08241e0780902613200908480382640c0f815400d0310b41c40000411f1005001d4090005003003181440d0205041d407150503044107005075100d04e0000706032690900c1500644044402040c1c00104002039404018519004050a0083c114a030075400000b001c20000318803020f0b4909000c652001c25a0241907000002e02d00a01340a5450000010310702c107111090041d248198442c1c0c0200d04400d108058480c401d00c112a906455034a4120080c0c0e01d60000809103410448414008200803c4c0810752800504051550800b2810312002c0b499800c50020403010420034519400c00205894556040e01580c0509010f40d0340c2d16003e013070241c4202190841ca00406503d000a5445080010145021400340c0142e51850710345200180503100600c0da4281d00031045003003070003280780c642c0c0304a030002d60200c0c0d5252224016590020244c1c0c09010740040904810410868540b041c4455680900f0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 239171276 1250 239170026 239170033
    0x30106080609060f031f060f24020a1203090606080d030c1101140103020d050705091008060a06030c14040e0a1a0106080106050403151d0d20030414030307081812 71
    0x8118042583c1d80b40c0d580780364030b1b6074841e03600624020390359034080030282180101c2c00800c1a203070b01050014074980100203282242e400085504244042100803000f41d12504c40c0c4601039094500710081c081400b016030b1215994940010841c400f0403c100d420000d944000c60f641c1c80018010f030840c5610501301c1c18507410100310881221841e5401030550b541180c1d14110f05115080c07a40c909411604100d03040088282805014010a4207981c1150003480859a0580d0380a162000340c13100c3d0302c0700519803450990140004400300384c0b20f00b0f000c04080d00c0081c41580c104111490316200c1c000555892143c42180907014410070300080c09000c0328100041207524040303008200740304500c0003800b2000c801e40e8088404020b42c000c070180035040d840106580c00c0c01c10366540c4494040e18144080740c240315864028880c604c012540540c201c801a5083c01d00d450400900b2107003888001d98107000070819140020350940250159403d00810264100b800c1004d00000c40324440304c0d5400c650 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 239172526 1250 239171276 239171299
    0x6050f0904060c050d0603080301030c1e300809090601140712030e030304140607020f0c1318050c0301110315040b060904020f09040b0a0303171b03010608060906 71
    0x446569005401942c400303070010301c0840c40c0c4811200c81c020404140310103402c1880000034846e50314040c42c10307039008410f4500b41c2a07807a89165001420791044114130300d0054010803007000305a81c20f1500380b69803400e55604004105e280c04a04220743c038119080900440c559409007000009140c2c03041d001e007020040511ba9000144c0c0c2d9000d1600e004101d030200e00c1085010620a40203009801525411640c40e1700f020710340711410411050388422a0700c0740307800146c0c2c020320015019070000d104002078885c075a4107005000f030941c5a000043c0b8200d850b1042d1906006108816440c81805030000e01701c00c1044a0406003510341006071070900c031605005000800d102406403808608085400141500411000c01e82600034800d0565100d440420b00a40310b24400d0010019007408513410440452094100b1400c0c030200d01001d030009181061042e0804002c410340d9401c0001035a004134007900c01015a1400d81c401d8214400095101e0b0070b01c0b106040c01148542c00c450100c811072100c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 239173776 1250 239172526 239172529
    0x3011107060f09020a0312030c03051e0c0417100b012d020114071d0d0f0b0c070f062708091e0406030506190905150c0d0507030c0306050f 61
    0x1400380380409000c199440c5800c0d503001c0003680c01402d4007a4060113051440d9604e0401d195100c0c880001c0b01c0c0801d003071840d0050094400d104540c480da1600742ca2084c0d52041e41d401301a8200010401858204200000300d040e0b0340c41490580480345030030082203101c0c1315140900c10386500c800340905100c0c4151b0404840c000100c420703014880382200041c0741002d5131400300d0150511100102010b000d079814011810b500c80602d56003031080d00d400c0103025400c8c10900500c00100c6202803c04182c1504800c00640300c0d04600da0001c46131010300e4182103140c0c640101d24444001c044540c151364107060382001d1109450240010010701c40c0400304110303a207621003607110f00d0a0441c8a80026403040c41185d551009501c501000035104005154503031500301d82d01c3c0780a81e08010f404090381413420a0100d240100c10142c1d502101030100019400b81c690403942d40601504c14220341409000c8040d40d0600c40c0c188600650355004c14064144140035089650726000540908029250762546 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 239175026 1250 239173776 239173811
    0x908090a060e01210b090403110f0a0f060b012102070c081b010323090a0c0b030420010c020424080708190f0b01030602090411030f0411120f1b0301 65
    0x43c03e004d0740c003c41840104071198000d0840d030200d194402006400d00c4141036211500d1020007105808580d04442d5038a502d43d42c3c0c030016400200601c0c1d04480301400188290020000e03101c06040c00074a60f54404500c1400f140850301c000341c03d540c04200e16081c00121282c0c0d030010015100076140b45203404107100d51005500d00c03043d06054580d4031207844000c0c1c01c6005230104113400441456800c0c489025501c07050a0002034650340b013400804181d4200c160104c9002d5a03000e03e240c58400004041c1d8640c400c10400d0950500c0002c400d4800581c45500a440103240394804402c652a45110100319940c0c45400080c03544d80410404e00c8150400107070301c0307450340d00340103160740127034151400466410300400018149442080000200155600079082000301105d0600c0b140500781000f510030f000440e80c030481a040b00340030802044451000c1006454050034099250b545124003504d0080d00402c4006a6403040c107012520583d80800c0c01080f02003180240420b05844014924 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 239176276 1250 239175026 239175047
    0x1703090a080d030c170406150b1303050d09050105030a050c070f0503070c0608010602100e030904090317011d0c0a0c051b031002210717040305090414010810020a09090908090a060e01 80
    0xc10365a51102c266800e0000b070302d0000038807814401540e184108ac82c10a60040300b403208450920400c0d0f150303202d85011b070512038255041a524541565900030007a000b8000c064044001d0007000c000391004614800c25460100b40908020b40e990455480c4c040410303241039000d1010001c0075401400700941c0400e010350104218100402c00c00f9600001d6400d501c40e030a030040d403040c504450002056000381581030007240341170f041000e5a99030030807030a500c2902001c1d0809440380b00009090303940b11401501c0e1802d50341c0390912025199a803450314048480750444958280210781e020349103000c001e48200f0800170f0900f507060026410100b0345505c00050200324042410000034401031044500380400406032510b200c1c24102410041c00070344c410410030340a1414455030041403566400120704031284003008104215400e44c1500082d00802c0450040014424000452142c540281c024060280700310070f40c0d0f07410400800000f44c440343e01030401d00c100204a072400d40c2c2c1207003201c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 239177526 1250 239176276 239176283
    0x6010201060e0705070c0b13030309090506060904090501150e10050316050904050321060a06020307050d050d09020405010f0504180b010e0a0f020a0207080705191703090a080d030c1704 81
    0x3601d44845e4038245090700160f4000c0c1400c107401003026508583c601100b002100d0007525a00c00440c0c80c2e1440000b80c5204031401038129a08025065030341c1403d0b03016401c40c0c3c2c0a1030002980202d10840c00140f800300d0b5120715075601c2420144248070180c006c65800920048005001881111000c1c3d00d02010741d10406109004500000742402030620803140d00c00e050b040004012a0f40042003038000300156034031401030800c00004140540004121498140c10500030816010550000c86042d072050325017101164444a100c00142c54600134140a069490b101c0d160850501c818807044454042104081e00102029030f4042a041901a41542d4824010588030b81c8c81c46810703c05401e80f015080f0082d8030028140d94420b0f40030501000f0b031740da00b00944074402c0c0c0c1c072410810345111011612451080000702003004d1400d10300d141680c0902030f410341307040c00940000a4140e022542c04825160040c0f03200500450349481601058045424913243c4000100c2c0c4184c0d03107400080009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 239178776 1250 239177526 239177537
    0xa0f0209040204020412050616110319020c0307030525260c09041b0504020f040902091807020a110306070c020904140105130219080a020613030804170606010201060e07 74
    0x2600b551a182c0440b0040c018645400d80002040e29105e03948100480b202001050040c04070a080c600c110380e0701707413100d074044019410005160348201d0220480c143e44000d5100e4800060030b191014003a40c401580030340c02070b060118600340f1a0740341260070149904407800f07884c0180700984030b080d2041e00c100c0143c03030001081c0c1940c00c440d6141c2038464140070f5011104808100420154843c2c140c0f1543c500382d03211620564030024071007640039014a082c9104000d02007070000051070f602406540e07400a206141203003101b503034800e052070300f80d17510300046e0018814801400350070081c1036080d42003500100280e14080340b005180300300e00000248100070040110303092195501c4252214841300c1300030081c80c1802d41800b0401455400300328003e2030301c0700802c102456540702007000c0b211010058183d212440c0d0801c4616407111803106c1082060407008000300b4003d40151020b4032061644681415084903100d1505500805040c1160304114003802005c40c00b00a140d040081400c01c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 239180026 1250 239178776 239178781
    0x10510050a0c2604081b1e0d0c0902030f130b010302011b050d260f01060c08120106210207050c06090411033d03030503070e120a140a0f0209 62
    0x9401e4409860754003081890603400301140000d4000c001300121004a01158480407406070003210301644180300781e81c40f0b103001b000320814075a29041488020001020350100242c01e40e035540c000c0446411641c2441c4d400701c10001d2040c8441d403201d0b00300e811403541e04807541c0e103583c035103e0109050000904200000314002c04a002e5003071200d4030f40b503000c810394401851009000b000d0a145c1490401c1c151481c4076541c0b854141c01001500420801591721510f82c02e089041d5484155680c003201c01100401002c4420b403600c08a840c06044103036200c02010340c400e1410090440f01345610010103104001910020b000003440b064109001c0d201151201c0503900054001e12040142c03008544000003080b14410981c2c0382c070518112184001c9011103d09144010703410803403280c05120002d0150b0a0011a01500145500c08501d14001c1c00f403505450124014085c01d62081d0015440314908204200c003c5026102c0002c00320001c21010100c1d45689045100500000e8000c40c0550302 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 239181276 1250 239180026 239180033
    0xa050d03020a12020a0c020102010b040608030304111c05010501080d0503070e120708010f090b090105130813050a0b0d0e0f1b12070605071a01050105030705030a09121106010510050a0c 81
    0x21002c03441c0f09540045495520013800075180108040080740103510303120a20846280611495040d101c1010045082d41d40b0703a5603464490001130342c03081d40444960f040905040105818030081440f9800102c1c05500d8a411a4a0b094940100300305102c828000c00ca16140c4c0004103002c00201141c0c00c6005244045000e07007824200d03006201c0d954209080a018100c0e19040000d02030711422485c40e15654000c050303800c0b18401c3e00c41c184141e40c00b050326404186420050010801145101c482d215603e40000f44001c03d5688420f12004e0702041450780882d03240304900000d00020042c14003460b0358146a1b86800c41c901e0540e050580c00c0700588110380310324840911070314181d07080314007154403074002924039044420222580c3d6a200d240101e5890364903166412203206171111811915000d40c141c030340342c1004001c844c80b41d5442603001d02003204043e15417540600342d150103046403100d904840c2000383c160071175401032412449046199900500702c8502030071302d19042c8035010140c903 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 239182526 1250 239181276 239181287
    0x1a03060f1801062111031b1c0603140721050319021c030209060a03240311011214070c0c0b130603050906060f040507090e150102060601020a050d03020a 67
    0x81040c4004078a09001040c0c4035007050100d96510000014813803505a00c9106030190342c3c600119507550f110910100d40e60070160360078a0404041c110301c00d03007814540100342212854003048402d001d61204000c20074048000041b41d091034000018110f03035030418080c5490a0306607213044c0b2840070040e804105000062003a20752405505604038403211900ea0002d540d0f500a0300380744d030640140a04425128064401ca51100e180503000e141011035042c8254002c2c0802007078604100d04800094010710f001c4103075000a584640803003c08112040b000600300040c00b4541c107260703481e0440040c40000b080c072030301790302c2101484e141e290010545400d1300701108541c80070156800214a47c01c070044c10401c6e60068a00540d0200301a556800000c6d136a94008c0c0d405a0b000040c9007034580c0c16003403a8021551249990501003050340d500c10141c0c0300c42b1411900d880d802540e07059203e680750703410700019800031400d10007845120b14640382d00d0f403a0030034105113009169000030101001d50244 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 239183776 1250 239182526 239182549
    0x4020915031b12090c090103050c0d1410090b0a060501050d0b0d120f1206050906210a06020702101103180f0603040302100f06180b0a2408011a03060f 66
    0x20b0440c0d12220480b036032000030305040d201c120450040d0107800c250703070402c1c213800ea048940010040c61003541100a10800c016900401d441c046522070700ba00b50b0050401000d4451001034100240e035400c0c0782481085000050441800c0e46c5c203114003004661b1340030b002d0351900c805950001400c0300d036507400600080441c15005100d07902244103140c9164000190140001c3c0315103814420181d101d03450400c644040c000d01d54855287e03030110b43c40742004142905001c10b00d414852081c4031582401c0e2401c45540c504507001e64002880f20f00318242000c0700c0d03c010400741040c4013001d4101228980300d01800c00c0941c0700350310000019078207680302c005034010074901030701305940c0741002d04000392038913103800110000b142005245622448180f040c0300072031b648030690f2003010703800761000409800c03c0c1c116a0717031012402c1008650030544031810240b00201010140ca0350304002c0c8090003400c4141d008a07624840c1b4041407004040301421aa4820801c0304c540215080842c00500f51030800c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 239185026 1250 239183776 239183821
    0x2043002040c1205060405010f1707080105090a0201021e0601030b220b0702061e011e0503100c02160b1801030e0d05040503011d0d08090f010903020705040b0402091503 74
    0x1012200d0300c000f608420f0700d20541008441c14001c507070b15030043c4000e40d038080c45030540c40c0003460420805040700c080c0700007822403c0c00585810700d699000080c2903031815034890030309801080740740c0110741c1c0401030300654807000000801c400451a0096071900e40500c00030708040070034800100d44094400b51004841c4401d00404201d00003400d120b180074400310f82d104058440c200c041451303402e07445885541c0040c0c9124070f065503820403850004034031071601a500c0d0794010b0800810951340a01945261020b8000000790840790190000d24003030b44101e0080314010710310018024050300c00100d52143c0744060100c181c000138540124001d010b507141004480c040c811f410b520440e4401300610407154201c0c0240302d81200c12a5030038061487c020765448544c03203d205100094002d4159540c4407142c40c0503202203d40450407a03003950048170301200181c00c2190280310f20324142c4551b049240d0103450840c10000c5000c040744030030070380500200e4203410200000d0f04d03d4200c60080c81c40e0002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 239186276 1250 239185026 239185031
    0x30c0911070c090209131b05090f1e1f0816050712090f050a06022a030a0b0a140c090d0204110d090209091216050709060803030711010204300204 64
    0x35160503e10080d008101d040c3d2040c51644400506181c1c07074021055030180303401402d107101d50f600c102a0b540b90300440b80710707130401070364190f4041640d0f5800c44002c106a6100301868150b84140421499014003c03d400212060305090f1480607030100603d1350040f8510910500342c1c0c0d420310305aa0a005580c0001c042600c05078505500035401140e8000300d0f48115480901e01d600d41c400c1000510042c0150070040c0d1001c0800110703882101502c165400003842141c6440f00c02e44003190810500e00016500c0511000a011852040748652a21040301601e20079190a10040da24424801c035481144140c100f00184419980c0701c0d40700c003160f0060308020980c0d4090101c0030f000076024024081e40705109041c00103e1844011421080e00301d1104000f40c54549550600807040e06000d00a80d032030b104400001c110341e001c44c8161000740045800a6440345882c2070002e00c000882c042450440e40140310400c03690f5440075a03903004685441d036001c601c00c0300c0c4040c01101c09402c40e010b54450b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 239187526 1250 239186276 239186279
    0xa0305031e010b07110907170402060405030f030a0806090c04120507080d0e0f03030a1b0c0e041401150b1e070624060c08160203030c0106170c0109030c0911070c 71
    0x300000044c4602d902c2001d0704a50307840c2417010001100400c03540c1d000804c24030000801030100071100c1d546d1051004101904060315040401d20b03000c502030281d1682d41c800624001c01607003065403250310040440b5446001d00d004019541c0500883c030451030074850b00c04141007040400d102c4e00c405818201c082303d000081c50078000b8095100980701c14003e0b001c42140c007016090201c11265a0105c5031104a00c44440c0e0001c3c00e04004290340680340b0003000c64000c5600e5014280d03140c060341c05400001c0444400000311405c42d40da00e22103030220403226404103d6000101c041e10f0700122a4000342c00c44900f200c0101441d4032807210018083c1d45003013000149984030b29585145004030300d00b500e00168491400f074590800206015105403400d20022490460040c241d01400e0302c098140e0b4141040b4500440c00d6400036044103404040b4803400301d01a03030003006070320742410003481e0000b0310038a59203504a10003030300d01401440d55120211320040d401e1110846007141e41c030040b22210203 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 239188776 1250 239187526 239187539
    0xa0b0c1c23190c020102030d140a0b030f0a03200a060204060215010602030706021303021201060608070c03120507140301030804050109091e0c090b04090b030f07080a0305031e01 78
    0x2440c02841c107003041c1c103540c11034001c0c8100c000180e03110b0300c1000291210540342440250f40350b40450710201e0443c842000703d440d1400b400d0240b01320150301c62450b246d1600300640c1c407500b139407401412513000303038800806041d0840e0000354054080d03405091160f10603c0714403000c0001d410760002d81c0010b00c900340384074003000545d50081040b25078036800c1d52032262a00c103008101a13000c1c801c640040c2e0060204101251166004100302c2c0d0714030300103500d842d5030313030380402c0404080ca484c1d07040d1a5503d600030044650406521640305500c1d192180100180381d030041c041040d99003c0304d210315170380e000240300d040c0644001c0010004c0c1074116600c943e580d01d80711150340d0160007080d0020b0141d0800050445160065801d501c0681102e07070a11400404041e000380141000001000610f080c0010008401001440501070264001c9001e024620a05152409401c07c00360180c0c014003007040f070783c40c1c08552208003a0385807900315504d45800c0d120f400c1c4942c66a0000e40c80440c40700000401c3e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 239190026 1250 239188776 239188787
    0x10e0703050c09060a03030504180b0409081b01060b2203020312030709050f22091203020c0c0904111309060203100e090a081801050f0c03120a0504020a0b0c1c 70
    0x4802048416000503030304c100c144070781c90269100003000306a0512090090880042071100c840302c407620009102820940001d054624807041541c8103000028080c4600c54080700c3d200c00480100000c3c071020b40f4180104245106481021030107249050540744c942104185000085070000c08484202d4050341000060358800c0d20300d040400d440d42d07400a020f05046460b034a200c40c00034103204828961149900565800d50070950140799030310042d00002d6001015181024460b58005032140c01d140c944525007096182c580d0f01c141100400c0000140006a20400e69181611080c60b80401008020040e10b02d11200a15660001c4100324002003003d13540c000301c89052141902607240d00066540314142c0700e0020f810f03020300704448400d800c1c079144900390300c00044c5031452500d84110210a29500241613800e540c1d0400191070064105038881c0341e0300f103000c2c0c0008100ea410658005200e8100b64429144000d002050500c0c0d00b520a00499182880c86440c0c0c2d452046c01c003400401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 239191276 1250 239190026 239190043
    0x5070515040602270306060409050115030501272006040315090201080c0a08060f060702030a08040905090d0f14040306051302091f0b1b030c0105160806010e010e03010e070305 77
    0x41c607001d0b40c94100700090344e0344800503540a8050640307500c848042c0710203808111410f407440d64840c2894401c1991403640e00004600410000542c0c0c00c00081d070508200c190080c0c0160020f2160417507011450b082c20460031001403100040100140e04085a268003ca52014101041c1e0070010346076250075802c9110854800da03a4819155900e280360070071400741c06200b070001000040041d07068144a203030b0809074800201620304020081e40003900d00092070f4001ca80c0709401050400150250740903854014481c0e101618002090800080111060042407001c00203500907008000c1f080b40304940180d1b400c44020700040c50700489a8140c0e05004500700d029800d1940010100040c50480c0920140c0440410940c5858844060025046030781640e952848510840c01502400c0000b081d09044150020070f0710310700210a840c07440034501c0e81c0c005220514081051681e44504002441b00c02404e0401001c0340010202e401090a181005614400c5030008420f011000400340f4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 239192526 1250 239191276 239191297
    0x1204080d0915050313020a0510050c010b010206010501051c060b0c0102221505031801061502060a0606120f06032a170c010c030e1008041211070605070515040602 71
    0x1c407110b0b5507044000768400000c0c8800d000910900c04104d0701c00d11a05c2e07188105000520004c0c0542d2100001030340e211002c60302c1c90200d81c00041622f04100203003e14030320150240003400ca40d41c50880080c0441c400c840c0a004840d2150890502d85400c50740040003501e02034020540b58568004214000d5004481101c42034008060b482c01c00c014944588044d44c20101c40300c1e11032044000d0a40d4141c00107040c0d000c400881554011f0820024403402c401422180071034451101d24020181c01d00e880030f06010221800e1030307030a103c102e030081912000c0d4040068001429281001d0290081c40150001000f80768a8100840d0803044c0361502800d103079613901c0c24802a1355034007400c5c620103070784404410350f0340045141d9502980101490000b09010f41488001003240400082c41004059074640200c0e1640b000c1c88103020508120f400200110304124035030b41401407489580b91b030544512410071030001600c4081081c1844203c241c01c68a000d00c1895080920f00040650899900300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 239193776 1250 239192526 239192537
    0x6090321071b0b0103032003040504090302031608090a170309010c0206091002010605040f0605030c0f0d1401050a05070815090c1b0105090f060c0d02130510110c010f080f091204080d 80
    0x400710307c490040341c1480d05404100a510302441d200a220180070f114600350103600003070108500c0f80f070104c140340458511814100c3c0e91500c0178810000c404206820860061001c190340c414118000021214185000d003800d0030f490681e48000307826403203191085900301c6215180100400d40540000050740c0c0201c1303043c414046800d510701c00319441480341d960b00d03038071802d80480c8500b0001c140301c1c5d0003480502502818030243d1101c40000c5044040444107030754500c200010b0341002d01c80c0903080031b4103240001607800d001504140a00041e24654400d452417400300d0514081d140465200410400e21140404041c41041d4001c0c01d046664403441d0156281c035454254011031700c40d100384081e401f05410b000b41c5101d00c07002504a05d1070b0f004000d15161001c03485540d018074998040002d503070750b0030b41130075040c041c98282481d11808905006c200c82e052240c9a8100c8600c0e0b60020421201d5142c0e6540c41c5101c03881c0040140000c2c448080001d0b003c600b124012807011a004070b86d888a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 239195026 1250 239193776 239193797
    0x2106060607170307110708030d050c091f1101060806101208030106050a03061a0306010905041a090907030614010314030a0e010c0204090602040b040806090321071b0b010303 76
    0x2800441d2140000042c405901ca24a1900c0c101400d009950400203d103004030408072a22001c5281c0103494103c01c051394408500391507010418041e06901c080548215030030401d4900c0440c0f500c02d08092101002031000303807429802403080c00da481d00345807204001c0c440c3c40c0d03541c41c01c00d44900b020359144072070307903408200480d0642c19160403111417640180c64914503803802d0001c03115a04074840c40000c040c0c690303c000030215500421041c201340040b0449650b0305280001400f0346001f640006d003e2801d0448980b0805d50001d03410b551104103850031a06c0d40c0da0034601c0c07414030605400c010051490045258903200000c1e1480e07050b030744101840e90546180d40d410a589010b0800180300013028001551059449030340844082807015201240c1c50259984100a903009a044245c810300040390411003c602045410740000f11640918a44051504038040d41c819200c038080c8c0c598800c0000c54500740c403802085500f140504010580700c4a41d01d802400040c080c442900001c0b0100392 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 239196276 1250 239195026 239195029
    0x20307080c100804051f1b03060b0d090312051003050607080126011b050a0f0e13021605030a120b0102012f04050d060f051608060d060209210606 64
    0x1c03049012000204126051880c101045449202c0100115024042c815882d07001c5403a0701e0182d400190f43d40c60229407072100140030a41600500150030401d1b082c44410060f443d42001114090841800003040c015075a050603141d079121804107048080c1361a0801058a25a28141d0241d030300c00c1c0262a0b0700e8407100f01c221007040c000c1c080d5075a6003001104103200000d0702031003001d182040c0c40000c00c81d13401201d85408409420590740d0040b4500140221029a0003a540c1c105803103075080900202c001d80c0040380600803800d5455075210390001d0010b5800f59417055201c0c04c907170701c0302c101d0b40c0d91010844014101c1c0100360f0040e20f1541040c4200c5510340c0103014602c00d81004d001d000c0a95400c0780c228151070701d00d202844400d04c40401000c1031f81c1c0c40d0403510300c4004e0702451000c50005080c000500465900800e83d9040d802d02c0307040001503591202207541c0042c401c40f6000d914200030300b0440028401c10b580e103a4403100e035070139a605031002c42e03114150410501c0103403412652000d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 239197526 1250 239196276 239196283
    0xf04090603121707050918070206040b011208091203040b0a0201270305120a0204050a08030c0f03090105040315180b06030610120224040e01150212090405071205011202030708 77
    0x3c0c041c0701250740400060000340c0b00d1406800034007070052101d0010002844d0120303002c0e805442600060700210300704024001030400e568010001d843c242c5c010000151076040d564005c8200d4648960b2058a00d00c000c11400c106440160180c2166103989400b8010064020310002f00390b10400040d20b94200b0000502007900d07500c4a4154032241d160035608010300d20384820017132000020725401d00c00841c1c20744420074102c0107011084015071340c83d444085264030301242221507040b5a0310800805d080d41e41d2280645040380e600c421060b40c03440c03061621030301600c520381c103182c003802d00c4401e00b60610103000c241c03601500e82a429904240c59042c42c0b0b591450b90340c040e1480134110b040004005040c10305525150005140c08015817507004080c01840c0c0c0c0c4280c0c00906602d00c104014084030300e008070061890b6029000600594025100810540c0103049029200e1a030b83c1000507511703809281000002d0602810402c1290b864401030700e100d01201c20306a00034070502402050325032000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 239198776 1250 239197526 239197547
    0x403080c060702071d06040b040905011506030f0b03070506030a0e191e0c06121107050606090a0902010c060509162408100504091e08040501030c0f0906080c0f0409060312 75
    0x440010110342d07031b084244005016107005042c0c0090350340e22240c0115000788650711100b50202d25001c8031614003100102075802c400788004449103401441d90541d94001200300c1107520548001c0d03141e980d9015094002c080303002c1000384501070800c2c404040b00c1d1034800d0b44090380c0301d14400d00350140340300b0710f0003200509400d006000391619201400203a00501203503100401588010440001201c1105107580121808035400e5100401703000003880c2030603000d9480340005008110306441e50300002c14041c030040b40549810b503113902040b51184148402c908014600f00392421099403402c0d128403c10f4211503400c06042980a1142c0b5a80305020740ca004040b440d81030b00e942410a0108001080e69950403590f50b043d04c4500650419403480203d05580200400c50300c0c1c0c0c0c60500090300742c4028050b40342c1000441c02080341c5064004d004c00d001d6810030b03c2c04020b00d5a6080700602180f013025103402002e10007040006d01080c80b134210b202906d1080300d0701c1d6590f80c00640c081c1d900c800c44 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 239200026 1250 239198776 239198819
    0x121200f251e21140c070305070b030103170a02030f0a1209050610061803020f010c0203100f0510210309211a16031109060301080c090105090702210403080c06070207 73
    0xd00c150701c0400c0c85140068200440654151021b499490b43d03040c0c68071004d94009496848044010000d101d070303140d8102c1e545c2d842c0c00303075040c900180800029185d10921792209440d03100410f031140300304c0c400c01c0c16119108241c2000c12031801941800d6644840450340494071500c02c80e0085461031040c11369401c41c1c0820440040c5d03031421a800c11100200202030513040000350000381d400b41c0d50400142641c843c9080c400581d80780340c8a849000e50340010001c030354214034580e00300300d02a000032000041201c2482c107141d03480180d04d81141d10261552210707601c068a103071610240460803580c0c0c100301d8071800000122610002d41000640000c956400c04240071130b00800300940a504902c0b440340019a42d5440d000c0c2220000d51240c001ba04001007940c0310320140f90341ca003024038516014200c04c0380c402d1450b1608a00c003d60b54844600701e2440e1440b000c84140c5d07100b00c0d9000f990003460f400401161507106042c84640d8408045170a40018495590002217100320046081072001c1c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 239201276 1250 239200026 239200037
    0x9070809011d1e01200301140301021905090a080708250302010c1502040b040306270803010902180402030406020a090b03010303080c090121200f251e21 67
    0x4410081800c0c000f5000d20816555261150003410b1103001c3c81903403400380c044003541e480e54140b91000b49284405034955009a04c10484645144004a9024005071070f41c641144e0301d01e64000441c00c62034072980581350038840c0140205041d10040344411101c803035020350307803652484d0f48106403010409110190109114240a0010902d1300c0b45840072000440e002514103990340c115100264466801903844c165142c0301f884d4a0101c1680880043d000304451407880016034591056511040c17040c801c5080e800524032004c03030a40482c410041c00003c1045480c0c2c40c00d820f14001a6129002201c002490b55001142038190324041d01c1c1680e40650380c42689544039010154954030034543e060612580e102104c001c140e4940000c1083c0d01c0008003c18000da00825000f844020b1034101e0400074400e00008800203081e5064440da441407002501ca1803520f00744c00e021400c1085000b9010b01d81c5401c40a80b00034030030381c81e001810310492080d00c4000c000c0c80c10030403000004510b1400190f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 239202526 1250 239201276 239201293
    0x3061a031216021804030c0308070f091503060503010f0e1603050a11120a0507091b1b020103020906030906010501090e060108060108040c08070e09060603070b0f030709030209070809011d 82
    0x44032003009a8982c0b01800c40c0c800f0780080f005040e504681105e040f80015400d100503010550700c021216040121418680b40280440780f001e003210301c01e80100c4e400c5010405e41902428441d40287c0010503019008000e1041d4500c0c1083c023408180e50000540c2c410003c008500a2115403000c0c120307500840034000c4511541c0c0c8005100c01d004d40720340d40c0048004580d42d05071906102c091001e41c403420041166616142200082d625200c3c000082c9031110074070030f12840c1e000b4143c0313002407408038150081070340d07180f005030b000b8090b0444164024501000304030030443c00041d07450681d8000d0300c07800700241d911500822012422610180044d1700c01010034840e50281003180d8000348114440d89000303440381c03001881e107070b40ca80c13094041d9140c4105000740304009025040d000714058025000183c184042404c0d0751013409500101d1030000000610414802c14100d80a07507402008040f50f8107011800030900c1c0c4d400e0b100c2c42900d501e0400e40c0340c001d14102c0241d50004000382c001d0240603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 239203776 1250 239202526 239202547
    0x304020d08070c090c0e2d0105030a180305070b06040b1c03090305010f020a110a171c110711040911010c080c030a021608011e0506011803061a0312 65
    0x15040103074101d07000c4108100100352000c250013545d1800c0c1040d40e40c01c600da18000100581041398000030345503284004a0a0088403e0442e800c222404c28200b10b43c1d00d444003207080005000102c88118020fa040182208150340718006140c0700b4095080142d19455203020002213070b50050780300783e01611010358259404101390300d803d03001d8002d081c907909a0f80d99440c1d842c29226030600700340705d0940c00250004080d8000310f2240c09500544020241080701c0e07034a080b2107500b10241319002980c0422001085a801c1c40340b1404540b00d6074040c030034030782d2218502034550421501121000d450303050921030381c10540300303060789150800c25055122580f04010f449031000c025090311680030801140b40655410070007440c50f91007542c0100901c030f021005071002c065071078220000e940d06044000949020050045902c4502d100000540351500c00040e54803c040d250f110640080012002090103066400400020010305141061100c2c14040546415941d00840c51510050103560020b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 239205026 1250 239203776 239203793
    0x4080604020f130f0e10020906070305091516200d02131413030f020a05030a030c050c0d0e0a0f05010206012c0a0204050103110403031b320d050304020d 67
    0x2d424090320b48000c403214407250310141c40781c1150040c540c50b01c0701036502403080c0800000b428048101d004500b4050400c0010300d06100b1618060b08000d03000c10300b04c0260380c60240300403540280d1210340d0390300c441c2d51054000c04a010f8106640031000c012680018144840b00e94005c0e890080100d400410250b00700811884500035180c10b82d581c0340c03c0010b24840c1002103a00801c0388590410a0003c5890014030707000c2e070101090115001907035aa4001100041581c417003c0080c24085460990b0380c0c02141d031409a6480c9070502e1040e00e510310320280d08851407131020380081e16007044541c4c45440e4900001680e1081c140103921a0300104040c00c100b1401d140990032103220390346102e9181a42481d12001910303480c0910360b000030100140d42c0c05d8410a40a034808840c030504062468801030400107960114210300304d01680410304200d800101c023000603078000644082010300c040750502e2000303030390703c890030503c00e050071444007a0050003640e11580c0c3c0100b44c0e0310380304190f9607071619 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 239206276 1250 239205026 239205049
    0x209060d14010c02010e0d0212041404020909270c0307091e0204032a030807030c1b0f0602060108060103110618130203040615061202070203101104030203060106050408060402 77
    0x1c4070400d4803081c0c42041020300441851295030790000c80e4412030b6110341410085014410820f55001c00d4250104901400507074049405c2d02d0800d400f841a980b004ca0081d110300903015a001c07040300c0810420040c0340c12541440d403010f05044c03481e0040c280119076100c4ca403081403545a4030a200401006a843c3c12801c2c200300c420700c003180b84802011251081c0e8119400c200c07000b012004243c1d418082c9881095003041c400341e00030204510350349950a0038424440054208039004a150090144840360f500e2801d2440b48006440303646d030368000d02c02d4040e41c06010014021b050001854a40008a040c10303240c0081e001001540e66100704a4998450408094940c020075034501e400c0d0740d540401d08082500b00005aa20318107403900104554115507403011291a00100703101da0342e400420940704e0800d41c403005995103500d0001910b0445030340c811a030014100768400220750010f01c0540304a9200740c04503509a40c0703d07882a11940a1800f03001240d030301510000d009490503a11540 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 239207526 1250 239206276 239206283
    0x10219020d050a0303051e06010903062408010e1e07060f0908010212060a050d050c0f060c0102040b071403070b06060f0408100c0e031b0904050c1008040209010f030209060d 76
    0x1000004555640b60514403200000e8010036507a8040000042c0708050000710404042003d0749103150060020781443d03103d0001074842c540e941185407580d03151140c460f0803d6408915241c0036a6201403040c0078240b030b00d8240d0124096080d004a50340e0b2540040703c118001040901601414030200b102c0c4100e601e5046420032040341c400094201007840200518240766800202500d0044140034109680c1e41c062402580c0d06104c240110300d01140c980c4010000321081c800b5810050009142c03802516031700e801e154800038000602c0d01007000281212441007403042021a00242c605880f030190040c080c1c03104503044002011071404800401c0c4259004120700e0a10342c850000d24500840030040d800300b00c0c0d80710a0140190740000c0400202d0004030018003603603060f00407200c2c0078807020074407900800b1000003260800005101d01074901401421072504107103201d031b0040c115882502c0690103031000c900041900c40c490103c01d415280c0217000c0d940d00389c0f40d20051151030502040160b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 239208633 1107 239207526 239207539
    0x40305060f090708010e071401180306090f0b0403021f0e0c040f09140604030e04061202010c060615050d050f07080c0f0913020301090e0c01021902 65
    0x5941c0c4180d18000106a98a82410841c6004000d0304070301e105500340584426032034400207244044a03040d6a0441030a141600103461180381da2000350302550754181c00744042401500710205a80c4648682d8816055584078603100302c0050740c00b1401030304928003804604545c2222042e0700010840304004811542ca6415a81d21212000b40c1c05a500c0314130762140420141d00040c00580c0012440a2887e000b5001c1c03911242c0032501103010460403130f90242c0504084c4546000d80c1c8403c51081c2c2c170402690015210a59011000c8854070f40b0b40001042a06404003902c40c0940c0548a00303444d90781038071480095403401800c110304000c6200c108110385a0058989401c220f060559a0b81d40c4408007031040d9030302c296410541c0210503d00103400072000307a13006604071500c4000420400714807901050f10b440c42c4510b420300692015170b02401015800c1114200c05200134240e = true := by decide +kernel

theorem cover : BRFrame.Cov 239028776 239208633 := by
  have h0 := BRFrame.cov_init 239028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 239028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 239028776 ≤ n) (h2 : n < 239208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
