-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2844
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:54:13.15299+00:00
-- url     : https://prove2.me/submissions/f3eb3b73-bd72-477b-948d-4feec1be0cfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 511330935 ≤ n < 511510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 511332185 1250 511330935 511330943
    0x120c020d060c022a0d050a0507080c120313060e03030912030307081b031b07021f1101020906180301021306030e060106030905060727090e0d0f0504060810050904 71
    0x40d00b05020182d01044010202905200030b070600101034840b80c1c0803801c0f4000344500c1110850112001e02109000301410039410030192521643c454414640d00c426181c840c0b4010842c0042403e4071076804010781d41c10b4041401c18503103807840e00e10b086a074004030204956050104002d080610754440013100541e0b54014040c54881c0340c8024040d028440c0101060740b1414260300d07107400b038a401000c496000040000e140521860040810746901400c000203411002c9a041d80c461130f0042d180c5030301c9005560340e65441d0030b048108028203074050300404070340100c0c0c1800007003403840c041c000b80c0e1000000900014240a680312401d580d100740c5500840110703070744440182c80d1aa042c41142e01401d0715050a0156900395070b902a0b892500400003800c00400402c900078a0160038204100c1c236241040400c1250b40300c4081c0002400c00c0d001c450114031440042032800e9010345415548190301d0740f1007904007440d151060301c4c00640104070780210b248543c0d020500b035072410095400b49010f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 511333435 1250 511332185 511332191
    0xf110a030c14072d1d0c120705030a11040f260303100f0b1306051303082217070b0c0c03011a040b0f060d09020a12060507090605040e04120c020d06 65
    0x3110304041c840d8010051402619200d48024031002c0c3c02452404083c3e694458500199079411b44c02d841913018070000c600c5010024001e0121060340400990701980402c1e0040021101e0024072480074031a03403241948034080b074542040040c2e000e42200100300a020350000200c1d182c15081802c50b402183e4490440d200030342c007030101d0440d961403800903010129450780740201041640016001502c5140c080100000302c03079910f442d540c00068011644941c44e207849603082d00b0f41d102c000c41d0b2100600314040c00708100040803519440c25260520002c000781049606100f4405903a034080303a100354207881952150001ca45003441001051380402e09680040400300c010441030302c003200e4074148100014000c640311a95446d0458440741404000007503983c40302e201140c9020003a5216085012034400c40d0828001c69801c001d22032002c581d110350099464180a8415000d6401000506a006400140040e0411107501107003100360521200580d503950000d81d4132aa484d90803103100391 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 511334685 1250 511333435 511333469
    0xa030e01050a050919080405040506011806030c141206010c0218010b1308032b060b16020f152d0c0f0d0e010e0411071505070f110a030c1407 62
    0x40c4140c0022419000070460b417070f0345589940f14113005c1ca0040300d2155039a040810880d81c09140000e03812640070000d104007594504015004214022846011640c0c40030002240c0d1040d008840411484400ca5004c6441d980011500e42111078012030300010746030000951511405d424034002d220326500b040d5a00c900a017481c01940003940041919807040c880e08112407419104841c1c2c2440c101c0d104d03920100c0310720b4107c1c041c1caa0383c0e0000074501c90020762201c203200c540d0030021505000740c40121b400c242c69000e2006040f44904140405a004d00c08a9481a2039a008a48030b010003180f070801c8208048440d00d50360320030400852207600120607440084014015070142e9203c0d400c2c4094020704500c0041d10f0f0003070003114144115511a48445101818400d44c1c1c00c03907401400c4c2d500d0b4007142c40c45440092505035406c0c00800c1c40b8070303058a0203070b01c20348280140c2d507101d9004d044a02c000e990203a41014900900300c13000c0c060704440d8404c0140410130000209004c8001640c1e1344 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 511335935 1250 511334685 511334701
    0x90d0201111204152004051c0c0303080907031202060402040b010212091917100f05040218060f040515010809120a1209050304090b09060a05030d050a030e01050a05 72
    0x1494000503021207490600c0744070205045981c201d58400c2c4c0281005040004181640000789102c03145000c0541140442d0703008212664081e009403102070301d80100203549031801c5102040d08078001000459141c4080c0700180c481c01900d0380010f104001c507040980c6035510a0020480b60503401c00580c00b6408000651829001d50b040c440390170b00103000c08000510107843e081c407030000d82d2806107040c0b030790b07070030100c003c20f0500310041080d07901180a01110484240d00c1d200c0100446103a01c7c200404e03c0b101c0c4650740300380c0380501e50007040b50100300d164070a901c000354001840954013245001c6503442c0351300c0700d0244034400d91490399036181e4803130a40005005000050b100d204541c2c0411140051050003000725480003182e4101b441520450988482c00781c0541c000007006400003150000d40703001240c20612002c081110700c000903603030310401c0c001ea2031082d103d42039056018924040655001320014002d0391310700c2c94089140c5100580c04e6081d11404e0b01c001c4079031681c441c1001049 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 511337185 1250 511335935 511335941
    0x150403031404081605070f06020d080108030906030112020609280902160206130b0d0f0f0c0f0302092d010e0303031e0c04080115050109080304060219020f09090d0201 73
    0x5841030160160503400c0035169401d15008071040700c282041c01c41d84c00740500800700100c40003441940328882203184c503103400a40f1500d11703103802c202080c01c3c1e00c0040381c0e01c000841a5503d100003d081c880c2542c0c64840c5800781e10355600710580e08002c0410420704a44c80e602e040c00c0b072a654000c00d0381c0350300a1400944a80700c0032a407010b1195071052110382420004000c0b610390542d01142e08030344405000e43d04d01c42d00c201c00d0b0301508102800141e9052401070030b4110001030b0404113020408844035814031400e03105241000c800298141603004281d50196014081c129008ac040f038244035441c503507400d21440c444c400300c507038204402100791039580d00c9207900810300e03001e601031401d6040c00041c2031501242003240603403c1c04940e00080304140c0000a41d802130500200078484030340d01140c204400b0016020710b0303000a151035000301d0010f40c0001105c04079582d036030041142c00d03100313142d8801d540c810420803a4400d448110070009681d896101e180105008409410300000d80c102c040c0c21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 511338435 1250 511337185 511337201
    0xa03110f06042009070201090231050403140a03061e062114040f0506011a0d1109040219030c09030c120302100614010206010806160f050c15040303 65
    0x2035014030400001140049410364125600000e901d40311180c45a4050590a07846052a0040e01003410410155415048010703154000d44a5140d400001090362141e07080841c2c85001c4901e4910b03860b4004401a40415400f500a181c20500000e05440703003001e80d84800003160020b5103c000a20800c03038502d0326002c0d400080305007102c0c1e0030b241440c0a0540303514001d10003295000c2d176100a6245205401284000c00704001c3d0b00494a403501e803036409a80d007400f080e20144035400000c121030820070b2a09102a0b1000b6809042441d44034903c0003600c19403507814056071b01440758420644403400513094400c500d1000410110300d201004044814490b80c50b41003007403e100c1040850400410901980c090054034150032905017000e0380303070200240f00d150b41e04d4500076002440d002031001c0040a604240d00f6a105a40d03580891550b603c01610782030440884507290107083c2d0300a40714030f41a507000c2c0c00c2075400c0c074050a8a80e03003803900b030084511502e201d541c1004100766140c801c0e44c1d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 511339685 1250 511338435 511338467
    0x131b050909010905091e03090a030c0e070c051207060b0a0f1e1406030402030109020d0506090114040507060f020f01090b06090a152c040c050f27060409140a03 70
    0x204d2840c000e040d666888120340c21280780b07103070340546009048105104580c148d4802511058106989252001514440d40314a810001003040032940341d521416117200322907003000c014081c6004000703801c1d00c039604c80f020032100181d40ba0159841034072012032060051010382d43d096a01450600400d0031444045400118800d11400034000f02c1c0940340d10700e0460300c040d11110b449550318030129005044c1010080e6000c0003c1403070320104071000a810740326604000091040381c50f004140114080c0589008105030003100091042d6849000c407c03180c400c2600c100c2d41c00e1044048200c0c01c580000c1020784a0902e42810801c582c10246411a004a080c2d40c0810554050070480e070381c0000326000d080c7c0340ca02c400044442c00b0f00703600d00f41200c0405d081103030102403c061409400980951044500511b20380c1400052403800d04450804005400b68204d4818100400c0d00454a0010405030780300f540c0e0b4980101081814840a40038000d0307000501c80e03400e0302c1c107024001050420580d6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 511340935 1250 511339685 511339691
    0xc011e0605090f190609020d1d07030b0109020906070b09010626030d15080d080a0c050301030c14040f0606021e0d170a0e0d170606030c0405131b0509090109 69
    0x11035680030004550784e002e814421070403641501039164802804483d0b01140c8800e0012654010034000b9601c04100707030751000c0c41064110361030444191070300101c1c40040c00b60500c410040190704201c0d001002405401030810349400e003140c0e15038941507400d41e0301544c06c0c0e54881040c04540703c40d00700032006911a980301c0b400c0302480034205e40e0700c0c80744072034901040391200c080d40c003403003c50010784001c0c0400900740c6a000001c0c1030001d0050b0400c84d101402d5a00340701d00c0f4075040f0f0082c41182c0c16030340c0080c854080d4074140300c2211450f880520426410036a10080c401e543d0000340b203968080d2102d81d018101800c0c2c03001001b010403014403000c550642004030587c083c07503000880381c00c181e070301d881504541e41d40d0301b83c0000003408041041140c500810b0b2041840960020f03186002c3c900600005400d41c41d44010b00069000459a464110504210500180c40c08c1c0c40b4104082081d1301002c03c00c1144581151012102d00316108003040d000f0541c04401c1c030b42441000d000d000244020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 511342185 1250 511340935 511340941
    0x19020906090609010c08030727030507061103120c0306030d0e031e0319050910020d02150a1523040905060f0601170709031403030405061b0c011e060509 67
    0x3504620800356018802c800000700b60450341d000c0c1242c401000e4000e90b00c0c546030318010b01c0c084d040030f01c100e036180c10110181c1440c1440c40001884101526009002443c0c401d080c01420b661b1080144c418100f07520090013240d6001004c41440ba107e542c849502035100c0c1014002d040c43c200e0400d46820900220490450041c0c9000a100000703400c151200c940c149a01e03920319046108407601d40c189280c04424403115150411300600850406444150234441c9040707089071111140124038005801000c8544030542c84110341d1b42d0420800480014810703100040301c44102640c0e80482040203554020b400b2101450008900e804401c1d03c0500000125541d0640c8550700201442c8070b01c0350307140200e030860b4400d100c4400180b1550bc00345140c1d0500d0040035021030705510048030100a40f03100703440000c0011054901841d4400010315643d11098000002d44005040c01c400c29201403041d400112400d015549000c000b0201c2e001e0ba80c4441a0000d00351992a0400c60054010300c080c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 511343435 1250 511342185 511342189
    0x14130203130602160501020f0403112d0a0506120405160806010e09011805060105130908090f01020c03070906031b0b030a0203060102030702041b0206090607120b0d061103190209 78
    0x2088250b00080041e5624001000041414280c503009004c0c0e6202285844044040318020003d482c01000c46141c4c0c5a01d51082033401e0040d000e0311108030075482000500c882c004e01804c051228018015040070340c079240032a2a580101c00e000c3d1030205594103100c00d104081c001d2804000c90f090710003641904100140e5541c85041c405e800f0200c950b0030008a40c60829441001a0200604030421400c594145990354100a000d540c1c42182c013008904000d049621900030310b290301010090030074000204000c0c00c811801911815170240740c109801d5642c05100b05c4000e00920b00000582908505104c100d041c10040142c1c0b040030000c50500003c0b031201c007075a6001603858005a034030350750580100d04600071814025005810070041101e841ca24510f000550040d50342207456645e140300d60556224030541d401d4000c03d07501101caa140d907081d900228043c10b40501203d0601809589440c11180c42c0d25003100905804403e001540003600450164814804419410b041c04080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 511344685 1250 511343435 511343461
    0x70206070917031606020d05010e0708070e131a0a1d063309102d08150612090115120b06120c0301050a0b0a09050c0417030408030414130203 62
    0x10004d24040300d1040c525040040d0741d01210510043d2200c14411540d490017903c0c2010070941d46000803856500c00201c60302d1080031401102d180c010306040301c05c0440c024543c018920810601c01c000700611b0698002d8441401c4840146441c070f2008880a00f0380f912904c81c56070181c1904d2041014154078210704d07061080750f1000e2114000044901e000b05024101244202d625058005600c0c118850989800a800007500300800d050342e038045080584820030b43c010200303c1c90208000101040c000304002c0c420301c41152014144500e07020601507040381e8140202c8446071160b4407002c007080400c2e000c2e039899004241c43c008903225000e0594491050500062045012305120510020114401c10031111002e4014000704060b040500070007010388540d00655019902030b050001c1d1013500c910070b29118101c146201400c050811404210100240300c0c0d6031a288000d020206518400780001c1006005103840c1c00c0804000030309114042e010a0100a244c80c070600c03c126400160300c3d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 511345935 1250 511344685 511344697
    0x20d030b0f0a062f100b1c080903030f040807050111070807060315030b1e0606090a091503050f15011d070c030201061211040f051b09150307020607091703 68
    0x8141128120000c806030131140102c15400d085000c2c00d446035500702e010205460040d0110203000344081e10300c460130301544140103401c0c1d90802e1b6030251001c0c045910b240c0501840703500241a2032800c00b0480104400d90403942090403070ba0840302c010002d960b000620030701d11a6060001c0d0050b58901030a4075262101d41c81840d06140d1211300114040f42018411806554054051069410640c104c40120b0b1000b1001d48600c0d0076076800700e01246010f1059801130140101201402c40c1040a803a003e080d10f66500703102405049404130000742e0030300030131003028813940042c0060200b6601e10004240180d0100f00f8110ba9035200035141181c2e020800d510005034101481c80217a9450103d00416882d03001031100c18494081004010480548001c07410040f82c05000848a46420000b29039082c2c038402c25041801e020386001076488005825110001401a60b40480c0c1b0394410f01c8a034411900040142c21a10030812010380041c0641c015007003080c030120803040003491180d40d0f88155 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 511347185 1250 511345935 511345937
    0x90b01020606100c03022d01201606020d0204030f060b01051306180b030a0903031406101407020301060603020703030e0d08011e090207050a050f0102180f01020c03010903020d030b0f0a06 82
    0x41d040714024103008020f629802210003881c0385440181501542400900b51101c102039401c1c4141c82e26009810f06240201e031001d03244061032b01c00110702d90204060750303a10854059800380f003034907445d04040c4050002075004019289140d000e070300e8140101c030884541d203818884244000c007581c031009a850020b444446c1002c42c3d010512034407141e40c0018a920443c0d558100100308800c00740c1a40011520a129460070310035081d1904082064000456015030080340020758043c0c1203100364015201207600b000014a0008076402103400c1d145980c10240c04203400045103801c05525100d0803000515500103050f82d41c6210900500108040c45240c0190848048040c01c00500c441000010502c11004540d103864034075100f40ca400d1611001d80d0240a000c14a03481510103008440d524844410380f0840e86860304100407840112144483c1144503882030102c1d5a00c00b4130444100034040c0e0001c02c0e9000c0011801016500e2127503c241c002d141d056041201c40d11004031602c01e039291 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 511348435 1250 511347185 511347197
    0x71502070507051507050628110307050304210504030209090d021015081b0103060b030708011503091b150309030203070212150403031a0f06120405100213090b0102060610 75
    0x4146038580a40100300f406086c90251000340020041804502ca20031a0400d0907000003d220410344022101c103650082d400300000c00c0002c1c141e602c23074002940c0c003030303c200441045002c0c0d190200300c0c050f80740d00e02e03080410b00c001400d0007949400d181c1c0c190700c01f683c03900030180c00c00b56010080d10f030b601c400001601261030303060145906040c402c529001e0f100345011100011300e4058000b94461100c803509004c2450060040707007c0540e001107a201f03182e540c4030009564130300742001080304402c8080d0000c0542c3c40318104002041d503422006003940006c00040307058241510b403271070034110f0f030b10810600d89425018000240c010040d5110b691701103075004100306100b40900d043c2095420f0110003807904004010801d90140d100d80b01640c207156508101512240074004083c42004210b54010420302c1300c080f0000103a1586c03603020b072040041e10700303880c00d05401005032b0300110450800c015042606221b01c80c4180705000500009100504050030a400072030700c041c0f1560341140030085 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 511349685 1250 511348435 511348459
    0x501121e090309050d030503060f0f1507080d02041404060b09033004060804260d0f11030903040503060c03100302100320030f090d0815012307150207050705 69
    0x40502090700013401c0141003407101c11100d20f002415640101c030840d102ea22007291070110390900301d1040c038418501403e801e00729100a101042990030440088030140c5080000e84c080c0303542d0340040c00c01400c0c044405084094200100000e4030544c0d00030201c0d0748018020000e03140c0d8000f951540c40d200c05988094580c055000110119030000c1448042c0f00d00020001211a4400b0340d02e44a00d014558006002542d11107010401d020700c12181401c560500180095400c10740c00000c06e08039410000400c0750107001184a980c00803280540b058001140c10402d074101070003455070003980340b203078186035261048032940d000d161400b005c0c0c05025040e51510089000c2e900081d01461442140400b2082c0302624160b01d03881160380007090115540800c01a08000030300d10380c41400340d1103e640c01d544d0013142802088071000107a04016055094540c003007803100745440021442d80e0516940e0046060650901c0044918801480d204100c92000308a01084250960b00115002c4282c80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 511350935 1250 511349685 511349687
    0x90e06010305152416150e03070803070e0d0b0117060609010303050901051c02030406060501020a02010c030f0e061204060e070807030201030515091008070b13030f02030f0a0c0501121e0903 83
    0x200c085000404c0800d000484036140c5400031108510144221031501e0800043d604507425243c2c0c000900b00c0c40c0d80107104240004011a010b954040c0892500001034601880016242d82091200341c0d9071f0800200107002480741c03007000c1c420300070700301c002403000b42004004100c04090502c0003408005020030507100d01e070302c01c0046600d26203160350b1060380310f0f49490101c402544103660845500c0d2070841d00180550020484a81d502e80584540c81641e030507460980702d043e203400008041000c0644102c00301d54880000d4521251a02181c1c80c10789401d24041044070710402503c404c0d5032103104204001c10000030103c05695082c85e001c60039407160202d8031085d0302111061580080660b08205204200ea0b2440c0c0032903217001e049401c8503030b071070751040c140e44070380ca0010311801044041800418030341c4445000d020b101504540d0b0064003400c0700f43c01c1029201084410340c2a0540070400380d0380c0501c04911210510790100007400b48650702c00ca030011f047d40c0d44240152140f00d240241 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 511352185 1250 511350935 511350979
    0x1060c050c450a18020d031e020d1704020607060b0a1203050913050105132c0a03120612080c072d08030301050a06030e0c031c0224040201110a0210090e0601030515 72
    0x19504a50086401a011440270352502012195900004e030070800c628a504e040c0390940b809960090607051909080c0c2c2c5401014000062089400000818000900400d03203051501c001e80a80d60b600e4988006104204400300c584a01104c00d509200c018405562441c40404a129001d00000340c20500d104004100208404d1201920140204100c4007040701146015000b8820380d5411404402c0452500440b0b039136009801d0b011421501510020726140c000303150f0403040c0412101444d90303a06510011100f01061030300c9213010708018541600700c0c1f000d4000549400c3c0061400c42d03050801040c40e0030303ca8818042015111f58a101141a0510403040c045074044c095900c0c50380400c501d42c0e014594070700310341300500c205200e0040c1c00740b2041c11010401c516460f00b0700203441c3da400440303010821030f003006158082d10555a0050f507400d4081e80020765241c40305800c203854958900550440141680d042c58144010405010346c09004190a2002111014035058800e00c01c5181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 511353435 1250 511352185 511352207
    0x801120609020a0605040302040c021615020a12030207050609010902030a0807110a0306021815040515040b0409050103020a0801140a150e100e01060c050c450a18020d03 74
    0x80700f4040e80100c2e9480c4d00400502c140c9000f990b00340725040d4110000ca07581d40341c03101d072003121018200050200310020702d1440d0f100810ba2044a4512000b42c4520701d590288134180004294001182c0c02000f00921030303180d000540c074000f0045903c080d00032940b14402d0b601c0040c0440d000095131001c0001b80d10b10600400c0c03000e885500c6068603454000c5c020f502251401e400c048000c4100141407800c20203019205450f0395805040c00c0c40e000c1406007252441106a00c0c5000502c40031511120100203840280704002c1d022607994510b005124203010280c204045a904060f68010010310140d03043e80c001c1c00484001600080701406003002d000701c0d801803402c5181d05401e00c15215044103c800690700350704841403d90f41d83d2031058075144446000100f450f00842e0f182030b240d10702010010507020100c40c87d00034041100c0140d40581500c031030084140140480302d05408210044e8440c3d104007614420060902c07601c00701e00c107800c962000203205d03c2500e00d50f5010588a20202e10b5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 511354685 1250 511353435 511353439
    0x80418020f0d0b010201050907140909070e04050307031d010c12030204080d0305040c140a141302210a0203100b03180303070206041110090504051b2b0507080112060902 74
    0x1031119a103596501c080c0030078103c0b450045d030030f00c07000c24000070f8007040c900200e03440c4100f6044401300010511911140c0204540c100780605000012800791001160348a40d114001540d650540d5280240c6803d02500502d052460040b0080d09240d800920f0020419040600c4201070451804100c0183c811900501004c1c010310580381500d0b50035030801d078003551090148220316034560700030400c0d03880c401401590214482c0c1c003c004484400814442c1440040c01c0c101d9440603401103401641e1040140c000c1080d16006040050000d40ca00c0780c0d0000340611055240d8101254138000300d0201e401a10880c050000125026241800c110711151450400b07403622450030540294032598210380030b444000314810f1020360340c82e1034481031a00402c0d98527000a4603003010180001840020b2602c0c1000c402c071228501c0c08024a40034261100080b00d4001c10031240003008200c580c11400ea00c11500e04001c1030004013604090014191810341c014148501c5442c105440900145003010b9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 511355935 1250 511354685 511354687
    0x60e0f1504050a0b03090c090403140a05032e21020a030f0201020f060408040909050c091807080f03160c090504050a140a1212020c060a0204090e0a080418020f 70
    0x206603800359101801c100c039422a0100c950300c2d61962800180e200480f81c00b03005030400c00c3c0d60444c614003000b40c1078109000c2d1900c900206808031074200301d580800c9074140440c60120030858030000e1011a09a0000064500e00410004041e0a20200114091040700d4075080b210001024055074032140302e00d400030310803c00300e0f549061403402c4d40c0c070100341a80140502d401040b087c440010300d6a0280d0303800a0a14a86890f10351040d00405030351204035002d001e21410415640d5450410a0064040104003121188028500c0e0f1420b0410350000640360400c40400c4e40c0190040103803450000200c007160b40c1403043e0b00d007005e04150700f41c0003081424031707243c103202c00c0c0300001400c0c00040c2c2c41025000f551028200310301d652941010402000c9040b4003200d0340d00213200e030381503641e1404884c0d0050f0070210141d410031704050b001c440407440e40d5030204041003241d1090042c50340f40407140c0d000d801064a10f880300078103449103025000300c204400c0ba404c1c44102c0c10f94100d0f012240071501c42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 511357185 1250 511355935 511355959
    0xf13022115010e090f061302040510020f1905070311010c02030d021c0305090c01031a12060f01060f12050709090606020322050109262401060f09060e0f 67
    0x441c03102100420260000d08a00741440b01400d202500030701640100c01d042150b560b400d0b003000001546103100d10080e0340c090000050b9511014004128840560050424a08801c4003207142c44010104008050009103d5001040021076440300ba25044540e08140c03113050f00060341c0094100d28025003611603504070b10249580418107a070100c40c0f800c6c04035800c0d0b895031402c5058441c01c0d241c02071036401c80044419030b5030103640003d108030048403084c0185000340d000107126850290b2541c2540d0840b0040081c3c01052640c007030701405550900c440b01e510180c034018401380461a2108015548002203040039015001d4107008100c502002d12030a910b5550094882d017004c10300d200100b1554085040000c2c4448400d0181c42c0b041e52584070141c50300d60041c99100c46800103002000d01500b1040d20408240100800c50207010701c1c0480c1d0217102601003808040591003142000000081c0c0d0b01340a50145070030301100e05070319041c90019045000101d82001043d03410f40c5c042181c01712 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 511358435 1250 511357185 511357201
    0xb0d0f090c08060a06060503060604092c03070201020c041505100c0803150906121b1504082a0a0e06030f011b020709020403050c010c17070f0c050f130221 68
    0x41d0f1440340190600c1404165502c20f41503075603020540d0b41c2540010f0512041c00300480d60352156500c1c0c0c1c1500c06031580030490300c01442c4015920400c0d07207141e4000040e41015940c0403c0700840c203100a59040090070040c00d43c002c680741d024040c95110b140c034032040200282c17042002018494024440076aa81842402282c1d201c0c5801d00390750082966200181c854038201c071405812941d0340d0090881c5000d1000c80c84524003211449652190b000c140703421070410003101400241803031400078041c0c58181d00c0034a00414900940c440c9590056800030384130307111600140200c910310100c14400d80c503079200107400c2c00c0e10007056403006d601c4c041c621000106600602c0e820112541c085c0d030b480b40d4603000e080042e880303640405001544104882d0415501c600400165140280c0050346076026884858500f070b0b220502c1550034001110011041c058907480580003050121000c0030b0718144200460070340200c0d0200054002da000c00c0031060185101003540c070580e40245550450326140f80b07 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 511359685 1250 511358435 511358443
    0x504050c07080c01230603070611030f040905060301110712050d1409011b11280c0803091f02061f0f0f0e01090204060210020a020a02060d1a0a0b0d0f090c08 69
    0x440a1700c610b4580c406540044406102d0017081c02401502680382400410f032581d00c600891015184400c0181c0b4804030902c00103480504400d0b03034080740900b82001014203481030310b407412a5080b000c01c46840045d01d4401080c0702c84507a42802510384490803c008024600208000c06000300201086881e0406610010320990042424141c060342d00504075543c040346440240d8652041c5801418a22040961110030742e400d101070200c0002c690b00d16035400c0322540180382c640d00114424240c4e1421000200914546000345c00729916001f42c020746d00d0b007016100090301c59980107661030a261254000000d080c03840d540c011950341d034840a80d6084120b01c1007001d05030111001241310140b0b8021201126603030703401824207104480544000790b00183c01d14040d03101c1c2c15490401a1034820240888150810740041c0101c22590740c051070100c0c005e95244036400c4801c0c2408600014820f03202803c00c00c1c0300000d4003c50800c0850001c0c0030800703015080039541500041c0c0301030005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511360935 1250 511359685 511359701
    0xf0b1c030305010e07020a021c0606080f060a0b010e061c1a040b0d0c0b1303150203220b1305010917130602070803041a22080d08100504050c07080c01 66
    0x1940c100280d07a624695040c13105019101140141c00c100203d2000d490725500c600c0c1c0d80000e154490244950070398690342160032992014200350070112003155503200c203105d03c0743d00010482d4280b00321100d010000704944a44031419115150102d001d44c1500313405180a07001e040f28000c01c01100e8400c0900003030095003080c1c3c0c18412410448040d8203400d017070505003421a4400d07540d01d9400e00344201620b003900004040a4150a059400004a42101c2d2a95600d0034800c40046c1e40b8103108426200d01c0340e0492031100e4000042d0500000100110081c84c6e0000d011102e9a5880016141541c05030080581c050910b240050941701e0380d20b0110003d0822450001d0003807521595960b0590311034882e84a548400e810a100801640164011003036101e01000b001d185866000c43c00f00d00c401d46c00850019420820990510100303504015144400440d420031504602e001080c1d4034541206008460144d07407124041082050b10304140c420440d88040080e84a071100d80e49980202100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511362185 1250 511360935 511360937
    0x304032106230f0a0506070f060f05070813050606010e06160503040501090f0f0506070c05031c030c02210903070b07110901050105070b07031a10031509021303060f0b1c03 75
    0x10350307203400c82d4a000d21690704a0500070b499142c150f4907107000c00c21a90466001901d1000c0c80d112064001550380c481c0d50340d18024140002494140384070010503141d0700401f080541d901001d500d030045000010070640c451424a402030b60502010080b4600d4043c1529115074012621007a80400c50088003620507985d0a980d000c090030f5407816030002c014014030840c084106403410902c0b2600742000100003a9000b0307c00c01102079a2840400d1510410441404510b64400399041d40c070b95040c000c540304815103100408551218282d00c00c1c80b610305505258500384006060559a2400c1c4844030081c880d501c0516200c504605120006050140c12584140f0490001080960280045e43c507025001103c0030010b94848505a004040144414080b05e84800710714070720303550f10b103280c810480c490b41c0c0100d581c0b00d00600302103050309a40c203e40c05890040c02414448510f059000d000c070380d044040031130000c850004680041c220001625005a00007100340c9504920400c0ac0c0e83e507501c0703 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511363435 1250 511362185 511362239
    0x1812071a03061c080a030f02070209070c1a060f0909010f06170d0503010320040b0a062007061710090c031a011d04090c05040212040c0f0305030304032106 68
    0x94030f01010011400604002c0841000b0303c00e00040d18032070b03030081d401c07801c2c10880140752240540000d20304c0c00040355084002016800900d0801c07c0c0a02100640114601e9094003402c00f5000980f04103035440c0061b0042003c6c20000b02410003d4000c007007051200441001070039196070065640099084a1500720f208105d1656919481602180e0413203401c400e4940c00c41103d03059103415105200b40559110392190a1800c043d40c600d040d0a0050015481c0d46003c140110304a1440d0705c84408142d00b00d8000d04000c101c42c079048104a00300004012079402c0b40ea03100080c812581c0b459030000c4246600e8101c0007204942c15900a0002405406580c81a095003100444401e05212032044c00f510300911008a00c1c10300350404072100740b0503107282c6500c1c0c2e1214003003800c0360000d5803282c04007080c800c148014070034500d032120084c0c0380da0b2004005050560b2289a0751303100c094001002c10056440c000c40b180c059030381c4c1109580c600101404425990761108250429a807500600000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511364685 1250 511363435 511363459
    0x80d0203182a0f01113c1b12010603030203031b130501030e010f180b0108070e13020a03211b0203151f0308070303060501051812071a0306 61
    0x2662060b0020381d000001601040391821418031081c0200401181d050020603454410034000500c8110501c028140810351000440ca2541605070743c42c02028040c4480720402e803000f50004100d442c1201c00b001c01c00b0340d204d107484000c2000080c54107002206946031600100805030302000440c000d0a0201c008041c40c2c40313580c2090641d200f01040420502c540c41020000f55010740c02000c0c14551050000403000fa9401900301a01c1103056042428064608083c0030448000684d601500288000b080b0241c00c044e07507205a801c001d0f020915107141c1841120840d0f6500084038007a55026a801c08c929801011840070640712a6a260215071128110350441110769514000c641d001001400003c00300110300c102802d010f000100074028007510b0401801d10b260007040150721459500d640c551550034010201c43c6150809810000104521501503e81c81915040520205c0d2090f181e440e0f805443c500c0c0040715404454400f484118803c2c0c080000800f45d44103e00564046003088 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511365935 1250 511364685 511364713
    0x180a05032a0d080910060f050a060305040327090204080d0905220515040524010503011a090102070305190311160b1b07090515180a09080d020318 64
    0x34030303005030300e800742d100950000700c1e50302c5085569080442c0c002502e030080d14100c110002d481c542d400a00b00b50a042c00100940c0c140b06246100500f080d260130085820203036401012455100c42c01c2d90140e20355409000b03c010a0b0103180002c240341101155241c0c0e4441da01c07034950840304410310101d4591180042c4500380f01c02c2d040d40d044805c03c0303c00740042260780300c1001080007400d0a000041005003420b21074456211341c85c055010001c2516000c0100c00354464044503071709900e41000418001045040e03070000b00300b00c01060b500b0074551948c420200403403902e030b82c41c0d202911521542c03041d41988161800c25240590180c0da8000810714a0f260440d43c4d6030180303404070611080e2040400070340c9080303005020000404074141c42c5012080c0466441c00d141d03500610502d566034014490b00760003583e020307042e10b582582c4c041840320300b0081d52140140000c00b030344041501c0e4001c14041150120469000340c5000c1000c640300e040c02030320191028001c0c1c210f40c1c414880c148010f40321b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511367185 1250 511365935 511365997
    0x5040b1003080a1101090b09070e01090c08070c0323090f010302041203110a0b010f1809030f0509042a090b03040c090908070f03020607090902040f0e180a0503 70
    0x150b504407100d02c2ca041c4840c03500b282c4140f025400c40145550300c0e03001c1e000194414890350f00a1040d0401017400300c1c2000015002d081040c0c0c410745031305250014104e03607103401c210450f0b4080030f07600740304480c100c03a030400303482281c00a4120031010f10341c5c41c0c0035034000c224a00070789440c0f07109541c000000c90118005500303c2c40f503030040030856085500c14200282c41a00000c00c048403000c10b891104c10756554428040c0000e0b0011804240c0e0030b2410721900c0c900c0421405075601d592010311050020b6103005d000503903250f00350800c011000034071524640381c54210300540c0c451061a00c4990f8100074a80c051140ca1105200c0041d41072000000e809082c442664001c607000901050314038a0135450768010120341408a903011010303c45000461800d09550403a14042d40140c6a94038001000401c2c0b42040e82041d440c0c0d6105100902a80045442c03078410f0f9003052013501c5854941080396080300f00b490b414901923210705030f030410401c10007102a202c03040103a141c00300c2d5804a4450b054407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511368435 1250 511367185 511367189
    0x70f08031602010f0902011205090102090a1202090708010b1614030c071707030c0b07020301110c030c250314010b0d0c0e060d08030a02070f022d060304081e0d0f05040b10 75
    0x5010303901c8d500303039844003a40801d412868410005250002490116106500c81e0703000384107547c580700b03e400941c00d0140d4400c1d4020b6140c503151070741d176060800c3e921482c0900340d11103480030fa13000c01d45c0040144004603e90001581c004407600c403644088525074605044c001e89403620719038038008416450010b82c9a00b943c2c2e212900400d02c03400c100a41d010380d0016031080c0e034150340f04c850b626400019107004010311040c0348040e603911004e005c070700c521f0081440880401c90b810310407420394408912884100741c0c2d41c005c1c00554100034000c1010301500900c1402544201890030103020440d4600d807200483c4c0007015903441a40d592820044503110700e102c003804020007000090207500440d401042801e125080e03858003102c175070b00424603000160804001a904400220b02c003540d07024005445598216401469407070555940c1c04507001d60030058019140110813150b02000c81e4003070b10803801d01120100100d0380710801c0c060103440207660941e100e544040104550003031003111541 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511369685 1250 511368435 511368437
    0x130309090e030301050607080d020a0816210b010309150204170319050c031b0d02010b0904050d0c2105030a0c1106190905011a01020105070809060c070f08031602010f090201 76
    0x1007075070b1a05c0709122850740055005c40302c1079020418803002d00624405000450700a40d20314440d0301e8809002107904600031103000900107a10303440b900c85030f541d0b101d40b0445040000046a04480da800590103880c800c200100200c800c01d0b41803042007490341c00f800c21960310b50800c0911300c00f5012030325264482c00604481c2151004800c24515000300000d2400f000f01c903003168034100c1419075240348815405040c40c0560081d9030400c1c501340d424010140010f104450f00803050400b641c4407030791800c030f0b50b800c2d00611440314080c0017440320480c20300500c066503905442c3e5800c240f10f0000c109510485c1c003807189901d04000b02c1c92240c422107910156140b10002800d60351103610104a030140c040c02580d11982d1540390ba600010070030300420300e0603d01c002da100e400f08460000a4250360700207011008000c0100704002d80790300700190840d000440445442d542e41c03054107042c210407400c03c030040e00c01040003003407200d100d01c0c02c55602c2e803911040d40200106024070000d2420b64440400c0a4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511370935 1250 511369685 511369687
    0x703031d0a020126040f050c1c0b07030e030a02061e010e07110c060f0301030b0c1314040f06030b061206090c0603130215030f0105060306130207020a0806130309090e03 74
    0x10010350048881c84d0200798024141d01105400c60100072140008640845044004001c0c001c01c1080401c48030007005401c403003802000f450995800391801c10404003800b40e0a0380c01c0401c109902a6100f8905000c3c400c041c0da9464110084c065a238a109031610502c170b80f0516441c41b11100c20780c203100c3c1038810396070321186036171507010341255000c07286840b18a40e0301545c0d901007138a640b22001800301d0040d80f0300c1e0f140c5039071441c20b00e0a9480001043e0700790f04001000742d6902407480140751815500003101d581c020f58140341c00b040c01002e140414100c4c032440c0580c080184059600c00c01d2080f941180d280080031150156507450f01c500f5125003a45521480185203c1d142a10146074024050855000743c01001c1e0001200c40c64001800c0b01104000820300010320360b002d130400e000d00070035a034051640c2000e001003044600344040b00b5444543c0821010110f6644800701c1000b0400f82003181c18034184000210514050400d0840100300c2e1000300150615003030154041c0140048003075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511372185 1250 511370935 511370953
    0x609050112050403030608030307020d2a0b0907031e02030f16051216030c051e09010308070311060903270a06140f0c0d09060c0f1106040e0c0703031d 66
    0x110703024040281c411000d160f146c203004908a9420005541305503203c0d4001d01d1805d030b02001c00380c2209440341d102e20341408203140000d06091500002034215502c508484131554500c901d55041040c01e0304020481e9440c501041e041c0f031121710b503c2d020b0038000c0f402c4e03034101b441c11440ca40e902c0e040d0070403600d20340c00361103010407080c50210791100e0241c249005540c4618004444158014010b0304100e90903142c00750140720314180754102c1c41d02d411011020506401884000030740f18941488020003140000512104061007103d004011403010310442e9101c5c100307661261344039040f500c59000d0b000040c1110620001c26114410038444001c1c07c11007020b41408400c84201019106104000c5410000c440304014440000d101d1724041c40017500c007080840f800148101c2d041d62204080000c03554055021599030300d08110491340c040a500e071200c85000104c0e85078080d0394040c029400b04d000401030309030345220040c5403540c480d0b9010010307070080b1000791000301150402d060b125440108a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511373435 1250 511372185 511372217
    0xc0f020303060a050f01140706020403050c030a2d060e061504060b16080c1b0f0603090d120e010e0703061d190204090b0c1b120a05090a09091a0106090501 68
    0x388072803c010325218147c54032400030f048869208000880350194000740810030300000344504003820508070040c020f000341c4c80d154030780d810f1034400c5a94901200421030f10201810305525042d03071540200d092001c103100301400d5454400844c0d0395100840b80c845808401e2405114602c250b0350391882080c10550100d2607540c6000380000c088403d0407040010489a0300108078041c2d9031680c1c20b9004000510302e00921000c5542020482c1c003c520900503c40b62410216080d01184410724180307401c590011a20b8000e080850b03050b03261546440d010a04291010881030140d82c081d000910496902e1016000c0d100c103a209000d4068001d061021030340700b04041c4166609000070000319020b0411740b40c113110b10394207940354000b941d000a50068804541c1e0711000d07003c142000501000c101c1055041128842c06030600d0410000146820840d9070790400d07403010300403406040000b480c680c50440200b400c051812440c40242c600009246842951004165401030751030442d5120f800c11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511374685 1250 511373435 511373449
    0x106050724060e09100c0813020307090e011a0a0e06011206081c110105011a130b030c041a090102030f07060f090809010306080a0b0103080c1606030c0f020303060a05 73
    0x30038102000300070146084480074900500010f40800e03d020300003400c1218210b45005100c2101c003103010b0406c4000d1215039000304a0780c2e4410301c4c1e401e000e003d850444c8002424041c0c9600040d503102d2400040c40c0d10010b0552040c117480d00f04090701c1d86004041401c0004c03402841c883c0d200500502800560b15510490b20105031401100c004204151115400c07410800341b100f031101800102020320224580c0000303c204c2c203860000c001c00903941021000220810301c2c0c982e1507500a40040c5003040800d501007071000034070814040b16101e05003040c0d00a40382d4000c0c821f0078050100080f0b8565224460340c00c50b003581c00d058004525107400b505c52084540c01214040d6401e80d5221451544291103010340d5004c24403c2c940160342d250542c0000d0308507440c0703820400c0242e004000340740004182400160540e608050000d84848041075254600241c2401031086001d00d000300107100c0ba01500402d80710340054480d24103c44404ea0b08036620b00080303031364660140f0064030070405803c1c4030f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511375935 1250 511374685 511374713
    0x9120807030e0a320105030f07030c170112020108071806031109060a030f11180d081e041d0f0402100e0418150203010303050f031302100206040b0109020301060507 72
    0x16101e402003643d200c805440381285070103864082c0130900303082d40034008070103100100c645007420018114109800d810841c1d180041c0303a401410390702d4070b003c52080d0003a06030380740314402d042c44c2803106d40c2c407121200c2101440640482c0801d80c401e0204980341e0141ca42e10096004020011003142d140c09011005800c66820078114103604121100039502e903800140b01c4040d0a45001c100d100403203801d10101d80c840d104150410a042c4101c0c01c0c0d000084400042203442200c1c0d0002c003800c18100400d00b441a00080011141c43c034003800d50445a60001c1c000300d038076111440c03071b2040c6d20200090503c3e00490b8204405101c90300090010300d80035500081c100790380d02e002c400c403002c0712020400304c4a000100240c0c0e083c03950110020041d50307540010340341c400c43c4010360442d45941d8001d8840c0c010198041303121080800007820440b18040c0c2030600070b40007000320051812161010703450703e000b0f03201664945040c60000c0f65032032030750080764100c1d8542e80d14186010003e845011101100b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511377185 1250 511375935 511375939
    0x51504110405010303050a0e03010b1c11030106030b04050f06060a0b07060e250821030c0c0a060b13060501050405220f0c09080c091306020903120a09120807030e 71
    0x19081090440d2568450b8074041c4d4030a444656a0328240030016101a6080b4070b0355110b68180700c900c4031b00b030719204d2010310074094114a05520034100d00e445410b840c8569013090701503292190000500810382412802140180c05442c0004900780d06c0645404044a40d283c0100d010f0400f0803070801e81c8002000034602981c1e00048006846602c0c0341821010030180e440110580d401402840001d40e500000300081d8000b000050601d9000088500341c0c4e4100b1208440c000c80003a00c2c1840038401c88285400a10644010840d14503000c0010000c00700550b020f100001e040c3e4801400380d109c0d90058480503120310742000e140c1001c121002840503075190503916021a600302c100581d00402500400844003c52222125000206005100e91145825070301c20361a40f1400e0320b54013507294200305441e01c1860089858181107002c0e106c0c04501d150103209041100071500036940140c200c210341030352080d441540c0e48201400e80c91840e02c01034044481002002c0000c0c0c000c0618030b84400300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511378435 1250 511377185 511377203
    0x30c080d240806010f0902070c1a04060e0f0121141501030c1d13020f070c051c05030906070507120302010f050106050a0e0409020406180e06090307051504 68
    0x909419003040d10072031a00010404a0038030072070304200c40d00750307080c025040b40300c000e11403985000b0100307050b08610321400300460382c00900c40d81408004560380000d09503c040501d440310400040346440c0d842482030b840000e086c0f00003030301a8074004e800383c045480140c0d40c001e10b10324881c840311f00000310058450f1550750740d06040f001c1c0342981402c140c82400c0400342036110f00000da00140a407400c0500700303020031440ba10300d0349079400d11800110383e4400a4400c414203002d01503845000b449080d900140642011486000b0403800b000030206841d800d0343d40000745c04480b41e000541b0300c145c0400600d903030001e010800e02b90502c24040c00d4480d01038002c85030105d030365003d41c2c10000760055050340140d44031214100c0703142950040c18010300403440d16500e0700c810440020203900120342028403482c0c032080080f055540c1c1d0341002c030240001c1285808401003554044c0d000b0401c00c4c4203800039018140000340805804401d031400180c010b03024200e10744260401c00d4a400b802801203481a034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511379685 1250 511378435 511378447
    0x3080403211103040b13020d0f0602070b011e0803040f0e0405160611060105030a02150c1002040609050102060c031302090901020c0d0305061807020714280614030402060403030c08 79
    0x1d403401040070764440c1012840c0d5038100350610341d0240b030740200f050b00b000540f4050030006840d00303d0b40c00c004070b0b088405809503415a01d0700384060b200d5100c0240c001c1e42054000304041005066000c500002e514045460710340d80c0040940b00c0c040c0c0d12a054509404040400c10300b000c490381c00360b000d8419801d0b01d084246071510360004a070f603074203d2000668040200381403208200074050140204034000c16100c840e070750020f0102800c07403150060010010034003032402c14040280409031205803100795191a140c000041c2040a41d125180c01841000302040c0317030485c084e003202e0145c0300d107504a15000302d0326009d1100c000300c00b5000302c0043d9420400130554a4050126141d0392481d0740d07000c9114180302c000c06c01c05c1d840424172841d9614654040c08083c3c2d8001800302c089605021120fa0540002d4000581c40090f00340c02081450320720811100e0110b0842c03081c410354900d03450300c41036608030024220301030204840003074000e402000144040b0f406801200240c500c175428841c5889 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511380935 1250 511379685 511379747
    0xa02030c250828060e010606110d0302030c03130807060f05192c01060509011d010e04030e0f15070c0302010f0201090209011a07050304150f0c03080403 67
    0x1603400401c180c01100e51401044150440c0403080180002e1004007105a4480c400100d2440c078401c00b0003420b00807240900400145070005402d112050b002001100e82c0d4103c080c3c000301b024140c000c85405040d1020898a003e40301342c9001d085449100c60441d5116000c00c210070851960640d041035090254000040303071801507059a003900d0f00c012078181000e5442c00020481c4a10b400c04440c10140312003d804041c1c005150301c1600700b80e0340403030038503140502401044a6000290401c00d01d80010a007492003503540c0b0841c2c9541c12594001c0d80e40c5200d8000e10640654000380010109103024456281541142e004040014034031707600d5601448140945600c210300403104014003e070104107541c0c01040e4802010101d000902c4030a10690001d1a094414041da0340c417040c0a601c03000c02811640c05490f40d6661003000c495556072a01c90722024508601c1c501d0000a084132900d5680510a84680da03400754103444071001c41e2100d03902901c1a10811488c80b14141a01d21240814 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511382185 1250 511380935 511380943
    0xe0d0203030c10020a0e1806040b040b0301020a05030603150f130c09051510031104182003010819020a030b090109081b100b0a170c10170a0603080a050a02030c 70
    0x8440c40d070380060740c170010302c03801509020340c2e030030b0f480d102c0c480b103402c0b03043d422519404d06584280b0484000a603285001e0000303000f4441642c2240e007561000c552105007c4e0000c00843c010380b070440840ba004060301c1e10200740c4140c1100c0607903060401c1c0c5d002c11a1441100300542d655031103503803244000c0b91680590806c440b021202220402c04007440a40c86041c503080c00f1101c041246020711140c503c2c0484020350303116600c26500e00102001084034402c0341640030814102100100c1c0d10007000c0d014604501d60000c0c0210841c0f80104116072010942914205840355405090f02e4480d510796112200750b030000030301404141d52507140140010f01000020300d01000c0c60b085580c41c030040701c4101450041c140c000c800c0c15070329198410080d80e88950144080301c0c100c81021402000400c9078078200321311174a0b00313a04440080c02d0406d406400003000f03040618404403100483d65075010070710945029200c00f4101a5082003440081803140d00100b14071802c0d40116031901111404540c60 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511383435 1250 511382185 511382203
    0x10501080d050a03060e070c230c0d0201051c0504020306090a0210050724020406110105090304030b0903121302040c05031005040c1106010f09050603030f0a18080a050a030f0903030e0d0203030c 85
    0x60203445c8c0d103404000400408640b030801c81c0c2115082c02040820650f07031040700180180c0308914004108045a1103101200c0b20404800720740d0829824400000d0050042235070224407038020500003903a48840002d41c1d619a03a001483c441c03142081800540359a0320200041c0c910b01d140300b40741000b80310012003950320f11310010001665245014001031034680408a402c10302e904110a210484a000080d41c0076a5041103080d00c0075100e92188170301e1841980c2886c51083c541c0405c00540001e4107400c1040345000780c030b040c810580d41d03450440d4584030403241c502c0011b00001c81400380d0301300f582c088410b0b903500b800c1842041100300101c0b46042d100764018882c12840501c1800f081c405401a01d070400800d80007542031961a080d4060345025655902e03041041000002d1010445e00e09002d00510111050780c0fa072a07001e050254a0748030b48901a8082804441440c482500c034074420300c2140e400d5911844003503040c204001581e40030001c1640d2600c010302401842d07241c00e100c8009 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511384685 1250 511383435 511383437
    0xf0b1012150302010c080d0b0a0306140c04030228050315040507050102030304080304060c050f0d0504050c0108100e09010b2707091508040302012a0809010501080d050a03060e07 78
    0xe000c038642804a015625544071092078a4403001c01000140d80141d0b04070442035104903d03d03110281c000703002d0018a1071605840c0d008181280000620070550b1100c0040502000c400402d9903601420b002103100b01c1c40020341200012a0f00c1000801d2104405107000e956002d8525183d0356200107445e0241015000c0e448500d0b20301408204041040050014042800034506500d45916101180d02008001030811034441e20255139040c070405c200c40c800315148171180e0701d4841b100c0c81c0c2002001300701c600316000e102e150544105503014035107a901c2107103104040c000c20fa0070103204106100f00501007140f659240c1c18040c075207540b083c0b40d000d000090740c2420000075010442480d20800054900c0d418051130810602960900c54400844c0c400c40c0e00b050b81c0c054070b035494224010203402c44400095000119005d07104d844070119609010080da64441180d00c64611355805c03981c081c4214810ba60007600008055806880035180780300c1a401c001951507a140f10304071aa180407140c1710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511385935 1250 511384685 511384697
    0x30e0d0e040501050d020906130e06010b250c12030c02040603061b0305040b010302040b0f090c0921030409090f080703200a030e060c010617010902010e0d1101030f0b10 74
    0x210300705441454014407048138030304103480c6550013090050b4006001c1c940a41c1c0c14980304070b9184c11b150465401e03141c031041114000d41c0d40f80e1115200390071260310a0032000744021800058403105811205203900844007040c45803400c03030400c0e44080c1500e4100d041c400400005005640c85200d090000c41c01400003103080300080c4490011403011400d0034086c9860f143c2400003092524000506580d41a03800091030300c8040d00251448880c40b0400f540300c1c98800801c010040c190000c0c2660300e5068030b21000d401c0100000781c07d00707401100c1c200515030003440100110340150300108582070103801c0510b00602c060300e07040c9065103d68010340100343d0000c9235001d100e1004100244101e809000b40196043e5a68000c00700c5060400c083e1207002c0100316400e070010b0a5102c0401000b2010005c0c0104081c01d0f0603034040e00d02c0a9081c0c0c041614031074002c0c0c441c1410341a0309134969000c44256201d80e2614015401050311040009105580320141d05103610340035462381a08a0503201e603 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511387185 1250 511385935 511385957
    0x9020301150e010f080c0d0f1e0501210b0c07050a03020303010806010614120c0d0f06080c01030c0906050a020307080c10060803090a0b0d0f05190e01061401030c030e0d 74
    0x1806010b0b140402c6410800c0780700e003050080ea4010303840c98008480707031542c0c0d58403002510a0b50150108509080f210b030700d440604040c80c1140c4942290b0702080380c409000750b0f0790303c2408014a008240050880c2078540400900085602d005190b109820141f501d080401ca6200c6030701d01001003070120f0169000000501049a0800410f801801c40e803030680e20001c00d160b981019402100000c0b001100c4290100310b03142d40700300a03500c00225080c0b003001007410700b5070310300c01030503040c424820030b4081e40388140845d5101e8016005c180180307468002c2c1003841c042c0b0445140d402500c5401c21804103000d004005140100240880c2c030352403004050041205900b88100c4203d5031100c1800c2c3c1c0700704100082502e038509801c00b00c80c0c11083c5a80c030342560801e02c402801c0301108040d40d1341d01d01010095581004400c3c03c0c181c1000d40c4040007501d0742c4040b00b50803902d060041c10250f5a1001a06506620035081104050000e150105031039040c201d44030310300300400341ca110104940c5071030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511388435 1250 511387185 511387187
    0x304150606122003160e040b010f110109200f100906140c010204060e12010b010219110904030c12080601020601150c12030506040f090209010623030c191d0603100902030115 76
    0x130306c0d0220304c0100c1e0204040340311900041c21050728651000140a0308000600580c1003c1d449048015000341d200882c880114000b14018044a03d00c50301c1450740a070310010700d0030401152003e1040d140c03134a80c1d4880c10a04140e81d190040042442c98800400003a2910340c1c081c0083c1c4010141511020007151021080049a461104240f03643c1d81c50b002e50460b2582c0d001800340728007101101c40e11031200c3e02e81403010307002c1c1c0c040566640008800062108045d48000c44540305402521035000c502c0c0e4000701100d00b403c0683d8800e0042e030040c0014000d511060301540341182d2103041c0550200000d50b00d588042400700b83d960007081c0d6640c20808942040c1c0a050140700200238200043d100f0783d80010414401800784a08200e21020740e24201c02400f8070025043c501c0903006526460010a650000d60100d2080e004d40000d44001141003801609841021075890041d846082c4000e800d0004c19040189425035204450030001120000c6200960203005440c560740005241d0306d0b4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511389685 1250 511388435 511388447
    0xe033c070213020904060503010618050c13050405060111190312091a1302060409060303170c03040f021306060504080105091203042009010605030415060612200316 72
    0x61841810804001140c01030766403004400024802500042e2205a0000842c00510030f42d04103076015843d00340042115420003060b86031903500f8100a101582c3d80c0004051140074a01034080c038143c40c1d09013440701d0300d0941c01c815840701c1c062401111a040c04a401c61404020382142c2e80c03801c200c14206001e040e030205d42c3c8285140840024012048a55980b4050021440703000003000d040344041002034510700b00c030382d01c1c1c0ca07001003281e510f941c2c503a4410030003440c8521046000c511104c3c401a00f6031403c003500752041c5611b14649040d80c3d103948a4a00c03c980054040f40d000324615485440107a880c070907130000d0600e43c2c0d140340e01d45042c45055401c552015103140110f41c003010311090740d0403264085a0303109074003805696801c840580d10240c0c10701d8048581d9444055000041072895002d4003451090307008072140180c036490110b2006c00c0382c01c0ca002d4000002c020103072114130002e40750010194000c080c601d0100b201f40302c0390b1f071040756041640e242002144444190943c20781c400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511390935 1250 511389685 511389787
    0x15050603030f070b0c0409021c0f110a050d0b0a060f03050c0903062208270a080601060302070206040302031015090b030d08091c0201061a03040809040e03 68
    0x14004610381500c0b5900351101c2c0c003412400403c24040800098001d5014034190790081000c52801c1d921282070100504030203000c0200c0c091140c4c83d0078051111900306000324620884405200d81c40d004031420222510340c803690f00c440213a1b0322114184070076119070602030011300c2c90f03580382c8000e0406801c00801b511009004582680801d004c403070f485540100e102d42e00501c0c45059010890f008225207400884205000303004001c0100f1074522564501c0f0b4090204240100c1c070754946140c2e9020801748400f00d0044d8111544003000501c5124040e500819100740000c007041d040a990764006483c000180e145445002c0c1c03642c81e18140b0300300b014028005803000e502c0c14000c40e01640d02190741ca056030034459082003440e42c081a0000018000050001d13000d804c51f4114156140000e4040e02e214070900d6410b0700950f511500c80c9a00c50700303590241c2e07405410a80390062170741c02c200c0500b804544081040c0003c015205600c56103540c010000180744224090b004040c03d9100c40c1a2401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511392185 1250 511390935 511390939
    0x5490213050a0b12180d03050f091b0f0a0807032603010b0d050711061e07180302061e03180d090806060d061e1a0409050d050309010f0603150506 64
    0xb8600501c42a41000143c810700c1d48603140040b00c030341c2c540011000b003140d0043d84071060300441806840082e07044e04414410018108a61055290501d40c80e0340c80e03c803141d0b05200c824004403042d440c2c0c5011b40310b0030503008000b000411096210b41065040210700e5008643c41c0c1300e1044400d01441641d00e192000d030551040c402d0444d8941075522403144106812003d03200c2ea0f500000d074030756000d200591501c0007a1022200d29240c0b03071460180444070490704a0502203c0310009000c2441102c66000103111000d00ca010b8901c1e55080c0420750300a076007405400410040000100c1034004003540c403502106112901ca44080101c030b900f043d501c4014042002440d40041c00500c4002440941198041e18604d0300d402d04d500708040240300d400c501444131b290340314541150740d4040e08560314202d07007018032941c0400d83c00304200480d03445480052064001045000225016a01543d03105141c10000300b0410380d840c182d80202c41c2c0740d03001180c20310060303088007601d01030601c40e580c1d2081007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511393435 1250 511392185 511392199
    0x608010f120f0f0c0b030a0509060a05130308060619050a11030702010c111f200114010302010807030204150c120207060912020a0504110403120549021305 68
    0x41da2941940a4040340c0080d045145202e00c9800300a045140100101000c05100351681811140d80e000b13000d0540706402d0600c202404140189610b12450b8004c5081e100c030501c07841999603054940400041035598408824403e012010340302044ea0000c41142d91796403030b83c68019460140c41d06c0c203503411f0040780b40c0c410b000050050343c200e0180c1c00800c1c6c0010841c8101c0742404005020407141561082820000c000c0c0326000c01e4000c050185949040c050103080089100007282c2210080d25074280d06003a0b0744010000755024560454000b0b500303213005880e15403103a00200b03002c3d05a800000004010b00400802d120300f5400890f101410391004e80420741c6031240043c1a50f10300d01402016403410b003004811941c450001d04001c14010740305200001008642d994107400a03c400d0b40ca1381341c42c28125846511801c211000c2d40348001090110048480c024130501060707226042a900300308a4549000d8042c4e940f441504040d03400159848cc0c20702404691421158400350007581 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511394685 1250 511393435 511393469
    0x605150408031e0705072c060f010503070c0c03080301030b1e04060e0c210d020303191805031201060e0d02030a02060a140c030c010b1002100e12040608010f 69
    0x1c01104881180e284510702c00700b14a40701c680d0040324890300c00d00800900c1028400900f60b801c000c1074040304a034016031030811210702403145442041c2104c04580c05050301030840c0380c0d98090006540c0101c82c500d0514524074450b130700c1e0340c00b00c03041d60402d90b4403103004001041081440110141d00c80c0d0a04c540320740081406808110604000d00010505a1100b0081030540030802c814031801c080107101c5414400500441080039607000c007001901d008e14070880d0546800041100d005030460303200d44207503080d5a19100c00030000300e54070700b40110004150402140082000d00075180004002d80302c254580030b009401ca103904803d09004400402c006c00c00b507500481ca03404017940603206075a80c1d40140c0403c55100b40903000d607050801c004164070004640c00006090080010f000800015040c0d40800c41440010310290300140c0c401604149400c0c60354009604242045d8110740b0090902c458450f45c07500250803c0000580c00001005110040c44a9400500500c00c031000064 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511395935 1250 511394685 511394699
    0x603060c04030f020909010213060c02120703081c02070602121501030c090b0f04120302030c07120803010902070302070b03070e03011503081209070f0b03070e0a0e2202030f0106051504 81
    0x3c1150001038850fa81000000303802040a4049032110302110f02c0c80320a860312041e0103020340110030000d034020303004410b68480449000848800392600300d51510700782071075240780c825880301d00f0500018030b41d028042c0c04002407450014040c48140400001d03000c3c504070001d1080110880c50a60405050445100c211600200c944060303803200001180d4829201385108100c0c4100d03401091480100081b4006056000c8058402552484107a070a456580e29a00351500d041d0000500b1411040004000600c1070780c2c010800c2a100c0d0068034061591483d0883c040d410495641012424102d0094941e140a10400c9011900d00d046500301a0031034507078481c01c1c05401010310140e1101e0010520300e903020402000104802c3c4036070410ba64946100e501103030825648403002c1580341a0241007803515205000640301c4e085401c0b0110340e80d400600c2c0f00c0c0281c4e00343da041d19890369490750700561001d02004070014860b03400880d01500d082c1c14004140c030030b26034560b540b0905000500c488 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511397185 1250 511395935 511395953
    0x209130b01030e01113708040308010806090c0112140c0301140d080f1b060103050d0f053a0509010504050712080a0c030e031c0201180c121a0f0603060c0403 69
    0x209040540380d001030b200300c0900b048003a08229190384186c50162104c02c0b883d4071804a40c41070b44266511006a680d51400941e901c0066421400c150007004688050394070500fa950707400311351002c02140b001c00f52000750804c4035003901d440103140e40003c014040c40c48401c807230403003407102910142c0a4148075264108180201d00304800134242c00161284d0050320980f139401280c0056003650310303a503500c1c90040d654681c2142003001080c0196190b01c00140120305035000d910002c448846800c40c2100030344d8800100c0e40c1c070002c0200084024134407002c0184038440c424005500005400d0609050044c070302822940020807487e2600b0072100003d18850550f409081c0b0742c10a0311030041e561405a07040388285607040c0e0140706250800841c2c1c0c00703480b100e507031054440c0c0003040001090105504d40301407922000d0100480540200704d501c288a003009500c074040c400d200701200c2070001e50381a42d00240c484185334000c6109100c403924051001030782118040103040d203881d2660b5110014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511398435 1250 511397185 511397197
    0x1204080a0b0a0e0d02010507031b120f060f030c09060b030c120901060306051608060603131403130602030301030b0708011410030902060a0201062606060d060209130b01030e0111 78
    0x7201c401804900c00ca41190001840b00b80e1000039601c02d2103048000a000740300407241c0c00e002070b003000d00013406e160034806000042c00c441c0e910890440d010142103001380c6007240c20854000e581e0040091014000d00c03a01000d0342c170410800303811901d0320a501c003c0da041034028601e481c8040007030084030078254046800020307000404004a5071006041e03030040030164006460705041200b0022001d40030308041c1c0c00c081c0903494554150f00c45009200361800b044988402d500c03402c6142c030010840955807010400120011640360690b00c031501d035090041d0782d04c4030003d40e2004c001801004403114402d0350000483c6000d004540c0b400d18056011144515040d0203100d6003044014058441c0d0070001c00290068a166640c51400b44001d000300104d122f1620200c8080703400300035148850311440e20001054004244c59120b00040003015001002c048482590801221105440310005040150f6030b0220014200c1924070024081d142e04994500301030b498201e50f04421100740066400c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511399685 1250 511398435 511398443
    0x1060906140904090f021023250c03030219020a0303050306010210050108070513050405030910090906081b0409120f030603080d0518030310050616150b031204080a 72
    0x1070391008440006218820035014030340190400c1e141006000040307840341c3d219807090740c0350107051034a1503007251556402d03018050700a001b402d1103000046000058800e8503001c070710005c4850300d9000361110690106900300c2c4c411514920401c18540c06100d414a07550102800c03c030000302940c001481ea5503e4040102801804030104505034801c1181603851191a402040302d0750f19500c00320383e50403041c1300340c83c8100008800c219aa076490701400b8010f81d8000011801c10b40120204520488060050780410803035160005501106002d400000c045800242c01013100f1045001e44459182c40b200c0e00071424a814540091566401440480340a2a01c3c545804407112b04402510701030b4009042c480300814000c074642079540c8654090144a250300d0076000f0b65010341900c81c002241d20880c0b1151a075420005800c001d40200900040403d440410301560354035020703507003452081902200d40d1940000c40030b041c01c006101500e4035064440303042c24a069500c075035035051088010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511400935 1250 511399685 511399697
    0xe010303031109060703110d210902180a060306180f030e04180606090b010309020312030606120103060509060105011805060903030705061e060f060307050705280204050a0501060906 80
    0x4282d5903001c81a40c0070304800904542c0c0d42c003001d0900611403003400e0403411082c0541440145124001c000f809004c0c4900c414404a0f884000c11402c0101244a000d076000484017800e06003224503040080d05c6030b408103c000601902b9801c01400315001c4a44403144400f00010800100d0000c0a8080c4020703490f01d0404501800c000c0030030f000d0a44ea1800d000c04900301c06d0f19504205072a08420159a840c140c100302040810004400707032580f056010350150490b0803182e88003a10b24000b103620500c003820092400615000c002e40100c400d030300540c2c00340c2c0c0d20404d10401d0300341403011500409013407070110081646004241941403180c8121403184c88002100c1c501c2e51424402c0d40d0041d0b8000701a11020f1606e1950160701c08054444e100e01d50750740400007102840e003128945008000030303241500750790f04c20b041030b60203a00190095415100b055000e00070100303450b1100384038503e9800307c034051107031074414003058407030103007020183c80e04010062010940c89480350046403054a045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511402185 1250 511400935 511400951
    0x320240405011b120e0303060a0e040c0e1815040c05010c0519080a11070e040204020d02070c08070510030e0c0105070c0902030708100503010506091b0c0609010f060f0e01030303 78
    0x38018030f4401044140107000d80032103002d039038200e60000300d001d4581e0030903c00304000395000c81d101c0c03200301d60030f6511614882040c400ca40e8940c0075694400d00c01c486480046803075810440c02600100e45000082094005003903c4c0b5909109503200035000c078801c6007003414240e0703034400069401c2c0035090400038850701e04030a015080011031111490704022400d80c1c00e2034100307140194051074012003c5005500f40c0c40c1c0d99800004c20000703c92140d01c071a801c580f119800c000103580034a02c0094841c0d004c0c00a07034041000562600001c1505000402556142409115890020b100101d0030305151038640040321402041c10010160309103401580c48220303180c00707590342c640da4001114441c80441004403080c0c000f0750316401101c1e0002050360003aa908100342c02c3e0f842c03c50340140c01480c14004542e8441100c0c5030004020f12200c6a00d042a241c3c0c00650701c1d10400b21001d07005a0344903100b6100d03241103407080d00b0190040c3c0f03030031042841c00c00040200000701032000030100340e510481f0f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511403435 1250 511402185 511402193
    0xc030b04020a0804170f130801050c12070e060c0d0c111e09130c06030608060c0408031812010908090a0e01050105070308060d020907020616050c0a021e04060303202404 74
    0x1240c5004100c110f0454651f0703071800100c0000300250050ba0340c503601e410f0216001c00d600744c00752500e030101400d030320109681e0160102d0b1084806541650801401c2c0a045213078034050101c540c8801e00da03075460042c818182801c9840d0141124042d000310750560444e0381d5404540001d6a0741c0d0f2094802c28210b450348600f001c01d041811401a10612240c00046442070b4142c01103002c49002d2030403100e80d0f4484c440368407040d10882c811160036901c1004110500ca000b8228007011820007031114110800030341895080da00c03008004c4400c02d80002e4408118504039034404041e145100c80110f5560510001900c2d40c4a03070350010f818040a400040d80320b549504c48130f000c5680c0500140300c68182160702943e11501500c62500c1c26503a424103d120a2082056a41c058805401024480c8058086c4102c0d2094070320850803140c0c204000c5203180e1110700880700110311075550310140d40075820980e04588503800c0040f2003a0000c0750400034001000c211b01040d41e00b05038a0100e26225490 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511404685 1250 511403435 511403437
    0x5060106140d1505060705030304151503020f0f0604080d2312280b0405090a02010912031e261905150d1b050a031a09030c0f010c030b04020a080417 65
    0xc81315500100004100c2d041040100c06580250710400042c009020701c07155942c00c2c3d91003288800e030b000b11245010400342c078200800342c1910a000e010102da0000203030124001e5031140e080100c0552112924410469100307800012500101c1045505080500a0702d0700742d10520003065048030a180219901c04034030381201440030601640711070480050752140c3c0240c2007801c0c0303061085282c840043d2aa05000c11034202d507540c140d44121540782003800c02c041c030f45483c1109900f0415000c060a41c00a40304e100d0713002c00c00c03994481c1003100d441030808400b59002c010507510261007060901160004103081d01285c42c040180104040e40e0308001800c1a402d00c04185910050f407103501d10611070039a00b00e103580c1e40080b0340300500680b03440a000e10f00b06035200080407481e1200c0b07102481d941d01003610760000e031500c00340d03841e2030984000140713009014447c11030030380d41d00d0b600c03082030070b800d031041003070300310060398154240b070441c400151403083d00410181507001c0c2444105030341c0815030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511405935 1250 511404685 511404689
    0x708010207050105070906080f010e071701030b09160b040902030703110a0807120c170a090b150a060e012f010212040c0f08030712140408010905060106140d15 70
    0x1000841d241c401c03074140355010300710980b40b810100b00c68001c08071700684030314040c0b0312522907030700c4200349c5920700b140d0501c90b40c400070100410402480c121740c0d0300b00c64551500d4000e5000e000d0b884030908081f00d00314104540c11140000c15607401c001008000c009030161401c6903c800c0d030040c0c5076958403c095000c0c291980c01003004610000b0035031035483d080f41d4440d015203c40d0350b404440b40035480031007080b00c1100c00c0d1480441c49200602100c14002e001450303000f4001f01c030101c0c460350b803541c51013100e00f0141c807500240381100f40e120304c1c4e9040c0b0a105900420031454181f405101210010706043c031f03003001480c00b8110002d0014003642040e0a10284100894021036480448007814058003500f07580448013540300203800202c2000010035201510a0480610b14065032079581d90343c8031691040000900c10301c0c0b00c0782c014101d5608050001014444008140020319140c65810030005030814804d00c181e42c01c10340c48640341201601c003144048600000c5016039a1940180b0a2440d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511407185 1250 511405935 511405949
    0x20a030f05160603020d061a1606060b0a0f12060f03030c020a0e07020c030c0a150521041a0a090b01051909090302030a081501080c07030e041a03070b0c1e07 69
    0x2d5000100c150f810b600421941501d100100041c80e19402c400c00c2110071140784403890a0306001d0131061304c0f851890340340c4007440366000241840da14507018045801000f1000042580d24a114003525000071410b54001c004007420080c4c40d00b401c44641c0a101e06000c050f0030040ba070501e12003192940c5108a0190400803429000c03464240c4000350740da003120084501901410584c60321a0401c0040c26050b180c80350608042161440782c112003907040040c01c90071248501000410b54207403c00314501841c015402ca100c03000041c8451120864050714060100e03103001000b0000c2002940ba46064031b200700c0f081c0e441900d4003d600b03030f4208030541000351803920703000e40c0e44100350300080104801032503030b2660940c1e40d0b2100e101d8400c141c440c48a036030220b000c0d02e0008214410f081c00803c081480b0b41402514444202c010504907244e01841800c6640400000071075464200450401854580586803400c050001c0443c0c4071b0041e00340e051052807024407104030340303481482110054200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511408435 1250 511407185 511407223
    0x71b0f090e032a24150102150903070c0e0f0703020f0d05012903091b120a1103011a061917040606090f062909060d02070209090307020a030f05 63
    0x2c85035200701900f94003044611030707101e2680f40611011300300550342d13076811840c424482e055071107100c1d100b8186041c4411038118042c444190251030703e44a4000e003c1d88a2100440e101c403040d1820002c81c203480d4210000700856101084042400741e00c007203900c9015840c0140c0c645212409403242e600810b40340407400f60801c0300201c0d529034148000d424004070006400352000d040003281c2d6451105035100651074200e11702001c8100b204c0d040032101d0900203005007d0017001084038900307100504034101c441410012204016182c240a45038000c0c030115660b2442041500c0018500d204486802140c00039082281d46c109000d0710f044c1c0d4140c0421215a2081e103000e24042000384414060032190501c0c002c0300d401c120a041c8101801c3e50360744aa40c6034114400d0b05180035601b00300f81c440c03a00f01c0041001c03144644906000d0414084d0b8280056107400c650710411403150b5000340041815401804014003603500c404204040300d03000024615411000e0900b81c3c10300b806120440e625140b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511409685 1250 511408435 511408477
    0x803030f150d0f150e120d0c0e150c1e1c080907185001091d070801060501090b1218010b09040803090d0e130c03060812071b0f090e03 59
    0x481000501c7c00700141c8604000c000310495060b030b82c090f0001e151681022003840c011203250a450000c0484180500171203c14180300d400440740440c0b24a0850403035040120b0680c08034186091840d960250b030708240c2c00b1841c09910300c1d999010783d44107505030340d9058114450380c00060b40c00001c151100b03550b8016400450107505521058100300f4a02041d4a42c64405c000c001090000810001ca80c44401c0564038144294001e440e118040d20b000c49052034100c01841002c0202000070f040a20020034698945030000d401c1003c503a0041307103844810814500c03006c04400c40580d100120220046040340c2c145401801046113025942e040400d000c140001e200340383d0082d6104025440444009011040c812075282840842a0350042000200545041801c0e0800725800c0814940080d44039580c5070264580068865440c10300341e400510304040c007094404400d01141503090082103645840c5902c000241e85116800d040c6a440182c003241003401d1085804044500014000d807030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511410935 1250 511409685 511409713
    0x70932090f100e04030e120102220503120405060d0c09120b060f010309030206040605150d060905061b0702040b0409080304051006060e01020703020f01090803030f150d0f150e 77
    0x340095958029514102d07000140d0120341d032119130b21842d450380d60180058058004e0181d00462480505615502400044040000d41d848881e0440303417030301c4000c1400e01d032100380750404598031100002d041c0304010900858407050111580b50317600d59000a01e21503400c8007201c202495802c02d640303407184254980c003448440c0c40c4003030041000702e85e4001c00d404010010f6003110010710004025800800004000c291158419a8801d1f107464001d1a0010307903c00184648a04910840d4010350f07070400c120a1000402640303500c2200603c80c081801d6005130091243d01074140024482c1c0d8441c112922142c4032038100028042e40000c81e43d4070383c142490500e4860641a61410a051a007035001520078403d1000d4030800d841a00900f040382c0c19a001d0140703a655070046079061084210000558800400042d0300c12105110b400e101c60900c02480b1520f107100d916011f200d006000c1c00c51001ca030009004624607070348020b1b905000300d444c0e41e207000580014240d4040900031118101054 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511412185 1250 511410935 511410961
    0x2010b010e0f06070b0f041703061c060f0204170d09051c0503040b190e0a0f212f01050406080723130305060f0c030c03070e040c1707093209 62
    0x4c40c8150488d070780502007101c02e0300c41c60001308c034901e5014080c202c8040500c640801030a181c540502ca02050b500e414400c40e0341a0ba000d07034040340055602c1902980840424004802c0300b80c030510303044107168640000a8101d520f01301d40c85186450321034001082000c01c00840e002001c070742181540f5403110070b221101540c0c0002212011907400c007410034851804503d0b200603103648440e0140301600b00080c07184a116240408410103031003c4000012683d0085207d00c42040d8007911000780d68403a048005a29103020783d9030500c1030a02c024800950880e030210750102c02c82c40c00c0900340d0320041c400300034174000c0000030300060400030b0360081c031001c0c1070041c00c180d0340103808448950303c070f00842200c00d6108403449048034000340007240040100704010368000d002c0b840d0500c415440c00c80007030308481d07401d02c02802041500c415940762541d10203060368004400c2c20000b501514041005101420661210380300944104c04007007001d003580020740d41008041d00003862890503298060003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511413435 1250 511412185 511412191
    0x10906080c21120c061e0a02071e3206040f05190803010602120f0415021005090312010602010504020102060604050c0c25080d020309010516020402030f0f060102010b010e0f06070b0f 80
    0x119018910002c0c032017020040c6c0c1c141c02c000101100300e0290383c9140c9454020f4209031400c0f105030100006450382d02d8880d10031000364500613400043d1150440f12444940e6803e0f1881d11071800e220b08810a240e000440d60a600c07641185400c0c81c0160146412403c050707034800d41c080c02e00c5401e0b90800c2400340003070145058803c644c0840d01d040124880e1240c113801401250f601182d0308000603c98001802d0140080002500444181c00040d0f4003074810399000301c07082c09103948003250548121030b000d00024018a102d000800003401c16400007034442d1801800d50740216100d001180c0c0001e82c6004454044085c070050750300c590650207040210720146900144280c0e0303030907800710310424042041c00795000f076900110f2a00300444010741d01500103e022108080c0c90140d0300002da210340c00190300c2062820450003480c0b9140c10380740c40b05440a010b46046a240ca108654166001340c2d03c00408003084500c1b4071034a0032a8001038a5100303446000301080000018054680344e414101c2d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511414685 1250 511413435 511413457
    0x80f1308030403032702061b1c02010902030d080103030e0d0203190c080c180406150b0d090312060b0405010806131d0d05211009020a09030209010906080c2112 70
    0x445000d4401724441c480c0440710043e5020008020490b908400100810300300c98144056800c040844080501c0e81c003420702d5008050303512015601c0c02c524050100c814042604d043c4003615506640300281001c070324982140c012581d41007600259a41040180b044414401d60070014898520748291a21041d1280e5002d41c407484401d00c100340340c804440d418074017000b6181c11442d41c460700d40ea00130f00344245030404014690040801d030b00c0320020041ca5030340b0780b495011441544500e03004142c21035011186030103334900030041c0503410014040740d040f40d0007443c24110948a40c400190b004000640c1040001d20b0b20711590100560080d00e84040c1c240390003603900404003010240c3c4c442c031850070070100c059448104070040d1440491100d8014a0403904001e100d030f280e0196108981c0403000060200b048100c0070400c51502494050140c01d02d04001d0007800d00d090407991703490150003074807441440c80d454490484040412140c2c41694100c04980d00d40720100c040c60516801003000303072 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511415935 1250 511414685 511414721
    0xc09130e07061706120a02090a060812271c022101090c080607050301090c0c1212060807030c0501140c100603020f0301051e0705040e090705040606020d080f130803040303 75
    0x4d6003501c4d040020390302d0b42d0403d8003c1c280c2103249070b00300100d01c01d0040602290a554030000b28040304100714130804c070046c40c000d50f5511900e04c02d1a01c00e20722001a90b84200240040d42011606e40120821a0803801c0f00560b2146250344001420454000b805811140c25100b6481a02005420125016000f84441c40889403103a5855441c3c0108640100209008000411208480f0b6006001c841490718100303180da4005c0d501c04a441000b401a0800289503005e606001d000510a990083c104070005100880c5950f03552102c003202442001d05200701402e0685814200d50b045511000c1048140d42e002060051802c005110500041c0c2c040c03060000c3c02060341c1030512555008583c55903c00760141880143c04041a138020000e500b001820300001446081e224000e41c012503044001d44005400e0030203000c12111280e010204561002403500106a004402c041c1c07c0903c4e840c1f8090350380e079201100e0f020b09142c3c0900820720f1600104100078994507503c2100c0118030100d2403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511417185 1250 511415935 511415941
    0x41413080c281b030305040e060d2a05030c0a090c031112010305060a050c07110118030b09060c040f140f0a0b0703030605041a04180605090303100e0c09130e070617 72
    0x83e20011030300c0e0100074003003102008140009103400d4940c81d40144010704050b0600900d698022801c3d01800b103c0f880300900c410781401c010440803448014100c00c1d401040064001000288850364910840d4511039446500c0960310b0300c40c0d040b21f54245208040f46555040003185504a03003000d110944e058000c2c0c4020405400441c02030b5409111104420350802c0901d49a90011251400109041c0058200351102032240c1101f00c0c0d00440c0200285103492910000321804c150700201300031048501000f0512540c0002440b650a540e071068500c00f002030458041b44903c0c60200c001603024007071502c00500c15172a00c0c010600d6274480d50302407100c15561000d100c00c0e102050382c21004c26200c002d8504131070038541e104086900c00041d241d081c00b125038681c030007184d105030b40395142a0000001c00030240c0752041caa44c000c0038180c17440b003c0c5103850b41d40c170307c0c41c1c0c001c087c40c46100718204c40b400502520300fa004091550b0020055854841ea2418003501841c002010240022004c04c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511418435 1250 511417185 511417223
    0x30f05010c1404050112060306050a020a020c100f0c1e0c05030d110607050a0e060c030a080f01050f0603041506060f0311030c0d0209030a0c06020c041413080c28 71
    0x844400741d00c4400c002d508180c140720040d10111403841c43d4041c0a03580340e000102056140c01414007481c4040c0c401640e5200b2048000d08060103510058010700b04d031f090140281c0e0384180c82c00c0c0c11649519040c581c904182ca00640324202d1746e003c0002e812924a81c520901240d06082da048500880445106c55822801a514090950000703040341d003000c400114414041d8008042c54201450154800701107980004d0483d0400343c1d00d00e400c0d40c0041025852160046905d81e0011811074840e0f11039071410001550300303440325007110b0082101001081c20880c40b0030b0b249040610806050200d40d48a40b0000c02c1c00c801c240461002900f00341c500011a1720501c122030065600004c581d10304140c140d0301d503000e98001414150180b05488001002c11103140114020b4840c0b50b000d010030030f00c0700b0f080100742e920721014465850020741c00d210510101215002c021540600c2c85a12209800a86c9091440c4004a06200d00301c068a0040c0380307140a2103c89800c1c86002c10b0b0b0369125030201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511419685 1250 511418435 511418447
    0x7060e0a141518040c2f0c0307030b0103060c08040b0c07030309050f161a090d05160b070b1501020a0605060303160b0f010906080a030e04021603260903070b0a0e07030f05010c 77
    0x2d684004e880103c0c01c007101c101c1c00c6c44040b6000003640001c075207101c0445004280703001102e900581344210720f00014401c0140602031000c403036240340340100c46410951152000c650000c0e100b43e40c038620000708041018000c0e0404940395810400b41c1e1040041085519210394850101109494050401046400d120084000c7ea513070651060390405090700288402050407107810384040c4185c5504500510880010601408074001c03083d480b10030701e2603c6480124054001a064550f42d69100c8850342d00098050b9000d81000e0007060b00d0f00c5480200b801c0d803080440040d413400344c00301c020091062050030070b40503c01c238491565090b80c0e00e4400380c088414070b026061160f0058a26440880d210702e401d4441804014030041c60654200840d00350814196000c4001c00d4640f440c1308001c1c04120543c956069414041a2043c5812100c3d00d4803480340e0400140340591582c003090003c41164803402c20003170003d080713488807070b120300b44004071071114001120a98205100d0b02c2d58144100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511420935 1250 511419685 511419707
    0x60c0e0301050c07060902060f03040318090221060103060308030106020d2618010609020301230f0603071805030109080c070609060f051b060a020c07060e0a141518040c 74
    0x8010541407141a985e400c015004901080c1d920850502c80e00c0050b20240c8000c41c0924442d49540150380800401c0f800710050380d40c0480003803803042c800703440ba10300702242030094420202210002030340d40c440182c2c01001c05410290560304088004a02c3c00d030005010101405142c84408803c50075150200c4511a40341e10031050942c1480410441c000509403191546591800820801e45840000b8102e0f0000d074003c1c0244400d844100b5100c440d0807443d0713100718070103071652001ca03203203800889c41c1d80c400905044100010007104904c0700c3c00c02031010010340b00041c001d1011141030304000245800c01d1660030040d000b503070800103d081c005c1d4111022200152075000c8129481d140590341c0340c0020032000d41d8400800d0b07030381c0380340ca0081c072105106600a8900607192105000c5541c84c22f60a03401205c180501050a2041a0364098114040b1000000030b015600d1070720021440e00c503404405c900840e070022503600e100c0d46410400400b4440143c408001b49000e92a049456100007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511422185 1250 511420935 511420951
    0x1d12090616020105070f0309050f09160503090708030d05151009030b040317070903050d0216090207053316080402040536010501120c0b03040c0e04060c0e030105 71
    0x104141c0010740e030481000904107005050180c1040b4542d22501c421101134101140000c600308070900c81440d00740b00084204005031607500d0030303261598040d100c030003041e1054030500c0307400b00014604490400918014100c61802e698644021400b007001074002620210808a54503a800c2c890f41041d02030900030b000c0a1351100038061a580300c04101440c044c0c0b0a82c1042a0b00020285244a030100d80d4000c617500d6a80c45012403540c14414107200c80083c588003190018194403c842072550120300c141e80210500680e9030340640b510b20300c0c0076082d1a0458280c0a04505103181d036a00103500100c418000c800750301150f5410803070b90501804500283c4c0810300b480040b40140c18654401c2d540110920307d98070341002c09200d241e16110346035111010748550107000385007020080c0a46801808c41070a00c040c00074455407410407580c014007035101c0320000440010288209961080000c21500c0b403d0180d41c1000d0900c1c00180400004850124082c208031407210b090500c02d192040c0d0407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511423435 1250 511422185 511422187
    0x10201020a0225050d150e030924120f01080f060402090a090c0302310e070312030f0f0e0606010c032a1a160801050a090c02010e011d120906 62
    0x20012843c0d1800d48049405a00301540e40c6010401e619030321070741039816001d40c4c0c500c0c00d500200a400c00a03600382c4008554690070622214011b80c44210280d58455420700441d55a01d00407040e203409401081c0000c140d914200f004d00060003410943c1a069425400543e5445840d086440350b03a880706940080d0041c5018000a028844660203c0442c0d44201d40680f840342e520340020308030380d5482c0c400c1c06407904c0ba4501d022810000110b08407040038022000d02c1940c0030b100e42c841e10750a2a10000e851640e481c490440d459200c0d0f80248240300390184104000100903924000030219419102110310403540071070442c1d0b010b800c03080c2800754980d8030403451a50340307612807a64000e0000420701300d001e2001c03000009031400541072084405600c59011501e040750030404500c0b900302410302400740c2d2400522158035000e0180c0b055540484001c1403c09403001c0407401031841606400d81ca5182c01c4e58002500314030658508a01100b504907020000d90140021880c40752506a5600580c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511424685 1250 511423435 511423453
    0x510081c03021602030f0c1206010f0e1317090a091517150c22030f061505190e01061d15130f18020306090f190c02011406010201020a02 60
    0x101c00c0d00204000881ca03100c543c021105980442c0c9032043c50b03000707007546800c41c00d80c4207205d00340480d14003940040f0b08018103039549448000454030040707008110058100500241c13292010402180001d8bd00440c603102c4103404800c00680c40d003142002e1442200045800039401542c0e0041c214024080240c502c0140e240000d05060504903031200701c0f02d80104004000c2d80c180d071070f205034400c0103810540c1d0b03551140302c8901d01d25403030441405400c8400c038a8050010a01410714007491640c04800014004034518000319215110b1340f05550100901142d11070300c3c41080c094004484040c1c0701d0600503626040207488008168104030001d040c0100480741e2440e010342415006610803107980c1c9050303807140180c151304c8216049a06074a840080c2003025680c4400043c0140903181021811810050001002c3c5d6401401d816035186080000c1880c03000d0790505940110304102040106114544002e40030780702e0030050380101c28070350780004c030254018001c6070080d070f03a194082c0800107 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511425935 1250 511424685 511424687
    0x10b010e030c1009080f1f020a0206010909170313110f010509130e0706053402040b0a0905070908010e06060a030b130203120c0606041a010c05010e030d0510081c 71
    0x1040f5645060100020711600045101081c803480d80c40b0319201000c0c041e0380c11002c10659580040310301003003044d8410003007510610b030301040b0541500c0c400c4401084201807410840c2440c40900c2c01c9040318000003040c07040e45040c25980c0d404a1f8814054000008494002c00104d013170250313180f5012903001c01c003a8401d45010317035080349002440100010442041d081d114504100e40e044200814000a049444034101c8100c3d0f030020840300001040196a0300d060241600d03070301c4070017409191a803c0700b81c459920440b600000d0901c001081129241c81c036030003010000343e031096000c55481c005445154a0020036003034801c44000d810580d03114a0342d600c008400500801c0e01c481c009224841000681c0c003444010a860029080c8030344810390701440d54240704001e41400e1045141c0422904445e44150201c1e90700c04e02400d10407030500c1c6d5814001c0c09090200401450340c04001004a502d104560080740104001400c003840aa2180c2040c0d0381c0384141c0703070800c59202e00164007420107 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511427185 1250 511425935 511425949
    0xe040f110301060c0204140f06011709031905070204050c040f0602031809040c0b030709030b090a02010212090d0807050d030b01020316330f15180f020403050a03020102070203010b010e030c 83
    0x940f006d840050440303801d03d0307007125121003030310000d100304610018880f05603808101c11401c100d0b681d82e4603003142003080070b0942d43d2041c030305450b03100700c0f416041c811854002e100303840c0000e03000340c0240203901c0c2c9406c8040d81640140a00c50410541442c0410b0481c0300005680d00c8980005e107000744100458100700d60140020000c070740312851100d0101d50f16030030308003541c000c0075103481e013510319404c44c0b400c1a80d1050007072464849074804101140036030790018001019005210040d80e4410070b000105e2150608420040c00b102d000050500400c00e0008076182840710302d0354204480061440120f8891040c42510300c0c844000c0188980440c10078a00201414200e4805107005c001c030f80100a1800c040c803c0140c9066640c2c000400310000d9800f8040c4100d000d12590102c1078102968051882d00c28441c0843c103c2d902c06401c91036903450740c1150081c42d00002107681c00e450620b0300038040e51007400102c5c001c1d401d011481d44a94040c150420841c24000c0282103419000c409010f0341c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511428435 1250 511427185 511427207
    0x90c17090a080408030306100f08070305090c1203071509030909050624091002031c0e030706060803070c120c09050703090212070f0e040302030a08180d0e040f11030106 74
    0x8074040d030407800d40001c200400910040080070b0145880c3e1422004120345d000728110f030102403003001100c0e015006d40c0401c1d81383e4400510300700021341d41c4a04060a1030019201c20058211261408100da2014004080c00d03900d4480c00da01a061451440780005650510718000d010521245040c03000d90941d412555015070090a000c44240350b405c00b0100503181d11500741400a1300050540701030412880d4003c1511b100e00003186031091042c203025080481c000c1e09020542d580c081410016002c3c4129140039170049000d0041540310701407961a5031140300c04580340e6143c0c100000d01403055803281d827141504035441d030030300030f2810b40c07400003500000700310100301a900d01c0a1401a510039100201c0c43c40e410b0000c00c1044c1c10001c901071a40c000d40c004a81d8a0706000810000960000c111a02c42803549084116a1100059004400c07000d4903144000e00441213001c00059014101c644050700403501804590554918542224600a00b426a1140801c01800780034061449122 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511429685 1250 511428435 511428451
    0x1b0905010f030e0307030914040b0f061605030403050d0908012f1c05070e030309092802072607020a0b1308010f0504020f060307020c100c1a04030306090c17 69
    0x62000c03183d060860840c1d000d80c00480103d480349809000200c46c0118400a07580161020400c09445d0400038410000c1010110321603040000d0401800300d03880810b0550680c00001c41c1e80391516032034055103d8200c0319900c000a41c40388400540044140160b03500e144101c0c003841c02c5030f59868540070907800301044154074040b08100341c81d04403581282903041c4600c078030310000c0e0b641441c0d4401040100d800344024030992050244040c1c5503160f00c0942e4110361080c410200c0080ac80c840c5030400c1515007041c0206a00c00319000d070503c0504c4008035140c640382d1300e2150b24404840c0c00c004546c0201c1c0ca000c0d40000c84c210082c040d00940c1da00a1644050300382c0380c1c07806960390b0b615150944e02c0002e400f4840a4071803081c8011810440100e01d0889811140300d410362800050081d40c486403103003039078411a50441c402e40708900400d4000c0b907194001506500e090b00e54258640e50030400e590480010b8138000000a8041031413182200f1484960b0340c1640d6407032000d820315510760010301090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511430935 1250 511429685 511429691
    0x1b09031a2e090e01060e062704110f09011d0a0f0606020705040f0b060a0c0f061d0c100e06090a080f0d090504140402040c0309060e0304091b0905010f03 67
    0x9001101d800d24000150155800c1c0c10901810a80c48409072282d00b0082c0c01541c0c1004030500032031402a05441e0301035000d640441501043c03000c810b40003840740161041c540094400c0c4814001a00000420b40000347d61039403080e1482014402880d00c24030038550a03030002d42e03114012909064800390403c3c90444c011032101d1081c031500007240c29070340c0300d0000b590100d0b0080095003013501030b2100a94000a08019800c0d004001c1181072103481445410041468011b01c100410240084c10680d0021000c0200c122101689103215800780a10202071003109861441303031801585903209007a080d80c03009580e1f0020024403085400c23070348180d0ba20524104010526240400c0102c11641d000c0008051780340c80100040d181c00c1050b00014041d0b8145010112911a0700c81c1c00d43d04140c0c107071000550140200c00880c028481194010b0005041c5110300c0070103000000600150b070618042000b03940000c5510903003112242ea4084042103104100f000650b0051508100d203205a05000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511432185 1250 511430935 511430971
    0x60b0a060807081f06050a02010501090b060702150f040b030f0a270c090c03020919140d0f0b040302030307030e070510080c0f030a021c05060307030204050c0c0304091b09031a 77
    0x80149201035400c08800506c0100c0e06030052942401920300400303109800700710342000301d40070078180e205503c40079004030888a03080307480c03240c000c04071580320841d052800d48071a03d62082d0100d6501c241d40b2040f8810742e80001c203000b0462481074a804424a02540303400302a08030f41c80e003c5e00d4584809480f10900c00d14000361501d02c50145182c050126500142e80306100b82c1000082c618903002c070303882c6c54800441400b60192040d401003855000300c03820012582c46240030742058890341d00003840d555500080c801019000005540a200345403001d0141000070030303803a507072040c1e94400c2c503070310282c0071100490701409980b6250700700020055540c0f40c06810580000945c1c0142c900c000025070008440400402071220184440710081003400541031070b00010365074902da0300000c0c0c421580c03080460381420881046508140b00413050f284c54580e60801d401c02000f4101072402e00d556241d04104900f03100391810f4040d40c2d400f072071206480d140b032040c0c40c080c403200030310b1909032802c20911 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511433435 1250 511432185 511432231
    0x60f0a0306020c07060809030a021b0d051e010b010509090a020c0316030903151e0b03030412030201050415050709030b13170a03151a0d02040918060b0a06080708 71
    0x1030010f080c051006100030707468072a0007030080e030f001845500190002d0204440ea0395010908541944c407800020040c20b81c5840018030074400311000601d580304000c4401c5018000445125049005030000c0000b184012300640b0702d80320b5401c1d0300340e10818000009660255540c0904414031645040b00c0c00c203511842c4601c4076200300c80c030035004039280510800402088000c0c040e00d4100c0c0b00828448071034543c0384403410140300c0070b02900d90340e01d82c1c00780207481d1800c20a583c0200003425990380789043c02d080c017900814040d1015207446002e00441d481c01a00c6029850180000d45e64501e1007174915220311075502000740000441c0340711f0064541c0422100300319400d401e000388040387e5841a6440c80074007142c1d011f050103072280014007020040d0080481c041d038880c45841024540c0c460b84022824004e1280340c00059841d40340000c4001003516485d912048144038000400904018000300030401e8081d108080001c0d024000040401d4420746105030800c2182035180c0484844800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511434685 1250 511433435 511433437
    0x140603011a0913020a0f03050d2c030a0506330109210501060314061e0c070f080c0c030f0303150607051912091a030601050f041a07150b0108060f0a030602 68
    0x3102c4c4084008580051051040610140030403072759500341410070640c100720f120a0651100245925549199800e800d1601c0c02c5c0040081c46500009a81e10761038400c181003501c54024011440c038000c0319070980e1011001e0f4400314691103058644a00c458078002420b6009558be80e07600c0700480c1d040e010703100050f40034003814001e5072180c502c290410031604003041c50020010b00303803200440903107840418800b5a002598011001110440c0c1d55149428070000d40c840800c00245421b60011702901c41c11000700f880408140b0450a8031030300d15821074826524003040d102480d0301e1800d032014902601e02580248a5244200151001c2c40c9080d0004041d2411005055a60710074a0740350401240d40440c1c07040180c003c40c80d0b00d10b400b80070405400d020703002c01000a814001c001035030f020b03003d4842c000d0790020595192403029941e0030150344480703500a6403048590152620106890041c1401080540321060b51a02200e988030010800d0012000c0e075899000701ea480008030104000e80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511435935 1250 511434685 511434689
    0x60e130509030d1b270314010b0303070f052406010309030e130f05130c090513120509090c032404020904060906080f1207060c1e03140603011a0913020a 67
    0x80b8134070300c106030031003000341c41200303030311050020645007041e0b040105034001d5014042e00e4118010210001c1242c503c54018010701ca00d86030b05210105845007002410043c07488200e1081d02900c0c1156101e01e10782c0103c14074244019198603065000441c5548607500c420041400380c94030b449440d0b045408138141e0828420986c1107181c0b1000055a611036600442c0d411140c2040481980012526540b01d400c1050141d0340060f07848501048414000c0c0458245051b089501d402170220540c1c800790a42c0d01600c04180540490300006005940ba041a82d1050603001800a99103400d900d603540d41c8400000f960390303c00d9080c080c81949854030310030400a40094000020b800c3d0614000170701c0c10010200c3d0703608552101d102c84e22800d14817000d80c1c805c280d00c05030104d0700140900301a07403d668201d9003480c005990300c1d0b20080056154001d142103072013403401c0c0c0409864120925098850b0000c0400c180e0079010100038007402c0c01d2108561100340b241320004408040d034006003000c0865 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511437185 1250 511435935 511435961
    0x807080d020d06060e1c0f081606050c1201030201210c030207050f0a0c0506030c040b030a0219230a03060b07060c0909020909130809210106060e130509030d 69
    0x801c42503030080b00d92064078050720507800c10f0b060703140c035041c0058000b6810740002c2002488600c110380c10003e001c0e40050500f1b0307200501c00e131034004158060311030080075034041e56607601709408074601c641800115002800440301c4022243c0c219001501c80c90810f510001481100f44450b1a07078142038419400d50690a50700541d4070000d50820518205466220740516045012081c000606280c26002140c01c01e480d556165039600d54840c10314012944901d1814100004110842e0b0040e030045c68015824424003005040081040f29040401e029440e42c0791030700d80d0503000400d45180a468025071034a40460055200c0c1c12a00d09508000c2044455503100e0002ca01c08a03001022100a403c5d000801c5040c030318040c001410480c405070861281c0c0361480501405e01032204100d840300c4001a1251035811280e9480840d036550b10780c0c00011035403900714003154440c81110700181ca083e0042c48101e0703024450010400404001d0117410080c8410080480314810a00640d0168580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511438435 1250 511437185 511437187
    0xa2a0611030c1b030d210c1103030903031012120302090a170309030715020703030c141504021f05090f180124030b031e01061a0c01110918040807080d02 67
    0x6401d0529007440d2075170440a01454100c00580c160f92140c00c1e4030310a864440201e0451201c01040d00d4401100598004c50700001080081e0110000010b60183c50a40ca00141c150396842c0b14035000038007124000c0c92007404441c544001407094002c0d2019190041000f020955109011080c400c0480800b4440f40c0001c01c2000f801d1500b0710024004000440003080a034285800082d1107200c0c0b0b000041c00d1056407000f1006100086070141891458001102c40a0300c240780c400d25415001c85049102c3c403444404006203204c0480b9003004503900741c5416081110314000c01498000e0f00120540089800c800c2210032892003281c14020144007101d111510406928014040d900307500050506052524000c4240c4002410301000c0c070f15425425003100450721464003419042e4407841c4010f10790301d01c542d07040840000902184015100030001e0000780c0c40e1291503409042121644441d03a4a40f18100203419040c0b154000c1c8207001862520140d0341c1c803400160000c00f045101c3e294 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511439685 1250 511438435 511438483
    0x62404060314100204030210230f0d06050a06021f15031208060301140601050705010e030c100f050705160305041503060303031d030a12020702120a2a0611030c 70
    0x150030f00904012592001d410341c0f503d0700703680220300a80c040c5202c1004001034201c3e41300c9040c85125000c02403109001c030041d9601601021018035401c840c52080d045440c000380000c0518001c0350030001c4030035507006041d07581581e11680350909945244000e44c030303854a950449607100c00705624051441a1944581d02402100040c1140801442c480c081c0e03240403503404088100d1503145074005c100740780c05075554245180c21400b40c0500705421485202c003103060b1480302404502d100c0f00c40c52800c01040030450001e0702c5000e8507015106036000c6031040204070b0140c0141c0528880d003500900f003843c985076440c0c2040400709035241c020400030365034107001d0042603454061020407c0401c0c2c2e204846081440d0103503180d1091a030030034207229103502c500705461140d4065031130f10790300205982400204060581e0300c2d8182c12000b2200c00c00e400000349201d1841d1040840074006100072445241d007801010781d503905a4040400c520f2206000c140c05840e82013220b07106c40c5030400d0050074203203 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511440935 1250 511439685 511439723
    0x120103030f140f090d1104060b04050103140609060d030c08030f0103290f1b0c030c010b0303040b0a0315052106061815010e101812050624040603 64
    0x4540c0c2c1900c404140000c12880070540000c8040d900001d50071030b1a0304c041c48542ca040d0102081402c00150004e007050700008400c02c0c0840903000701c9034280c90621064840410401d03441c081280d113a07a00c0b00b0003c000c1a22810900303201c2003564460300b40606070080da130300c443d8510f400840d100890480104014010051802c1210320340500c44094445107540341c101d51445204001c140010b81030100001810b000341105080c104c520780700300803503910416490801d40b00c1d484111000e05541c03c165000e01c007070034008115421100320307401c040c0c24560011030031409803010b82e1444003400403c0d00302261982c0e0f008010b801441c4c0c9590368002e00c4050b255180c0c200080181081e10444072007000c1090060340001c02c5902120310b1300c00b04a4803480340c0050710b002030702d08082d036000060811007425031a00300c000301d10400401d20f403403c103081d600d07881c000282c4010303c1d0080070b6070810b0300403d0300340b040200741d1001410b606520100311a0b0703002c0418200c0300c4640c0182d488090b0144110514 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511442185 1250 511440935 511440947
    0xc061005010f02030d0b13020c03270a092a050c0105060a06120f0603050609060a0e0703020d1e021203090109090504020a2102040501170f160b0c03120103030f 70
    0x800c800c0c01c0c560599900c200300603441c0d008141100c3c550503219800341480d561450403048002e40b61800464550700500c440941c1c0743c000100d0300415100002c0041480c0b03070202c040c2080b500004100c00b03045414000e03854080c0c6503813540d0700103084000ca40701205040124000c0c52461050b62181d8441c040498410b0a468005d82403500038110b400c02841219485003080ca0940f00e203040100300300c0c48111640000300f9580d0300c007520303901a0384241300d080c903030220340c0701c1c0248409841030040c0c40c0b845030850b44405583c0f0000b544021544d030b51800007080082d594a40f40c403042e07081c0501d4416a00454842107550b103084450b500009041011903800c110520064285114208800d00c0d0580c045820400d039400780c1e455040016004401040300f2059485965501078014482c0e946d40340a414150340000d481d101082c050285c200415000020f080c00014246105c070cc2c03d5280b8201c401c0d0f050358401c1c07007280746030b00040180c0d00080a05500941c000c6105c0e40e51301c41e0414550b5801090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511443435 1250 511442185 511442189
    0x3080703050603100c020c0d06021b011802010f11060109020d060806090a0b1b0c0606090105030303070f0e06070c0305031201150905100905090901060e06040902011b050109080c0610 80
    0x1850324040c02d100305a1800034504d50480286500000c0d031484005007a0700d03000349501080c1d4403050b03006d800b80c02c000283e00586400302100c0311580114100c240c0840c203a840c40c4094000c1d9511050202c8003561003000034580003000c40c207004500b091041c901e10b050000176008070344002e400152620b00c46080e40328010003403078204050011400d29000c4c00e5101c010784000503142040380c1001c2133b2490300043c00a20603a0b8500c680698400c0c040307088a03101d81d02140c80b00e101c0c4c02d41000005860801104892082071181e80d1000d1400c0e2001c130564070010081d1501d03811460034420a00010200810036010314020030085481300b5400854018020058102150b0011480016079425030001582020344100f121110340b0302c030030744008450150300c03940907983c401040001d001840c101075000c0d5055a02c50500b00c03503140d4070303003040c8015103100784402400100021900340c0028039491451030003520820000c980800d003030302c0b0000c094218801c0c40625070000c10602103282d0710031000d100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511444685 1250 511443435 511443437
    0x2030d030b130f020903070f0602010c050315040c14120a06060f02120a030902040f0e070609050a090e0a060510080607090308030c09040e0303240301112a0a0f030807 73
    0x1107096000c04100642c100e01c080b16802c0e07071181098000040d80d41c058030614800681203035039480d65103079600a0841a8496140036519144201c404a845035003100e2140d0900046503018920003000c0c0402042130003e28020860410807901c21400d10000401034540d05410cc0c1c001c6091aa030404d01311a502e900490611842c04406c0700079640128900200c0000a944039403141d025034400c0d030140920400082d0f02c20315207040551036420651000345040c600904682d16140c4a0500741d03a0f001c5940180c551052040c2000c00403910641c01a04000d14000f0690300c2c1240a50b560005070307901540c052104444001041c41003800070841240e00c82201d1511980c1c2c1495038640d0794152101901c0c401070809c000072048100d8a50ba082190260300c0e81d41100e0f60f13480c1042c0e2440603441010a820220b4080b03070011803880c41c050040540c00e0800d00030480c80c19a140741140c8038800000703800310411a404e50504035034601400b071700402d02d00a0020060302001c0707190007004048003c0c4500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511445935 1250 511444685 511444691
    0x2040b030606030a0b09013206101d0402070b09072103090e0c1603050d23070c0c030503130515031006050a120204080f010605060412020607080d02031302030d03 71
    0x100141d50f00280100b1800e8003c050180341d80c48402c1045d001d8030000b00207003c010141e01c0b450404400401d00035000a00e0106c01b201141c070382c034040007240f00050181c000012a45841079501e049088011084803c0040005161103210795441400700001c4480c1901900405c0342001020b105000002d120030b018004c1080c10722841d034001d84503000750f0007502103001000b00000c0c21000301c0c90032100c40e0400c0c0c0020404210703803490010720030744c4401d041116207410704410107011040c0300500361448c020348402d40c40c1d964079008101e69003080030b502590f00c14915007002000c900180014042c0d454405804180740e41400288500b41c61561740700a4801420010005a41c114080c030b501610f50340d1420690301c0c40282030480d0705c05059001d1041d1144006800111004002001c906070704134800280b00a56841040114a005502c24911507802d0303480400014038000004140c00ca1081ca241800c03c0a0040c022080782c00032079844003031031031850101c1e003549000c00c40424040402e15080c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511447185 1250 511445935 511445941
    0x50a021014040e0601140309010e1e1b040618020307140315010f020c031603051501031a090a080d0b090610050405010507061d0319020d05030c0a21020702040b0306 72
    0x7140c8648038912815003100600404100c0c43c5c0c0c8140810303e042e44a500c0c2180d183d0400101e02402804010300110301d601c590034485100c403669206825140c8020406843c161051403030344041044208030700c5074455a41d010200c0d4001540b00071410340d4403041d1005031a13107007404014140c0d400d800480d140952061040000203c050400090409000c2ca8000034500340504e0983c90310b500f0498032079260055900f0000c3e0f5207a80c10a00c03044038002c07000c4401c0b08140103543c1e41981402e00025028040884100c001e015502507000d030021a0b601c02c640300725940c0d48030100e650300031f08500c22080b51a80304607941890084115034022104a0f841d240032a40741c100600f151245110b92414803002150100038401a640140e150380c40700002c0302e8000400108070b07600d0b940144c0b00c10894040341078400403018800140000c0b0900707542c80700c078039548a50081d0005500a504030800300010456168a91002c00c7c4803015914002d110241c3c0310440d5104000075203810f021018041d070300ca1420 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511448435 1250 511447185 511447217
    0x1b0e01020c060d0e0f1501090614271303090506090108060108040f06061502011a060901030c0302040b0301080a021504030b0402060f1b0f0111030402030622050307080315031c0311040e04050a0210 86
    0x104140b81001182c500b4030b24541c6070b44644bd126184d49201801c500c41e81d0130407001000322029080d4880c4203540d081803441e107480c20480343d40100d00c6202c1c0011002c0b0001001d55014450030361f04a0700520200d1089402903903182e081c0c1e0b0342c0d50051740440004030381029801c0d8090180c191980c444d050500c1c05c55661740003180e894014150030f603040603102c034001c1220311701941c102c50242c810202610340c0c81d030311a080c4555030704880000b01c0c0902085220400301d40707152800c4c0d80c15a6030040701307c0c40c26151034081000d1608a071803007010218007003115010f5030400081c1528081c005802614503141c0407641d40b03007195225401d020300e01004004010050381d0104596502c02d5030b4031892107010f04844450000901c031014010201d204c0050600c080c000031401452003260303500203240390b11080400b8140c40d01e00001c2e040203d80c00440c00d1148040c0650401c4010b0250b400d0040d0501d5507402c8081fa542605443c2560781c0c1c0c10150030403040d82405188000e034a42141490b166865001d21 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511449685 1250 511448435 511448459
    0x207111c060216050703080309120309071a0d09060b0306060102070e0c0d02040f0306020301030b010504060503101e06030b0a060f0605030a090201120f1b0e01020c060d0e0f15010906 80
    0x305826400526070303924021400742407961507005011074620b80d4807440c21f04030903481036442d5181c070300c508109404004182400c40e0b01c0341c0164800307030040034905910f018000c18040c28800c10403805102d01c5422840718400c1512040c011000410008210000e140c10845d0141a960464000950610824070818034880e0091003002490b6905d480c01510b0000a002e540c102c02c0038202120800400c0c00390580182d4141d074011641c950f166641d9500300801c45100780b20f40e42d01900009100520710b01030344d0065400d01d011060f43e010008880b0f00c010110741d01500102c0304000303510705110214150b4402c42e400b03804074442e02000c072400c004000d0240e0100904400354261034070424003c40e4070030759a1501c03901d540030b010303c007410044082c080a01a01c201c2c0e285402440030229581c90b1244400502007181a005004004000010700503da840f2145080006494064400200300d040060781c0341d4000301e10142c83d00f040c4115138083d150406910000039681400301c2401419111b40c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511450935 1250 511449685 511449739
    0x50f0f011a07031b020a0605040e060102032125020106170d0915030621050d020703020604120501060e011d0f09060c03041e1101030f0614040209010c060c03020711 72
    0x800c1c032420360701340003100401c6800440300c001d4011402a000117615034110014000b82d4401b0300400780650782d5003004aa4a02500720307a010248890801c0c0f032078142c6100912501700105060080b01c18800410b903400f0890203514190040c0e5540408001c0d408910b5030400301c060320500a04043d00048100800307901c83c40c0a1100d0421140b419486c00602aa0146006180205500c441000c201038403664401b03c1e91800d0b203990181c0384040090754400b01e050300560354010b0050341000d0401c0c480a20b14502410104c6d5070790340c0c464012800e1008241e603a40248142e0310000040c00a070030b408074030b80e03002902e01c0c1d0108030402c045c01b94030040030401c07580c40204013442c00d032690383d10b04102d401006e001d070144000744803240d4503000307010300b0701c2140301c1306242a04c0610000c0400e183c9001211414494a81858503025584080d072506800401c9000814940701d0404859508d0f8007045990051542000c03c3d40020500d00b0094026112165003034215903024541c07165081d4070081404003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511452185 1250 511450935 511450937
    0x318080301060818010c030b010e040507082403060a0911030303010609180b040504050a020a0b09031f091a01090b0d030203190207270b040207080d1a04050f0f011a0703 74
    0x41c100040d52401384001c200c0d1510350780f000074403003050418805002000c5219896001500b4102e0241060074540101401403000380d41d041480e507102060014444140c0c9284080194996a0010656020402039021b03640c02d101c002a007800b2864a4480d14072010f018502a81082c0010800542c21000c240100c0d0880720b60300104284030944c43d00100041601e5a034024980300038001808400203118142504c2541c00102040c0c0f1070b60400d29034098422900e50580c0030b005104c000c06040d52200503c4044c000011a400071640e84a100d040e40361640c0d01c40c0f9600020040100d0b2400703000303c044040e0103440d46010840c054800070345901c11201c0d10650780c219031001101a0703200b0800140240030205641e0b01d19940392803242a0351500d1030006000c0c5050290503641d5142c10b00c05c440354654041c580c1ca2a1618030800f04001c1c05c0c224000781c80b940c000301000801500c940c000c040c1f20340c095400703010181c58a00003201c603800f410b8018503105069076040c815645407039401c0f28152901 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511453435 1250 511452185 511452197
    0x30b0a020f0d110307120203011526011814070903030518040e030705100b0603272b0c020901051905040f05040b010b0307020604060c0509041a01031808030106 70
    0x89240c210040c0e20480802012451400f01c0c01d00001240501944c02501d4a6032500c0244160061020583c0804c2c00342851909520741e14901403406000e40b0340010b07400c16000303001c0403c6240e07c2031084c6001d030f1240511009c44050b8501c40d44207407052505004901055400504041000500c0e10042d40002814004001012803801400c44641c0080d80f9000380244503942c60b40210648a4012940071682e900c40c44c80c00612111070350107418007910014001c181190b80d141d80c135a621072502d50107100e00070f074446003803207a5007014045800b5190b03080100509070348a10100d280103154401110782080469545580141d40d5032070800e044030030031a1118003120125074070301000f008035031000d648a03140410b403c04e845841e401c1140b095000c2c4640484d04da90301c1080c02d03218401251010016000840000c000600913407201000410354a4100d04110203040400c0484070817102c2d1020245024880400d9980d050141e504040b1054880c0010000c2560702c6181900041c0600d07003d000d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511454685 1250 511453435 511453447
    0x150b13050d060b030607230c12090613080d0816080115020c06030f04060e0f0a03180e0f1f0612050403140304060b010305070c1a0403020f01090c0f050307030b0a02 72
    0x61980c0005180920040545d0b070141007441015040e0360840910341d2448400d80707141c40c1012094010b03102034200010103001d003510204444035040e4030220265600180500c00c0c50403940c61b1016840140ca04a0020468220065006400801c1c010104010b1f500103591000d4210b501c20b20260450309198620030480020350016428852404911074010101100304061602c10707981071802540500010441c9007014180f081e00c400b419101d242d0f81da03000c140b00c200002d03c5606900c0c1c042c41c00705154031215454031a44060b5035015030b2244900a0707208184440085000000c0c801808080180e0303500e140b50000103450380c01c1c03c014009110b0341c1c841c00541407500a0490000040400807400e075245018030b008001880708004003030001c0c0c40d1a0002e10311600459402012130341200d80394031806491140c0100b04a0002c01c101c0c11400b4907848504084000d00401c06014411080703c03841d14148026440d0301d2080341e01851003680b10300410000702e003019070004e422407420b10016a0300d01e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511455935 1250 511454685 511454693
    0x6170709080114060a0b04050a06050c0a0803090a0201031b020703150f05011503060f06050d0c140a0e01110c0922020315072003030a0903170109150b13050d 69
    0x11406074030064080d4205000350041e0410b00c060b043c455402100da81541c2034803100011454012409990b8008031020418004036003d20003400100d1441170449081c00701681d18648907030000d4404000d035901a5071140d0456030540a5900d6101c40c40081c00001100d55100951340c109500c00a040b403540004111100080c940101d04207022050742440607581d02c1c851041c032120402d0708400040d1901c07402040180c0c82202e003800701d601d207036996400c041900010500500350740400d0001d1000180c0140c0250480f040074007809020b6440e01001400140000340004040c801100d015130051010202503548030360040303401107003c0840c10f81c1c40e50302e80140060715000d0740001e0741c144100d1415900362540c082c1d80d40d1280400e6a5480b030980b800d4200f800d110b444451f030000c0c00d504184001a01e40800b81d001c14503150180c40d0808181540c54601542c13503a00707030009007015840350110070340c41a081001d800180070031003400d498542104124048100f47c2d0051510031004003840c14280 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511457185 1250 511455935 511455947
    0x50409030c06050f01050a0b0f1e1c2322051f2a020a1104150e160507050303061011100605010206070207140f0d0507030b150604061707 60
    0x32a4400b4040049041a010381c10303842100748030710b41c41030040704401b141c4d045044d410baa01c880044800d030341c2080c001c1641d000400004850801d014a0f091012020918401100d900050010800013401003003800e440460307480f203c800051000244001e1103030a82c0c0c01800d800840d0b500301d400d4800c041840c9000741c146075880402d88650109035000440c100126401044203a90b020101c004424602030303040c004414940c4135030b0240c1c2101c40d079040400c41c820346402182000801c005500c0c034481013071010301105500424002c0e204e040c00c00280e40042c1611000c19405401c086003484016990586c0d40e10004142c0c5006214452000110318060301241d642c1c40317404030940d18002220032141000700040c1c032940d8010711410000c15072860000c00c81106455805080030350415290742400503100101c90728a401c4904201801d012410910400c5c000c3c500c80c1c2e152208a00741482c03030415032600c10304580c1c81844100010842030790854203690080500d03c250260564071541c058400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511458435 1250 511457185 511457207
    0x150b040b0d060e070f080f01060507060905010209030a1a0714030a090f0212010f060e0105031005250216140a030b0402040f020a230708160c080d080114030604030905040903 76
    0x11644800040c050001d42044000c044894580d554240555070b03840c500b000c07107c0138892400421020050240840c410760031600c01c1074085d000240c5803600c580c012030703e044280e400030340303141a070120883c40501c44e1887c2203030004840c1c85c0050510310014090040c80c07001810381912165607101c007108012175600c0071004150010000c060b04040f11411a02030049903c0300c04200f450050080307162800403505074140c0d14040c0061410f6040900100014507010342914000c54603460107000c0034910010440c80e07596680e02070f080d0742d40720040105c5d03204d0281c3c00a00440a4044075031210351604820902220740145508100d62500d001041c01415001c2040341c2580c0001171000352241c201143d20850300e803c42e0b18225a400c80350607040c05010314080144001410405000c0005280a03090b0865004003c0c0800040c0d9034100b043c03400319411052808100c081b401040f55003075a40104e041c0380300c19000360440d458541da000b0040211402803d110310b950780c247d102494401c0e1100c01c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511459685 1250 511458435 511458449
    0xc06020d080a0e1f1e0e10050705090d1a040602040f080307031b061e05060f01020109020a1a1b060a0e010c0e01030515190302040b031c12020c0619150b040b0d06 71
    0x40f502d0250245c4101811600a00c034009210303d02000040c1c2405220725481601c09650311801c00240c042000441c20700a20244e440e90b1040c2c0010544020f0011114000c5108000060f43c8a18000494581d105194040d4026030001c0c4506004070350824090480941d00306d1004103103d0345032a021004210001c0c010800380f031400180410385000703910980c043c0c40101c03020560b400440004900740c03100c40d003000b50010040c102c10010003810003c02c4010407003030900141010480848001e0b8600750741c401e440c566014109028a1076a503104a65414601c1c1009100041c032404000e0b080c1111003540e0b0341050780d1140001c1008905800120880000030200701e030310007080039240791800807800260321561411906075840d14001070240c0303024203900c1071024541c01e80e4405546042150748201c0c03486408114568980c3c800b842458032860070240c1d0f213003001d0550f4804504880902985181c405c01c403050901c800c21400c0c090300c0455280c5414030780c1e00c12002691002404080d88040 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 511460935 1250 511459685 511459721
    0x9032d07030c03031b21020c16030303051302100f030f110c0114010e07030203090307020a080d181406030603070f030302030a0e180a180c06020d080a0e1f 68
    0x40304060784071079001902d5000e50342c14004059920781c0800700010b000f94940104100c03c00d1a600c911012131050701e034035044c2c9801400d0050050300305081c24025810a8600c0c410780c1d806004140d094480c10b500106018a4209102c7c160f5010451580805401d203080c0030304c0303006900d08544260400a0541003071107046c0004180c60411381c0070303a00081d940b14140e500b0500c4c1c280761203811b07402e524103d4000c2200b00749103807143e400c260001c0d8030150001d4524001040024003680720810200f00500396040200300425218800600c10030710b8400140703e0000a403c01c0001580c0802c14100850303088840c15540e0312804002440c1007131a60003d518004072090000a05401001910f4404c071b2030703122140945041380400c01491121032440145181d0500491101e86140d84a0000100441c84d030420811241e1a203681a6043c0d038000070040c0d21046c03c0c5003005e680101415003110714000f062020091541407580c4820600000d900801d6010301c0c22503903c81c03240c01125040070326030410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 511462185 1250 511460935 511460947
    0x303040902040609050316030f080d1404140d0f0f0e12010b13231e091f0b0a1401090b0d0b0a08030c07030b0606070203060f04031709032d 61
    0x100603400c0b034031840000c44e40d0715200103000e08011403d003801c44866039a41c00c007507007903a9031038003511003244050310321480500850303c9100761481984203803082d4000b040c0b214545450f002103080d4003102420001d8101504946250b604184880303401070050802c3e0307d05c0c1c054042c007120003110600000d64403071040c4000c000c43d81c106510800101c00306480f5070b1202c4d0881513103402a50b007800703940d264070110000055018a604a1416040034045401044084902d8420700350303510150351126031504400b41d00f8007070041c1040100c0c103c8040b824107021002e10080003410504032032150078030082d0203036018407550f80b05060110107403045048840d01c07150f0260718100100066821180a40c20b256070101d040340001064038054841000207000d0641541c1d190b0060b01c0024000030303000703c401d0241e400107a800380041441048031141ca03890302d00d00b03414011b150300e00135131403149590080303402d01c2106d01000c001c5444460410700003402485190a404071801d007900007400ca80d00c404220 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 511463435 1250 511462185 511462199
    0xe0901090534030b2205030706050105090109060b04150302120a0605090a0603081b0709020a020a060f0905071e0e0f06030106061110110c0717010c080f07180302030304 74
    0x400c90100358002c01d4005003514900420144440720b01010b040d03070254a00040100080c0c0c00702c00e013144001c540316aa5901c2039640c40b45140c001040c112182c5880d80c00500290415a000c2da0050601134030078043c16241c040b1f1210320744514001c800011607141b01c29000c00b1f01a404846405450440322160351512450140080c002030007607030720035510100451030908060040328142c98020003940e103460600c0b081100e004100b680e0703100c0680591304000a24548074806040c000403680c0103081f0f1821545404800c484000f0b1412084a19050f200d03008520001031780016149c509000c81d100c50280031070a8041d0200358070403400541d00300c080000e01c0d0840c41005025a1040e00203200c2d0301d40340d600039200c6580c10b0300e081c5150b51115541c040000c019401100c00041440740e85440c251415440d6410900f15412910250803007007110142c40c0c81c00d115a1100401c03901e000c9500d42081c030f0005150b03070340141416040207a1035100b500c0344201d114108000310b40c01400c8030392f25591203030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 511464685 1250 511463435 511463473
    0x4020405151902010203190506180c0d230402060307030207050102130e13110d26190207030c090b12070e070e030604020a030f05030f0c03040f09090308010e09010905 73
    0x100c0015940d01c50b0002103801402a01d011b1000110502405102071503940300901d8001c2640b1740c841c84100c5072801080b5500c1055020700075800300555039034415903246060b41c0d07040116000030600c140c3c6046103c07000e038020682080d8101e030050b0b41d0b41c59495084010303000d20240580305502c00a004ea600802c4a070700c140440c1c82c00b960004141e524806540e030b07041070b00710002d06650f22001204542d8546001a1501d0b80d21500420380b0281c600444002003401c95104120190310000d402c01d03000b1805900103031401540e20080c4600c0d411507950500b27104162207107030141500d418501c0710946d0742c02d450340c41c982c4c20a4221082d181d40c0e030414020100050715440d020512614044a5070709011817100d12554010301415069442d40d0f88102103580c10300810385130349c0010b12a0411a00300c1d64000c0a40d0384884000390b0301e42c0c3c06c01001c0c00317144015a00c880c031f015281030b008000194010f911070781111001d00c052100c41d51100071039800b4240d0420300a02900680007200e6800c1d600e08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 511465935 1250 511464685 511464697
    0x303190504320609090423031603090e220c0803120711010e070e040201030612050606040f0218010c14030d02040806010603060e040807020d0c09140c0a1b020402040515 74
    0x90107003100000d1810a120f003501c1410251900248098001800319440c06101c01900003d5542a1152140310158900b581c101120118284220000b10303c1410341c0000701001a0801944216250800450310320b98210b41e110b0400c20702c00d25a40107414465140720314002801c42c0700c107803039459000048200c000b843c1120280d01280d102030b103185405105100e012020415800104085421301c0c640c0000fa110041040b41015110b19002c2044005551010f4549103c9c40052200e42099010001500e04007800c07480305510600842c0e90365642c0c403145201c0e1420a003040240740485061040c10041c06501f207801c2c4c0e1000291451032069142e0040c0115020001580c1a07640c0340c400c00c40c107441c41031003848280c3c0d9426010a000c220154014219140b0040882038410050764a14041c90040d5004041d20b51752003c90a14950170500f915521402e40c1c81e0070782c41c1114608018105074800440b118180980003003030340031912a6811140a450014a041c101801100d0039000d168040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 511467185 1250 511465935 511466009
    0x604050702030c10050a020c0706050304120309110f03070f08030706240608090a0b010308030a0c03050105012c040e1c050f0d0b04200310050303090303190504 70
    0x10001410303a51022054030080e2402001404810515a000c500900340140c40000032075400c00480410f0407040240600505030358546985a1806003883c0412801d9810b400d03090604200548000a0200c1c2c13000c44503940460720306a540d000034010034175008154128450f124243e460103d0700361000405841294800c0d0400c0c425511044400d124519204029540e078a507a1a0309208541c000c41e01a58030854903411551800c082e43c40d4949201c10071b90042d00c481c14000f0500403081e1050044020300034490405210951421000074a120014001040c6102d803100640d0121000ca081c0f030004010020b106026241810030f04035194100c0700c00c000040361002c1c46045200c2c1c001c5080d281c5903002d244903182803a1f40300c0c180001900c00740440b20b034450b544030783c4810280c41c20900c07aa1444242400b694030b03840c01080e41c028401d8950049841b9610030301110b815076a0010803503500390304409550faa02c80c5022000d480030700841d0403c500d415290311b0020280c0381c1000c026007004c00c131 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 511468435 1250 511467185 511467191
    0xb07051b1f0905030a030c0c06020403060207020906030109020f0f03010e0105090f010507171303030b0d1412090f04090f120215060405090a060908361504121b0803030604 75
    0x40a00802c40c0c01c20305008155070030a21480d60424002d80c0b000c0340f845546d05107441c08007801d0780c550f001c83c1d000360022034640750701240540035420100e92142d40000c05800810003820550001008408103099142c1324044075181746680d52800c0d0407011101122100901c89800d0102c0303e180c440d00d590628080035032800e40040e98452241c0740002241c80741d40301e200c4140e15070751580c2c80485100c134020b42c00d140e02d640310394619444c0c40305580318190041d00010454000f807800d480c180031071048a9000164107100481095690340c010f205008400c0700d00060108040c6003410180c1024000079000c0300029000383c4003d1f802181c81300e0b10901c0910012071555594081204440b02900d155285034000030b01800010710310343c4018085406085550b05012040a0300108a05900c0603568841c41c01c012940082c50000d61a0131800301c2150054010842c004070312030180204c2c40341d03c000388640d10045040c40101c0704012481e0701e8440880750b105489100070741e030300d500503190345001303510b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 511469685 1250 511468435 511468483
    0x30415110c100f0f0e1c05091c0f0b0f0a0b04020306220b0406180b0a060804020105210709080606090606071e06092a0e070e03120a1e05160b07051b 65
    0x44120101d80023043e00520104e0402881c07220300510b0021640120b030484280d81d441c002040d0080d00300c510615070000c0003200c0c1d00e4103120340300580780704c1c04e003140c040c50052051200d00c0e600ca030030030940e070205500070821040080e1084c1d0040c2c10103100c0240c0107458200c01041d5840782e00400000c210748104180584085d403001c5c001840514806c0c0400110706401113130044d0300c03804c002e08c2c4004003a02590402c4403a04686840b9010551301d1a0204040a03020005113800b4002c03554000e40c111107160840c5848400b0903078071311492100521034010880d144119940705c0005482c3d454101c0c0c410090f00f6442e1804418139900c0c2e503000480c280840340319a02e1040c1121608041d40c0b916101410207441d00e40d015141804a508002c0c1d0501800c1c1c2c24811204070303803016018100c403543e5008100303468069030340920051961280d040220030050321002030600ba682c0c410140e40f20541d40303207641e078140e01102c03180221f64038480a44c5445424000d40ea0b000034104400703074407125041c84208 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 511470935 1250 511469685 511469687
    0xc0a0b0306011d060304030302030a021201060806030d110a02011b06050c1312050d1115130b1f0509060103021204050601150c0b0f1803030415110c100f0f0e1c 70
    0x14043d5004070341c2c025070410001d40020710940144d900038034040009410003a6000200c419040240c21250005604408100840c9010000c1d50b00b84002820030741ca5a0b01030b1414291111400074010b07061060014585991280c810a02c00106401200800c018181b0401a0306158050998941025290200032a0103028032014814699100008110740d00c1c105409494804078611143c5450190111030215048011140c0d4443e5120344a00c038502c002920f80f001b03c068002d044601c0080d01e0041c09400c0a08451211040d28001c03516240c03070760b41d5040100c02070300c550308052441c000004240002c11600199041c180c5007800c40b600945c1c14414811100c08075001005001640b0042c003107078103092018815504103a500c501c0c0c40c00802405070007403469106a500300c0d86c10722087c408403040a5144a00d200141903420701d0b034503101402d4030066503140418810210281e81c1c034481841c03015a030707000b45481815880c080c8024850310120540b1760582c1c00d00d0021011068410b81882 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 511472185 1250 511470935 511470977
    0xb1b030d020705120901050d0e01020408190b0106020a02220b04020a0c03080604050c04030609150510060915201606030906060f050a1a0c1b030c0409050d110c0a0b030601 75
    0x442011f03583c10382030020440107030000d020a544907402c603550030403020409140a01c410b640340325400307030103841c4485140f0b40b44102a00c164001401c540041d50900010390314020701c03280408169480040741000e0100c000d0080641e07104080e8054400134241400c1504916580c0a840c000e0f12001c00300e60740c02d000d01c01526421100030b0340d0101d0420045c070005041d5408800000c0c0210007420541d0b4102088204a4030141c481000400c4424410815a9030010196020b0007000081c1e242010ba1100d0140c801c200090a80c88122102c200324030050204201002c07900d00741408506a80d0740d25540500101a003140540f955404c04101182c0b084d043c3e401101103030b10207842407006500c0e20024000016103010340502c80c0001f00081d00e00c0d081e04020b0080004440c580031b41010004404140c13402044c01c1d8600d009600f05a0583c011480200701d4072403202d000e051143d0991508c07042141000c020b0070785a5030241f402c0c1004581c0500711005188a140280c0700c00340d120420420740e5881c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 511473435 1250 511472185 511472197
    0x305070206060f151317371407060810050301050615070510050408090916020606040b0a0f08030a1b0c060c06180f17040f0b1b030d02070512 62
    0x5000624800d400d400c10005803a01804044091410109504a61040d06010340d01007070411041c3d105002103400c003401158074041f111607080703401c24003040d9422001c0c04007850358071010780c0d4540750710705010003a19000046065041916100ea458100190196400380d50b1000901904400800e40d0f003014460307107014001c001d003041e552040345e01e5082c0321940030b1401140c56005020702d125000b0100d0244901079031181107a9a15103803044180601000000c000300103031a1100100f484d1581c020504c00d03000031050714082050b81c5e0101c0401c0e11110a030f8046110707101080b0001507101804405171018040c5659206401c06041003250a544041400a0940c0f034a58904100507409041c0102c140c1d4803880010031120070300b6800c02d505508258098034070a10300c4604034104440d0a40320421210800001e03803d0604207090200d00001500500c044c810000650484d07900303d200500040d5404141280d0b40c40d052020041d01a40190310700312034901c94200d000002840b85810707070302 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 511474685 1250 511473435 511473439
    0x31a0414010e0c090907090e070c151a0d0c08211b01090c060305151c030309050a0830071409040b0301020a030b0a17072d060e01030507020606 63
    0x4203900b032200b034039a4044054400141c0750010014000c0070b8a0380c083c0c451050041d45c030342403402444c000456880a9009042208000c04140e1200000740700100964150b0240440014002d032000044420111418031095203d60201512802c02007185248e0003910400030540d0f0380341c0c4650700c2c1900104246c080d04a03c1c0392041c8140700c1502d0032400110b85204c00c0d58000700d80c2d81d04d29168150103511a07044030000075180c404104c0010300c0805400800c500540308151001034201d0f500c18644441d045c0103081649509400c4140f02d010804100c0c1300e5003003140155070301d07072500e032079010782384920300d40f40400401d6600000100c40040040c3c0c800c41d01515000451003548000200690040c82c5669210380d50b13400741c001c40d1724244040c1c0452542034800150402c0720b002040006200d07603000503840c5800d801c90030b440034000304080d01181c0c1d001c1005007898041501c07581c2e2404600e094114407648170a000201e05131300207650800d4800a803010012030711000c40490300e40c5000c80b0025 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 511475935 1250 511474685 511474721
    0x1a0306060d1b03080403060615140a050d021b16060e0d021012141f030503160c0b07150b030f0a020616060f0209040e070e040605060a15031a04 63
    0x1001c981424902c540d0704207030045100180d9200c1d502c00d00c3c160090b4106845540e0790780014003004103504005202e0b0b07646400c01810320544949451943d100e50258502080800306140000e520380340c050b607000d9102c0b005c158001e80342850031603540340a45e40011400702402c0600050f0b0b20300601500d02401e0029154001481e210307000c0c003502c00c1c00f0300d07036040800540c500784004080710340c40740107443d450703541c3c1c001100d04045d040450701c01c3e00301d07403a41400c43d140582000050347c008102d40c0c0004020f1200750b005005d038205100304103003560015010141c0020748200b000f8003420508086c800783c4400308400d0204005040c0d56003401c24080109a001a6401001d4030b40301c006401c240d4101480c4031201980396840d40191410200000c200036004500e2184a1811703000c0e001e90a49008001c10106152401c001d903084070181000c0c10307030756848002c160759440f07000d40540a402c880b0588c00030703140e43d084004c004021040c0c01d80680c0031818a525001d140c00c2c0112035110800016103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 511477185 1250 511475935 511475959
    0x1f05130c150908010504120201051e010e060a0305031c06090911041a100206060901150f03020a0e120c0103050a0204050307050613050301241401080109090c0503101a030606 76
    0x52400c0255607071010103200d100140080c00e80d40034090030b4030561052180d41800d020520b00a400d498000e00102c080c0c408034400418a201e5480700da60442d14400366211140e00c4040210f0342d2902036805c09801408001141030785021643c4118254900040081062980d5002c22100711104010b008110021081c88030b040b510700341e04003080300b001c1420b20362010020100007a50f120031742d00030000560030100030041c50b46071000050b0300410b07440c9440101005428002001300d1810340c0010185540400c1c881501031241c00f4071000d075400509440c021400b00c40c0b081c0e42d200350074505140060b0900c0700140050025009443c03c641c3c0c050001c103d16410182045140d0300000444402c4200c20301001407642d0b424020b04141c0c1000d0600c44c0d00034080c24000711003d1031103400802d9001c034801c10301c0c3c00d541d03840450a81143c000b80c40c0000c03404507038600000000050b070300072549407040d0012440440321a0f40500051f02d8440301204c001140c2d0001d250f00c0d01c81c00c4a40981c021010300c11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 511478435 1250 511477185 511477199
    0x503011a09090106170a02030f0f0a0b04080c070611060610020d0c02060d0203070903030f090501201e0d021e030901080907080d17011403070519081f05130c 69
    0x1042d00640c5031000441e45030303150700c000c00d07050820003080082c59002201e0f440550405006540090703460354050b2619030143c0e03180660301e101141c0010070500346100003400f80f184960960344550030389030a98030100d0b901c0700300506981490040302d0f078a020301e5022901d00c0c40d101e00b4402c00d028046c0c000d00609003112000b90348280d04980d06980000c020802c09601000500c02548203011075210340e5080340c11800c00a2240d4071032030415091101c6107000703000a83e0005440059a0300e00656504842c04101d807103410b00c40710211043c240780010301480c1c1c194074007003040d080c50b10389a400c4807444001c42c03442180301c0c4204a010003464104000c1c0c1605540302d1081207501c030160700f046659280d03440040030718060420a851002407400000c00e030380c1b803960703a90351801000400854400c01c01e071180040e466003490f2166034452203404040c87c41c0302280c811354200502c0f4450558540c200103801034a604891014a00c001c286040005140041c201451009030f039084400705081c00c2c10010f0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 511479685 1250 511478435 511478449
    0x40b0307031508150a05060a08030706150b0c2107021917070f0e1506030106030501050406090207050c010c0c2c09011b050a03060f2c07020a0206092b0b010503011a 72
    0x101150f0417030908000801c5a5100300010810183302d031000181540203109440300e014226040f005468604105440c0c4e0007400003034925a000309003203004140900c242c22103400344103e4800035048018101d48060760b50f601d404540c120f070000c0403102d100300402d4000342e4440107903000f502d185900c2d9030000c3c0b07d07032443c0d411000c0d03024540c400090423200d489000035505070001d0b400600061f88030001400142068014000104045607055040254560700c40d83c4a42207020340504003d040748059090100c2c0b0040e001c010581c084141070300e01707221220400200341d4150303d8084840114041603c001052140124084d4902001230443c1d00d01142203504e90b02000c402010961180030100d00341620310440302c010901507046a1051500c01505504c8000341d0300596004e0801404004a55070007140c0a8a42641180e09a6842082d02c0002e20b903424100c0b03007940d0380401001050b50745046590041d4031a03001e840880110781c2d8990805090b12080c000105440504085210752414010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 511480935 1250 511479685 511479691
    0xb0a05060607030305060f0619110d090302130f0c030f0e060601080f070c1a07110f060604020f071406060316081905102901052805040b0307031508150a05 68
    0x900841541000c0c00001380d00c1d82000c0c182c80d2744030610304c00117520300d40c1194488440c01060006050b00343c1d80c0130005071030714046100280c01038080d01241d00312050039074000b20f84c8500030f02e410400b003c2c0502d401030003000040130030b0085a241c6505030f019160300107076103840303111f050703481040d607503035070b081c01944e5881c00b814800501280d41d051300c0016843c101c560401074143c06103d0502c1c80e11801c0203040c3d00383c1e4003503054036030800d603c01d444104000c0f0b10b895010340180d40140c0d8501001c1501c05a0707100340da2002d010310104540c0321b02c02100211307085000300412000c032440e4000d29080255845907510514401d9404821980d540c0ea411601c02e24a0724041c0c01901c600e8800004a001502c040100c1880580074507182d0101c5802c0307030588154044001c1ca0568104840d901241c445a1007010f0f400d82c3c2e6281d1541ca40500511502c00c550140c8a1a0121500c85c10510000340282000071003030000209070a90100f1808000100440340c8441c0300d8401340c96071902c1c00c0d004002c01b005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 511482185 1250 511480935 511480939
    0xd020d080c01140f1f0b0a0c0609060501050a0f1401030504020a03050a0302060417040f0902090d1b051014071202071508090c030610090f0212040803040b0a0506060703030506 77
    0x1031240c0d0761412020303c10b2200048900c1c035209124035004180c0e0110b00f40c0108a1521840c0d40c84456413601140d0440000f074a00200c030940d42d800341c01106540c810602d02c0300030140c030f041120035000c0050540cc140d04880081c1d03206500140c0310920b00702400000d0196041c40f607818920341f42c0b558400e400c4241c000380080d110781d04050300d03a102c05007441801882540542d1190703080c40708019041d909003204400800c5260704041c1807100e040b80c1910703103101c0c20040940104080b44140e49569481d919180d2000344400100701c4030b80110851100c1d03109503481004a90043c280f01c03401041c140c00c0f0100001c0006141c000199520003518841c1c13a00e490840c441c210022070440c02d40d80c4c01c000e00e614a07440700c4000d4030b800280e807450b09031380d040d03442e0098000d4800d01400c0c800a0324083d080d202200b1000c20340c1d69810030b4510090207200307a03642048540d0030a000c18002400000c60049018170f0303800b91603035038144a03035040c2c803000c0d83c440e0740020003001260f0109101c0c1d0300a0340c001c040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 511483435 1250 511482185 511482187
    0x40f0b0303031303140a0201021e03010501020a02010c052b0f08060d0201050c120d09020301060f0b0708030a0227040c170c090d0f060e0d0813060c02011506111b0d020d08 75
    0xc884a1842146c100303c0c45040580c2d4009290148000003d0300480c107246150201403840d0f040c81c1c0001d403a03684000703001341808924018002041014020040c01380c021441446104600100d280c2030510030a4044001ca040c41010003442442082c0340351144038080c080c411065050390045810b5030146401107038a020701241103076140360b40f5000300100c800322840411241160f0041508503155a4000000396034803041c00c2041e0300b0310100341e41d055900310780c3c42520b0b07585060704080a48078401004d40c003c030700ca103103145c0c01c00341d0700507200318015090741d0400c400d04000c00292110231402205181000c0c01d680054444500b0500074044020040e15901c1c040d205642c6070000c43c00c0d25041207501c3d584440b481c03e0011020041c51820703c0203460411a142400740310522851480c1d0401b80009444006c00c441090003508186a507000e030030841d02e54650b0f54000104039015416031a241c80c0200d02c0f00500c21091030b4031007610080000c06a03221594143d0821030500095241140d0101d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 511484685 1250 511483435 511483457
    0x20127050f0f04050703050a0b040b03060f101221080f04120c0602030414062419051201091110050409150317071205030910091103030711040f0b0303031303 69
    0x1504d00906004410548020a05040589850082d6106002458022460403d03120300550340040e4054001e4443d4010030740d90749810001c2900080243c101c40c0907010b400d001e40f01003160119140d401c05181808211781d22b00f854104640c00003055901030242d21680000c1030104030701c2ca155031103100036400c4c2440f90125a550b08000c3c0d030800c03030702651030b40c3c40b0900501c12800e00b07018607548a1001071844a4019840c0082c0c140041c241c0d00d1180285851940d0140108600752110041e01008207155884412113481c14040d002450342200c240760510034400c0b0030b0a088440c810910000e888003801c040c10111101c000741074402d0003443d900208032001010a82206200202055410102d41e80e556a820240803141044403a5005c00c80100204130041030007144405204030b5504d00032950342c81c2410100c014104411400354140400140384d820407200c40072851004909840c148180300d91079000204482c1000d245540503081000003440e5282900000c0b50500d20904100c40200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 511485935 1250 511484685 511484689
    0x181e1011011103010807060e010c0303050a110304050a0201120c0903020112150b0a18060503060607050a14030414030c010801031401180c090510030c0920070b0103020127050f0f 78
    0x280100000c10070982c07000005016000060140e034016080300d0400c00c01d00e0126a000138501a0380080240801d669000031858011307040e00500034102c0e0744070b0301546a00b41410405c0d121924aa400c078041100303100300c3c2c0780411050040c0c400009840d200c05003038a01d550015a1017040e81148403199554460ba01140e158041040c68044d00d103030b010311500d4022904c0090098051605c0b010700d5540d0380340c400c01025900c0303c200d070340c040c100752000d41d00c420721483c1291401482917001880650122000c0c00c0429001000d00111514040f1308100c1c005100e090648506003941c03518000340c02440140040783e629039424032105c1d001c50000802103440b10014126400d0310030200c4a150440c9001c100c41c0d40640a166081010051410805491503a841d184120584590002c03540c680340c1c1d811403003483d5a182e41040c1c603012042a5140100e01d000c1c0c4015609000c224085080801e08003e003580342c0316100c074507401d8107800c0c03c1c0141c10801080b802c020390036602c903803021803018611166 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 511487185 1250 511485935 511485941
    0x905030c0f060f0f15121c03021c06030b0a050402011707080703050906160f0c150209041b050717041503060501021b030601050f12070605181e101101 66
    0x218402000b918241c148418605009440689140701512406082c80340b040e00d2402c04445580c4111070219281c9004440301e401e01e285160584080a948111002a145c158000788900d2a121501000200d02e0039100d5003261801c0c0000340034000c4010008401030345550080d50410300504003118150790580d50801182d80840c0c1200001e000d40781804440d035011b01420750000340c1100231381881d00d4048a0501104000203184007005a171000c61310016000ba1600b00820717420041801c10035200a603201d0280d40210b42c91406070b46010340b040c22504100811400c82d95841d074a6602c1c0212070b4031994030002100600c078903840805c00001501012a8010300b54440300380e00c012540f9460400064213103195002c0304001c085007080ba55007551380c040b90b2641500d81c00c90300386511b02802c8000c50b070046802c020b0350340913104200c0041412508000030301030b12a801c5110035900c2c402d80c01804425280340d00a00310003101a1031b04c0540740303029016400c82114928000b80108a1089000c1c29 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 511488435 1250 511487185 511487203
    0x2505041517030903100501030201020a0f0606080f0703020306010b04030b0c030a02190f11070b075304030b0613140109090515040803070c05010209060406050d0b1f030905030c 77
    0x542c00041c5510250506000072003100030305290402c651b40c9942c002079228007480c00010f1940001440c06000c00245921140282001404840d5003185442440d07644514a00069200f0321030140000f80481c2d02100722000d5135800b00303030000241c540c0c16850780349070009800e100300950280a50403102c0244d0708605085541982c9407400b0b4040c00700c000c1c3c02800030703001e80001500890000d0008100d5802100c05030340d44018548002303404e2041d04008110101d43c9203064840c402e10307035070000701c84080c1d207451940e010761400700c3d81d4502c010030407440c0700f98070008140c40180350018640e45041d48a88001c00c4e84d41c5000300c0c02440d40c91084240c2c4000743c0245803d51340d00d58404081c08401c10000812910103024110f190806485200d00b6000003410102001541c11200c02006420340540d0800e0402420300b036103c1d0345800024087e82c0050130001e1495140442c80501440c10b049514429901210241c00702c6801c100c0890160681e000d0a44092104000d08146450304004403d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 511489685 1250 511488435 511488479
    0x23030102030a06050414010b0f0a141315020309130c021009060c0311070c03121215090b10080103061805070e061c330e0c010225050415 60
    0x41c1a420b00c4c042204403a08034036401007154003900180072a4009008855503800c0710551103888101d401e4089581c0b09a42c002d2052560020070111099011030112005036090512400d44078802c420041340d907402402207a0341e0011080c1006d10300e1001c80d43c001c455000d15031054a07408580c01c10b0740c500b5903081130411515155103003000300c00d259041c400c200c40082c0d20a040d034070301716294503460032108941c0000760182079000c200f09a028010308800c0240080c001d030a004d2411a1075844041c05064030500400c5030508042522070324042003c01000c480c16107540c0190f03400d5481d500c000345140700988103104c84240640c030224808100c07460040582d03914039402071910308140201c0c4c9d20740010140a08007d8403a0b400040c11506c144842582803020f212441d0000d42006038446e00c0b44100b0354500c920f4521801d0913a03401041c0c00f220024207070202c1c0d80303400300081c0207500484020b81c00400b045a004050003240340a410075010160f451800341d4030a503c40350850701c2c901e84002822 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 511490935 1250 511489685 511489691
    0x280c090e0709030209040809030703150c03060b0c0615010201110c030c0106090209031f0f020d05150a0807090b04020d0e1509060c03010e040309032102010f0c0923030102030a 77
    0x400c4080c848569400001071030851000c614540c08940100c0c0f000c3c000400c882008100c1300c0c1030b520100203290046802041081c540c0c0075240428008003640320366100024140280440d200c800e220440350181c81030401801340c4c1e5662400982d0368030f040c183d0b00d41155203034405600034191a0014096200081010b540e0300c041e0554610b003140d40c142d21591020340144201c1c0441c2d036010490462417003600034100400d42d00314815000600441d07142e480564030105003080d07c03003060ba11992042078240c2c85403125902d101d0802c514080305104c1c06089078000305d0140014045a08440d15405020b003001d420007820b46650303410303901c11003480d00c840c3e0300c0700620b00d18100c1c0e40800550444094806081c507800d101550b010107200c14001c1000400907900820b04141c82448150001c64000304147c2025010b4201c1d000c1c1d1640b80c660800043d0300308510174244105030b2086440141d000d45031a11810b24019600c0344101c6d45032202c1001103003d1642d42c4882d1001c0c0015886650351413000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 511492185 1250 511490935 511490939
    0xc0206070e060306030a02120d020c0307031a10030c0306051e061e120703051f0e07050103020f07050a030302040923010e06030f030408100f021303230a05030c24280c09 74
    0xbe01d01441465140c2c13090340401c0741040800c1c0700100c0449140034000304e07506582e40e40c1c0c821903550002e644c8010840602e0b0200001480100e52020b401381c1d02d0044050011010040c1c100c121080680b00507038441711854404604c2251450450301090015055003000c0001200c440d00f803200ca68030960f2541c0210700a0150100528180503100000007400c2040d034805540c000c2c0d48001c1805420f051503800a400c2c00440002400d40360899880700482e07000d14140e2070018042e4000344a40300e0003034240003031903050500640b0000485135404110f00c0a6a03c1c149492107000320240c90103400d40180a5080303042c0b10144001c1000e4071211008020204002c0a032500305c80e0082114030700e0764810b0000078450f192410801d800c880c0c10901c840a00c0b5580c0c40d04030341c1c2c2d40440b007041c0e00324450750450703008004021000c0c21400013003000f81d46840d010440d09100d203070040ea0002e51800c0800000a0300700c88d003039101641c0c021402034500389000041440385c04880703c0d03030600c4011070040081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 511493435 1250 511492185 511492187
    0x111160b0f0f2a130503070b090d112d0324070c080c10050109050a0b0108010603091506031103010c030c2a0f150c0206070e060306030a02120d 63
    0x294122140c0c16440303881e440c042400d00c50414001d054200640721a40d542d0000303c486100140504140c1c4035030b07680c0c4401091811002e1050703845028020f0269400004052078601c003134404038074010300040075155a036034908508100103454564480b5203250b218034070520500c45d00e031807039090300429001154405d0800d4580345200f003424104201d0025010300c0341c5100810b0320741140e0141004900c46202d4078003002039001d412122000391041c1e8508000c009801e410850480d01030000130091034558200786d0b0152030310281300d54040703082c40e00100a0503210794412110a40140304c510010802800100309544440d441600c0c40b00325842c408100d440d00f072141c17201030846420304101d00c2c3c40006e030161044041361030f100303401c42c0d40c110220f60300060413040f400340310780c811402000021189001e11208108060705190b070703803400040c40b5a86000046040c000c140649500308a500303004100032003513100402542c0c243c00ba400e20540140c89030b43d1682c044070340d86000741101c1c0c000c2c4d0310 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 511494685 1250 511493435 511493453
    0x309070807090504120c14011104051e030a0308150406030b01140405240d0b0702030a0f0e090a1e14072304030b091504030306050f0f090f09011116 65
    0x101c02c0e01031904080c000000c03c0407094240d081c203c0d04000b140c140c41070400b2803051485840350300c6075508060070071042004e000c00410035240102c64480c0b8048004042c0004040b003200700c01e8166100041c03c1000ca0700070580786030710513203000b8611100d140090101c3c1c255031440d0304c103c0302049008010301c0703000030020040161031001d403010401e925044c07a80340c003051442122403c1301c10903214410044c1d110001003030700454018194101c40d06250900075907036400f100c2280005000e101001d17800c503200d03d00c07032a0324003c0101882e015498181c800c5005140c4e18a112a03c0340c00483e499944080c07a00a881c15034889246035102881c015101411040c20301408100b8128062900c00708800081e0a560569820a420300031555404590f03d1802c002d0300480c040301c040002c100b0042581c1500b2a070160303901a6200d891a0002c0420300c2004907003034840c95840a89100054840e1082040d120b034044422400070605c01d01d0700b00302100d65480382d59980f0040094407065000c0c001000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 511495935 1250 511494685 511494689
    0x4060c030b090c180418020f030a08041e090903171003081206030c03070308042309070c0c0b0a09050301050108120307120b090a0507030b0a060e090a09080309070807 73
    0x2080500840ca07960001030a121401010541040740200780100040207010007000f40301c0000e802086164548441c0061008445400b00d12a0a50b6034800d0032a080c00b241c0c60801c00d51183c041400c0c1801c040c11700040080074806100500c1c650000026540d48500602e0255030003611409a00300d445010303624203240050420041e01e4820608100041d5228111111100450034001c6c1d292a4180000e0030304410507905985845500c0000c020700401c2c100820454100805610a4151004610110680301c1e40120b03400509000002c000038002c00788908074600c95000180d181c0c0e1111600c4081c0e40140031218000340309804207000500b8244078040c0540100c400030160095000b078916000c1c44020b01100c108964003084180c6c2221079041110700b020001d080507140d103800b440340e0b002444200c0301080003134200204030710300d410121403400545105503642110403d091050021201b07010703018094080da00e9015602180004020b0340c00b0307100c080007410fa01440e11041a241c00d640b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 511497185 1250 511495935 511495937
    0xc0306060f09030b06040b090f0906060f09040f05102f09030705011202120f0703140402010807030908090907030903080121021c0510051602120a11071d04060c 70
    0xd03030001c1c9120741100c030010460f40d1000700038032280d940b00042806424103841c8660424951000d01c0b2440e0121100c00b40310b00c1554007100c0c03555a03080304110351f445101a0b11908540742c100424003040c82a15009401402441101c14003512410f80000b154801c81030703042c0002d012a848680361843c00d0103503c5100103c1400c1d403d091615001a480301c01303510401d070601840c40e1400b403a5030040d80550750302110400d060f84103031400d003101009071030701151206d0010b80707455804009000980e170481d000d20740681d5200c1c6c05641d13580040e00141070b908070503100c062080c440034403603549120301c00c0d200c1d807070b5558046010401d52401901c04803061308001d08a0200030b0114520b1040c014801c079400390111001312041c80d441415040d01e0211840160043c007806106803207204094100307078012080301c000710200790300e540000c0b41c032510f898203081e6109a08100c0d1007142845600040801500c003815522881d95403038014450928034481194060b204804200c14407042c0e02c541e07600b07848030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 511498435 1250 511497185 511497197
    0x170108210c0709270506190504050c0111011d0f210304020105090105040803032503020a02100905071e03050c060f090d1e050304030b070212270a090c030606 69
    0x146540a9210841ca0040c10300d0a83e0380c407241c208000d044c40c00d101c40031100d0020140400c0850030b000b501c41c4001c4404650490315046049421005840340078031954211000e0032204048400454000341c0e107100303159056480b01c24154403080c14401c0b44c1403513a1401d0050602c01d00d944620742c180756410b05001a07108003012864140d001c0e610849a019034240382c8550307540030100060f00c0e43d000725080150148800300c2000b100241d420701076504041d45080c00099548903400880a91090012410042c5c01c859800c41102d0b03c140c001c15105481081980c01c41a218049400008200e032105d81c40c2d01440d201c108280407052003c02c40400050b2803451601140400351302c00c40c0b10340707a00640101c4548001c502800000e40e0008444255a0310081021400381801030b82c0c6e81280c0803d554614402000c00c0340103000160750721640414407406404c0c401002c0369501c90302404c1500c1c2e07008024101003c0650380e20040301002800c46840c0000b28180c0d0000e009044400c1e0303421000078441 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 511499685 1250 511498435 511498447
    0x507030207061803060f1d07050604060305090c04020a0215160519030e061501020708070e18010905150411180a020f041d010518012417010821 63
    0x15001c2000001d440007400c10745000320071402000803812a95002400007032600a9034200640749400400b00c498070f403860741203000342222078651030b959070344030302e46d4003040401003001114001d80195030710840e01d100382c1c2c0724048643c0105041c0e0b800102400b0058000228241001d01381844042d002104034010b682d00908050024000d0b20641c400c000c0c00241002000f2081031182d0401d000707451003082038030740600f001d0801004a5450030f4000c0e0150141550100c1d9003c40003034a00c00f258002170841086880300d580318507605119a0181e0425521003c0b02c002080041011030752550403103400c0401031800e400c0a13070802c090032540724420343d90f5401c4000c00d04601e40016800000e0030600503660040c802d1003021600c1a84d02c26080260310300b111140070f11400581c070741201e800b56500618100308100e1270310444d1b001d005450714802c0b03040400c40c5141e0880b40038000c030b00d21414001004144048002212102603100d0b040d07035846410303072044080045624251818003d00701c40c0c1040c03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 511500935 1250 511499685 511499687
    0x17010b0901060302030c0d11040603110c034003120e090a02031509041203050108030301060c03030c12050f161701051c0212010509070b0a1e090b0c011b050703 70
    0x10810b00c80c4004044d00400070480d08110320086441c00001018108041c0c1104010081300350064820440481d241040004401903071404032044c480415000e90300e00a6400c0110400510700350b000d2045c260701c2035100990380030306428040304214000070040c1c0546545804900d44440b006128200192440340c10004e85501c1c15054102c03100709005601c907a12041d4404032245002c1201d580042080c4c10311052101d0102c90301070000c46a9014801d0340e03260040f03140c1d81e110a200710f42c0010704907582d40000c24400d60106801402c40d1402d84241981c910300c9005550302520420f10b094501010f000d41101d04001a510b00246414506240c1d1304900d100503e42e0300503c6014050711003042c200034070441400040c1d030b185034010140c590031010303400b0090007020b045403608103070f00c542c50000c90056034035015200004500e99821030003200b2941032091711490324500c0d0086c06602d540208100d600707500500500010240001480c82c500d0611403600d64580310100700f804800c0004902007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 511502185 1250 511500935 511500949
    0x30c061b041401080405102301060906230d0e0309030c10050d02070507051002100c17040618140c090f0f0402120c0a0e090d0207080c0f01020309150417010b 69
    0x21071800d0a0030300c4070b42d86608103d400c11a85c90005075007140b83c41d42311500c044110601190058100c4446a25030b80c03280c030700745c503111964001d41e00815811052502d0040e0425030094000b450260303030505003451000d810007618140f03041130384244c00225000d400d500341081280131100c01225220100c07004c50001400510440d64408240d507000203145d4140403041150300010200030f4408850000c0d5003800035240c1010f22420640641403c184d07241c068030813094030042406c4284642419110b541d40c541c010324001201080800000f003131800403882e1504040621a41807000d4080f5610170810170203c50b10050120424030280810b021428542007001a8090b90540d1150240d0080011091a02c40f204d8070b410745c41040b4141c080f62202020f1030150040c2440001c0307a01140c01d080f0140c0e100c080600441b2602e0744002c80040a5107091464401c1c400b030103005a0b4900407101011603280e031000d150242c1d020000107030030048a40305003204211110120001c105000300e03440040c03d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 511503435 1250 511502185 511502219
    0x904060b0c061609050f03010e03040f030c08030315040c11070b191b111305100e060102011b0f050d0609021206100f0f05040506070c03232d030c061b04 67
    0x44c400d1b106061441c1d403800d40c007440300007200d20103ca4a0f195181881054540d1600007154141c9102100281e80d82e000015240100d05080328024149512010300000f4802403101100300603080100900b441010300524002e8020403000c103959a08021211780100b0b0040c080c0020060030024046041c00c00181400c0010385c00442c0d00000c88100700050f04645c084951540210b19201c18045e00c122000118401c4902290f000c490b01c1ea17070000107a00b2200702c18450140f0b403113070748a0039035142d11543c90320a820303210703080c042d0501c0b9170300100b00c04a0f0310a411a91200f680001d10007519802015451b52001049034208002c1105540007007540f0514030480e0305000610b00c0c0b4491f020b008000343d601402010b05070589850039400c2c12585906d16102c1600c0c0b00300c0d0441c01c0300c1c0da0000d000003084141006802040656402c0e4240a0115142580740c0105c3d2290308905450304414002459041c40150041c4039a060101e090504010120420303010035004000401111403000070a0403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 511504685 1250 511503435 511503439
    0x503070b0301171c03060302010207050103051e0a0608030711030111040b040b03062205040b0601031b080606070b131202011a24030a02070b010b03090c060304080904060b0c06160905 80
    0x2c514003111103d890800040980d1000c1c0f8400641c90f1a100e40c0350340001e00b103a00076421101e58030358600043d0210b0702c040d80d803000d40744a903469241105124000c0c254001081050014003c0d9540e5503e600b5070700448821994083c4060f000c0d40039103000d00a5164440741500c0c01480c0030310300f440c22144c603c03c51140403080140400000c01c0c540d103019001480014a00040500385550400e900041c2000c030f80c100d50456a010201d025540b09124214540f011010f0781c16944005c44429503100c040206015030003802005201c00240311481c100d4003625410398840d81040e02da20b08181c08204190030502107a00d00b80003001d920b0161030118100030000d0398400031101216040842c000301d850090101c5c80c41c0001402a0803182d0390041200c0c078056643e00c0340303076600c480210041d0300c4192030200e010f5219255003021072900a00441e00035201b0401c91f8034121941000c5000d841450780701090f60b0a0109070705503400c2041c8070565110348000d01101c04031a65a001800a101a0185078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 511505935 1250 511504685 511504709
    0x1d030319150e270303010905012303030405060d090f08130902211306060303080106030606050405090a240312031b0f1115010902180102030301060203040b07020a0e1905010503070b0301 81
    0x20010f429654080344080f030081a40d54075a1281c0030080507140030b20660349040c03041516682246c809140284100100501a42c501807804041012070741000100a038550350b500d50440005200060710382c40c0c94460034201b42c40300a40f01c2564016184c550006032580d004010005801c0400c501d910101c8034010034105047d15102c440180c04840d200c2d0082040745000d1003c424103030040b1101b4100c4071565002c0c081c50341c1340c840c103c90358000c42c800c281e080b1238481d021403191402d98100248101800561003060010046041d115010f41e80c03003550420f981d2419200c00b16070600842283d80039514540203100320b0402d00420741c0c90501501d42c104a418842c40f0a480000c0c0403080002c1c000a003540c006585840c020402035205140c2d00e0003030041d407035058a0f15400841134904841c06034001d981402e10b0700001c071101e980f191a0813079000b54841c00c04121401d0951600d400b40c40851100b16a600300101d5a500b2108181c12089c0700b40e0100904205410500c005c8a0650304034120300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 511507185 1250 511505935 511505971
    0xa030e0402070f080c060a20120a02090a06110622020d0213090302060105100c0803070804021903081e0408030f0906120708160305010f03061d030319150e 68
    0x29420319145244010210700700007407211700c07070200007551a0103000100c070100702c050307140481c01c0c490303002070040b094080c0f600f40300800c6440c00e1264903560000100c2000751400d0403130300010f50702c500709070841400700c1c2181002400a0200704680c99200007540307040101001004200d921400041d80000c1c49843c1c0b04180e40704540369034013a0342d1844c020140034058044a480e019441d0482401120b00070a00424843da016200d000300c82e403044e8100812a24544400104541d501c10081059800c41c20013880340e44508110103d400065004103c12515560f80c041300c903603814a26901e4852800b000e2105011141d008000c440842c8410800c2d9a554001e42000c20f4960066640440042c02380c03c04100b0325a40060b50140b050904087d400e8044640c004c0079812070704280114050b440300c102c0c0500004840d1341c458107480d221b2190411200e584154190b1a50b80201c4154009103090700c258a030b214081d0007032489a0b5031040b040c45680c3c0c01c00642001d0400000c00003810540e150f00c01c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 511508435 1250 511507185 511507193
    0x10309020d0f060b1302120a05040c03120903050a1101020d0e09060d060b0a083f0a020a0c0f15020319210204030819020c211015050a080a030e040207 66
    0x1040704d900b010304400f4880080c040710030000e40200315403a03550100400014501c103041d12805218681c042c8400c40c0c0caa0454480d00515020402c0c40402e20861010100c0417035000c000d150f1310b8503c02c0144107440f115001c002414088003c0703480c41801203402080002d42d454172101c0758000300c191781c07551408209042070000703012624130098121003d400c000c6030501004c40d203880c040042640000400171960901070360b00c8000c00e8060326240c8071b12a0003280a443c03000401c1030340d940d441121144852901c0e00140100140e01c580d920340c403103847c200010129100001c03100758450015605041c181d401400d421400384144a04000d4000d881c024550344001c40046000700301329045481d60384131724191680d6449448100b40d8896591211300d8820710002c0c890300d9000d0050070100c510341643c2c048040402550b04100f8040c011003900e003030120703014401d1172188840c00b01108042c3e86000c041c40200400d0340c020184a4214120202c0401d41141e400e602013503041e900183c0d80e0065042c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 511509685 1250 511508435 511508441
    0x2701061805040905161a0403112808070b0c19030c080403120e09092d0a0b10080c0303030115020a0b0705030a050f06010e0103020903070b07150605010309020d0f06 72
    0x709a6009190441030014000e0004500004c1e0350240d15200c00152500c0002c0400014400d4603a0b0394103082005100103140b02205103146000a01104009000c1000082100ca43c168542e8404038903c0301c20048c1181c00c201c90720041c03144070000c03450a4002c007140ba8503a5028901c1d170a41d40001c8100400701340c407807659807151075000400b154850f40c80b4035140c01000c9140c1201c000054040100c1c0740f85281a03202c46006d00c00f25001005040f410b01d5850b4030a43c0c9070344010940749141c0008880c0e19009000742ca150600ca9410340320146040000c107002441c842d0021082a40000c103000c84c10303200081168192070700c2c420200780f1140c55040032480c0c24600c541c020305d17426410081c02042a000b10195014401d030404c14419030381c0b6150074403100303002110583d000030108185115a540a03500404007504040c0985a40c1070b11000c0e030036032aa20142085a20f01684003036401b014000303121307502c0a040d013441c00303001101c8290005000800002c9010344004031040c0712508100b0158 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 511510791 1106 511509685 511509689
    0x160f060e010f080f190204120302060c03011a16080d0204080d0206042f091305061509010e15090103051605010e090408030c07150203010527010618 65
    0x6420904e031405420381ca014840c21518019480351400103002038020491204480110303450020324121004050744140394007480107109140c0301800c0c403c200c580310143c0c240c8855010040c460078000d040340c001c1180400084030440d5001c99000381040395104400c0d200005106e0304242c1e00c4d64011100208003001c0030380c0450f40512404100725880c5030b0302c02c8260200e1400740118414000c1915204950400c020b00e140030400100000e580c07282080102400b400ea03c240030440480c5c06002d801114140c000004a5600d401440c8081c0b04034000e140181a595a0804a4170307041101702130b2640e030b0603914011550b5409080d08034509400501507209a54035a1100209130704007408247c0d120700f0400003500401c1e401556081d424102402c0141d40c3e5140c01d080254a41c0d2280d541552920713000480b640103c54134a03880d044400314201400b1500c40480e030540003070750356 = true := by decide +kernel

theorem cover : BRFrame.Cov 511330935 511510791 := by
  have h0 := BRFrame.cov_init 511330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 511330935 ≤ n) (h2 : n < 511510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
