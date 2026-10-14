-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1067
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:05:38.492097+00:00
-- url     : https://prove2.me/submissions/1e4e9d43-3fa0-4bdc-b56b-4f6c7b2aa383

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 191726618 ≤ n < 191906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 191727868 1250 191726618 191726651
    0x11030106050f010509011107030302060103170a080a02091824030a05060403111e01091101030e0c040e15040c0806220f0c08010c02060a050615041503110406030e01 72
    0x12501d020b400c141a10854000454095101d482d50318148407403044559104030080001e07030051071090300100728039411400e14040002c41016400e0500e08108050502c03164000007243e0040804c0e980581c880d810705000600d51381011801c0c0005580c4c1004005807016484003030b401d0300d102c040050364030810307860515440d540080400381040d8004030106000078460300700c0610740010482035802d00b401d064038030103140e140fa40e0b0200450307446200003011301101100b601a8540f003401c08001521000240980b45d054402103d440b850388d803a90b044483d0320511000d03264080d04481d0303007440d10b0103180c04100b440d001d0081d48818440c240c009591050403d25103444107400014600c0502482d40d1042e0050351940740442d200301000c0000600d0510900401414140c1034010307100519181c4019011200003c007400d22a21100b980c000328496603504036400c1c3e90f0303101c0d003441a44081d0300d001d40c040c003032104640c1003c86002600182683d0305601c1818840004e05c000d11920015001222 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 191729118 1250 191727868 191727881
    0x103110d08040311030a050604050102070203011a030a0b04150603061a01020d0801120303021b0a05061f0603020f070503040e07030609061401030b1801090b01110604120503150406030f110301 84
    0x240898002c10052012514034120402c00490041c01c07913540c1809a603826041540a503002c85441c4e4021500c0301c21480c003030059407085500c441c4030301211301000c0c00003940c1d050480c4001d844050b01c280031070188008002c020503518141201071281d55620300d003480003400c1003903000c42c0104034a1840c0c2d031190700c0494107280c61041990341c801d40e41d0a00403443c1c4501e0303075507000724203150b42084600e130500340c407088034a910101c0c3c01c09803000c800743c0c0c00c0682c00c0c24001030400c0482249510b00c4410f007a65948450140d07102da00c1d005803200c1002d0229005803007200000340207484049000240d105800961911612040d0b40c00d1056950b2405150150744041c007aa904081203561042c1c940c1d4825884094081c40c0140585002c1c20302c02052000e2a0003030304000d441d1a00c0d0740700c1200c5540c0140e8408070081e4000000c0c1804d1501b5111440400461900c071802c0100010204d00c0080d400204e490307400f200140308000d180d9507840e18841040140304112040302c3e503903150710450300e01803103004d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 191730368 1250 191729118 191729123
    0x9080115080d1404050a09060e0f0c16060e070803031605071104090809090c03090d050705061303050d0509160506070201020d080705040909050604110604150e0103020d050703050103110d 82
    0x81c1400e5040c81000d0300d4810a01c440081c41c00f0042c0000207840d90f03119074000080040c5000001c140c1e042180c5aa5010340040c1744129400e02d140600c560700034060115a12032075601c03421000c1c80e15528050003e04603080d600d0b1014442e880c0c001c200c452021000314062618000310441e24241802c0942d410302a401000e0800300004001480c5801c0036040742c40640d105841581c6041c440394009540f04c1401d0b01d601840e25408020400245810054407007403030f2250400604043c0b207541ea9940c0c0d05001050806a1810301032000704050281c1c082e28403510203040f042c045850b107a2645a80e03010104410b000c42c496401c0002243c1c14110211000c05c1d030180d02803c80b440d00500103035100c913400703018281040400c120005806d20035100d41c01911340304030041d05072401c042c242416001c420481c4e46e0710801c01004100240c2d011070071002d5036100b040c01c1c8800b95601840041e40203001c0c00940b00340305802d1100700b109140c1d05a00080c1600d1244000c110b00705084424414000841c8000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 191731618 1250 191730368 191730373
    0x18120712030c11060a030e210d021317061e091518010f1b031104090504210806010f0201021305040b040207060c08070e100c0807050c100908011508 65
    0x2450040382c0700c1c0c41041442030103491001e41c1d1584280200301c40354044403c40e00040c3c0e656803600104842400503801d41c8020040c400140c0100b0700701040c2d184180b10f00044245c2c0e00040e5404030090807843d8000500d68034221b0410b5580e0000076540f24902160b440c0381c80e9000c0c0c051180d030701c244107400754040c400b1900280521079070086207a102c05030283c00420b114146a903203044020003402010044880300d40301142204da00741d0040e603c4944980040140f5042240000132241600181c60071101c1c01480401d154442d800c1008621043d41d29200c4032031240300d2a2064660040b007014015042039880f941c00300d081c00401ca080b801426911000d840001c042003015181c10b030812810007000800040c070b4a000c0ea030301d020031a148050040040307002d0b101002503160f00128880b8510300c05503484120081c084000610019500000610914000c210701007400002c000a00300b100001e003900a00000a6030080e05c00d659031310881c80b0940c2041a645005c4920b0101c403012034206200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 191732868 1250 191731618 191731649
    0x6051003110d02010c02091f2117040e0a0b0906030606031b031f060609170303040b0408130303020c120f0606060702130507050415031505120111181207 67
    0x802c000310905a900b07a040004d451032210250361840d007521701035a81c8252184e0101c0d01c0041e030300e659041a50280e00248480c0d2403041c10081c1301c002800003030f40e0010b85500c00d072040444c0c0040500075600503500e1f940c03422040184203840c40d030181c03013403040c03c940d000b07629030310703001055a00d403412504250590040d586408030150044e038130580e011030050655010364544d850320b0f0010200800354074440742d01c0341020401142c06c03510301009800a030706c01c41d0134680d40d410115981d20010b00014107a1403020001010f00840000f502d00b00c070b01c104000d80d64240c0d2810029a941401d282ca03903c50000c40b11030300c40002c40004c0c905007001888010304819660101007002c182c02c00340c0160380014000541840c140380314411a88202c0c0c040e110170341c850303041c0000030905120740642d91090504d0070b02000c200031000890b0342d04548084a0022440980340b9006024200b0203401201d2401c01289160801c00052030390543c0755002e460382c8444440b02c2201d159203801c240300b000c100748083c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 191734118 1250 191732868 191732903
    0x4050709090e010f0f14060d0803041e060e0609120408060103020915060705061506070b06040b010302040536070813050c090403200105090d1b02040603080706051003 73
    0x42201c18090644000010481c043e44240c605642c81466044003d41c2d86c3c980c841a04907600107641d400560644004000700c0c0c80b40c1c1d407840f6600c0007a001607c0c603120075101102105040c14074001031030f407002041c4807003a03a111940340c0d036542c1961460414096008200700450702c2000750750403111120001c21540c0d29507004d000c0d4420010b08170710b0300c6544400c8405000e448a40c005c140b00e6105d40010001441c1c40304c080805011004c480034452001001740310049440c40040542003c4100d500040c0101c02c0c42c0168000d101e036501642d0054260b0042d1884149491a62000e80d03e034016407400c00b0050425841d01e541c41156044040b070229000b2522000311944581501403040040b6003028070307402d0001c2c410542c02c1350100c0000300e06440c601c1007801c010610441d40b04641c0700034003440c10990300d1680c66a8000d1085810444140e00c810030b00c2d504119569100c1d07402034010804180c4178280300303030706511404040c2c071030340e081c140440d010004190b800c900701c942006084c50028040c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 191735368 1250 191734118 191734121
    0x20030a080402030304170f0708190b09100e01020406082a030a02070516090f05010f15180902041d06090f060402090901090b030f121207050d02071208060405070909 72
    0x103007050f40c0501c070a12012450769021140715243e08400d000503c00681060080d07898050307650043c1005400407900d406a0030fa46510401d56282d0080d07250940d0340d601040c662402d18140303a428031550400003042d241101c190300900035542940d40e0f10030541c1d03030148110341e8281072401c01002c03c0b00c1c1c0c510019185c00410040c0d0341049076058058500680307900d8191411300585003401c04da2030382d9541009240c01034455071340b60149001c0180300f950314001241e29a0006031040c4020718085207014501c55115810080d00d42560a841078207090325001c1e14402500f00c1c2c020f450003c0c0885040d9940d00c06884030326031180000070300443c41c65841101e402e00351200980403640003034003400f0609956894000141c00f074a4065000038031a01030108142ca0400004030410180d0880103030740b403113024024221203040c0306041d244800ca4a84103c1103032a03108601240e080944007040810420250221150008030a41d50750b074010b4403104200021200c05948010100e05c4444c1c04004021a6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 191736618 1250 191735368 191735371
    0x4170705181320100309050c040b0d140d1b080306040f0906020304030c0c05060f09060901090515040e0703021911010e0d090515090d03112103040320030a08 69
    0xc82c0d0a8400030540e0b1101c42d64010704080342c9030421020390b01d0140d8185030500d200b1420040ca028009170080d038451546546490542d14061910381160f0f00c041c6e11480d48031034240d907110345102d01c20100810000c0d10703038050542d41c0b00010001405417552008800500000c0d5030000c001c0d502e56103c0c03034100320042c030351401c6034901e141e110341c03d404c08282c8520145101ea13020380c0740d040c5100d40a141c001450000e60f00414480c1005011844404100c8010b6604030305003500c07a03035035410007070006a0394000a640030951101c240c01d950b2910080480c00303001100d00604240003030383c03607480c0f05900b0303405a50303c1350711080c20007104c503044944256a4108040400400054400403000301d60f07090840000c482404514000c60070401030a00d03000c01910002924000e500300000d400010311094681c1c103001d810007902141040c2c10000030301070748a500c010342242068902d680c02800c030158000701c07000c1e804a003c40303104041c1c484450130404190201a000ba5107018051401910220740 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 191737868 1250 191736618 191736631
    0x506010c0812101d06130e0309040908070b01080a0605070306030b0609181b180f07080415020d0506090901140c0d060801060303091502011a040e01020c01110417070518 74
    0x200f1440004c0c4400102500c2d04400056040355900b0b031510750180540c3c1c0c00e02c00c1100041c580740600148040300044140c03607d50381c080703d011440c0000341c2454030807030059440c0904019400c000009100d840040c041c001144942d405000580d00c00c0c805500710748540c407014003140d801200155881c64110b00785075200100f801605e4148010750142c0b807804900e1a501d4054600ca190594805e11302114000190f9402c2c071402c0b100341c41c04192520701a003000c0d1031541880411004035003048002d802c400342c0070003281c1e82191034681d14801c1c900540000c0d140c040c050301040001c103801c010107000e04841141c0d07007002e050664071001c56135070320355205410b070019081d0b9680303000c03581070000c1c0100c0c80158020380c0d640c01c6013400c0ca0040c2c40b483d192aa68002568540001062000f81078012080b204204640002e43c0c3e41544004034003a1245001d0541c0c95413034a05841850031801c805032065030f400364510300000300e2520900e0381d260a1409a6907220340c90141100c0071640e0390000990180c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 191739118 1250 191737868 191737891
    0x20a020a050d030b0a0b07050705061e0a0203030402090114010914131d0105090319030c0c050d09080d03090302061f031202070801110f090d11180108010506010c0812 73
    0xe03041c0c4410b400c106010380301d030300040c1e100c404503440d41c64001240c20217021400001c1e0b01c0c0c651180d82e616aa000705100d1103019000205118002d140d606200410011501e90030315943c0300000002034582d8030480f03040f44a5401e043c004541c0c02d201d00030031030b06100f060316001c801500784640f0b0402c5400300e004603070b401001940100b00303600d8540070b40001402034520000b61840d240520078251b0300d0082030f01075158410f1083d403410241d50350303414842d00013900b000680c40c8049130040b9802a040d40c40540680300f00700c0d4528840303500c0700410088555000c182c44081300c1440045040c6c510158014006034454400329118882d84070740b0401d0604102d1401c0411692a56002e8643c02c0c882042c1c00940c101c54000c02614800b0700405641c07680380462203190240c41c2110500c1801080d01d06802250200320402c20020003034000f500c17100300144045401403801a84007075aa03001d0203801c18650800303010603282d5000c1d281030416070b0303444640301e424400c40764600c07640320300010522039080 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 191740368 1250 191739118 191739133
    0x2060904050408090406080c130506030a030507030201060914060414090a150902100512060a2d180b0310060e010e0406240303180602031b030c0304080706090608130204020a02 77
    0xc1d9601c6c40380304003d04a10700034140701070010003000f8034007806881c000300c030030f00301003c1110f243e030041841d0020b6941810304540360306603420201d0040c545a08610b10a503e020004081c0001d1401d026102d0081294103100300c0c1c0011242e40b080703000c2528940c44139409600303010006140e1114441004d40c500c9400142045540c00180701540412400e90100380700003801900b8400422100750f00200581c4c80310542c51400c42e451000650061003140011140340b051900d00310038055060040809000c200d0821411281007002003090515282c800c0c41181420ac0210883c3e0040504884940701c400741c45078600000700901060081c07084800a070b031a0508141c02040d000041100644a110f10303901c603080d85005080c1071143c1e90011500a070007181086582e500108894050344421985000c2c04160700c95039140d4003c030066408503001c0420041780e20980000c0110803110103946181c800d41d5194400d8460000c1900c1400c46540e4a0070034a01500f05074000340b280c1c000910455584 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 191741618 1250 191740368 191740387
    0x60305071211061801140703050a050912010e1e0105010e0711120a0e0a050d02090403120603141014070e0108060d020418030905030c09040f030c05030c030a021902060904050408 78
    0x250360001e0000d150809541142e5013240d40c0c04132062000000100c4110716101c116100540b6500903016040d04111000881c00010b45541e444003800c00c0494000b400840d5420f585a074070f943c030501441c120403607150500303e004d180c1401750a04030340301e1629034121a140c580c0200c2d4402400003002d912446045160024008600010101e850450b540c0b496007000640070010725070010b038402440703070405c0e000b18005a42d91040050700300c1e515042000c0012110f42401c8060640c9038006406801e96401140381c4a0380452503580100842000b00070b4a94105650803090034261030090018034040328084180d4041d00c502c6030481c03002000c291550040e81e0000c1c007a074500d03142084400b00c1080300380c000c150300240d9a02c003402089000c0d2034001d01c180045030550070020320103051000c08940780400e150007040304002c000d40010a8964a501e04c1092560766403001504400511440e41106408885c050f6000c20701980100a81d02e030412145c100000ba240142060710b0590042141a11 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 191742868 1250 191741618 191741629
    0x1060807060206041203021c050604060506040e0618071b030201060e01060f4d160602070e16030209031c020a050c06030f0c0f0706050a090213060305071211 69
    0xa15a82d4000c000324a8185400ca02080d0384000e807078181401407014507030241c00860002c0c0b60500c04000040d181e40c0c0ca20008000d4503440e0311880d040000010045400300f13003d48031502c640403c0d144c0d910320030851846040c9104048030108000340c5021034550450380083d400466440c041c1c4000704100ea00e030845503100c1d0200303901c10404280f20080c05c505458204003030b101c0d841d9130388041c07254503203a003544801940d1100c40c081450722601c03100c607030601d0321110b9101d00f1408510f04450598488100c085040c00f41c0c1d01030fa00142c86450800200c000003071241d039120b1240341070351141200f26000c0079806508082c90041d850f003d40740d0348411403440c242c10000650601e5004061303400080c10b000b4140a952012030380503c804104000c01040800d1016400c40900f034110f980e5510740305108000d500980a0061409040c04184060380a540d004007580500869290700303d007400181c0c3c17508580740f610009010303800c1000200280c801c4514070981d901d0250803804884c010701400a003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 191744118 1250 191742868 191742883
    0x708071505070915020106080618030c0312190b01020a021c050a0b0a0c050702031207020315010b032401020a030f09050d081905120105041d031809102303010608 71
    0x40001d03e0351002040042d40009034090940701c50700003001041e00b004481501e81100401500c8501e04401400c20701c07080400c00c07560201d8911042c0c0740c0740e00c41e180034252102015140c40c5651440035100201003806c4d0710075000903000580080412108030360034481031940c08458040000c0c1140700d41e03008580188403075603010b4441c0c00e440e500d0f807a0452080c0c040311000301d0102c0811006016000040e00c0005a0b1500c2d80c0201c400541c0300c22103840000c6c40c00c4155100300d9400d0076840000500300850001540c0034488102000808808058090841382d080340826030041e1b01082c0c3c8500400c7c0583c07281c247c1c200d10b0b840d013507031031079140c00c0483c0e004c0c10100c104564003480012041c03d03100e0f102d03405402c501524075099103010b500c05003040b8100018050740d88078669509040100d1011502010002c11020040d40e031546280840902c2e942c442064003030141d03c5120005440d05440728202040c1c50b0780c001c40d07803020700b1031010518129a0550440f40c04d90340e50440071811820800000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 191745368 1250 191744118 191744131
    0xf040e0c01030507020d0503060402220306020c073c08030c03070506011e14010509180604051f03030c05150f070207060503040803011502070308041d15060708071505 73
    0x100218240c40c00014200c4100504420454014400d00408a680f103c1201d41141c8200c03409600c0300300344094041e404615183c03004282d03052840001c10014190003400402c04100140c03020155101b1959001c200401d45c0254200c0e01ea41900302c00e601091040c5a240d40400e4452419607160040745d840e55221440384001c80e0305c00700702035041100407c5001d024100000300d801c18a044aa05030000f02b46502075445010584c03100c0d1030060f4821029507580c510002c3c0091410800400d1080028100340c41050041d800e00c1c00103000c16002180091400190110f443d10741440c6844c22240351605030401c075420301854107454401c2d20115140ca02038105d2031070f20101030070301400c045c1c40d00c5043e41c0403800380b0506004220119401c201a41c0c11290f406d140e0584c11155030208a00307102c01500010300050001c900424062400c00510012020101e00d40c1d815890f1865003068080344003003540c1e40070108114a10014560300c0140040078030403083e2007002c0c205000d245058480442d00d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 191746618 1250 191745368 191745373
    0x180807140102180306090c01080c0a02011103070908011802100e03071206050601020601150906030b1f0201060f14100c0201050706060801050f1e04080a090f08030408010b01110303060f0f040e 84
    0x3207040d45000e0018a406c0341000008144018400c1e00190075580c0080590a4103040410b40c690070314000e4115417101510041030550381d18102d0405400e80504d4003484d41c280d8a4510611020148032640e2981e0503002041054202e071550b00880384020401c250581601400d800003034101650714021290078455803000c12140341c0a8002813420794143d101c0240914a03031f1404e10559007100b4cd460588a06260105180005501280c002c800403c401c1d86020043e0b200c0074981941940440f003910a403861100407566200d64280b00102d110b01d06c544d2101c00640d02c0f5000304d01030f00601d603400e841030412a0801140c1c0c1c44000440e0300c15440519140d444e5001c00280051098011b03910092001004010503030010105c9803201c80144000c1403108009000000b071401030201e103008165481c0d060080359100d01076a500d0b90080c2c0b045404a60904030184140e41c042c15800c0509000300c0011170850392070000b044080701a100407144c0085081910301010303280e41c081c845400518400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 191747868 1250 191746618 191746657
    0x50f010b1e0c0f06091f0b01200607030c0906140307020c06040602031806040e15030f01020d0605120d020d0c0f21090f0f1701180c030b0a180807140102 67
    0x5220f00b0403d0040580c40742d900708103080900200058286e0442c464a1080082d03080960b000680714107044a0001607040910340e4801303481c07903000034154800ca034103650910404a00d24019194441680030350000304440e0107000c9004003180010f190f015107507204594507448010302058840c0c0c02600604016040000c00781200d10300032401b81038001041e241d5a140a1510300810361904004d0402c0c6110117403401c0280c11990200440482c02000a00845d91544100ca0660091143e4031509000f000000c003140744807503020409500100007a00645803c08440f4012140407540c8981102c035003682400000104040c00000090400c048044045c040410300019115900550141c0184422480240030b000e03600c4807240d0850b40350514084000c052085518050109011070664070b2540c421200d0500480c0b680c050100ca000703001c0300020b511001c10000c00d440c4d840c58100e208001d2456500000b9141d00001d10103203008403203007401c125003162540c0c00c2e40c0c401c1140e59021300040c0c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 191749118 1250 191747868 191747893
    0x4060806010207140d0c05090c0c1504050706080c1204030306090b0a050604180204080d030c12050912090d1202100b270613050a150801050f010b1e0c 66
    0x1110240c219009000a0016504e407081d00300c3c03ea2084444140101000b861090411005407140e0026103002807615a007450f20040048540d04100140080c0d8428140b40e1840c114207155510301072a0845e011305135841c00c0900542d0302c004003030300e050504541004031051031902c1c80240e90251f031003607802060040c503201948090b940c900c0c0405d031040310900c00411250384e80108690480c0d00d001480c003500300c0d034489260024003c0e6801001a8001d8150b0010001d0341540600070100c06502d40d0016641c91f2803820341211022104856240c2c0140c180700d0302d988081c40501203c0034024410100c03c81d29a440c669019001003100b80540d0201c0f900106040c100e00410310002016501d0001d07022903c0300d013000b000d071000140321407800303c07201080c46c581380c0050382c100f640205102841369090000240000b420aa21030125118200300c000c41c0720700060084c1402240c00c400500c078180d0034a601c510860b80046040040a965802e081082c1840030000d40b4900280d40064070080c640311 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 191750368 1250 191749118 191749127
    0x102030f1005030312010e0903250605100b07030309170a090510021b040203041122110403080a0f050408070f05030105070e0306180a0c270204050105070b0603071203050406 76
    0x581000f4400e8006015502e44e021054040a04480a010004009889100c111411803040c1c01c0c80340e0446c40e0002c2a00c82040c1c030703603170b1092010380300b200f08003e550b492188081c010401070003110255202004894003082c40380d00100c491902558802001445080d425a656448507508002188908404018600e0b00483d02c9241800178005400d030b140d0000049501118407414962045a010010405101c1080d1210030620400f0301501554801d941c20180e03e0380d2200c0f0308984c600c0c200f034020b100608541007610112a4450303845401e006d0011020349410064001000400c83c0c00e100000c1d4503241002044010121854240380d080e0401003810709655000700b00c1000d0102e0000c40c0c400585000031001e038008031a481c11020000e90007032039030070300344120800781c50304c80c10040101e0442e40c010694401e0101c24801205000b002c80c0d442d00c241d0050b446043c0c00308034203010080c0803d01066101e41c2c4158001c00392107106807030300d071411445109000140d0020f100420280b0070190071 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 191751618 1250 191750368 191750401
    0x1050a0e010b030705010c0f0b09030c0105100506030604242603281112030108010f050405061f080703080a08070c020603040212030c011e0f020310030f02010c050102030f 75
    0x11400900401c1c010b000401d80e51615846840e0400852000c900144050741505042440d4060b40e41401420322001d2540d03a07800c01c0d10401c0095181c6800b158503d0603480c0304004644020713080b5801c60f0f440e03000700300040c0126000303d528600c40040b890044116207068601070800c00100182c501c429030380014000c003040166400c130354001c0000c603000c417840464560316118012064254148074010840f0320309000d12501350188114203000c07503002188400745041c1e8507594000c010700d40d0b0a82030041918800d03030300905260003d2021440d450000700072400200c0155541c540350f01e9031070b003000303240035016481035880740c03000308900301d50a520680050f00002e00d40b40c545480d84c540d8000450605c0041c1c8028400d051a001c4040d131224140f0a031040e03140000000c0140ca03214412510b0040c040440c440100b500c5c010384448000250b1080e03d00840a8882803030205083d561000840307070406a041e0f040c00101702900000510034002548184a1103040255608180c0f1054044130038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 191752868 1250 191751618 191751641
    0x27010f02040f090902060315010216080a152315180109050c0309060606161407060206160507020f01020a15020c06010e090303060108040c05120a1707080403030302090a0b040801050a 80
    0x30a844c49015070340300400e9903007003043c00c10503032034003212400180c7c90030012404810781d0004c00ca00006101700c001c14010b030214002d200349031161000354042c2c012210041c0e00e8800c1c02d4120f400060200c4504d2003400d80c00140700046114801d0884001141a896899514201c0e054980180148140e9015140e040309a003c8564258240400e96030389503000205158007030040891b041004103c1d030100030a5064016101000e0412003400c2c03a51030386028003d542c0540700300310100301c42400d9184044003801c0c1321b5507903034100741469003000710400135000c856045200303c07021000421009203031001d2048101d01c00581d10010880380c2800d1000580c4071000304000c15003013120b0f20342c02100300d81d4006c1d02481d02c11916951444c10080c0500317540c0000303812841640200101400001b4580102e501034900d0744074801c41c15002403058407603420010500c3c0e000f80001c100082c02a0040c260980004000d400c045442c0c2d001c4400e0394000b40d01a601ca1f80d154018070008043e1817244408504 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 191754118 1250 191752868 191752871
    0x30a0b040b060a0f0302090d05030703110f0a080306060c01110c0111030708011206060305031603120b0307062d0e01110604031d120102030c03040201080c030402030627010f02040f09 80
    0x1d550400201940118140341e42400050500701d0211403099040718403114000b8000c2d9400001810103580e203400c4000d044020803800280c025805600082080d0852003040050081804a548a041d103410242c030030394200e94144440141e00314280500101c04240d0240a81c0b42d90003040b040c1d007562500d40c54109a04c40030818003188950061009054131160310155400441c60b262582c0200b40c1070740043d00d00e01020401c0000340c18501101c5803058001d640d0204907022244c440021528440e05036035241d032010904010841c040c50515074810a0b89030f14503407904000c5011400c0c500002008000a03881420b00a4030f0360700282c0746003141e5600b600038011450700c3d075405440d42c25000030a641210b0510150201c6548092007210907080910003551603050a030503000080d001503d08131b021070410b130002008980c2440c2503d101c0c980043c0180096201c102449101d10300004095001444550300c0d94100c45090050a0102a014100590726481c048698a0f8402584c10508009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 191755368 1250 191754118 191754131
    0x2060325050c060a05040503070605010f1a032401020712050309040c0f0e060d060801020720090415021b031210060306030512160b01030804060801060807121e0f02030a0b04 76
    0x42e0005640d0780c000000440058039403180e0604a20b907000d10f80d0010f10090402c000801d200e594401500d0031107025108280344031400740c0718200d0700d0108031010503d4a0084030403900401017610300903038001060042e5554240c03610505c42c4414018031080d1040d600009009503a418188a40c04040500d4548002080050a0300411441c104a03010b44a00800305001029640540c03081e0300400d03121000315920112445e20900001a0301440c0c4007242600c102c1c209642007101089120b030f070740810b0011880801c1100c4a000b03400150368102c03e48541281c1c01c055800400090101500000d103948040c58a0007507400e00003a5a00310b00c08160901c002040042d030001240e0101d0482180c48585801021038420441f000903400074005290406c000800e01955200501c00d45501c0c0d40c4585441ea00d41c042035030041410303691038001888010b8186014602d56210408c4402c6041000c0b02c4014080c0e80141502c1014400c0000641d00100b4080180201e1080300300c190b40039101031140c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 191756618 1250 191755368 191755387
    0xb07140405011e050f270307030206030f040501060b040905040c05120a060e03190c05010f06030b040b0a1415190518070309081908060a0b04210206032505 68
    0xb20036403103c80d034901c01ca01801d11030610340220305a550310000f45440544405c05220464620144841446860300d0000314480c29420f000c45c2e590250b0780c01074055441c40d02c511103401008040103100b42d0b025541c80230040381d482000c2000300010711060001141a0405040071000ca01290b401944241e40c030400442100e1004110442e000390031034000294118095401815445410100003040d5102d420241c2041d8121518400d0b940c010310080010707609003940d8604480103070101425503841c0c1400140010140310600d0b03071080300c14801103840b015040303401b12a2001a18044400c1fa9400708082841c1040c29004001416801440b86464a84404902c01c1c808400380003028541c0700000615060081d02b0904c821036208120544d2030354026a6034003071780070700d4070400d0010300c2001c0030511030b10b02022040c1c1a02d8940103e10310302484c00d9041d601042c442300d01850000f402d054403401590711200034522645482050070310555205010201c1c07410700101400910001f448404103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 191757868 1250 191756618 191756627
    0x301060b18040e0c1003060e070507050d09080c10020a0b04080c0c0a15030b22091502210a0b06070f030801050904030504030308100305010f0b01020705060702180403030b0d0b0714040501 82
    0x804100903178410010f42c1341c00c1c8040b005440341d41c00401540301074000344040554040c0c010081c060148060300c64112060404480c001918858400d2650100342a20803518000761941e0304061140116801c1c1c103040d0740c035042e94240881e01507801c014082590740d1030030350501040e490200102d0b402d02680e0305144c05c0301031900c0145107070ba040581c2d88a4000c101d480380e619100000c8009031400200400384000100030700070b50841100c6001d1840105030048655000f51110b240c0407a040201d50f603240e02010710807890080804101c0c6448420707103d8603450340c4008007055400ba001e1451055070314240503000b8031042c0e000c98000c0321000100301c0030aa014041e43c003541c0c0d05161440a54950103201d1141d001e082c0c002071300d40c1d441c006060010b0131681c1e02048207a402a000d071025142d4400400c8024040d103070707010b5049110801070b0801410290a032613400b80c402d00300003a1002c83d21000c40c040040c0810704071004030b00b10091000c025004a121080005c103c000740386003500300000200b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 191759118 1250 191757868 191757883
    0x709090c1209020a08030c0c190e0412030f020418060b0703080103080a0306090c111b130f02040f030c06030605040203042d061503020f060414010f030b0301060b18040e 74
    0xd00103551050311100f1940d410b1988801030a481301201d0302e907103250000395101d0101c060502d10840700c622607c07038884074406504d412990181890503036603950761203250a80b541c181010003050740e500c00e50f004118583c40684042c0c49102c24025104011840e010100c0350103400c507554480b000e1000b4400640c0c031034807041c1901c1d400880a81c59010103030040e406440c20f9080713141980d01b821200c07500240c0c800e406030010031441c0d00301ca045c024034040850401e112840002c1e00250f04103400160080e6a400446600740301d820014079040d500c1e0f0741b41d0700406503a00f0441d2030944012040025561500804000d0a401c490451460904da52907030903807855865000444041142c80c6140007040c81e16801e00039400003414040c030745d0b61203488807942203a4041280309001040030454141010030031f8600395020862010500d045e00300041d980d180518180404040d110103040341c8a03202030003001e0040586801898850b5840c5800b40200c1e0458512507000d07603d4003914401100c000035281 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 191760368 1250 191759118 191759147
    0x807090b101103090301060b09030c12190f020d050f0609070f1202010203070f080327030d0518010905010c0806031507050f09040905060103050607020307031e1e080709090c 76
    0x210056003810000f803d50140e240003c0d495443c0900010707100a094006004000c2c044050b82c40c0b40d401001004a080d40d80c03000342b4810351084801a251000100e00f640d0418007078103802481980d0303903002811032810140c00303c03019049100e180d40c0100c0c0410210350418080e0001d4050741b030914400c0c14250480c0d1140c1c040314020524807800b503900078000c60340e02d035402041901c4c240742301e400c000c407040d4010350303c0c42206940c00b02501844c0840450b82030f170b03003e94003016500d803051180301c0002414010301100e24a484c24810078181200900c90100c42030712500012400c04040300380034140b858014840f5019402c51301445501089950701d0f9544401c8a00b00076480c1c41144880c0c00c9540149511607402c07900c0c000c5a40288000010191b0480313110300c04844e00c03580c599800b241c803409118002804903064100d20312100007098909412900310f4940a260420007040801c0d40d00c034841c5105020500c02c0c01070010013580401c500c0301a2080c20024041d1810f8600d00414000303100140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 191761618 1250 191760368 191760377
    0x8060403080c121e010b13050d0204060e090d030b010915120e030f0405030c0103020708040b03060d080406030b030c01030501062c03070305101a0108040303020c0a12090807090b10 79
    0xb03100c0841c00d4060300c0c0c40c144505a40781080c64000d443c1100000c603480340050501282c400014100640c10441d41100512500f41e60071a160200340850b0741d40018080b40c1c0a51142800f05860140c02421031242c1074000050504145610780541155058080b0504001140005002e14a004220a000c40486107411141c0880703841d49a00200f644420300621404000b60003155007288101030015601304070300380d5401400c001c0041d0228420440c0082c5910824001002001c02c040044c0d640550050500402010565281c00d2a0350113070300150086a520178403803001341003c0000c220b0b12107003030030200250750602c0005441c0200940003202c08001070410340840c1b0030b8055030b66a001c4400b60484e81d5030f5449142c0613403103502807144020414a4001ea0b5600da255210120b100e441c411307128102d00c1d0700c81c0e0b14100e020394080c1307294010620806c81c0c0e03000098140da0250040d81116510240c49d141840040b5082106aa2004c080141480c0c0005060780d01e190580740d4824076411b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 191762868 1250 191761618 191761621
    0x15120a060b03101e03050c1201090c03061b030e1c020304090c0e0306090316080a17040308060102010b040b151c0e0a060c02011a090c04090501150f0206010806040308 73
    0x40600141a854004400d20310000c01841504580b08810900b41c40301c008044103012030301c03e00d03181c02c1100f520020740a944a210341413000c0c01c000c1c2070301403201d402030004982213140b9115883c003440d0b00d900442d40503554103c5144000104041ea820807005071505106221030303611415900c0c08140c0040250012024219118500030003c403402410205014000a040010054000310401d94480e00a004000001e08200d0340402142c00c22200d00490113604c80040d00d85c0800b940102c00164248000d00220465115814040d288224402d65030540680381c07210009080d00c803101c2d429070143c0d09080145490b903403042d00154030402034810013a198401c92034107855411200350703030364a06403030220803107a1158007046840a90380141002d0040c5003035124100c0c04c880c003580381d206e1080c02201103681c0301d20300703588a03c2d000700d03000707040c1e90070981c45840c00320840c1e40a80c86660519914103240e094160860201d5040d041240041d102544c505031205803a020010001800c101e1080b0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 191764118 1250 191762868 191762881
    0x204050906071409240c15101e08010f050405011a1509040b0604030302011a062505070801150e060d0507060804020118030b04150506030a030e03071a030a0b1512 71
    0x80780c0c96500a80b0300000e0386030031140520031490340c0c4500b0046d4040d001d0310040411143c0f0424605000d4003103104071040d03107454204100c2c002501c101140c00c813410505400200402c090058403504035040300001505e051500e00542140c084c40c110401d0107c3c8900300000382e58417555130b043c0c031070180219035507651840c0c0c000800030003000c081c030703a40000041404810300d68154003c01c0600c464034000e01c40080104200030190003120000351110315000fa2032080303240300210b140111440744080303e5402e92100d80749801e48002c072091a000100c462020040a003d4020440e0018400c2d500034281d880d15403603564441c08540038000c00e201e0340ca408542164415695000d240e03070068106c00e0400d48900c5c0859101c2425035043c4e40ca4880315482030351030440307842140d015040003001021070140301c1d90151813a401d446071466060082c02e100081b0740c0b4001c114840c2c0c100059003016600d15084c2e4440080760001c0c52100c1c05181044c0c7d104200c150340340200d0740807020030400c1c45103d90790003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 191765368 1250 191764118 191764129
    0x51906210507120f17070b0411030f01050114090a090b06011d130204030b07021501050d060e030f19020105011505070f0c03030f020705010809060403030509070e0907030204050906071409 82
    0xa5110075114000f01201c0ba05004d00e01c490707110558801c024000f42c0c489201903d411368015120050814180312003c0b800062494991004040d4094196001940018501400c64109a0250000b4807400007244542c1c03400403891680000542000c0204c0100c1c2d8403040104c1d10010245d5040c0014420a1041019641c6000b00781070401440c03000303114035a114000103904140300445079081c00d1800304180900105401d200c40d0807042500341c040c0c1c03030002001034003d22141c0a981e11a9102081004101c05000070030000728041c080964504412580041c00e0215407600c4045902d0303d4014402c0d82003541b52a02c50300c44501c0c00c191202070a0801c241c81d00c00341d050007000901040c100004054000700001100c0346136030255500c0554450054820542c01c80315081150042070002d030000e40a44d111700c0c1c011000c1d104482c14251107041e20303500d0300c3d000c0c1c8050000b503102e02820021403409005881c1c0c0b04102801a1200703003041c40000e0b0151300d1101303002403001c601007080740c01521103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 191766618 1250 191765368 191765383
    0x53304170d061509120209070503130f0c06110d0f0513080604111c050c060a03020415211406130b0a06080406050c0c1213030b01090519062105 63
    0x3200c20030145640e500070f00d07100b6003042d540d08089401410000b075540074801c400c07a4895006410361004d80e446440c01c03141a40001d04000c9404410b520308800301d003c0c40d00414000e844ac51b001c442403818407901809504840f80c0d0000d15601c244040e429259004001040d600300a0a0064485d0580101050204401c0d0030004d4144940410401400300306c6151009501c0d0984144112004521000352000550740000d8490f0b8000c62841007107050613401450000340a1600504107620340f100400203c00c8840d4010004406468240e0100c80031950340041d501e00110422a00c040f00303240090182d40200741d140700740707102d80f10700b0300c0483d0755041481000d4000380002d143c0d546541001c0c082910a031015130740d03e841e00000884050180e000c03246012084070040101100030b01d29000f0580c07101d00c0c42c004107505500000001251103180c103020301a080d0000c9890300c2c0c000c441100f000070512a01c40800d007030840030020741c0725810290103d1142400c12082607550303414400d20b881c02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 191767868 1250 191766618 191766637
    0x3040308070510050105060a0203180609060301060c1e0201090b0d1104060c05010b0a050d20090a090302011a06041205010b030a06020c160b090907021905330417 71
    0x1001510710204080403c02012040d05003900304204d90300c61060004a00a0a4490b00543d10400940030304060320980f111b0013040007000700f40382c00310000c041100c50b0030aa2141000c82d1010307045c81e082102a6403c107507040c01c4000304441400d45500028002000ca21450166020008440c0307484581600810a10f0300b43c41005507039030341e56480c0240030400000d8203948a5181550b0900b061a111200d0030407914003c0c0744000000c00340e01c03545d0f4070341070f808240781e1034124030404c1c491540c40399039006114207060344002a604a0030b040180c01d492402000f01842814003910160380d980c0d1109690a4440e0074241d0645003e107803500714010070384d100740c00e9810321480080c2c00c200507454000700030b0044c0c3c1c1c00a0b04d83c1a5103200802921420300d00130003401c0002481054540d050400c510b42d8009140d10440340441c588120503a86150989002d503100c0e0449540d110407203d038503081200a030801c045e003071800081d02c460380090b914013600050185060050590446a1103010354500e0780 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 191769118 1250 191767868 191767883
    0xc030905070609050f010518041e0507050a1b0f06180507120c08070f15031b0801080c01050c030313030c050303130b010e010305030a0c1b0b0c010b060c070e060102030403 75
    0x40d12500043c020740c440e442080e00c6528200c20101a41d480749041d68910700c01e0319120344001e80d4182c01c00c00942200c480070f1b215a0030081422035080d0003809039500403603c988441e40e645210000051420740d07504c0090382c2d800b0f0b400001c980005c009000c403500d4560002070004101c050354030140a501e0302090041c00c07a05c54039401240a20200c844004807a12a0404501095482c4c04250301c85800f071040008066170880100311810429203c680021510320700050701001004d281840d0820049050000800c3c000c014003c400040144003100340d42400c1050408281361407250341d030305c4024500e4000c03220203110281014082c140e02d185284c1e0141c182c035201d160448982148082c42c940607188440450000a00c1c0d000301154641070b640c1007009175207090003400041d07502f81e640000848801c0c003051141070f036100c0180c40150140049150490b40e80c2004020f09094940c011009442040200a00e0600b07000008002003141ca50220000301e90b941e010045c0c1c1103004560002e403044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 191770368 1250 191769118 191769133
    0x30510091103061c02030a0b0910020a08040c091104060e120607080f0601030b0a0b0a1107140312032e080a060203060102010515060f181f02150c0d0c030905 69
    0x111294002d5449039a0541e42c0328120009800d155400c0008a240650140c000440000210b03040c1010305502041180841c1d41030100000340f04200da11459110000036035407400e1108000d0340921400c024403840714144100c40d56410241e8442c0b2861190750180500450126056158050800d00c400641310544045141141c0301400b030102c1180c40e040c200d94604000b076000d6000e88113000c5170740030141070030708894149000c4549550010340e200307082c001d4400501a1900041020f44003174290503100318054289281131515010040c14504a0180283f0800842d4805131240c820102c032005010400300c5e140015180c4252140e0f00640760320b0003407120140601217143c00940c00381c07a0a0b8001c1000780d4031502c03030030780440c60340d141c0540c49001001012009c8887e82c015094920600e92011880a540d01c0010311640d010070100030500014180d1241d600d0301400b44c0c00d60034075005001c406c0c070301c0c0c03603c80c8681600c1031001270750300e00b43e6608401180c01d2107580a1040036030720404990300e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 191771618 1250 191770368 191770391
    0x50901030b0d0f03080c03070f03090206070b010f06031a030d030908041505180103200d1103091623012312060a0b0a05190c080a0f0201050703060e04020103051009 72
    0xfa079200a00590116501c280072801c0c5440303000807240304611507901d1004641101c0001c5000c1d040b840ba0a0f83e002509101090110b03490402d024002e100504242d041a40307410303800307000d5440b803030a0385613035050110452410707480116810080d5031080c0b400103182c02281c50014403500075904200c040410004108c01e203550040c0042040140045040e180440002d004500b540c4401e4030081c9800e200c12480c40c04504c080028242c000c0115101094415460903110900d40003101c5030a06c96001208442000c03040608000c045c101d0000d050500194081ca0041c504038008800360402c982d0010001030116121817095154400500d141d0382e41c0c201c03003107100b0407003802d8503000c4c8141c1c09450000364a51441003103589902c85900c03a0750410ba0344d074070880210070040e030b910000d22074500b01d01400505580c0c014080d84059440e2012000700050303000b0308403400202010140b40c81e140e003d000c0f82541e01c0c1c18079072203542441e0108080c1e86480d030b04640b03d02c959110241d20760414400440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 191772868 1250 191771618 191771633
    0x16090209010e09091f0f0207060902130606081602070e040311010c1b1106040b0c0714100804110411040b0408010b0a0f03020904031103070b0114030604050706050901030b0d 76
    0x3549090381c0d42200a45220100203070001c05442481440e0b12405001d4104c24101c1c0c292040c40100c050001010780301c2d06071080c241c0e80000e408440c11036a4480150840c6802d411951081c0100002080141d08144000c2c01d0001c0140c841062199103086481d2518801c00c154405090b201841c60100c1c00c1514010305110f0324032846940035400c0042c084082c0d440782140741884400301030401c00b4001d661f00c03641c4818250b05034503904030104100110b0741c2e104403001452144000c00003000400c0c503282d203107020740e602503d44611a40005004000081c1d02071030864106030012002d040074030b0b00c04001401000c600000c0304403c2c40c0030034001040308840c0064812203407030300000d000803070300c2c241040504802400354916403aa002018009418118002c540c410300c203080005810079a03403042d1703107990000e0308202c0e060309100c80148001c04d45d01910707400e407400640c000c18290038030350f40e2540c50b88903038054407080060100d2a0b4003140e2180c0c10000043c100035003884100389190130100e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 191774118 1250 191772868 191772877
    0x60804170c1c11011b0e06090405040c080f03031302010305130f03030501060f111507021e010912020d08070305100e0103080c0d1b0206090f0405090f06090d02120c160902 75
    0x4103d00307001004080c0d406003e00c445440f031280c2c281241c400303c010251101c90010031030540091043c030040d55141c885110349805103000f40d00190b03115162580c0d07640742031036049050304603030001d10501c18100d24001035140c04581c24207012807240d49000e81085890203000000d0240100c82c1140300c2499013590140f4182c0b1940d641e8440c0c6811a40000d5902080b0610360400c554003c9900f0400040c1507040143c01a0f214419106280c0d01290b40c24010b18250381c500302c0c20307503540114208001d400710a4003915100c600213410000b02c840705c054080400104050181a00c400001d80401c2902c0c40c4403011700301e100d05020603543c5a0400c9022504000c640b200e0520078220307a40041c0740200d000e0001c0030390b480d540010304642d80e030078044150001610650801e0380b02024032819130300d502445101da07884400518502c4030308683d0a1a10f80040c040c0c06e402d4000800141d101540459082044492a04180d98580d03d1500312071801d02403044440d030041c00c40c0380204180710b07113400030b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 191775368 1250 191774118 191774173
    0x324060f0616060b0f0d0f030e100504050a090b06030a05041103030d152103050c0106090c080a050c030c040b180d0506010602060108161701090519020405010f060804170c 75
    0x4000404404080c80990741000c044035a200c81a11b10010009010515100320700c0d10910b44003c0d10050807012030104050520711b0303404518085000d2080e414912201c40003081000811300c9400c801c0b001007100b520003c2c0100e8480c98441d80000e00b488080c0d80d90740c02c008409411251307587c000c540c2c0f0b1402080003500320040b81d05031400001d8041c2c180404080c0b200c0c07a8480040421203a681c003a689a449804010034a5480c1c0000098a024611800300b0301041903c0d0303110686041003d1030200c0e03000800c0551241c90510500c44008566020340303007640c071000c104030356880c4d0700c5400713101d200040c0003420b500c020400003082c00c03c0030101e4618101c030025000c403200c0380d80750310402d51642c0d402c02503440520080c0a040002c80c03803000e90401307201d90070740001a46030f0031600d40d1030500c0c0d16011401c1a204c20f011000085040a1240740d0050600c242c0400750141408801004048041d1000d400b10483c0c58940d01100883e034102c07030b2107481c0b00b012203031003065007511050b020340a40d14a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 191776618 1250 191775368 191775371
    0x5071e02030d05041a04030803060607061404030c1a0c09040f02040b0c0c1c050c01260f090c01090e070c150e0709050a1505060d02070b090a050c0324060f061606 71
    0x600a20204006d503416240d0089002e400d6075507100a100390b5400a03c070940e8131540320008005a00e031401c0710075002c3d500075a540c0140c1d01c1941890710003d9100144075a24400304001c001c07500e42081c09440101c2021a40440d540304020f1001000c2d01031504400350403100050025041d000024dc0707c1e001e068152101640440121104a00d0b00203a41c4007509582103401801d203150301c10a01141160302c1c0410b00c48020009110300c000e081c008580d50061b0050100a20210703010402c51080d851009203001da88850a100c407c0d40d505d8070141c1400305001400844a04000010b802c2d401c3d90320707488008018003004090401e943e0b41c0c0c9441003290f403030b15040201d000071020b03020b01c60001100b904069aaa460142482081d03030105d8240f40c0a1f60b8248404000100c001000038095031480c0020025034285c0d041c0796080000d05941c1702d105c2e9104001010441100d080207001a0131302d54003600c080d075550008105205000c10718544d10900c0022164a05844c5480da21151400740c00f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 191777868 1250 191776618 191776649
    0x14090606150f03090106061413050f1201020c01061a040b0d0218030a0c140a0510080603030d060e0405060a0c140a020102070c26060907031b1e0317090105071e02030d0504 75
    0x658108d0f42c0314448010001091941c024071460500020b102a1501e01a09041c400040364252030308a03000b0101c40140c2c0d94480c0002c100030505c4c3c1508494509090744024505840d0141c00343d4a0b10a06803c8400d00f5000b2541051004600c46a040004809021754002051030300c1c0442035a01c09004000c400d03802442581c02900b000e06200c025110058a10000350050707800540700b8090080c9034507030620081004038040b0444c1e004001c02070204d11420b40c41f0f41004d28219040a800a18080c0964031301420050701c0f80e8041c3c00d424803108140003040d0703942ca108004038068450340c0707005002800036100000d60207101c01c1c4610031003000c6c101c0c1e20282c45842d254842c1c5900d410340f0114020ba00148003440414003a02c0c1100d410303c0c103005005601c1d40c0c1c450803100c100700099040e104900d00800204280184d50302c90104941c7c034031100c140340804079400648a03005821003e45001000410012803030584030304602e1141d0000e08507211501c0d4510002e050fa4030074002c1ea00c0b0180542c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 191779118 1250 191777868 191777897
    0x1128060c180303030905010b060c010c0801091401032303030103080417010e1f06030f03020f240c0705030706060b03190207020307030f021f050a0314090606150f0309010606 76
    0x1551845680c80070981c12440d40c03840e10120054081c00409131095541d0340c100720217540d100402031181001c214004a402e0100e17480c060245841640315103003c030709015070400141003811503d41500c1e40420140c141c42c14400200300c0d04440c5a040d07031603038800000088103000da80c0c000380c0111440d4910154251400f011090709890220710109095405032015288401e8540410020303058811800604940d4035141c0700c0607074203901d03015409600b00380c035004640d140070b1202c81072421640808101c44441031840343c013500c2c80104140880e0bc4081809400c108081c8115070500e6044078061001742c0c1c840480f1901030340140c60301002524484180c1144020600a4440301034004010b401c5092641c0c075a42450281414203c2e4061040100500d42402d120a00c01e44d00300160b40d42d035114803440e4009400c03240d507251884080000d144c10018401c0000481962140041e140300308007503190040504240541d00c01e5030564a00481000f007118415880082221500e9441516225201 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 191780368 1250 191779118 191779127
    0x31a10120605041e0f230106090209010801060c0506040b040201120c0305090c030d0e06090f150304020f042f04080d121505010807050a05040302040f050f0c0301151128060c 76
    0x1c444c000c0040321600e41c50b002041d04e5113000b03021a030680d00d0010b604242481014215002034000c0002d843e804220010b85517886405240940001d0030400c01000b1107440e855960f082c02031004040c2044500080d045921031181c506a60740c01c25014030840d04454006005480b0072240d40400d8803403104040301d603140000d00044104a141c8540c1100941c00c828401c50b41d01ca20704580d0040c01c1c0700d034102155156049590182c40a00c0c4000391207042920400c6441140c01580500c66403c20900d250120070b04800308040326001c0c44180c130f0b18141c40414078018087d9500c0300c0303801e002c2e09081552540d04500030f02c10303068420340208038040907030820010035134690040c1400660071704006440315000d4002428041241d0030a80d0130700c2d40d80c3d40010705032482c010040c100d02d9200d00038056091181400d681e00180919505401d43d0306110814560100c8025002c0800c0604032100e03820580910941032005907000700400031101d030029142100e40f000c03500320345180c41c001040c0041c6125 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 191781618 1250 191780368 191780423
    0x1606050f07050a0905010c080708040e0a05011d0a051f0b0901030b030304030c060503043e0d05100207080f0c0c1003060e010302100324060f020601031a1012060504 72
    0x540310044105d00346801181e40c3c00c0c5030002200e221104106080200314030b140500700600e1054210200341c5414081e2400703660041e071200d040c80342002044000d4040340c030501c0c6d90214449000140f2640da007a40d104000c0c40203c070f003001d440d003036903c0031400780c03030880c0101442e58003a2428042923940c1c0090507507034891407202030102840b040051103058455002185c009003e0130f02c0200100e50000d0800b0f842c1203030620b1007801b030040e00d682d0020f0051031512608140c030440e1422805451600c0f4551900c144a220b1086a0360004460b81009001c600340c0f0510001d580a80c0d84a00c1400f80840d646d2134500e00140c820a18140041c0f0034911900601d01681c035105020221a4a15030034030001a007a041c048080c50307110b861311307071226601030310324085010885041441c082c07401d0005040204400e2900c000c5410010043c404a004e8041c1c4222008069900c444c16580307403078180082c1c00c019046520005030030481e400c14011140c0005000d030f401980d0b0400c10019490b0016500c1c0503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 191782868 1250 191781618 191781637
    0x90b03040c14030a080a08040b060907020601050909190606060e06070c06031a1c060c090b0415020a0209010e0f0135010e1002120106030207020109090209061606050f0705 75
    0x116420144100682e840b45440d003060040c080700c1604086503540e001917001a0a20030000c2c610f002004240301c02c004400707410080c1030f26016040d041c0060001d403198414002ca600030148100490600e9004000000042c07507000e4400c0e0311114240b030f00b8409041e45214550004503a600c0c80e980740e26040c0304407003138030b5400100d05c02024580344080d80540341c0079510390300d00740075915540025101d41050320414055054007145030703465032030400225842c0034107a90030080d4000f03003442050200790071182031f2440c516150400c4019048104e19100c5c5ca900700035006a810f03000003610000d2450618062603145080040302d0b0307200c141d14010802b400e1080081880c09501d18980e00c60184000c00d50180200c00108040c01d101040320320702000b182405140650004050301d940348641c4945014040c1440c0652422029400003461070001c2e000d0360b404c0a6000a07024216604c000c1260562f131002c00c000800d040e21820031200800e01111408103a0003000c001505445c03180040f2851540c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 191784118 1250 191782868 191782883
    0x61707050a0509070e011209050f010c050315010809010609150f08030313030503090a141e0c0a05090a0b04050403032702210307080708030103031412070503070318060b01090b0304 79
    0x181c0304c40b011114600661a214180906110031422245131801201c0096014000524000d800d10030801e0850f6104031410080000038001e01078203c90405183c0c41c801024a442d24068603154003140c0105015804030b0a4507151202005c2c0715000c583d402012919144c05401c0c446a0b82e10040d40c4a01c0b00312441c035400c1c601002d8800001e4020005941c1000b000b40480c0d10710401e80c0e40d040450001001d00c2041640300c0c15442c0c035180408400c84507030401d01d2002d460b800e0340420100c0c1c0c20303403907e000e198405d00c0010700140804626501c6080034190080c400c0c021400d107030402500030803410404071b80d80e45510421700c104180b0340004aa419030702a0141d062140c650b14120b41060700c5a141c034070280001c00a23040400c94040242103040c0c0140740083d82e9502d940307070141042040118100310b00e10240300e40c00710806403040c1e044d4420424100b41d941c03503555000443c010003100d0085600d00003036048220a01c88d465124085002c000e0302c03038500e1780f6210701d0a42051b00046a0052161 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 191785368 1250 191784118 191784121
    0x25050607030e1203030a0624030203040f0506011413021303030e03010906020d020d29040b0120010f1107020a0302041808070b0403090902070210031d01061707050a0509 74
    0x1818210000c08069010707240c05480e214220000510380502000c401020b540080107009001500388100c0c4020006d01da140004618400d01d0124102810b840079030078158080b00040520211080d5044100d603c20103a070819030f102d01f800349501103030a176098065031961104d491400b0700e40c1308484444a13020240030a0b1840e640d000c503903c0e41c4542c49a9099502c44041900103409800580074100c60000c0260725002109109821100d19541d1114030b402c80441454024484008212070544251800710740e0301704110060300c8801c00c000071145558200b064582180b1019030050b003580c000002d043c00818080030340588680600000a580700c06011000c100500e080d40c0b0000c0d004004500c3d91400b05180e8640e003100e600640001c0e82d415003104104030800d5849281c003000f074a61104c003141481d080e074001c00c0c1949890071071f10701456079629481013000746082c4080c00000001c4024000c0588410750745002c1d11500f6502c150130310449001145520304503181400792180501201001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 191786618 1250 191785368 191785379
    0x171b0d0b0901020c121b01140a0b040212070503150f010912150203070906030e03040320010e060307030e060919080a0306030516290912030903060a0504030225 70
    0x40c1100640074802a41d0b080144104c02e070310500034044801c484244181e103e5091414580300000c17800c2e10340c4203a914240d806100d029080c09030a400c0b4a20000004000990b070340800c2c001c2c4140e00c203003070743c600c00b010800c1030030b83d4014005c6103d10782c48071041051420450030302c20f080c07008a4145000c114000410f10242c0944189070f4045402884d06140700110056a54100c1c0c0c42503a030307a40056541c0c1c2c418013031107416000d000d6004040500540c0742601d540c0740c0384501000b48040c0186d9040c0c43c1102040c503031082e10b081c2c0e000c00b00241940c2c0e0364180700030b010340145141c0c0b00d604001d01440002a81c2c10b040402c12540e000c1c001d4500394400c00050340c56811b690310400408050503655100417000c10b20030480c2140d0310500b82a031540f114100305400c04182c000c01c0d8510b8000305a00c0c8269110700d2120f0a843c94100c0c260354250100120458060440c02450506600f6129900421000103103d411450095001e9001d8420740c4e848506050720b07041c030b4100d40c58001200071008106 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 191787868 1250 191786618 191786633
    0x106050901120603080403020a3303090209101404110f0a11070308120f0405070320120a1101050c03032a0c010f150e01210c171b0d 58
    0x40c2001454084541035250001030100d510703541003a501c4c61004a0140110b0408a4801c0f01401d00b032003c80d0042c40c502d210f200e054041d840c01140031003240c000d00d5010140030ba00002012540201070030b04500c1c1c0014008080b804038401d14800c1400350220606074203141c4152140b0080400840307191403025038403040194011000780702048a0400386102d5040288034080c00703036120707500c3c4540c3e911500c0e480394200e402c0540300e4000340e441c0c00b0922000a0b80042c0c02c01c1140e83c0300400351400400c0e502d103180289071400c551740d0007140c2c8c82a014500e06011802c4006644521143d007000c030540e4004440a024000c0c0300d09242e40200701041c07596020781d584004180849088000b0103161882000342a045800f800307245a4543c180304500450302d00520b200d07d220154400101031070411549440c0b40103124a03204442220646502d54407140380300c503142900716455007002c0d0f0380e911501030b1008c0c1d0f101e0308030a103000781e5a610300e05070300301400d045c50080010304100e4441055100c0d100e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 191789118 1250 191787868 191787877
    0x70b06040e070f090b030706030506010c0f14100615081909021f020102030406060506030613020f0417030705060c070f030f020c09011d060904080a1b021504140307030b010605 77
    0x34602c0c4280000028105196100d4074003400040b400032441810050a161500b0280d8020310181414441081080c0e64820360095025801c500110b00c07410640c100040081060914116103018250102603141d030741d900300300212202d40d6200c054001c00500300b210761031015200550844c0041c4940c1081001581000c0703c818001002e0f84915a12100b552101040303850245025035004010001440703074138840d0200500e0282c9980303155207081c40001d06090a2041c081030341d503901240000c8c000da540401d4801500d4803540404015642d24446a50794000d038400726020300c07490700002d01c12503041d01501d0400c1d9203c4000806c580c2c4564040c2e60401000058408510901481c13000700da941c1000d2074004e10b9a214a143d40400380d07241e0200000c4d00070441405440e05d0307010f10001503c0b074000c1f03840c801941e160548640e98002c0d26040c00b0161008041d50251103d01044a8800c42c074000300100c0e07044620701d12030081920140f584455943c40040c02ca140d0b01c00040101e00d01820081 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 191790368 1250 191789118 191789141
    0x3121803130609030204150302060a1b0506100f0803040b07080f120117011103040b04020409030c0b15040501080a020a03020121051005010e0303520201021002070b0604 74
    0xc0e8100707000c001c41c19400390701660164000403203401c030400c250b0520740b041e4010840340303499481415040d0b401050292080300c1194041017107031003441a0000351603015689840e44042507503d03500b010f11920700d80c0045800790300004240b03501e001810031800002c0300c080b034003218165420041a0b80b1466010341084000c00420340c0200403006c10100303500c2074107018080314100d10311501001305d48036007190402c1c81c400b0a0004100203110219401d0541503a10541c101c90104000482c0d03e000c0700c0e40e032900308004102945020500030801c200c80d540c4080b2440545042042d6a6600c002c1640c030086a034000e5080070f20300d40c0900155201c1c0001070f800868512a900c010322000005404580c01210448640050398000b407100e90b900a00650564404034000e60802c411804880c00480070414280300d00d0310b81c854140d0011071140d0210382d40140407404200418400c288030704064591090490041c007500c61080032050251007510009600403201c000d00d0f07540e20060000400b100c4018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 191791618 1250 191790368 191790373
    0x906090703290405010603060f0b0a0e0601020102071401090b100302090f0601050f0406030204141f050705010b100e03150c121003080a0203070c1215020702010e03010e0717031218 79
    0x208440e541006660301d000f5489180000385031403a5060076070858084400d0b2500503810486032180c2c541d108a829019210706891042490301d4040060703009104000c0000d01450b070954803180c003d041903014101d180d014250700562951a21130a0707039240f00d903010095000c82070700049490582a5a13625900c00c3c41810021324000b01000c8a400580059001100094002070305111000c403118040c4054003098a4051140c6c20724034101c2014601c00e01200c041200110381807040c410309401c4004c5903140a0000d00180c00044001400d01026551b154040d201c3c0240598031080051441c40c850000ca070352181c2414010f00c8800744101001c1c000d0300403601401004004940840300600788100f00345c0080d603840303415181070300b1407101c140d2252558034841070620000c129544a49130030000c02c1103006903110302ca84016203140c070810241350b80540ca041d0f4802090500091148141d80018035524044203904800316074900c101e400140c4d010708020041811658034038003000d89030f40e2075003d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 191792868 1250 191791618 191791673
    0x1b03040c0509090a03090806060604060809030f1606050609070e120c090901021e120c09011205070905010210180215040b0f0a0f02060736090209090906090703 70
    0x502d10a50548a901d0340340c0004520500700f6030040c92a0000700143d4005c0c04080c41c0810009500d8000c42c0300795028080d6000004002c218140210341c0c1c2e09032400c0900351079068080407144400391801c070459070700b803419000c5107070341c80c000807414412459030307480c25102a080024460810f1000280241c03c0c40790a0302140c40da50303400031702d40c4561010307000180c803500c08040500d0307441e15000c0150f10038441040a10b25540e01050103981c043e440c1c1c4841587c6080c0603004075036024a1804400d101032a10f0140009194001c0c415801ca55090f400c0711071004803640546e044a8000c08525400031400d4a05001400e00328032403103600409645950826a8a1507007001942c840842400e62550006d105d03031141e60442c016070f0700101c951004028030318081d8030103003c1340d0709101c1100501e000c020b900221541d103940c002c0d413602d071058981405603a030394141e880a500303d041941d02c104d40c103500140312001e00188052013080e00d08020007002c0c0c17840c2c40740c180b41811072000700d40403602650b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 191794118 1250 191792868 191792879
    0x20f010e130c0e0d0501201c11091c030305010b16020f0d020a0801090c0f06080a0b0f0423011e090506010509040e0d030c020105060a030305090d0203010603030c14061b03040c 77
    0x1407440c11301d07009000105503140c2444001c4107501d2001c01c01010264144400c0040c06111088905201d4162034001244200c1110000305170103582e0655a21014421404014018000040380e03a14403a4034140300c1ca0340c0365202420140194000d08900455074240e403001f41c50a4421400d80000203009161a48815008204894042d8001150603915061580200003400032203400504211300c2d00115a414000c00402d28140500039900759a00e40034480199036440340c40d21240b480003001005040601c0540069903815031051242c1c1701082c00000529044119501010b0725582855001c0203080c6240b103c008c3c1405041c850401c48240880c1071280c580e88510000c41d1f1601c001002c2841403104c00078103441e99901c0020031641800c081c402540c8070050005c2c2981c0d410305000d0745034241400894680d00c903504c001b0354150b00301480003050540203130000c419140110884c7c005040000b0100d42d5504082ea000e151111181400d101e2080c06103000c0d40d0441d00c40c0c5a0200c16036605d4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 191795368 1250 191794118 191794129
    0xf0201020315010c110a0308030f0f06060a08040c1e08010f0b0f011b081611010c02010f0c050f0d080103051c050306040e012c0106081516021513020f010e130c0e 71
    0x1904107d235084000003c0c40340c18080000c0040d4406c6c42da00025410f0703c0c2030004a812400741d640100c0038080c1383c001040400848900000103468994a000103100c0104401d102c941610b12030482d45501c1d2180d191703812601070082040070040540741408050b0301c0c400440c1e0080e041e8195100c4583e1003031410300091380290013800d00101580d41d4016602031410039026081c44060400c0c140601c42c01c1400060760000003280100d9102e05050010081c1400c0440c201500b40d18681402c0c004d02981c241a160030641c007a060741d0140003110564013100102012140c4032905040100f0740c00e00002d0003501d0f290300801030300c207541d400125462541f480f003d140080443c050030400300c0c0800c01c20420314001d00c0340c1d000a00108c401000b00d01c04030500303000740c42c0c0c01910545c80b411070b0105890f80d95000b00080c805011005a40b13500d2440c2001103a00d000c05981c4049106008080c0c0c912103540c030070603004101c1c2c24010050001d5181019441000b0150b403d000000c1c8200e06446406c5075a50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 191796618 1250 191795368 191795389
    0x316140a050706050904060b03090a0803070203090613080717072303010219110a2301021b0d0305073e0d03050f06030604080a0f030b1f0f0201020315010c11 69
    0x44d88489490b40c0384034003004180e0305e040e003003010810b50030700802c101c0c05c000103148800b5907080458660b5980700e0400c02c034110300c20b003141150400ba00050401d4100d6820000c4400c540909095910581d20740e440f039098107107a21031442c0e03641d000300c0e0144545003440c000e4001c40028007031032260107160100484e0036600035501a03901101003810a00800350014504a48000480c0203002c05145981d40d40c00d0404c0b43e101200c0a04070344d0b02c0707148240d400c2541115400b0310703600b1f500d81440c0030030164a99036020018080f4006410700020a80f03080c0603100c5c072207644549501e00c4600e101602c000c4118414902d8144040710304400000124480034003214460050568020605103454608500e03d018044c10450080e03100004210115140000b500d0754207045281031703c08404104402c03005032041b66007150f4000c244109001c81c440408030794100009603501c54034541c4282c2e840c168200d0004860280c0c101000000500fa2503228125903811f840c071441090000c0340741c1d100820119180d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 191797868 1250 191796618 191796629
    0x2706011e09051906050f0105070f020a030516031e0210050307031103010b04050f0a0e06151c09060b03010614010507060204080706050c15060a170c030105040c0906080316140a0507 79
    0x81440700644840c943d80560409090700703a0341103c800f011500001c1403131240e07502c0501540e082814a104542c3c910402c84015a0010100e80324201c840c24000402400c61000321a60128049480340031548006040b03a1660000c000320001f0103504801e42c2c0d141e00c020001c00030140e8845030310601540c01005035002e070420214007521a0700307200500100034086c51200e8800e905e03010bc1040038010f140c0000c0d0340440c055804469503c0488030b0701d100c038000e140001c2c01500050b50681185c4105a0140c00e43c1c5000e1a030038000c00c00c155003414220f0b0202c0c0601421050110310004455005030000e00c05a481001c00610340395803640a241000c2d4540c0000300012070000c5c2c21200c40c2c0080101c007072407644a0007044c0c100c2c14420000342d070b4201180b28540250044140911003800180a401309002002e00240950302d0181340c02100703410136004a141c004e11740440404e80910010546416071055100181c48030302c0764890707400301ea01d54200b16141d40b044582010000e00113102c0c2800810 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 191799118 1250 191797868 191797891
    0x50f0d08011d090d0c0218070201021e03090606040e10050c0703020d02030c0307060b010c060207060b030f0109050a0b04020a08030a031a041806050c0906040b032706011e0905 77
    0x50404424801c0314101d01001002e2668200074462a00b00104000c1006440c03401c00182080f080c2c0302013040100141c0c042c1c4e074007240c070740100828940c041d0010840700080d400151185070100e0200001c80c0829519090310f6440080000d402e4203055101800d40900d00f0200c49419900d0302040054903001c03101c0950700714010410100f0580c0402c00c003030307102840340061400c0c591200101e0760380f8000d13280054002c0d51505210f4616900034145580307055003069082d5a40c41d402d0501d00b014040c12001e41d4000e01c034541181e50300031418030079407503610740c0716004c0c0481a0894035054060500507000340e0b4407003a883e80008414204100905403c00c00d600c01050020b030a2604402a6540c0f0b06080d00850a00c050051300d506504001d54140381e000c140060740380c440d03d0744417582e070003080c08064000350009000304441d240f0401075481100350700490201304c4030000300290001c0c0800c54070740c0c079548400014003100d4001d050b5a00911510004414025907a0140c0c20648205a44094405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 191800368 1250 191799118 191799121
    0xb07170c1e16050904120c08040b1c0608030d0e031303030f03050105090c0a08180607200a020a15050f0714190b0a02091512090714090105010507050f0d08 68
    0x8141441070845024079480761202c03a5150901103249002c00510050030b4070400c20f554489540550300c1d206595070003c1c038203038980b6290032040ea05030f0300c4041c9080b2411919401c00322018442c1c00741d48241c40c1c2c0f01c8041c6090202f001c03604006041c040c050f40c4c0f00f50000b07015410702e010b17800101d00700460096495410983d640c070740c090f0488506800c40c1340070f140382404200c550b00307404c0111440040a4a03000c01a640d40310482404415485001c80b00c07402058103210301c484c3d01031038402c01c0714007078500300200c22011102541d44410800000307400c080c509000b08a62031080c1480f45510b071450500e1482c3c16111002950b19034031086003251140483c0702480608407041100c00f101e20700c292020a130054132a10f804080100007824400e82d2038000075904595100c51400c003018421907250903072100342c0740806110004086400c0049803080420000d03400c0d940c414826400d000c0600183d8031030342840011a001e81c810f01d02078515100f11540300e850180e0400070009004010390310030f0b009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 191801618 1250 191800368 191800423
    0x921190507052d06011409060f04090b070f031514061608030411220e0f030f040608060901151d090a090201030506030d02072c01090f06060302040b07170c 68
    0x10700c0e80c41e0f0444611a0b01040060000c030f481410061039015085501014559406001404445158400640260806429904000290607110f0140800345c903030b01445c0201d0f650031011980300c40005140540009401c00030b40310b50508020551401400c0a07162008001c8100d80034805500120741c0c1c0310b800000c200c02e0080c42c690005014000300c0300030700600407001030400c0401010030b001c0502e40e13a9582c120070014003040100c0504d00c000d01920b0b04c6020862030684250014420f0a01240f09140081c019203462045c4506032071003230680c01d1100352440c00c1100c50685415003451013040d00c1e00740c41400d540f516011032040c903c04401240254141c8001000c0e240060038650103070b071100307209050060300468000d041c0c412284018101c4612025151541070071900254a401569800803500723001903000b00642880c00003044c0304490355404224200d101d00e1084490046040c00000c1c005004d040d004020b000e00d40318581d0510034201e54075400e1280c1c0c4405281c504400c4c8110654 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 191802868 1250 191801618 191801683
    0x9060201110a0804020f030106091416020613080705100608100c03021c0e01020712230909010b0a0908070b0a09090501050d030c06140f092119050705 66
    0x8801c0500300303090300b4110040806061034201400080c841c440c0c1004007034968400758003010003040880b100f072041c9850300560002e030b803101b40c2d1240300c100200d25408080741d0000076601d000d001041100b480340142601d5000701504000b4080780c5074001d95010a940d102280600009414000040c4c0210341c2100c050707408907027500b5148000d150051161141c0501e414002011010701c11002148a901800c80c59009120700b0200400580b601cbc4118a16194041d401300e42980c05910200000f0501c4020703040d090050300300017540181124014400d09410101400f1401c1c514104030f00c2841c7c03115203150a010160304200c500036004500d0502160f8401a100024104420704100315410200403031600402c0480240070321aa4102c8001048440d50081e4a158940d2230610490b0601113040003442005230f0b00403156203e9145062704a80300302d400340c000311003121015442c0840303030508403c2d02c4207129002c03011b0180c203100c9040841c00c1400503c214903000c1c52928140016102000d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 191804118 1250 191802868 191802881
    0x5070806011b050a062a030228110618010c090b040b21040b010e07080f0103020108070c020315010608090d0c0201300603030f050c070e09120a09060201 67
    0x2044905028060140d801c030304071528400854140d0400c507034403410703c90328045401200800ea54604003100b134480940d002a40c581080e40070b0030b001e00710000c610031000e03802003003220000940d91058a2510507007070381080b0480611030802c0e00403441845482410071004880350b85200d001204c49484014080c496050058507d0512800090800e80503c0a80c0513034060301c20340c0c142c0060301440e542100c030b0212010107020084806245414a41075211501c00e200b044140c0342a80c021440769401070a920748100c402c003e54a4039a1b20755001142e1000026000b00140132041007c6005a101401184840c110030040c040455240a40041484030001d00208058005003604c2c1d40076a4890380f103105042d02441c190085819100072080040c9092408440e298410402421222142e130040c100300c1e40030340c84000c40e5060304e03c001c0d11140710b505103144946e0400b003014000411442c8016410854420440c2e0b61101e24420000480e0b10003010400410705084040045550900452 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 191805368 1250 191804118 191804131
    0x8100e2415031f05030d0336020d020406090e0c1203031306020d0f0603050d0207090204080d0c080c06091507050712080403020a02030613060b03070308030c0703020a050d09080105 79
    0x480c14803402548281c940005040c00b0001c0c0118100703140300031102ea000c1d030041d04005040c2c070800b4007801001340c0101080c4221112171500050702c22404091040700d00f240358900d6856107541c030601d9080007542241140201d90140c0d85402c00f083d0380e11544100d64040b500d0f200104051540ca02c200145580510f07504441a8420010400621170170442030566545c415009602c610340c000c00280940b201c800601d070800e2034071100005021002032100d04c00a10303078003903440485d2120316043c140d1080d4021101039900050000203100d101c0c1c0b50485803d23005451f16410110401803550a001d400e840614141c1c1c000074802d00c8803840c4074002034101c0100e00340b5918296840e2fa4048445440107018401d00c81c02400040505000b400103011840d802001d46520f07103420000790341071a909800030f40340586406583c1045050001d182d1050b690050301c6182581d851070f031040c25560104c1001c07401c6015110a0030000b500401c100c045030b540716166188820708019400b805c44a004018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 191806618 1250 191805368 191805379
    0x6060b041e0e0403021e010e12030117012c10090609020a08161208070f0503030702010b04020702030c06071a07050307080603150714040e0a2307090608100e24 70
    0x3030000103500081c0a6511101c0303246d0300c44145a09448860042801c5240c40c14513009115011040d2407240c070080d4160703880e000303408508645052140b03088910b0600c1e100080808200c1204440304000800c00301591054100d03a100314081c186101500c180b40000c9803403d440e440403500314030f0040c50f030501600c00c2000402c403000303c607041000b014a55225042001480403010018890200708503801e0541000e10100b0080141c41c04a07581d034402c840300c50065103010540c10651405000310359025030020010804681c180003004010307030190700e045520203040c03010030140d1103c0c0c0b0700440c4941c444e501c85940707a18180d40007a2072400010a46403081e00100c8001c8001100d80040c1030308039225141c000740c0c560a01d922001c1302d1042d50400c4071004035003820068080b1003504002c1070365011803c64180c0503103e0316a00c0c10380d4016266140403d400d00b03414400c0b14440c40c3e0b100e910002403038800300413694980c148c0e4220002910490302145506540d103410078510440c0d404184802e1b01d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 191807868 1250 191806618 191806621
    0x7060506060a05190507050d0c0c1202010504090f0b13050417030c030a0f0e0a0f0c050102070b0a03020f130306050406060e060105090910090c0f030c08010f1206060b041e0e 76
    0xb00100140b080ea0b9038010032464138841541ca0912800a4a044560000c00c1750154164a81c5c00340c5103024119045500c0e1032000c0012442003d00002c1c4036050f54181c44250801d41004020030240284100c101503160340e07011003107143d5894008140344038462000009913400e080c18101c07640a0440000f1001800400601090300601c10840760300203911000011042500680d49014100c2103144032000d1150f5032440040c0040610100e10742071203080b541154665690059031141e0540c8038403202d07e9014005101603038043c1d00240801440b01c810203250a01d40202d00305040181d400a8030300a0340c59040200300921b601c201406009002180819494900e00091903445881400c5000e0504280890075040b159034001002e0011130000780602000b28200808889010704480e00003403d00d518001d01038001c6203064180e0350030000c2e001219081c9000d8407040441180c084a0702640d03031a0008142071500c02400141c91007440d58902170603003901d1264003001d01d401c141402d040060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 191809118 1250 191807868 191807887
    0x5010c02060a0302090a030204020c010b180408030417040b04030606051c020901050d020d0c03080316111507180b0c011505060a11120a0810090c0e01111002040801020706050606 78
    0x3002d8032203440482ca005030761411404045008101d00d50f1009420600103d0014040303001074214000304a81918044851100025003032510401980c014080d1441080420301141c025800341ea00049001002443d142da214004103840c0d0081c0d00a03550310b550b902d8180300c0b602d4202206ca0000b203007541c0624000055800282c8520300c10b209143c0f150f1142035078101192506001340d0a9039400c1092020a42c0e074070b042030b8005a1007111807a402000107100c42e24924000c0c4840c01c40c190404004105100c0b00b81550080d442020707100c20284442c0018105400c94040030b204007600440740c03502d0f00c0d50b440001d21425180d140c0daa0070f1580300c15102c00e20080d2118400d541160185113042a24070b280c6082d0796041040d121008000c001000030140f00a0f45c0102040d401800f6440d84640340380c1c1c2d11034103d8103c07410050604c00040c1070100e140050740c411040340c8400011501540c1e02d1801d0169802c0403039109504c504082e0350046000700500c0303c14419594024030603520686480c5204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 191810368 1250 191809118 191809129
    0x910050702011e020708030418050601170a1107060510050909030a081b040503070f030201121109040b0f040e0a120201110d0e070302060d0b040c0f050904050a090c0b0a080105010c02 80
    0x3c19403140048002182d10b4180708010903c024000441600c0c3e5640d254055580100d07150084080c00b0340c104408a4019403182040c440e41e80121000c00350540c95284a18000d408591207200c0c08410610805022542d54440c481c00740e0b024010400c003061420052001000b0000c001c5d00d59500180301012150b900700c02d80c3c0b50301c180d14040c03107203070501c01a41018941c041c2c1e0b00a140c241c40340000206003000480020307010359000341c07100343c540d402e54407100042c2c803914504000403490600490200d810035410800984000406d5140c2c8a0102000b08040302c450040d040e0040d80215090002d100c442000003041c3c0a07641300a00c010b4140c040419114031602a900089030b40d282e051585104c001c1c420075019540c000c04140e6550142040e68028005050009205a01e0100b0141250f8014034200e00a004140c0b9000c0c00e180b080e004201c010540207040304c4155444141402c0000c4030900108090140903840c070381c0f2200c00d524010080c20050b0000f40c148480f0700c20303c6015039a0f4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 191811618 1250 191810368 191810387
    0x606050f0702011404031b17010c0c1b080303071709030307080402010c050715031b03050907050105180916170903030f070201021b1f0902090a0905070803070602091005070201 77
    0x81c01c103040c44134000710140000f4841e5034009495200c2c05100c0d0513060504410400071241844e0101840202204d1440c0c22078500d620198086202040d4140020f580e514038825035182c2c65242d4041e56694240d11030a581c001c6a50700000740741d49110036461071500340d009401c9030b25131008500314a80b4890240c00c1074030150004e8188800c11000c041086400c001c480060300c04c5801202c00f00d68607000c040c000e02103c4040d039011280e031305c5443c10203a1280c0b00e42c41c820301e081d50003010210702e84801540e00390711054800100100040200d07500352201810180240e01800c8240b181c5004004000c2c0803000039442c0c00b03900314101c024840c11785000001d50740c10480c0a07110601c07070744401074160300900c40e48155518072094104541c40141c1c0214100424500c080c65031803014000a01c2d00d001c0301e800c45402540008850302140c80250303294014281640b10307c04449459880340011751450b042140215041130f000150340450317044c0700c3c0044640302110f00b04582409580d03400640030006 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 191812868 1250 191811618 191811623
    0x1506030606140712080612010e070311010f080601080c070501020c0601050a050904050d05030a0212070e0108070201020408031b0114010b072f041a10080916060912060609020414040606050f07 84
    0x7117002c0411103e595848920150180e034030001c0000e0710070705c1d540c59142e00d80e510083c1c0d2507481e15007903505e0650140c0051402283c0541d900c403a280e960760300658000d00041d002000781c80c0140982030004c0d000744010060020b140006000c0c640c9840108000b440058124078003070071a041c280030005400050840d0200824141142c890b9190b0303050000074010b5805040080d04900c2c10312440e80d80207864642d1280081e81c0e42455a680c51600781c0c242d00c59882401c0f400d620030440c0c501549104050f802d85003c800e4008559409040d48000c5482e81c00c0c0c1100c0210740c400a000c804010720740b03412100c1e4103540c21415903150305003224010450881c0e0307041d5010f20340f103000d401814208810f41507428a001040168080c3c0c15840013800e0b040c4c120b03441c0d4070a202c0c1003032491091010540c030b02c0c01c072220fa030341d0740071a14141712145a813001022030840c0d441340c0310a000300ba018842e00142c0f02401d0160030680d80207a80604200c252807042d840790050040c2006803900c400b0b000400c4865068 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 191814118 1250 191812868 191812877
    0x702030c0303390a0806030601080a140102040b130602070e040f020f1206130317010e06100201110f0705101103010b0c0f0f0307021008060a090f1506030606140712 72
    0x201015600403d244090764011a220300c81040349141c0c40b080005070083e002e06598051075a034455003415030f01d910a020b5040c00d0761140c98071100144003040151401c861400001d0b04042d41d895520301141c200c0c02c410310400043c617205004455040211030002c0401a10b0b803105030506032130b03200d2510f82d02c0038041d002d45c00790401d010046c0c4a8200c0d164850894000326441440d1120107146000d041a104400285010b000c07280415070150507503050350040300b10300304a40c845804020071000190000405d40d52502400d952000503c4080e104030140c0000d43d0ba9500414981030741400501e103130324041e051600840180620891043d6070560300701c20b04981d0794058004195262410300c0c8200e07241440361044103500640c02102603d512132007591810b402d50035001055484e50704c1210000d400c01800c0004100c9a60305800c240380e40c10f00b42c0e00020310380c02601d43c80d0301645216000f940100391a50010411182d0200b0843c20380d00ba80603000d030070032000c1d50700d0b80324101c0c0035101b100402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 191815368 1250 191814118 191814151
    0x4080306040f0e120d0b030304030b06010323090c04111201052101150f05010c0308070e0406030b090f0c01110a080a09050a090e060115080703110c0d080f0702030c0303 74
    0x140700341d0b1283d041903500d00300316440000755a4062115a1085524066407070030009840b401d41000029601a00d40c03001e9a00840c0e0b454100450040c0b00d80a026101100510081c14410301c0c4100d900c1e010355200e10241582c00400e00a11085c2d405080800700b02c00e10030040d2900490b0740c9400641951400c070792800060340b201007c003200c020b10300060f1849518048500600e072082a0480d41150302c0d1101030029103aa038801940c210524100140c04100718100040620b8464024642100c41c02400010119200d03181d650f03511a003214038030160b51190410110607641001640325440d82440d10f0160026480d0215444c0c1c454200d0007050300c0d0b00810b140c40c0c0540103d482c10050200580b80b25031150362192035101900040b84080b88600a103c0085609441800d2402c50041c1d240c80d4542c040e254050308400618070943c40740400b260074030450210150900c09a10150030319a1507004a0910400030621407002a104100355841001070300d040170400b209803903001c0c401e0f001560700e2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 191816618 1250 191815368 191815391
    0x6061008070c08190504090b06040e0f090a23070807260f01020f0d1a31050c040e090601080703140a02060a0c150603050319051605070614030408030604 67
    0x2039018612941240410304c0f204004c043d03501c04080d00486a912005022001116080c001644602d0040c1207440e02c0b00c030005586000345408164100341000111840480c5944902d84040c0449501900341800c6c0c690010754158104009009007407090301070504141f07006400b0002141c961909610007001c4001c03c1c0c001d007400c0c0300c014010140c40c0025940c400140780a4000d5900c8001c1d002c000616045880d0064500c00b100c2c03980c08a00600100c0e82c0e03403035141f414a103148050803601c942c2a003511100000c22142c1c0070315070065401d001d09584030f9084c0144c4000380000241401081d0740003a004014248000400c0412030b90001c02ea05824468410301509020707100034060b400c100005150555154080c0081c0c652074010100c01d201c2d1340c160f5900c10180d852030f00c005401544107001070441030a809120b06000b02803420704515103038281c03a01c1c03032102d503030604143c41603013000e40208480f0ba001144bd20003c034281c0c00740d51a6203015a211101404050710140c055a82d480c6031004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 191817868 1250 191816618 191816633
    0x1080d0e040204050d0b0613050705040b0912010903050409061719020117160e1215070201140405030a08010e0415051803120702190f300203070506061008070c 70
    0x2130040a00482d0364406103082200c01c601003a645540201c150101d41c3c51300064511035103002d43c40035a9598940b40c68240d40301500d401003501954080320485044a8450007403180b9165144079072142070726545006c41003801c07582030394841c18036003d1500340d05000541c003207144008c45000c0303122102d5003041400100d034444001c000e50b110b007003070381002d01c01090a5006421062003842c0c0d151004842c205092051304a82e221105c0e050354080c018145a010110105660000d0349100004015241c400c0b441c03c1103e00307031016601034000103000e109896002480c2c23405005000e600d011103080c15603554202851045079071180a960303c011a40c07042003454155000303800c501c1100c3c5c0380c140031a07032041d024000395641c2026125143e0460b8042125132480302119070054122540c1ca25540c0381d6580c5e4400085050400c00807842901c1c000c01c4e40301e8200c502130740302503000b151240400d203400c0d03180840c050442841020440f1001c0e02891f4080d1090b40e00285500d4908109446440c0030003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 191819118 1250 191817868 191817877
    0x80a0209040f140105150f01020303130302010b0d03051c051b03040203010f1a1908120d0b04150e01091506030f0f1b090905041205070809061305010305090601080d0e0402 75
    0x600001480541500143c015007103e80902c4c000700c818602807980720304004188034020000c81c00340e0003e0001610440e410041404424003d0001151124a05c00011207000b2112002c901282000c81ca0200ca04403c80c040000c4c4040d1034010880d5007040c1c01205005000d80351480701c90f03003001001504641b000c0d00010b00142c424072b81031121f00214003195108880c030201d42402041048021410000d0070420502242c1d00389000e418010100c3c4001091507004041051142d0b480301215071468540d8030401035901c1114088005c10741c101200840c034a139060303000782841750514240c0036030903002c617628104a03012820f00144080d402d030360500103448003403a0201d4482c40d1400a84805a2134200000b0260031651401d6180344c0350342c3c060342200d40030350300034207114110040050a60b00810003815800e0050413180c0c1400b2942c00081c6181d8049a440702081811020030000f95816000d0359030000d81e04400703002c2541c100381d08169204441c0c240c0b00104240c0050b1003002c1c0e00c495040301c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 191820368 1250 191819118 191819123
    0x519030507060305150f0906010e2101050709080c03030d05060117090f191a060d15062103022a03010516021204060c0f030908010e1c09080a0209040f 66
    0x4500c103540e1804050000c4c68210303111405400100800c01c031614000d00402c40098004180360550b4454900443d40d000f1070940e1103800c08060f2000700c001044100100031b02004941c00440d040c60400e00c001c000c6d420940c0b12000d00e610024905400356804001d80d00b2002d019400060150340c1c800040716182c3c941e08000d03406105080601032174520110b901c180e103581c210112070b0b0440c00a08101103043c85200c0103091b000210078401c3c100c82c501d495068201600034058052107500340c03540c0d00784103032101a509603681c1c0c0f98410084a0030910642c9074041000310301340069130300c2d6100a52a080711008141a06080e6900500e044c1c0c00800040c6407244050003c00003841c01c004c461100c04803c40c040d002500c20f0003040e06204d04850101e8003941d90940e10700250042c141c0d02d400448922040440900c090312001203200703402480f8921105801c0c0000703010400d00c0040c0c40403020f0328102c0c40c5080040580042c0310806000541e81c40301d0b503054542442d50350741c1d400d09107130002c2d400500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 191821618 1250 191820368 191820373
    0x50103020d18031709030901090e040c08100507080c0901023414030601090b1e010e0d1109010b1908090a0804030327050f01030515040c050a080901140105190305 71
    0x180b10034036900200d400c5031240702c0c00e0b0405142c1c0742c922105a03607000e040121800100905024041e450421018540051041801c4a0650344a1050034102038070b00707040740d00e407503500d20401c0f00003030340034190303a80103200c40e10014030742056440000c1d19410b82d810040c0c0401010303004802e444c81d2440011860404541480f6803d0b9221003007265200303c41003156200f071003848004184d0f01c081d449849440714009040d10074001d03d00d4010703003c4d03c52103800306060001c5850106102e441d440c03862550320b4462280c9050545030801081059803040c0c006420660040c042100d00340300032040c0301c484400c2da0a0240300c0d5070b11520352601d0400c01071001005038501090020030507810180c071000d601e402e486440c04600c01030450130700e03003451480380d203a000703004c00c914140700e5010703501440c2c0080d07422400d002184124008182540c284090050010704001810383d0500e9001e008190400c0d0b00000920102c0524a45080c01d150f060203014414080c0362008c803803200784012070030011a409012f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 191822868 1250 191821618 191821661
    0xa0f180b071707020f0105010f050d121b0807030f030506010909110405030a08120106030c120902060d1406100516230115090b040b031b060c0f011b1107050103020d 72
    0xf009480300f001c039801250544c20301d000403c08441003081c400c15520040c010448a0030191258403030201c0b606488800c1c4408201d0540da01d0600355843c2008901030048150fa07882c240c64000c3c0741714200c907a034200301840c21090240d030ba80d0120f204000c07128882004100502c010b20040024484c65002e80d0703252240a000030b00700000d005c09010344400c1040480d0301d613a0b8500b019030541340401303019400a0300d005500f4030a0820741d40b055114900242615003442050700c40c61301100c0340800b007001c00c4d407140c400708522490844c5078802340da00c2518185080103621504406844040d0000605c0350344507a091040d1540320320316041407009654001e02c07240141c03050041c1508c10500541c0b0500303041102004850909000b032000e00800500100110118000691000845054030541c00f0208220f03c40c050f0f54200241c0c1d4013108480000214621440413400c184807902c1614002e00c1080003541e04c1080c408a911000c41d0021300300541d8466070b44c01742c00c0080c03d40d001c45103041f550441 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 191824118 1250 191822868 191822881
    0x4020903031b0105013c050d0c050f010302040812030417071b090207120807020708030409050f0f0103020d080304020a090e030c0111090a03080d0603020603010b030a0f180b0717 78
    0x10010510002c1d2002000180d8880248449265484600d03002001001c5081480052002c82c0a5803540240c00142d50031134690001030035a000c0c590041e02c1800f400c01050016252100b01da60001100b420b0031490186002c00168641050071180e0702c040d000440080c00b8028200407600d002100d2510f941e0f0b80c0c10143c41c0c483c080040050503000155402000030403070910910803100c445405c400142d410044211048403080f000034405801c41c010600d000801400801c007074002781c10044800300e002d2404410030300300c0c14401000c200112030700d0001080581c0710503540b02411500881200c0e038950311800450100c04940e480a0402d0345800170a16003244048003410105c82c1040088c05040c141032a0401e69000711600b156111800241c00c00000300e0340e50040100313002d030a00c003295a5030780341c00090150308240d104074021100042003100010309440740d01c640302554402080300540341400007030000445500180702c075403200c003c00c18243c0102c45214a000c4030403800c0c4450712b00403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 191825368 1250 191824118 191824147
    0x2160c0f050609060d0509070e070e01031a060403080a18030c080f01090507180608030301090902011806020a0212030913230f040210180f031403070b040605060402090303 75
    0xe208000d03111519410100355403501000b2500d03082c3c00100454240403c0341841e0b0010310015100c46414840d10000007581040b901c01d81c1d2060580c1d407616202c55080c50000350644140384001042c40040109242607a603822042d101940e410441554441d0b00c5440151240d06032640c0d00070980040c5e07034000040207040801107060740e11800079503201408003511107003603030013000d80201b06802c000030521140071240a10480010903050218000742d81d1b2014904590081e00a0b40602ea150288a400c0d56007046400c0d116407020301c60f004501d850088000c0d1a6422180000d1007840c0343c1e10010700c40e01c7c01b00150b540020004100f0484034049201a800600c1540d0b080340702001c1040341b00c10310303034440c0c01c000d0301c91f070740101000d0380681d515420061040d911070712450901c2003402115850440340c40400c4094042600091150307400d6013468603540d82e804150f00c2d41980304101d000c0010307040000c02600558030000102d001d0311142d0008001c0e000b55000386c0d4141c403001c21400c000f092503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 191826618 1250 191825368 191825393
    0x90109080f03190305060a180914060609070f020c06090d0501021303020a0807030308130309080d090501080c09010c0f02060d020d0b0a060f02030316030b090705030a14070c150216 79
    0x83c0380c50400c140841180c03e40c20741e54215629a0303c440d981e0420030910308008941d00324407140c03e0000649a00603910b03004100b101141c4960241e02c080100a01410810421504164281402081a44100c80003503031a2a00c020242c013400e80031902e800980c461300904451254010025515481400035410041c6440e12007644030b541c8074580091614008071340300381625010307030703403801c0681d20b800001c80a094094403c0301000604200010031210078080110044c49954821601c1444e10000510441c0d0103000c80041000801031035005a030080024507003e0b92284070000c105149000044003401544014010f440c000602e40a000c01103501c01070124104803149007445498444c101c4031a001d0f080000c000d60700800200d10101201800d280c0160503d01d00032030454900c60111390318500c1a00c2d02008504040140000110240500c0407030b03559241c40e60040e80b810b420010821441a0409001c40303942c51980251200503404984045105008421441242c0e24055840160 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 191827868 1250 191826618 191826637
    0x207050615100c030503060d080c0703060c0306060905010e030f0d0c060e010b0a05060c0a060f0207050f0d090501051b0109140d0e0f100e09070503100611060103030302090109080f03 80
    0x20304510707500ca10716050100440c9100c40742d96140700b110140c0d070156896030010b046658440b80103400321001410032030060070380402c6000034140c034a19524040d42503035034042c000c00502d41010f5090040303640c001d80b080b085480901c2c6c108290800140440d0600301207482d060860f02a0307400c10031107a034105902611483c840d0f4801c03c041003d6540302d41c00c0365a01e160321980300d0b0000004001070719110300a4111071110301c05407584015156100c03000c86281c00303105040c880d0086110000c2c008284614492030100102900005404000003804541280949070501c000441c10110186042541811070a150002008804428101030806031250703e40311009102d001c04000c005071003071000320601080507040011140024003040301d01c021511001d0204030440720000340d1660f950300c1e082c3c000c1c0310700c2d25119500e0510300b00004181e0202c1d0010000e001c80e51003144400c0200080180c11240c061400680754010f040040310403444030350180311700b44510014222000d05c080000e140c40e09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 191829118 1250 191827868 191827891
    0x70507290316080702070e0906180f1e07050a030c0e0115020601091a0907030b040606030209010228121d04060b0a0c0305130b0408012d0c050d02070506 67
    0x4000360803a00d210449000400c503a200c4200640103015040c2d40760400d6090040d0380c1d8041d102c0030b850b01c170441e04032503c000550105060040b41104454003030000210240902004031290300c01070390f45c410280491841c1c072004820612015410700040f4050040100b45043c020f9036414110482405400707180d10350030300d510001131240812150b40392590740c40e07006801c143c0c0ca0b04000300020b02e4150020002d9403500c0407600c00981c0c401c1d4410348120540e0f1000140c0b0b14103903041c80219001e6410260070702d0f204015030380007a0380015055207000044182d00c0075040100e01d00400362091000000c0100d1006085a013041d0741001d400301d2003041c0036148104001c0600104419941c152003030700b010304020455880040d104207207040c0a0b60081c20006d11340481101d81c0f14884403164800c0c0c802d8240802c06101200080c014841042000c04840f0740402d003c400002c19001c5160380100c0460b561010480d000340194242c40f1b038031041c04011500c40c0002c0c106142c488808541d9641d60030f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 191830368 1250 191829118 191829179
    0x131e0602160c1406070201090605030406060306050703150806071d0a08011e051605040306023604060821030a0603120e010201054206040305030a08010609050609100302070507 77
    0x742412421781e08072540594901c5001807418006451650000c2c1043d6480c6443d0400840400c2136402641d0040e08a60b8001070080c00541403417000e00390320707080b80d45d05800040a00c403009a200c600c0c01c000c151024a10f80100703882c40c0011750030803460381c4000407550800380245607001000144052200c070710303103060003956600e074809205401050ba901000c5503040c0002d00c0481c0305907000c0c0c080c1859030078503480c0b00c5082d0360308404c1c0d8042c10540752607900c50080070415030b4200350141074010700c0041e00510300c502440107003044203044501099906040070002500c008130303c1d00319070021070700040850280004200c0081940c040642810b000d03600305400304000b414251030585100c0200d0001c1524901c03041c0111348008151000951790702001d01071240c0ca540d800000340010f51240c0700a503a0394618640141c104181680410240400c4007010401034840c14102c1d48112000c072045451544c00b17400580c0207010fa010b01902500c60980c01154a82d8503021070051841c4241100241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 191831618 1250 191830368 191830409
    0x906090f040f0b151c050a0f06030b181207060b0d151b0206040b24120307050f03040602030d0207060f140405060112080403110d080304050c09131e0602160c 69
    0x43c4150071582c40071008451014892103030325800385822100c7c05202040746c080709810707002641c0ca240c0050703403001d81030410300c203442c0c000c8550356501c2103011005d00000c0c1d81c5020380d01c9090003112005030001d42c40c0c589a0045a840c1801e40c410143d00400b1160415042003040000304101109040181442030003800d0310380c00017655602c40c582c06400c11441ea0748100916118411910804941c1160600e8044055551490f90043c10120301d00854407580e45003030152409070307040f0300b0500d9504200414403802d40e021040365282224a10056940c01c841d10b0b140c401445688890119140707400d00c00c1e1030305003404030250301aa010f002201e4550762514000a41400c0e1090b0003455040100030820010780000086425108020120740741c00803591210300c11079104803000c940907003000640001514111210f2078008495429411548003180d4692104c10103502240c900340d00c075040f41408102641c0c04844c19844107400c810600e490320314045000b05c0d00d82c003400a1000c480c940d01e240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 191832868 1250 191831618 191831659
    0x803090a0509190e01060b0a030906050711031912090305211515041707030302070e0f0106031503023c0d0b0c070803010e010612060602030906090f040f0b 68
    0x1c0c0c070010f40908100d40705081e0038030051054a001d840d01d5500c0e900c0020350584030002804200300c494901280c645914901041140c0006105509101920945806600001098581c6c14580e028024184d1303203064402d0b01d51111b6009070803501400c0c601504101a8402c01820058407450032030b1002e810300b1390868a1010341122580b81705640001780703a51510745070340b0b820454031010708401d2401d511401c41a90601c2000a011540d602c0240c3c101b04060b8100003c034010010b050203c1824102541034100c4400d040c401d000c10152510740c10b580410000d0768141c0110b5004041001464030f0400b001140c007800d030034002d034180081c51042c00c9240c0c10010403003040b0f0010a140c201d440c2540e0f4114443c41e0150881304000360030300c903680004980d000114040c119403414910103614001c0010980c441d0045070710442c0e0f06046082001d1900001640e80c42c9004445e441d484035060704c00300e000810703050110f541c094101000c0c50941019640b2030811940f05407402080100c00340c01e84035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 191834118 1250 191832868 191832871
    0xc06050a0f020106350102040e0105031902060a0e01020f061f082116060203091e0102091f05090a0b09040b0d150f0603050604150b0d020d0206030601030212010803090a0509 76
    0x4051800c0c0001144510700307981c0b0180d1700102c041120315960161100d50880e0410703004030410303c0c215001401030340b03420017054610001e000d200700451002980822480d001e44041142800211a00468680c0c0203000952181800740d0860b1241d1070440c1407903070f0441c444c0d05045003001030204042031248000c600301070504080c00e80e0050460b25080108495031082c9481c2c005925069050780018400b030004502403985100100220758285083c0d811004040101519aa20402106140d51241d0401c501505400c1103c2e2410a4411106031090300c128807280b0340c00b1030a044040380c16803100000d00720610096400704019006003040c8500c1c8429a20040d010044980c18200d072550b80340c0148404281b54070010800076643e0f580c0d9440c00b40c05503400c4030040640019a003180031f440c451420007410841d0001000c102030340121705070260106010b03004200010018929034002d4040754444900000e5041007903070354505c03254aa81013804c80910485061100050b1850110400d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 191835368 1250 191834118 191834129
    0x3050a060b04051306050d0f030e0924060903030705010e0f030406090308131a09031513030305041b030b01180203040b0105040f1d031c06080a030f020a0c06050a0f020106 75
    0x842c6400d052004201950446461a07102d10b51501e001284079228000740303a0750307180314040b00d400310030285c60060080b8001001d018003078028002009299440300c5891500044510030266040c06800082002c130f01c00c445020b50940f0000078080d0400c00158000e058820050094504c041c40b41108030380c03648200e2040c0c2d00000d0665405101003030183d0018103101c1d69281d52015582d0f602c2c1314509140013891a411400803010500440c1424207010f0040c0304515501306d0181844c0640000080520100300a41010b0341c0d00005070401c0b44100c01440812800240c403448a952481c0401700344909000321003040d103280c080100540340394001d80b03024551280b5010001c1e0300b8003007400020503201160035030450f16130710440021480221000c6c035800e0648045c40d80e50421003034941400310303500d51180816141240c03c03c03c409021410209550745850804080d00010360100d10342300f01018040d0a10075140301c0051300a4002006102c041c4203501c0e0001403032071001d8141e0032a80c01e4401c0c1c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 191836618 1250 191835368 191835389
    0x204050a0b010f0f030b0d080a1205010503071a040b03010803070519050a06091115040801181a040f08030907050f04020c0a12020111030112050111030702070e0a020f03040b060103050a06 82
    0x240345454084d00c0d540c0b8044d19540b80004140541000051040e01402020b84100c80c0024200031280e600240c0030300b621101e18002d0265514020200e5a202c4044c402e07807440301c00c41800c000d5130940f00e0040700d000b4224030640588950311071050580300d911008c01200c2d284605a88600c0c4281c444c15000f6505070080058181d0b001c4036224100904000c0c50121144d4214040280e1141c3d104c80004035481800702c0c02c1500c3d0b50034010420308559100604200c200000a510400903802140080d8001444025116181c649141c031050b94140400c0040c02d9207400310130020807000006046e41200c02c12030f0209007030509202400b04a22680c0748a1510f9008a2001004680601c4c1c22113a50801440002194554440f00080b2900280c121480d001541da001341300380f100034000c1c40080400f843d0074510314200803001940e5442144545401c144429000503c011008c0e810b03108000c9540100079a41e15080c60030881f6150b0403150540072074075010108003201414401c81c01540d000424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 191837868 1250 191836618 191836637
    0x110a03050306040f06090c08010e060102121801050405030a0311010c0e06091011010e0c0a0b1312020307050406120c0e10050904020a08070621020a05030a0e280204050a0b01 76
    0x602010301200004000d40c13607120500043c070141c292003044200b43c4540e031140d10fa03504001c0140c8100c5d80c0030304281c0c119805000788000030000d40086908030190f034402241c1c010655801a0f459000d00d5100c180c0c140200340d11101416000000900e0350690400200111944644d09490200007450402d030002c206024803100742c10040c440400c1c01d405804c2c1148000342c201010b500713462000c4441256600203404258840c102203c446002d4810f8120f03c50422006491a000c0b0550b07522405003d44055070300c0909546040c0500f0000d800702801c2401055111100030701204c8400d04110384001008000282c2e4100c0925003d00800030403a514210b14540f408000304400080d00c144e80c040640c03400050100000c2040e107000b006a5100c801d410310018402c841d88030b0304c2c00d414a120a0040250034082a4072008403030340002c540300e00280e240207056000d803030058071020020a1820480c00d000718206005040c488951080310284065a10600b0003000d0700c1511303500d540441c90008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 191839118 1250 191837868 191837881
    0x180803210402040902090c09040609181b12031e110c0f12030a0806180103020d0221010f0203010906060302040e0703050903120703050f0901090b0414030d09060c110a030503 76
    0x106103038101d03000038004940106142c001801602064503c01b6820300c0021380c100850800d401790400400c50340d042080780d184040f201d5540100381c10300040500d08000203a40c40912040d070590003400180303202c0d00c54104586405802d54420343c1405c4500031403201c08803041d134404c442690100004101405070b40a200c0306100704980641c18181e417100340d0010f49034150100f0030140400c08099511280507061410030710560400a551207400702e81d02d8801403000d82c8401e40d116051036419500c4001014007443e02c902061061080d00b8030b035500b400f104d070114240640140d41130b42c018400800145a441e072080c1c0492180b4803640200c3c03181c120000d142140260700c20703a03018050805507850601b410344403004aa00464030400480d540f1002d001d140d0b840d0400087c2e002070600000c10410720281c603040d4007540700400007000d06408152407007148a040c02a20100c009200c1306004007549072034400082c1100a08400c0056008982c1000400c000150312003240c3d09038503064595100d80e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 191840368 1250 191839118 191839177
    0x1b19030f021b0304060305071e0f050904181520090a0b130608011505070b040822051003020306150a05071e05010f0522050a02030d180803 61
    0x11018030310401e60a2101c40440720075070306040007800031203000d543d503207003010005011214043c1c0305208020030401041c0800d800e0800c544500422800c107443d56458011007140e403440b440580f1a0410304090413443e000c21031366144000248070f03c45404d4480d1101801108944102001e403642e0b02e00c00e00c85070355403850300c0c00900080001410750080700da111100c401003540100501c81c02d001c1d84060411946510815450141210142105094241642c018841d000d0317000c01401c408a41c101040402c074030f070402c80300382540313884c2401780541a000305c2049412043c42064020013103144003082e114802d00c00c4a20841000b4180c1103050804d00c080f076180e4103e1500401846401c00c102c1020a0b0702503183d4005140c4040c4003160b849a0b440c18a00756901e4890050310141094180008142d810184444003000c1e50721014812600b03090141c5403c40038000650180110f4950382145d03a880b2a0b0241681d11950070f012019a440381351a0307480c4101c440a500c0718011811500f41d45608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 191841618 1250 191840368 191840381
    0xc090307060c11040203040507060f03061203030213090f0e160510050705030408070b0d180c090e030d050a140906010b0a050c0f0d0f0e090f010323010e061b1903 71
    0x6140c10701441e00f12000890100da2054500395200c0d8040c0c842000140d92000203851401c4292070140704503071808100c00c2d11541c44000c000d060540115194904c0c083c682e4061b070003800100002d00c55a4042c3c4a10300050500c00c1a01f0001e006800c00d8400c0000361404c01800c58a02400e0600006041c80301101c0076040b44104640074001000009501e460401070f060207003100144013551468407080c10b100b00d840340749241d04900d0203c03000002158480480004580380340b8800f05c0d05054003074100b4198410020448001e0b03181c030060180c03a60441d441600301c2803213090f5184c46510350110b420b81d00c400034490000e40003805c0003807004031031185014222076541304003159580103003100d03100d060002040a0a00040007900104040380e03100d517103148406802d40c0c1d0201c9604015241000c0b04034140400762048070344082083c0b49100800304440150349100007001f00907002514261500c1303040d107041125030303401d0034a09081003411044403102224801c12420100032840c017034001e00b16 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 191842868 1250 191841618 191841623
    0x303020a1106340207261606090b0403050a06090212011406150405130e0a02090c031504020307051206011b0308091203010303091e0f08010b04050c090307060c 70
    0x1c0508441607000d80c2000100e010350901c09101c854003011481c1211040c40110f070102c907041036000d90015681c0c0100c0c80c0e4040d034000149600014000f0340f80d003560640403080140d0641b0940c0f46004001d051062003400703540c0391341d440380d05050340d41419140368096400042c1040d048220b00d900014256880407806520281024062003842c1c003030b003401c5440b590084884040e0f60010001c441c035001110100c00d08581e500641440d007000046580e54402c0b417030241c0c41c140d55050805005004001c6050304a40c018402261441d000140c00001e03002030f100b0b01d01d01d1a810720304260900e00350099911892641d80c1d502e00f410154a107155640c00040c2c241818886941410b070b070903928409040380700038065202c041c1c0e5410403440f81443d01c0c0c245820403080b54002d01c01480040c1d8030502210846408036454558070b550700188005140103580000384041c202ca00021b440340e0103403c4907600030303030860b42084180c0ea407032034410961044001e0254141c004403401d010b41400344d08200e01450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 191844118 1250 191842868 191842877
    0x30c120c0e0a0902100915050705011d03070c060801060f080a060302060d0b0f0405060307151806030c08061e04090807020607050f06091906020309210a02010b0405010506070303020a 80
    0x36581e41c20301d0001103007696403210454880e40003005504004c010340000584514180e03584600d402071701a4840390407506c030020042c0c005910300c20700c4825000005c001404080c0b4082c00d0528400390f03640e0f6030025a08036620001458000b5281d805140a5812a50030340c550001d1f503c0005411941c03c100200100002c40c0d40d00404405600c50601a11036008e00000000d19006400104602540c540e541c580c4954242403c11699850100d071110072143c1c0c0061541d6100c04e00c01083c1e031003444000030380000d030009190001d05a0780c035405ca021b008086464603030700c640b941c0f0140142c44100c9140c84042828070903810000e800d0035804044418001c5030b00e181080925400180303698800c95091390f8a40c080110840114410301030542c00c0182d000040445900721080044445c0034144003030444c03a070200015889000a119503405820704041c00c58112114425280f40b5401024131b1030010340ca01800800d6600342845020305071880101030034108100d070783d012006035005804620401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 191845368 1250 191844118 191844143
    0x120a05060c0a0e040e1203100e04030f09060e090601050d09230706020601060807031802060d0e06010902091318021305070f080402010e0d11060a170a06030c12 70
    0x1400a010560003400c185a07810b40c1d418103980c00922041c050341e2041e100b185001c0703a914401c400081c04800c1a040424941c0c1ca035a50400a041e4040e03142c1d101004110a6000300810954081d080c102c4105c1b40c3d4507000724082d00c070712040741e00345803513480e05400405200c08a009503010300040d0210f074000400104942e203a6a5900c2204850003000c914210703007400380200394141c14001100a01074a03c010008c0350714000b401009144080c2a5509040e0340d04c2a1007070700b041c07610f0240585034000d46806c5d83e4144031102d030401003650804c0d0000d06e000320400030903030352802e000721550b480b80200100031503140d483d600d0008200d00200c002c802001c80700c040c2c0058031800340c40f1100d6031140400040b06d1610b00006458805401c0740c2e4030030454600104001070303810581c030562072a003d850794004c2140310f01c3c100070000308843d02c141c0e0006011070a0108994041c10907040420001d0180000703880310300554040d140c0d1400000c020483c62641840070304565012000068010000705007817 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 191846618 1250 191845368 191845373
    0x150302030c121606020307060c0e0603010b070602070812060906091905191e0b101e090b0d020703110c03120c0c04060f0e060d080f0a050705030d060608010605030c0306120a 76
    0x428510390044e005078001091240c00d0100c1c5100e10011090b290801e01003215140000841612050044003c00000410a0024460b1940c15180780750b0344001c55aa8680c189142e00d16164000c07158944203144400c0080d03400c0c04d0200e001e43c064101d80301a1680215020818006084010540d0006094030100c021507410917019040501d100f1000340141e020046080300f00791088903410b50300840155160384c2e50390343d11880800e0f0340c1d0002e084041e5644200d110407079201610340c0c0100c60680303022074981c3e8103401f179500500b0f03040d21944a03619028030483d0381540769524014002c0d8540c2005442005610a000040400f0079800c800c1e92900030840001031b08480054200c3c1200b4031940d04e0a020031120b0001c0c40d601302004851142c5200719a65407070710144508540c8840042c000303d40119124001d10a41d89150340c41415240c9401d01104208001c080324801c50000800c4203000040d418000d0381103030f0050101365501403442e40c41c0414841030755542c60384102d60b4130901e0001d201 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 191847868 1250 191846618 191846653
    0xd08070e03011b0c051c1b02190303030203090c010839070507030303050f0402130c0201090c03050102130506071e0c03020907080702070f060206220510020d150302030c12 75
    0x148803040380c584c3c1c1040000c82c00d000b840d0480c0a5880b810102050750705920417030304500c5080086030340c00d01840e410340803803000c200c112650022a50200442010100416404d600658403501e1180c04a64440d910540115802281680d461502554030005007030300c041024820424865200e6260350001c05146140b505c65105450586154100320418003c15915024964000700a11881c0c601070030b023600041d60000b005403400c40c3c515690212189054001c0d0040e008094000d0400010540c3e00d04145000c0d60107400400300f1410560400700b50b80c80c001060794074040e004491032480d943c210051200b202160401941c03021020035001006031b8413030142611401290341c07080c2ea6030403c400c000c6e14024803034001e0182070402000612002d9070008520354024025403003c91000c982059600e44070403004400341441c016202803600c040e01540080c440349030301400401250300039040803200d00015010095068019100035102403400041c199810180c031019078841c417040801c4081e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 191849118 1250 191847868 191847911
    0x102071a0c090a120605100e0601210e0106080d03020f0f0d0912020109060506030304270e01020a09061701050904080c010b03070621060305060f0711060f0105120d08070e0301 77
    0xd0031300821000a41000324502030580c00c4000501c4114070716051410900f15080000d1815040144904200d2817450014003036400c44100c1143c10030502a80300b0002d4007a01050045110034030614502a41183c441d108840314800000ca5803803c00703124401000140d4030500f0043c103000d0300e4000080101b1413a04d5102a02202a0000141075130307103280070340655a0080c0b4440c801d40007071004015640c1184c1d820109848a0485e42045002103408180100360744150f480e0150320114156298980080780c4a050711141d440d420142031824140038003080c024081c098200d290340c00070030700103a902030145c92010680f10000c240d440c001e80110380341602a40c0088006068401c8036030840590b02c5102c0c1e12000f100314240152070464541a5603088003410f00d81e0140c0302039000818280c030035213a0400300c0c1c11136010303a15030303051804010914481c03e001e1284141401c0801c4604560001071003421094a91210459a610368806031503245a182d07019405540b13590684204407240004107 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 191850368 1250 191849118 191849129
    0x40b0a0302030906070215060d020a030f0c30140c120c01120e0705101b03030f0b0105070309030308060a08190303110301080a0b0601200601170102071a0c090a 70
    0x16102e203070034072051303240207800340140d015904004200000000302400142c1c1c8070405803800c001100307039440400c40f0f0a8580d8006001d800d0307041c444038200080190800101c0d80b0100c08148601000000e503401d451201d071640600f4400800c03e080001c6001d500c001c50350101200307840200009001082062181e1481d03d410381c0c10161000c1d11568003e01240324440881c4410407035240010282d96035100c2602420b03105240303c41d08022000c1c130840b100c8070228100000712282c44c1d0b007440e0140c041c01c0c04040400c2000d0801000c43e40703551060041d0f40d0360f950035549454506155880c2aa1400b4018000d00c2e084031f424100450445070801030481180f90450104420b041281001411134903446181c21211108200410040c10000382e03081d40141c10064241c0551180f0005841480642c0e420700845054a600c449040c000414800c2c100c1e07012019880b801b00b80ba10b4804e08078450701000900710b20104111240315200c0c50410b6030f000c0940041540b134090640001601184c2c582d001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 191851618 1250 191850368 191850371
    0x5121e0a0f0621080c0109080712020c012d1103040803070c0f080601092a0c052b050318030c06010f09020306010c0f06062409140303031308040b0a03 66
    0x91140d40e14491107001c0c01032221244615445204042d028000f240800b0050140c01c40032484507840e560a50100420980c010405940c0703180c2440c1c0010380b1404103100d6405405071748160099540110355200b0342000c032403c1c20b40c1c21780c011102403a0b4040b260b1418010000d1080001014900800c01030010300f00c1e9030b0045840d021b5034644690782900540081911417071340401080141030004100c0d040d500d1149000c11160320480340501081c489200c684542c10b603010b40070115940104030162601c0c015400e460b01c2c00880e070b06e8000c00c1c22041c80c49007200120b104818501511800146422000440c000450045810700c440e00d140c2050003141c001d904061b00400509201c1a45140201141007096017949000d00010b000441c0341c81c80a08030361700d01c046a008100c015444074019040c0e221551502502c03502c0c0d03280c0b07000154000400400c11082000c1048800c8000d80b00641c44002c00035072031551076200301c01c074030421140100d0b1a030344d0a00000c0f81c00ba036030750080d001d4103c0d0340d40c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 191852868 1250 191851618 191851631
    0x206030a060311060f0f0d15090c120516110c09070818070311011214010602030a0f020c031c0512010605031e160e0609090a020c0607090605121e0a 65
    0xd15000340d0b120807502a04c211010000701c000c1002e84c0d81550903188642c51665220020700c84001c020b00407000101449180918010070004210740c4180c00340d20190795141c083c0e50302d102a907003c50b00c00392103203020395440300b5080e00120300c200440395440b4500d000b61101294590041100214152001c0c40441c041c0d50401c41840750050070302c2a0031a00500034541980385071101d0404902e01e01cac00c1810085150107078400718019411a401901c01c40007050115a5074810080d00c0340c0200d404600001c1c401d1a180000510008040400e80d02c0180589810003003450303072140a940705800e0f001841014030800151400c404030903402800a0f4036002d55070b00d003e040851030984021148016200400203000b03080131401d4003450301102504244108100580c0052118050800001d60154444003085140d40d0203030080c0003644094012140c503600d400a00303540800303450152400281060016060825916400980009251001140018203014901b2030700c00212142401b0945402 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 191854118 1250 191852868 191852873
    0x301020d0c0e03060106050304031b02180103060510030503162414010e16030f0608070303030f0e0d020a0f0303090b010b03090d090b090d06020c01050f0a05240d03020a0206030a0603 80
    0x2c5030000789000c210050000e030b40c10140003400b01c0c00050000341c200a507515030f0020900e09e807886c552840360000c00804c1e024035010806d401000090200320b94490070311020500044039100b04405803030b40300003e5400c200c0a810715242e030310000d90307003600c4000c010035982001d1403184014049048894001107031004070240003070700802041e40007141e8041c01500300300c0500c249900c4e200104861b403501192031801084000b018111942294109015101002082642560202640d80d40340c2c81d0a03c0081c1100214035200c0c3d250786941d4016030041c1c02024001031000d010780180510078100000e4020007a19002c840000c260042007120a0000038071010801c00c01112000030043d1074507850042c20040824203500598024501810032580c0913010881140c0503980030400c0e802c020070642c50903204d01000c03400150380607403025242401003030729980b1110001620004140010b03505240c40b60910820100c00c1030306904500076022844016030b9040015405041200d201144140c00d50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 191855368 1250 191854118 191854127
    0x6130306110304120c030e0a090f1109010c0312090803010603093e010c150501260d0c0f0605150102070905090a080a120204031a07020d0e04020a0c020301020d0c 71
    0x2081d224501000074400c1100054226401090b0b011242c6890564001645015550400e0341c203170245c0e005044810104104075240e00c0002d15a181081c107009035020388007a60102d104ea100c2c400e001500500c0d000740400d0107403924001c5000060000145078449807103000141c1c00a800a50010f0b4135410240107100d0070006007682401c86e4400c01c0c4030340407094411550507107081110130183c1038003080c210ac0d50780078100101c0740e00d0f001955038591600071180140182024014003506000880c2c0342c401c1c10908001850598505800518540b032200f0780507580e401a104084500b0544005101d0009440d40526401203502c0c44c20886d5204100c80060304200c0309400207046949480308000d80c0050014507989003031342025020b44c0d1040007420898000340c011039048181800000e0000801140040c481c0c3d840b01080b00342e0340c05c5c1e141d801003242c40b140c0c4064440d000402442c206019460268000c0c1449842814000e004503d00d6002c41d003603802145620302ca480d65024581540c5811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 191856618 1250 191855368 191855381
    0xe03090405070503131502070c09050601090f03150911060711120307230c0a0e0901150605030604110d0f0501090516051c27120f050405040e03070206130306 69
    0x180c14070310300314501030501e4201c40d49420405004900c0d40b0781b0086a45034194110740ba41d9030801c0f0090803081c0c07222103100140005403011800241c0b2441d0029007045800328810699a00c580c00802c640b03070000054000c0c001c005802d40d10181c144090a030a03075a0b400042c86001d00c140c00d4036110f110100c0030055903600c0240517505a800403c8900c0005184402a010001007a0710384001180003000c240e181c845205042d9420200e050000706040000f2000c4511500000c3e0003400006050f1158000700b0000d40f25003004a1000d02c00304a8911381508a80d4ad01550300840605080c42d09540c1c00507600c0744118035494a5482e030060002661a00940e944945a07074901e00b01c1d03260081004000b481140880030040705540c1800d01d00324426004205040354040c2d42c0c101510900600030219500100308840c40b00c0c1c095440302045000758075940c0f69800c1600c8203428145000e050202800c00c010741c50940b40003c020b64001070791003601500703048602031000d4414504502d08081210394 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 191857868 1250 191856618 191856631
    0x180f010b040501090614040b040b07150b0f270c04210b070c050703050742050a021903030e06011d0a0c020c0301050406050603161d0603030c010e03090405 68
    0x400c0105002c6030740c00041c0030b011601185060b90038035060066641e001d01032500184101b900002e0002200200741c40036140c020300030540509081801c69041007141c2c80c480322150820786014040f8410b01d040819540e00000310601184085a0000c6c0d83d00012400c0320200c520300000308040c4030a942113096030b488110304080717105500d0388035101d5489500d07006109000300400101c560b1b04109041c815075000703550160459000c66115034104c1c42d41c548400c5030304c5a6401c02a03000e81c09003500d440340c0140c1117040c0c0c800310303c0340310700c04088400d54440c89a032000c0d0300c00e8912660b0307110600c00319108041d019981c00a2141035500301d103400c0c101c0607404a80d1040c5004540e000503500101c6403504000081c0c40080c8102c4441c1c4181d003002d079084456039043d46004104010700c480c540009101d0407046060700d40010840c82c201070440c03444e00801000c060b0658900003d0002d0454085d007202000302101d04025100a0090a480280a8103021900085110311b007030b003054002c8907040352 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 191859118 1250 191857868 191857889
    0xc060405072607090234020f0613050f0103200903060c03090d0c021206040b090d1d0d0201090f08030a09050108060310050709050d11100201050906070c020a05180f01 73
    0x6040018265407558980100d5103407640c002004441e0218451111b40760039010340d602955440702c4851012030300001c44040c2d005501044400d190b500c8d0103811555114012000760700d0850800c0140841220011016814503036034020800c0251181c410184006d1400b005480d40c8080c00740c00e141c2071101c0900b002c03103643c0040c03050013210840403898a00802c1c0c140b80000394074541d400011040503035494881658011f840600044c020901440c2e8464075454088540380140b480e81190f4003400c4040c10500490740e01001d10080c5482c8034506209070052402040440d02d03000c403840b00c402e869010703c00320b52000595000301508001c24400800007428001a50f03e03003400842d48804e203002440c1100e5035a42d00180b011401220580007401010f415070354540682d1500074202c6004440c1b0341d1142007100c90400416105000d458820145d25002e02125180c000c0146c89075410800c0803640910b00c00c2011030b10351a54105400010819140641c030ba0818942c203e038482c3c03040e00302c1d9a144 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 191860368 1250 191859118 191859179
    0x203150103020310170111030901050601021204151413060f08010801141602161203030609020304110607050f010c05180d0206040605090307030602073807050d020c06040507 76
    0x16080d920300c0200da941044005c0015010300070745004200340a1841c08200003c42481b5800c6c5c415881281302d0300b002e808413890b2482d0b84226817030318004d0348910240e0b07200015010009c103120b8101c986004842d910144e04100030720880800340e00458220100203486141c0b030b001d403036610080103801010408002c0185c6451800e032602242001441214510702a10485650502c2005925a01c1034181d031040030780d9072100052000010700e10350641c0064186900443c09038494422607010b60360004440241840b03480604c00c89401c42e94064401d40510404040c03810028040d000364070440c1d95030196034110048101c1d040b20b40c0c421040c2d028074480c0c40740d40c00584a40023141c0940c1c801c2e080c91601c4842c2140004d15241c0980c00060407075001158a104024140c140701c04040e019591074070108140806180e4005075000e0321408040010340480e00a600520081c4409c80d5480ea0162400345442281440c1900075901201d00e5406007008000201000008816030950501201d501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 191861618 1250 191860368 191860381
    0xb061f02030304020603132004061a1b0708011401090507020c01020c0f0f0d0515010501081303030f0230070203131e080708010605010305060f060a0f030b03010f02031501030203 78
    0x120b00004100038041c0100202103000000c2110065402c0350307000c0913080743d1410030341c141c3c2901c0b12031411290081303050043c0458400b080301040383c050581132552b941000000169500c0205901d542d400484c020b8841c040341e54082030007200e0150f480250b00c02c1655142900f030104440d0000c110008540100d400c42d145607a001ca01b11700740034011203003110524502c0000a04101c090100c0f568040c1801802004015000c10900c46101d4080030301c240aa0361000155410001200c0d5030b0f850259a0b903595000a0003540321044406003080010b0501d40882c540c4100395082200e14201a000e201c0c4a8004140800714a54408130b45d101031030400706d24240e0070b1500141805202c90350340713402200201c0d0800000d0540c0042ca01a4200c44102d6a10b140060003000d86000f074034002420003001a0081c104039141d8119050050302c114540f40040e13104441204052181508060702d80c0a4074641d56400d010f2a084046501d10050352414410300d0071840e02c0848543d54103050061037005071 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 191862868 1250 191861618 191861623
    0x40b030103050714010c02121e0a0c06080402010c03030903020709020301120507060518090613110d05010e0f0f102303011a0a12080708041202280b0705011401030b061f02 75
    0x1b007594152400c4070249400601142031404102c0701c5080c9041d544401290444005000b07502c0900034034030302006a85502046400040894001e40400d40550800c00001e1180e80302c60390540c02071040c1c03100551186101d03402e980c402c1e0304c91490b24402c143c203001030010074880d6400428441c00d00900e00907807104012034560102100a01c41e1114500103400e5450310b218200b00f00e02c18280c1046400c18507a64030144da00040c03521403c0528000001c00c2404440741250702658206001100791b540d8144200c40001d0014403201c9a1306602100003070301d0340c607085a41c2000c4801d0541c2c084040f0b10034249070031641c603107050703010f01e0180c5c80c84822580c4403030003050142c450201400c0100079103400d100b0011301c12041c00800040e000900010f40400c134041c4500700601c203c4c2e54914070320750240b4101162813918400c240c000d041c80c008201005545004040e11072003800003090055010980070f8030010260710503074031500756004001d0701b4070f01540364405102140000c2c1c10f4810000c2c4000b903 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 191864118 1250 191862868 191862887
    0xb01031a090f063702041503060b090402071b0f3305070314070503030109180c050103050603100207110316060903020d0f0b1003053d11040b03010305071401 69
    0xc0c00d800011404034480c08960582546404500443c44c0c89044210741c4480294094400c10024501c0070851003400e610030301900040b02c5450240c14104005001004000e50000d001120800d88804810400e01e0246901d68000e107924000080c00f285010751184168002c00c2d2101030038045c4d000c000030200041c0c0f24580180311645840743d2100801d107800e40ba103201418441c12100301c01700d072460400600100850681e44400400d0141513001a03101490340c1d01804010013883d003608041c002c0f54826032000754800001400c80c1c10211a0300040310403030388800340c26119a0080311600c52039003010440c0d00c15401800d01c5a070b40c543e2800c000100b9840c018040284554040001380003170100c241c00c40034200d41c004910040c1800d00b078a1604031100544022102401a42d10390218081e2000c1c6010000300d451505401540586014641400183c641c241e049581e032401c140d003548079a8084c001410201240e03598075411401c2c400d08d041503a601034046221401580340590740d01caa590f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 191865368 1250 191864118 191864131
    0x1090801140f090304051e040b0d0812100909060207020a0b0a0503160203130801090b070e03100f0e0105040507080c030102180405090c03010e0705040f0605010c080f070b01031a090f06 81
    0x2c01c094540c501040e007148150760001c2e40c015070003940c488680380b104050074503c00003140c08104c060400d8003030100607520348d00040c015020620000703000000d590105540241e4010000e0807664a50b4000d90844a5103d0f095a45650200300c081c21410300b45524006028504416404e26901c2c040c02099440020405c0d11000c81c03043c1e088240742e00070003c0e214094940d4110500d0b503074440c00710307a000700034110090f81c0c0f0300d20507004038a0302030094003020040e9070050040c1c0201c0d4982c507c40300c064842a004507008a6031002446c14100c0d0a00c51a03004600ca02d000d058001d20309110030307140c00e001c40309451081c1d104201c4c2c1c10000e00d0310054084254000d40b80425250ba500c0009400e120518065903015420132120b010301d22000b00e048020744808580c100300b1b480c010100b0302c04891460040c180032800e0f0800900c0480d403080040c140e49000740c9030003450000c183d40c401040300d0342a0300840e118034039441c1ca50b54000900340c009611101046c01040c84405203283d0a45d10702d0b0240c0711 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 191866618 1250 191865368 191865391
    0x140402031e01090b16021903090902160807050102040815060a05010e130f06180b03062806060302091203031b0c070e01150e06161e05010504030309020109080114 71
    0x800440d00801e41101c480c413074000046059a00e08050740004110354040080014040e4001044003a000c0c00c000700e10f6030b60141d8401103020300341004c050096001d43c40c0840103131000071a82000070010402062080e206900160311030340740480305881c2c00c15101b005030380e52010108103c100d0b2280e2094500320382091806022080452004c60005841d51045035005420701c20300c0d00d0b4207110b81c1c05c800304580c81d007007039812211043d01590b01199081070403d45e154101d01c0c041681151406030b19a0040c546800e180c1c2900e0307626100108940c0d0661090300400c1d004100540d041c030340b010300c440c41182c603880a035140d0b00d00000d00b50b041074111500140b01c81804550450313000c074104005000342006200d0050f00356140d800e51001c5440c065202000640c9107104003525081c080c4c01e0f1386c0c00045d10120260b16074480d030340701806090007010b10760190581080203404610700b4010240214003c6c1ca00288113281c0e40001808070809400007690342c0c5c1001002035001940705400c81e40030090540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 191867868 1250 191866618 191866663
    0xe041109040c2c1804110a05030d050712020c030d080402030610120201030e010f181403070506010e0a0f060603140f0712110405041409010606080106120b0f031009050114040203 78
    0xa64084d401801c2c560820940c90104810000000c038484040e0350300b2185250826500c40c00c040e510100341030b024001600510095001801d40c0c3d14080000745180142d662503210f00c000b09140030328000c1010300017415101840251b08040c801c1a8011201255441140d811b010512480781982c9400074105950380c44040d1405a0a5014038044008808103000410780703044c14200c0c40a0508040d5041102026840035145002003214040d580c00400740c08aa0710b800210f2800041c014100c00c0c25544070356868107440c078079120307007005000d1030b031030008501685c90640180b001c4c000f00b181c4001d84012007400f040b00e402c007440503004445080e0114144003154061981809036a001c5d50700a41046000e010b0818541e002d5031050304008004c000155450000722201502072040c900400c0018a00741030090380b503084101805d80103481890f0410180d00070034940889184c02c43c5880c0c2e0340303030040410084280280c00c000e0604014071543e43c14590000703515000c88510f0204100c10004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 191869118 1250 191867868 191867957
    0x3f0919090501090c0e0f100c03110d1707020a11150c012a0503040c360c03060b07020a060c2301050403030c110604080a0e041109040c 59
    0x10515400350a0380c410621455039280700080c05003030100d8a01000c6001503850304020f0401300629000d03110010941040e40d1450102034404502e5010240c00f04010303080011030140d0100400688145165100c04092240d86491041c0310000740c155000c54022004150100320301c400c45030342c840401ca540701403203d4581d01c05200d80c481c41d0170045c2c041d400c0c00050b800c000000c0c5503006085800900800425111b44011500c130b210880d4010004e400100081c44030202d164040c079491441c125000700307494001c100000c080140440100100c81d11803005842c0142d060142100520a41700c181e07003000c0280e400505d00655038010341d41040b91100c545428841c415040048441c2a501603080c442c041500850180c542218240d001c64184a60f15034520300c181600801444488041c00c00ca484540c1c0351201c07603221607084410451400340c226801c0e03440b8451a004070320103d6841e99a201c0c6203003400240c903000d101c0d060078000401000185500b2000d5000c000300001850f03048466040c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 191870368 1250 191869118 191869159
    0x206090a110d020d0b06040b01090e0417090618010e0402121b27010801150f12020912060402030d0f140a0311121b031e090f3f09 57
    0x8a4081e51007520300c204d103414000350300030890048400761801e0140d8516040156241c511520131540740111400009000c2a4080021b081c450340350042c10f03240640c61400a8040d402008260031592141440d59009607000400c41c2c0d9130707e80076642541469661882d07100c001070010105440600880c02c070202d41a682d0007242c4800c0c01000c1d803520403000000c8410002c00c580c002da02d010940d82000031030b122052040001416004d9607808800984080080f50009000d44a203500c1c25000d1003c4038565490308141c4a00b411901e005003e2480d10740101480c01421049131014804e18400003030820342d0140d080c00002c2000441a699058901c00c1140201012140c442c07000d48081424600c003040450018005e401c2038042112101c02101d5440d07440c8010b40f50380c2030b02c91201c14a522100140d1a00e40d61042007501612a10990144400d040c00e40c0d00400303148030210003012200e2006020b0782000c05441007044858160001d8030011118414688268440d00300403003002c4c6420f04070b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 191871618 1250 191870368 191870389
    0x105090312061f020f012a05090a050901090f050a140601050f040b0f04090c090b16140706020a030207080c010906120f0c030605031203100306020a020304030f1a070206090a11 77
    0x100040c294603505211402900e1704804a07001589501f8180340111444801d00c0403032000320090302100c444285030000350f41c0c2e41c4c001003400c0c1e0071101184000403e5a0740c054400e008004c0040e02181100c1308081200031190700512a4064604e81804d0300343c02070b0030350310007a444402801d01c1a500d041c08900c241440c002c0380e014590b07241000403030a00351400400640221184c0000510401d042603c0989140d040d6024004414500b400031031030900c1c0b1181c04c6030750280561594080e00500d152810b05201c00f6400000c0580d00c411191420140d041198034003d040c080003600b0107000500008101c0c03642407103100100308041001280c469110381c4001003204242c0d2040102c261354101c040c02130300141c46814480d028041c1c21203112100141183d1040144405002403642550307141c81c02500922502e5007117101c2400301100044110500c40f1526025803a0701f005041c414052205000000f400d000854010b0801e000140c000042c00d9503000303911545014500c10045c2c04508044070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 191872868 1250 191871618 191871649
    0x912120606072d020a0803031b03130215041a0708120a020d05040c05100203092d0901030b1902070203030a0c03031b120c03051905070306031401020306010e03010509031206 76
    0x2d4424000d000b1401d940155040f031482694104142550707110f40c1500e9000442c0c1d01d01664150311104d154031004071001315881000b0181c0402c01043c6600401e040c0e015026801001900004081c0180c01c0c3c81e6850030440302e50050903034503212480e691001c0c0b9020740314080c0300c1000d50401080c2d2010f41078041c0c0340341c100d00c1442000f0602d00341c10450301001c0c3c1d03803040c10700034110840a100407038404012545d008002a0000700b24100455150381054071000b82c249080030b1a2410304400d0340c40f1041d090085008942e410800d0928403000707a000c4540a5108680510400c20040140c03004010340b1804040c5040c0301e0480712040c03c040d0050008000051030038500202c040540a0300105402185017280e0000c01007031501040039400c9441c141c07107030b40c44014000003040000140c0d410840c1d0000c141c1c500450180c0c0d0342da5940740150007c0c1d464941a035000b100704013455a01078104d83c84200105c00034491400d20701d098688a00c9802484210400c10318000750458030f031722000316070080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 191874118 1250 191872868 191872913
    0x151602100305040b060603100303050c1e2103010303090501030207051e1005090a0308010e07090b180907020c01050d0b03010b030610051903030206010e0601022103091212060607 78
    0x560810001c00501089030202e51004401c0046940c504001d01900e10807a00351801c02c4481e03007035031230668064120465902d510f20850b0040350f0b042048488004070a06d01c40d00520341d880041031180e0301c031145181d0010301e052080c401040801d80c40140c0904490081c2401070341c0e01014103040d42002132600c05404805101403031034000020020b040030a642002004001940f00c030503403076884240e09040070300041c0301c410041c00124080d101d5a50803010b24180103103425035607894a80305801c03601c2166503410200194103584d051a50f545640090548082c001c004180b1001801e075000d802a031102081d40c4d010030320f18a072030035406201c0c0d00c1801000c807103261504c0b0061078650300c20347c01040d0042804000d9081303982030031003511040ea503150b009480f45d81c0c00c10035610720f8a2401040241140301300c2c22603289080200b00c01d0307100c00d0740c1d0341c003000c0c0d491404140180c41c180003020030480d545000c0141095420f04074007070381d400c603d0480c0c400e503640034642002d88016044191040302035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 191875368 1250 191874118 191874139
    0x8090c13090501090b0114060c0c0402090a09060308070c080d020607031a0307090504050d052106010c0f030c120c11060c03040e090705030105010b0a080610110a06020d060f05151602 80
    0x17000c03151a0504031098454400c0c0c18421711010b22542d8025a41302561036444250040c441349001e402800d220f01c0e014021491099881e00200151403c80d072041d40e12001c000348241c00d218490046c1c00c081c0070460010484600100402560390000404000030156525012200380740855201070794402c0040441d140c960325a40440c0003480140ca084695200b0f15194050440c0500c0030340e1403e100254080840900390050455013450040c140c43c100201d8006c108009060700c0309407000c6070700907505c41c24104001d1402d202d003158106422010300050400d94000140038801c4c0ca0302c1c05400740c420680310343d8071031000c1c1d03d1030040340c00c405002002c40d410012030640003d101000c1784d038110020711151340d0b940d40300003030740c0314401d030b81000900f00320006607090a140d01c480082d01d207246801324114401c061100e00303000807118111007803034001070449440c084600070007002d49841100043c8051400340040c80e08051140810340c00c18000c01c0314100b41c00c003981c40d1100e00360041c0010204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 191876618 1250 191875368 191875373
    0xf0a03030f111e1606020609030301060e180a0903030501060206090a06020711030a0f051b060f0c070512030a021c020604031404180b040c0305040b010b090402190c1208090c1309050109 81
    0x889010904544c000f10b03459000240803803000510364041d41c0483c01540c0b540c0d00340002110340d40c408800c040d821002e02406449028030350500d2a03c1400e07215000a07402541d031a00a09031441a80300c801154003001c00e1005000300800d0303508500c0d0f4001c0b00182c3d108142d1400000c103d00300c41d06250301d401440d0021003844112084100c100d44680e0a90346040c4c21a440c4404000d036032229650400c0f02800b81d14170001c09600140664282d540844034440d58490009002d1914845000d40c607800100d0340d51031041e0104885c50f07a2400c100c00c0d0103580341c1220002580c4a600400140400c003c0110380c0701d400c0d090400710750161078445048000034401180f001d002d4880024228000c920700041d01c01e00720b10074812103015a0740100e481d4126480c3c0307039280c80c442e00008482988990300f0032022041601c45907400382c0c2d108035030301c90b00012045424100058080502c01070705120f0540c080160751000420035000000d41201d00c078940700d20b10803812008010313843c0024010740c600b80c807a409 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 191877868 1250 191876618 191876623
    0x60503010e01091a010c06020904060b130503030708090d140709140a020a140f0405130b0f060c030316211505040c050301050f010c02030d0c020f0a03030f111e 70
    0x141c0d80c841c0074660841c1d80c1d900d80c20f8210341e0802070040040c90045a102d4140d03100b10700903031b0141e02580c005030503e044a00041c003201d40745e034040301e40c541001807941c1900c0c52174038080000340012806107080c1002e540b0b80c910184503080c0243d200342c2905801c4001c0001c4405000304c202d15074021258030f6500e8030100c100410264014483e00403412001035100c03e0203008071903204082c2d41d15018142941500000d140c0c203c0c092150804205200110352521450400803007202d00c00408909506140140580280e000c10090301078501000448013514000046a81040126805107080c801402003140c1040200c00c3d03c40c0e84100c0003910310490340040e00980070305040c0e149095515559442000111284025070740040341c4107100410903440c0041c41c41c4030550041c1000407059400c1d90000f0f086c8410008020f010032038540e500819070034540c241c404891416200c42000358215103019110383c42d402d08410070048401c8483d0040842440b00343c1790802c190000c40c5085c1582006280c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 191879118 1250 191877868 191877871
    0x30c020706021e0717031210030206120c19032f0403080705150702010c02011a10030b1507031206060804020f1201320f10061d0d03050405010806030c1f1107060503 72
    0x480803d0b1f8403002c03440182410010f042200d030300030007080c41d20450004e0f00140c0c260003003c0714043d480c10b00040301c821101c005034036001102c55030002901204440403503491881e1401400da084881102c44400300440c0003100c050740e402c120155100c1919140c103500e010301141a544010111400740090326030150020030840b86690003c0c4501011101d032500c43c2441c0390280b90b8007081d501c9502e406513019500058000c08040d0482807005600407a000c8560b110140880015003d112032a21240305440b0356005450386150582403405c050700010340494201d00e01c00e1140c03400d403207002c40d03916003540009403008281d014030310078074000c9121030345168040e50006c80c1400d52030005101d0740c0c0800030f02c40c4a0703a0944020200315040403011100c010582c1100220007030a0440c1030515550349100e43c080358820354420703548500b8000010407605014180600a80c8060448462651004085441c00100e902a00503680c0d01c0e0300122085800d0392030200040c01404800b041181e0b1210086 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 191880368 1250 191879118 191879137
    0x5030d11030114010c0305030c0c0c0303070b0f100b0406050a0210061503060e04020d1b1a180d050d050f07020a080a050c010207080c1c05100606030c020706021e071703 74
    0x83c0c1c8618003c02c01035411032072101c0002d00180c81040003500360001c003406000c40c2d803078141c2100c0d00c0c540d0a40209145600c507260586d1110b0300301041000f54450606c086502c8142d0b00340301c0310b8140c03a03c3c000300c20600540c000da000b0b004010882c05036042c030030005200e6021003403000b400507a9585003049403044507549440700083c1402c20119550001803c000c1c040c560140c8144800744103511803041e100f50041400712150340d4403000040c001030100038455404940c44055684103441215620340040e01400b0900a601042002e8081800400c252021034010301713041f80d6690711420344d46c00910035040001d51124902d600400e04030320000309460f0f414840c0341224084000c0034016a500e400310f21400c800b56004500301002c0341081c80c0100302d010741580080d400d06c2110740e511800c0400041f541580e296445408104081d8180180142011980050400c1c41c0c00c1110003500d402141788020140148509503403002401040244024515050713140c000080f8070343c5180d140d6001c0d1284 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 191881618 1250 191880368 191880389
    0xb1c02010807170109051302060307090e130f06200c0c040501091407050f0d0903020f100623060d060b1c1811040e0106120b0a05010602030a0c05030d110301 69
    0x609480e00680d12443d45900c2032440c5000e90f031070300705000c1c01740c24028245414440c000b032140005807940c401a50184803140c8404070441d00f440c060fa2030061008000306440d00c84811040c020034a08011115582d41103030020440580c4103514000840404885803800003000400c55031030100421a2b90b82c07420200d90601040e640d0380d0781c1005031500410303011149034a62000c143c0803070060008003445c1c005c424034a81080c12280ba03081c100d4582440035400340c3c024a1901180107070a1050b00d4510582d0002004440c6c2408024511440c11814413003000c180a02c008500d59585801c0e52045003004a0911000f44c4911070407080d0381000794810808503000880b1040c0d519180601b403100f1010314030080c4148100d403295003a089050340120341155450405c0046e1130003e0203850041c18070940a2090000130345413060050034000d04044006282000500100354040300703c0d1802880f074038200301400140c0c1002800c0d8405d0321810b120041c900600d59190701d0426014604981900e0f25 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 191882868 1250 191881618 191881621
    0xa020a0e040219120b040f14250f050c12120702010603051209120109060c0e03030909010e0702070803190e040902091807121103010e07031509060b1c020108 69
    0x6010681c001c0c1c2d5072605008081903c107141507880b964410800c100b0116011400e4031140e0080350031240d0041c4c804007001c2e00c41c42c03203281c4c50303c034019000d0300309220301c191080e40355034100081d010102c200f4000040020141c230304142144100282c501a180740811798000c420118034240850303000e43c2d0f106400340010070000351802d0040c0715402c200c070b8010000d060a0001d60b0b00c0c1000329440381e803400764003809504405008071424451b401400f4801d003c001115284184007501c414a500140c500ca50b00420a00d60281c558040890444190f80e102054680301d00d0b2003030341058420b4001c10761511000c99596042d503080b03c5546542d0140b522034814a038480007c0c0400d6501043d00a500520f107000861049660004150740c22003aa10690390070540700c9044d082e103507610120659444030812944c0d5030740d19080c8102001020b1020040404c2880c60303980f0f01100780040e0301c14418694032100c8200307114031900103404d00d00c0010040c81450400005c51901516440010b0780082c20080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 191884118 1250 191882868 191882897
    0xf120702150c0a080c04090e013602090a0207151401090908030708060a0504060801020915030907090b010909140403030c020303063a03050301030605060105040605030406050a140a020a 81
    0x1c1080d000c0c09546601a190010588054410302c1000c0d10309400154204000210b484551090ba21181d00d20000803400d24102c1c49816001b102c0e11540307000002c0b55080c8a09010601340d00c00d494035030705460b41c07d11b683d24071000500a001e4241c000c1d084291b98081c0c070288041c990300802c414a0444070720502c42c2d0f20b510382601241e00c0d8000003407446000300042140b07140035070b100e2a400140240002c80c695161030200e415190380b580309031402d030f40104d5908283c4c074001c000c012800c42103260301c0c0d0651400850403580d0300418450f080c0d64034ac1c0d5507c00d48842e4401d8609401800c0800e00030700c1221000720700d240c00034a0071182500024905100468001d2010086034003608005000400c42ca540242d02e0001d11102441900201e400f081295a5010a011655000340c048c0d01c80c203859615509203103081d03e034010000360410804010a00040d900001a241c02542050000401d6030301c14145100800c240c5600c0b884000c00c1d03804218821785030707800600c1d107000181c2d00c00c2100d40002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 191885368 1250 191884118 191884153
    0x3030608030a0c03180515090f060a09180b10080901051501230c1c0207061119021309050d021009020a030321020a0201060f12020918030f120702 64
    0x11036580b0001280380d16180046403181100015409480b22501c621a69075000124030007841900c610501c0701c003248041d503520b4011070030324403030000f03a6049140c9804000000c0004489015400c030310f0083c030f0b90364000e00035560301c0000c0640000d001c90902c45115500903000c00401c03142d50025608180010b2550071040e4002d415100c0182c45481072040e00382443d00b032141444100740350900f018000810741c6801003240030190000ca11728485088100b80c402030811400c0d4106600380702d07100980c1c0c09203000002d18007060030004002e4803114081403000811044d0060001002641800e01741d00501401103808425002c40741c080322914058040921706960b1141d50196000040050802c0460f02804040380c00b41c0c42c05603800c0b108003000c00704c2c0c804c0380c000d05100300040c0e5480302c0501400440c0299030020f003070b000c4800080e40c449503002410100004180c455a00c503d4910a01840410020307a102d4210b41040e80f6166080c2d440c00d080e41a00c1294610010300c03c880380b060b40200c14 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 191886618 1250 191885368 191885377
    0x5150a1a0f010f05160b01030c052b0f021008070306050a081b040e1608010c090b0315011b03030905060a020c0303240a06020a05010608030306030a020f0d0615030303060803 76
    0x60011804207100000660b45100b000c0041000d1060811000c2c8485174007540305040f0602c11110b61100b9415400c0034812880590440f5002e64582c0440304401c690b440e42301503504001d0030b50300854030f1040c035003564000306452000350403900c0603200d015071f25004441a84140080c2d03404000d07842e81d076420045810380901c40e611072500102e44942c10b0302003004000c030791010090b10200380015803400711450440725400c04844608100c2c0140000c500038061461942d5091070004452418081c0300380d490301c405400700c0105440b0010103803144c0d0051085c0d100303030050050900002101c5050203800381142030021641409600001804281c040c0b007910300a0354801c00450455446080300d244914582032403c045482c42100c1000658030410740c600a0241507026010310b201500d00075007540c010390086c805640041c800c00000d41c40002d94030407010340448088030602603200210350000c2258201401c00c038200f00c1e84030a4142e02141c000110b034800d1341c00308100d036501c6407040d449014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 191887868 1250 191886618 191886671
    0x405040e1e1f0b041404050a0b0a050115050a030906020301060c0c0906080c12030c010203070f0f03050705030c07060b06030405011407020d0c020405150d050601081605090106030c0c05150a 83
    0x300b400001a046856004041c040f1015000081c2c030b80700e411328040c064108841c02c07504e95100700c40e08800c0140700c1460903080442500305010650400f014086a0b1810210795401c112010500715601d9120341c02c10503050360407010441d541e50311400002d104c0390944005580b8040d2020000039410b071a44601c03011035820354040c100726049102001035040107004084658402030050291080d07080c80214000d40b100e4031135545c1e95951010140c948000106140149454001003002c00d64010044a901c440038007070642e0b44603650701c2c09034014104c2c1420150401c0011080000b0003a0543c4100165850381c02489016540d200040741c0d5403088009502c0000c0040c00448014103254100f607802c1458030080c224034403441c002085018842e004180d440d82c1c401c0c4010070807032030b0511501d24490b1481c20032102041c24a0302003a00c812061050408240c0c0ea1003680180502c20101c1c1e4030b641d139000d82921700410307280d011020408001c0e40c013001c4940c6402c00f6200220354500306041d4180 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 191889118 1250 191887868 191887903
    0x1152306121f0305060f070e0f010c0803090102040f12031116030305210720010b010507020d021207090213121104240e040b090606030a060b060405040e1e 68
    0xd0340c61100e09201c401600ba100804482c80c0390100010301d09102c081d100d101450301d108224a40340130000c21820000380400e0181b1070103504a01c00781da20000101420742c211040a03560b0315220b014900900c03659000d41100494281c0106d0120108650320381c205019030340e070f030251101035003216445d04900da81240c5d8115a1413400c0000070301400240c00c102803c080112030028081c40c40c80c442d143c0071115200003415081c2d9a2080c4070584d050f010000e10b03000020050b2100000001e005171090010182c0309804002aa0382159129800c00d465244400c0039a00e16940d20903041c0040d4100001000c4000c1c0a84008203640100d8175090310410b82010384006044420411320000f03210f40480018202044112021b4940c05d1080c072a000381400c2c0c0d0316014030726084c140840300b00006801c41e0440e42007030f010f01c88039a40c001003810165400c170f0b10000d00001000c1c0042d40d1032045901058015081c0b0080c9405d080c00070403400d00d44003084050700210b410b403400031a1a00817500c200f42460 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 191890368 1250 191889118 191889121
    0x40b060c1c020a1a07110c030a060213050402071a130308270319021002090a17010b100e010206060f060406051e0f0418060806040605090115230612 65
    0x204508091500d840316401a108240c03e1510b440040d04042e1107450a1412008180405243d110f030074801d015030050041c009420100000a46504903040058505600030035103ca40b1210007480390300400c00144110344d9980b5a01d4600002100f11051881c1c3c1204200025100e12000403e80412a41950303407961994641e0b00c80400040844400c0b140f0580c4031a00c105254800c00080510744608009041c0000000c1002482c1c10b0701006a07006150041c07004120984070035071000240c40080e1407200c00b80543c2c0c1517039801451004041c9034003032411001103084e01d030000000d404c000c0342a820303580e5940d56107090003200b40c0200e0b0004e03040041000304003c0c10344034402801440280c40790700404150b400d01858000d40013a0795081c030160000804100c0e203a800d602c44480c0040307030f0005106551410751070584941e0010009001e10b602c81c8002070100c40290301a194000f02400952501c6844030101c010046031800c4040c4180501c1e11410120b103049425149030000520a580c150b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 191891618 1250 191890368 191890393
    0x15151603080a090204060b0d0609020f0d0b121006031a0402090a0506040e03031e1f030807030c0f0605010503010c030b06041509030b04060b030d051602040b13020a0e040b060c 77
    0x441600410b951016940e80d0702040041c0d5075801680000d06008504503210f00303100c491801101d035513521001d0601d04c101703c3c142115000c201510403480e03203040001654000240405c1005090a544110501407401d40c2c0c40c0341ca0347c03a03002c00f0549005040c45260720340402140102c04600740c801070f520200d42da001034640403080c1c2183c3c2d40303c0c0c0007410100341c40303555458640ca150000e6400c8040303005d1091050303242d4080321104640c00300c404c00d001c003000082c11680c0b03a01c000c0940005059100c0015610040c540544141c0100c50760001000c81d0201142c10f10310010315080c005c42d84a54241003002846620902481601c814003c140510b01442c00d2250f0b8541c0c4000d0908500b40300501c140040410300f07070300140344070314000c1c103011946400072410507040c03901e100e10040c20310406202001a400b11804640760003a81640c000401c500224005440708581400d0003a90324000075410103580c0c0e001e540700840980540341803140355019810000e450140038604001580014401e448 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 191892868 1250 191891618 191891627
    0x5092815140108130204020c101b020c010c06022104080702040b1509090415180308130c090525050a02060f040206190e03030d0509150403140a02031215151603 70
    0x4117100134801403a081c45281160b0070310701e6440a44000390340c2d0390b040c40b0484908569500000c0705902c0500a184521000600b400040c0480980355680c04521a04044005050020100d210050035941d41c41c0a280988180d802090228001c609021051006042610300403041100d04101c89007400d022505001000d4401402070705e46444090848000c0c800310302c600c1e0140201022924500c4c003e40c200a01114000380080c509488034818000c081800c503410001515180303100400c0e02c2e15010320001245c00a9818100400011804020041c1d0068014503482c4141e400303907800d560f18550b090b2090301080f103029400020402004814510721400321541d5991418080c0c101e4890300c0119107190001d1645100c19a6524240004184200611310000d440c02c84aa441d43c507003990010220500a000c00d0005140440c128510710300900c241e40c004c460521140246140c100b080d180140340d02c40e8114020b884403200c064400c3c400c0c00c100c9800c0580750040c07000c0c200c11a43e0448 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 191894118 1250 191892868 191892901
    0x181f17060109090c141803160501120203132a0902070503070807031205130606050d120f0e060f03181203060d0201090512070504111305092815140108 66
    0x208010002c500b01441074031700140800340225034142282040000506150489100403580c5144421340b0070441613030301480c1d0409424840c4005602c03901c54030031040520540940c0100210107506420390b00507000c0c50010010000001c210090301d035070b401c075041207100707040c07006e040d54008011000102d48444000c0103401d2181c50001280525001c407402201c00556511080280d410035000038001c80f4014900904400c07a896110070010b076071018000640f01c0e0000c428001d58004441401d809121071600303c4c24050701c0b00390b44d1119448044825801240c4c0700c2127404085644c0a2903600004030329014000114425117152515010402d10200385030341241044100e41c40890703603455000e1b120034803414a4006082545c100404c01040d2003da0812030104081403011032610032405000508503203098488406545038555520a440d02c865800e0100ca44c681028442400b01076110740b0381c110908030280d240c079896001d909601e40f001c0125034006511400400c00d160394000840 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 191895368 1250 191894118 191894141
    0x739050a080a021512010f060806010e012102041a03010305010e0c0105070b0a11040305010e1e0d120908030403080f070c03080609090a06061d0109020901090b181f1706010909 77
    0x81d0030001c0b0031080316003900c0247c1003041106687d0311300304405a000709030f07107401a40074203101c105841e060000825401c1003c10078030401b02504010722a100256040ba07015050a040d898000d0742c1040710081150300a00c0226065840c1c0b000c140d200c030702c01040741141e0040c143d40d05403a100d410b848003241903070040c2c182807050355a24403c900744203070300340100019807142c000803421460b071240c407034103200790700b221000002180d01c210386144e1800300e2070072280207003402c00c8154600d0f1440044002c0c90550802083d44200106100505420900440c81400400d00034032160395050001c407060010080002c01140c0120042000c3e480c0400107194032400501c1283c4002c08643c54540c26143d496001204028180c018101da041e010180c145c05021254815441c009850000808540f40c1c2d20a81c2c000d40c60221b40c404801c0500c2c10300c1d880040004005100c12003154a4460492900500e08008584c100d800d51400e011203804161040c04141c41c0c0015161030240180041c1941a104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 191896618 1250 191895368 191895409
    0x30e161230090806090705031f0902180610020c03071502210301140607021804080f03070201051602240c1308010b010320030403050739050a080a02 65
    0x820740d15a00500c14002094960380e11540d151901c00c426082003000b40200d200b5402c881c0c0309000540f400904c0c104002803020003070740d100320090b4990000707000c0d007800298081c803241d21505840003609591030140301c08136000e0b400c42000850582e81d902e4440c50f0b081c0c00d030b0001d0904000c1d0415035401d5401c2a8200c0c010398002014004014074400e030003026141d50710b0070101c0180200010780345200c1c60980180c94451500c1030742d4002030000e110b10703a8150180d102101c005010490403905035400043c030013210513201d09101501034040c01040310741900c00c01800e00700012043c030015110300e861075104032000310070f17100a41000e00e1070002071408085000c20011421005160000500140076040001928403412000101602c00d01d900c0c0c2010030f0307a5085000c01042c002002c880e0041c2d07040c04e043da5520030303030310b0031540600c10105030045400c10f00029440316040100715984c0b111071020500600d0381c55504200d07040d0120b00944860f944040c01242c0142443c1c0001c2c44210502101d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 191897868 1250 191896618 191896673
    0x30308010e04020f060a0201050f060612150f030703030309031205252a050d0c080d23010803070309050301110f0d0e010516030614010e040902040605030d030e1612 72
    0x320b85d0a034840008000140e42d11410001d040d00c0385641d442d00300c0313012106186060710b02d49580c00708503c0604030140c1c000b01c0c0b888100c0c0366604c017800b00c41d0003030000d8251070066543c1d040107030050000b18020340c0440c9001c13044e004c9042042c40342d284901030130b00c0e0648a40c1d070740100d504013002c1e01111050500c51442800390300351840f043c03c15890f215800c0c05000344002da03c0c0c42400c18070020300c0d0f8414803621804201c001521901900d034141c851403000903400b0041c1601c1008260140c00180c01c0d01060070000c244041d0100080011078042c0d211901210f503214145800c840f2280380d22521850103203c00c842d4001410000d24400700c1c245401300c1c5100c0302c50580d6003102c03802d455511130001d0f205400241250075020740e81c024034001c402001d0442c0c054001900c444a49180c0d50b00c00e9503514039420840d5903907070101010701400760446089100f90400a4000c010380d912442c0f841c41600d680d078005a46d000011000e0747c40c11a1314001403000f6903940d00400c5075095030090f01849c5000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 191899118 1250 191897868 191897899
    0x4240609061707150504150c0f060e1b0a18060512010606020d030207020901030b07020f0d090501110703110402071e291611070803040306020c011104030308010e0402 73
    0x1404040e1038030b1080c0307030011290034140e1442d201c001c1d4003001402950300c88000d03540380c12105440480309039200580605801003030443c0c00d40300c103050040495254099020904c9210f0f8020404002c81408517241903102c1c00c80c512190b0598044a648032145260501100c00c180a54080c0181038901c0070500c1340d15003000030f025242ea048200e01c00c2c0c0d900d11003004299810001d21240d4002030038110302d040510f4005c1600701ea4140001390200c801080861601442002940f40a003c40810b9617840142c006006100d0340381480b6075400602580308141100001041c840708481d030224542c10182c1d000e009100180d0000301007030b02c180f4400d0720015151030540c104a840f00d480f034100d0480d09a062a0044000d20640100c406401501010440c1c4a0a16410b40408003c5800e00d501c2c41481e048529180108540204001e404049800000c01100d900a0b0a14107428030080c000100044400031680c0100d1101400066010340100140c0718881030188c1c000703001509076020949511b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 191900368 1250 191899118 191899121
    0x20307051f060509191d0a0c03032019030903020a080a030815010206060d06150e0a06081606050a02010b041811120c0603150d0b18010504240609 64
    0xa00d860071503003102401c2a0004510744190005081c04441220880c1000d140d10003154000f00518101e40e699a804082031882c140200c1410000010031546035104500d04140c8208aa100460100369102060021540303420354035082d00e002c40e40100141203408101e0074030032080d9202901444078400d000300150f100d001d0040050804080182101482c600d801810548014442c04005216040b030201c2c1ba07a01150181c0c02807000c0360550280f0403141401e8008148a004201d20110b0030500082e89002e40c0c0355151080f046890704001302130390b6000d02c6803038034400f811340d10000380d607140c0901519000c0c05c041d1540170b8461000242d4543e40c80041401c40f51180d01040711007030015905810483e281a440c000c001003a03540c1d41c41207034040f82e01959542081441845100080300064181070700003c6000e204400038044a40c03903400c0d00304401c040d4401d450740c5000c449550020303101594140501c0b401140d10845110000040f205402d1a0422018026a0180e100c03540006c00c07030802e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 191901618 1250 191900368 191900383
    0xd060b061201170d030b180402120106060309060e0102030708010e04080d11070203010b03070605090103090f020d080307080901050402060d05180a11010e0406050609060f0c03030702010609050106020f100c02030705 94
    0x6146041c451210f43c58903240592451091040508042d4103074400d1b119103520a85010007408030048680b00e81c80000c440c080c41d03840d00a600d6103041d90025115606400086e203083c007070b04082101140740f0038542c0c20703848203d46040c0414181d00c0104000c0f08080c102d41e41c03280c090b082080c18404403040300415070380d0b65200301c0420400032855100307614081c85840d84d01d00040700103080c610305c1e090340603115000c1c113000306040c16580d421031014004401520020264000d0141c0d414541b0f40c41d1003801e03600183c0720180000d40060010b44d40010511401e4041d6800030102418407000e0080100944001480349201c0d00700136000f6007031143c0400c00304200d5403081603189001c0803510001419426241e20942c0300720300b458820842911410200c079001802641c2d10f582d04d1a142c1c0f000c5181c0d104000b0760b8142803100108204030341e82c0c10342c814401d5420b025802d0100d46da070b808080ba640d0001a900140c40d41000c0254514486154441e0010180c00e00540b401d000c5240c890350f042c030a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 191902868 1250 191901618 191901629
    0x110a110315100f0806100506161b0603050c0a0203030c0306011b0f1412071407030c0b09030606060414010f090b040605070c0501030606090b0a0509062101140d060b061201 75
    0x30060900034400c0f841c1c0c641c009003811100510f064a8030310198142c81649100f0a40944400500c00c207180c9031031580107540320780091008060490780e2003590745000161103a00000792400001c82c905003201402c07104020080e5004500f56120441e9110705648080e24950521100c40d00d078503000c8040c51050925540100f074200104a0241801c00510088050985054105003c40a10001c0c600f06540c0032540010740264030740180c6000501d810b03e10340000d807510b0144640062404801c0008114004064013170b40d08a8540c0b038103100e840d01440c00307203201e030300a252201440355204a0591040d4402c40c42d000c0440b594590002000d548141c01400018030000769100c00c0c40021402200106401e11f42041358503e0004001e02c002028004c0324480c68000031400e0300c143c0b0030410388240880c01054141d5803146001041d0749107030241c103000b040c0e00074031b400041e0501000c100d900d68504050f0207140c82401c03e9803102c0080102100b010751244080c841c603d420f04411891601030715 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 191904118 1250 191902868 191902891
    0x30b09090a0b0901061508060d170408010b03070b120402040912020f011d0d080915010f090e010b010905040b0109090507030e06090a0804090c0516060203010f06110a110315 76
    0x481e040a00b04100001d100d5446681880c2c07003001003c180000b2800072540c1c40c03034005d000d40c550b03000140d90000080d1000d0031014240b8014021610720200900c2184e40650080040700b001c00103040d11030903188664404004140042030301e203400904520340c440d01c01040011108440ea0315140042001d244210040e4480740584e22680802d1003480c5584840841440945c05204a0941e0399002e000350700003041241000300e86a801c0c02c0040b6964607146451404640d82c40d090060114042072144002240c204282004400c1042c801d0901310b45c4183d46000006007070030280000b51040c90181810084a048000b40985840c0300d410300a90b940d035004038101d1210f00c03500b0720746040030344442e51a402c1072543c140000c2e0014101c4e4100d4003410b0000c03c0403002080143e0f401d0140c00e01c6000402540703009403040011944c000e5047c1d42c031800d813080c402a00c8240c200d410100780002c0c7c4501d0390200d50360300042141c00c90504520f20008007290314034120150745d00e018080940d21f140108 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 191905368 1250 191904118 191904133
    0x7030b041409190f0b04080a090902090907050a0908060a05090d1d101106090105010810060815090a080f09090a0203040f0b041106040f0f060528030b0909 68
    0x614041c05075800015070049806000d04161040c0b0b0344070540000b40006034414040483c04000c020b400d402c0d101030f0001040f10062a0a00300000c143d40030b462104009041d070f401c0810490403a10a03222040d101600304103c1d80d1b20f4000655140e400b822940b001c1c4114441c2c00140301d0010020030348240042840840e5608000003c00d250181c0c1c00c10328010300200d101d1700041c08410183c5440001c4080b0390040880340d1503e03040d10320f4188400c6402940c001e01e000c001694005400141c100e811b944115120000400070800c2103411a00a5501340c0d00425031b0100c1c1c00d020700c4d0141c2e4200078640d040d204000150364901c220341d441483d01291400010641c0015403424141381940040003000c154610314040d640c00c041c121003020010038800c041c0010405003c4261055141100c001e01450303a600e40350000c4591003101031044080481c849807001c224180314200b07984010543c10b218060480c0b2030020f13000d0181c12080030000f05566034611481780c0e80c406010034010400c41003c0e1801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 191906474 1106 191905368 191905391
    0x20d0207050a0209060f060904090507080703050d0e0d15021602031905011503120516080f03010602100902130c050d06060306051017060603060f03060703 68
    0x45440840c4100400500103034911045008a4441e40c40f5078500c0d0410442030004a44560060010710102c0540d081c02d80068401c01c0c403c009442215403590605c2d031500e2516481034801d64000c1808071030258101c0d1003014020b03800c1e07618540900c47c0d83c403901020380000000c507400d50340c00210480700c1e1403000c0c800c0c10110f0740142941e0100f140310801d40302020f0024800d07199075203054038558241901c098090202c0c0d9101c0910044841d220500742c440f40c100c841e2120440c5607084914002400c2e010003032001c541c0b040000e90b100d50510000a00d040e0401060a02461034000c408016035500c0914454450100002082c00243c60404503624020041c81e40d13455410002c02194250701604241c040e58025a000911250100000c0310700422807000e2004615400b00460034a081c10342c01103034400f00103000a410a00300030b01281c94030b6400c540307140000f07540300c024105 = true := by decide +kernel

theorem cover : BRFrame.Cov 191726618 191906474 := by
  have h0 := BRFrame.cov_init 191726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 191726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 191726618 ≤ n) (h2 : n < 191906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
