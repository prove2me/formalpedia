-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2734
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:35:02.219216+00:00
-- url     : https://prove2.me/submissions/ac4f6d4f-ab68-4aab-ae60-50dab50e7608

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 491546762 ≤ n < 491726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 491548012 1250 491546762 491546771
    0x21908060a03061119092306040506090d0b0703090209060420070515042f130207030c020a32010c02060f090a06050301050f0405010b07230703061e 65
    0x14a03039421000748107880d404000020300b038070754200b0750319540030300e028610f45c1441c4d1481c0c184816030000c004c00203e84140b00c10f4a10504801c1c08030b40d0403150100d005030006400d1200b03214501d8020050400b003a0007508809206400c4e840c0c0c405801c6007501c1c10000301780e170341c0c440c1015400c10101955001406507418403d03408234480c4600d010640018081f002d41e00450400100701003800428418990140310f02c8990405050203554107034070801807952440e1001380c5400003060040720049511005000d160030902f6403066002943c00400b0807010041c0380c000c00e60040c1d541602c83c0c006000c2d00202030105c098221100c59880500450140985121a81082d0700c0c1c8c0e0701501303440f00d155050fa8100e45444070005c902c4d50a008149446921685000c030202c1d00540c4080030354100e400407182881040d02c4034080c48100c40c420300131a4059401000504085580b4511803440d620303401d40071030004001c801050b0b007010070903002249c106071180c80f41c00890b8a00020496009400d000030070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 491549262 1250 491548012 491548021
    0x210050f1909080904180803040602030a0605120d03020f07080c0a0605180c060a050403080c0132040f050f1005090705040c052703011814031c02070501091203021908 73
    0x80540603625089200c0ca44900700300c6940c0740c06c0c0c07000b10340d52079022a966840742000d18005c0d02940046442e00701d240d1400c00001840d140aa041800c010400c40140090b020401c10841c048d52210a800146c0a0f0812032200010281c03c01000022100e00240c030814440385000001d07168090510100740d41d002c003140c2c02e40754000c00c01e8508000100c03550b65844000490544541c0100c2d40f0240840c18040340c800c51b041c1c419006141101e0f4105241c031003c601c00c0300c120b00a42a01891800b002c81d003000060700041c00b00039010b0700d283c001e104507009100f8011081d442c000c00b020104145940b200d0900410785e0040144d4000f8102c2102c00740004100c0d0780f0b00510300d0040c2c4214100ba00184070f48464110001c840380c980040c0058020b05c030389084400a0400a07264010468440796a24189181c0f28404030030344e82a201d201040501403444200d07044041e4020341005d0310f080d540c54116400140342588140e8921041c0e440c0513848050140c40030070741848590225003071064100030003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 491550512 1250 491549262 491549273
    0x23090601090504030c060903110609030a1d0402041703071502280c0501050108160f0e0103030c0303060801060321030b01022a03070f17030f190210050f1909 69
    0x581911241e24000070b103555141401c80390800d500300050241403620a4140a055200c0c00a0106000c0b5400700d0f0800d894100d8120b5980c1714510482c0005580341a002d4016030690440c0c00355204028009410300b40c840007000103240e545443c0d0703041607000003200f80411210b0800030082d00329054045041c10200000451507140703070244039444140318070440c043c15000d0483c81b09115080700c020422980c54103541a40d440c0c1e401d68908104102441c00686104c030002030f5025680141400e0031203904c1c40d42c00340da803000e102c04200c040c1901c030b040100c0e40444c02d01c51000194040c0890140c080800502e0310444e10f030000c096401c0600340443c0d03503a56600064007090f0049103456440c003100041c0b41d40c00125031403403400380c0e060007692000220783d480c281d5604280d44d5001022002203c40c50101c5650388074105151030704072014407089001c903180c0481e01300c4c50b08003801500c4110003c07440e054101c6004030303680358a003050f4505010428509440f03048510340d070f42808004001458403503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 491551762 1250 491550512 491550523
    0x3011806080a030e012001020901020c0a05301b0a0e060a170f150a0606111213050d15110403030c122c01140a080412030e0a05012309 59
    0x140038000c3c80c2c414581281d210340115140c04031b000c40303041e84800c41c040030300b4040e60005c24498010300c01c9003032210b62071801600344012600c00400c000c9036005e500030028035004611032080300c074030440c1e20b51a00065042c80110032402a2860020004d91103000300425600190802d00c00c1e2925001080815103920030b6401c2510182c0c03440508815a00840c40d01d0b00a401c844480207004a1036400511818008481d0103a102c8090600000340c88000480d03105034803d0b140300080d4004000404600310103030081080304880245010300a0700c2d200885c0005060110858508440f800d0070350080c8800c0c480c52010399440e0000c50324003859924000d224014805001c0c1806420452a00c3c64030b000f00c0500c2c4240035078064403200261720340610342950000c5e08100b40455801500b401c8461505400c90b004814281c5900340701d07440340e0304e50003e422503110a001c14540da84007a8140b00700208400c1020521480022034460642c0c02400d040303008040c3c1080200319070106008070306a02061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 491553012 1250 491551762 491551783
    0x609080a020c01230a1d120109060b0301140a020313020a030809101107061206050405010303050408010b040506130518031c0f020a0203040b18040f020a0206060d0b1602030702090901020301180608 86
    0x10100b4036106c980e1002820392940702842035020303031421540700c404601904000812401160100708443d505801e150a8514181a07d030903000d86000254171501c066020b990403202e80e614504c2855000d13030102d52581e090790000d994040f004500a81c031442c04c2c400804200080d0302c2e0845d4070f9800d4801899540300180540024024111020071b0040c0b900da10034401403c0007003080c446540d4034240035105520600501f009542400e4000e035840c00c007809001d0151002409001004282c9003240b8001d05d401341200551414901980900c1c17a01007014007161320100780000e016913681c01308007049803494000303002c07030358018010050115004006c2d80c040300c140403100d65a03806006014034540f84090320b1160321034903100f40d00241d1080313680070b80003a103c1e94085443c2c0c0d40781c034010405c1c809142c10000300904840c00025000c04003007811208410743c01e00450742000400d5000441518044a503150169408001044000d915100843c8240780050b000c104840c104040036840e400520b9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 491554262 1250 491553012 491553017
    0x806091608130203031e04170703032a05010606050c0c030a020f0405190513020f010e0a050f0a030b0925060c06051504090b100501090f120609080a020c01230a 70
    0x503803503815900c082c42111b12008908404007130f11250382c604814280c00501803850075800c128243d0503103e0303000811105a135096110944008060001200071102d044c005000109410310550b0000e0424000c00c1c024100b0750b210070780c03a24900807a040c500202850750510a5010320f5403000075860302411201040b105403800b14030f5565101403d12507030003a40410452901e403004228200d07820081c9800020700c00c44030180d18051940045902c040c01c1844507030b1052500b40d08010a10b0840100c84030b140015010b072011696a8a036205000b001b00d501d000c05030440801030150150305405d01000305a0b503040900300c0340c2007540051a2017003500c0d0090860340c0c1c441c085070045552644001c0b103130800400c184040346d840c0c5020b811004096481d80c1c426212108081195805504040300b52000010440002c40c5004810300720303800d100314117503001c40d40c3d898800c01084002c3c00a00316421560010661402500c000401c18a03070400036104002809100144020307000b004c0f00c240c0324003407 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 491555512 1250 491554262 491554291
    0x60a050a060605120c0c06160206070503061c05070504020a0504090b0102010212181207060c0207080105092a040912090506190f0915030b0405010506070308011a070f030806091608 79
    0x719080e1480b44282a80b418852003500104023900041c500001260201c43e0300340c0d0115101d1440564260000b86c441c40d80c000000c0c2d500500b8283d01010a0007058003034812a803400d40e4490104080f030b4009000e03140040c400003070030301820455000310601c0e03a20178070085241c480308000445034558040d000080c0040020b40a0710100710400405001032030059009075960541d2818000520060341010302500034400e0001c1c0c001410300c01d4620482000010304000482d5244a00c0020a003041c08030340c0030003881c0b41c0820b41e2035600c14a0047c920950700762040c00035400d0b001d08440c0c0d450340028030031041081090446044142080102412030402c0a2090060b602c180c070309000640142e00894a40340702c01d98460342c0b5030400d10007554241c40802060341ca070010700035580f0032010054040341c20382c00100601110440d0544440c805428082d06080465541121550b05403005400050031070b0103000c5d461a20081058115000c071014903001d0710500340240c106440144559002c0400d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 491556762 1250 491555512 491555521
    0xf0f0303170a150b0c0d0c030206060112060b0c0a1e0c1511061510020a1a13140703030311070b061c1a040c1707090902040617060a050a06060512 64
    0x55001000350f00c10249800a25a4a50920010705d801181101d00603205900c016044180a4940c2150554150340a011a6a81e410041d030341854451103049134584c0c1c0b441c00003210762030000917040c56010600640030001080c00c3c139030800d1494801212600340540f119200107500383c18910704903501d000c260308105803594426103190004410860301400b49504201e903c01480010341a040400c4543c0200c000000208a80e1490003000c02003d1003050b0319940903806105942c141c1c8526002000c401140460f504c0a0700d540c10040c1c6041c5581c4036810601c100340e010301803c100907000c003210340c2c01c0600580f83c0c0d085c105d00c06052103000b040721107034000036400341e0800030600799044111404d030100e01c80680c103840c3d5403c990640d00001002404552a908811016001c22507103005203030302d85c1020510002026500c50407a44203a8544002031080c0060201c1440e8508040181040e8035200c400141640d800510005d0168545001806140e400c041a02c0320300420010300c8817203945 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 491558012 1250 491556762 491556781
    0x307030809131104094b0c080a200306040e070b0d02040f0608070219020604050a1d060d0b01030308130f060b040e010605030d051308030f1c05041208040213150f0f030317 75
    0x1b512000740c815a81454240c07071103143c200700710714060303c19110304200c01e4598900040311344140d56400003219a003000400c5031490243c101040b410400c0007901d525654036684a403161384005441c0070415000708d0100204101300f4048402000c7c0e50400c0d135442c0c41c0c010030007074403207500703880610800c02c41960040554903800261405040090700c03078814075481e4800307500e140d10030085c1d00e01c00680000010f8074901300f1034011000c050340008400b9142e42141c1e13090f03600e03110003810300d400c0c8002c07030b08c901c0081005040c200300b54600406000548035109000d0000b9600032a00552160b810710008001c2e6880c0000c041e980e0502510380107455441e0141942160780160348409041d10010550309000d4464030010710aa42e01c40003590b08904e03659140100350340e001ca4018000000001071407405a0240c18040d40c000c0c8010085002100c46406035011140c034040c880781d1440d10781c0818080d41405003480343c041c0c13140040240085156a070001c10729070428a0491400c00840c000c9840c178075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 491559262 1250 491558012 491558141
    0x9150816090b0d020d1b0c0b090309060d0204090b031f11090d1a0f060d030c031e0201050603070e24011404030305031b0306030703080913110409 64
    0x5040b050355039503140c510704050040c0d04888261050b103882c00284c041425a541b440e044138110986444c0711002040e20f80580002c0010100070160000b00a98030565850200078009400c0d40b403001600e80d410b0454580488441070b410038041d5100c048840207100c1c600e070307070162080042603011a61040c030000751448e602644041581005400744071a0030000c0d55040360804032450441000741f1f99400c805400c0a400c2920000d170004041515640480c0c442c46c90826194080e040210300c0d8400c101807440c1000c00081c04000503591241401814941400504000c103000250a075103410400c46600c40410002c40c2510340400c02105c0e40f056900030311300b000b00d07403802e11601a1180d40e41d080282203640201c80d040d1000b01311140c00741c4280c510f107095038012500034006050150640d95014500c0e031105071030310351180c485c0c48014a030158a00501e191402040660b0b61640d28100c0d440099940020420089411091800135002483d0003104000340c88070b100803d10500305400c0c00c1100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 491560512 1250 491559262 491559269
    0x603010905070e04050d0c0c0302040c0e421b0a020a030318050a0311091b0706020c010c05040509130326250f03150e160915081609 58
    0x1d0140e82c10000700c03400c01280561140340540300707603100801c003480b0480d80000c050400408444a903d424009810a07034003982e000742d2141020030030203920500045810411040f0400342c0d40d4403600710300c14405911500ca102c030a40f4030940700825020004110580111450300702036002031401401816401c001c503451043d0040c2400300000d84900f00180031711641c800780312469075003450001c0c40d030504003e000c04070f0b500044401d25280112081020014001e000c0040b9181030201d80d4001c260040020425103105107401a0344200f4203000381c0c20340e40340250f000c0c10300500344403c1150b0349940300080e0340030301c0a00c4500d2601d0211f140c00e40306451114064024424081612a0000600030601d802550206454a03640d021203203184c03240c10b403a034003000009500956800180d8041d401c080e06000100d104001700382c6d100e6825076400d41044881c968840920036140b20b032640c000140c000074001c1c1258050305404d03540d101600b10f04001e44400034040c6041840c101252040c40794030081c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 491561762 1250 491560512 491560523
    0x60e0d0c020910091b0809030306012a0204020406020304140603010b09010809030d140103020f040606021e0f0a03020c01120614090627060a14030a0303200703200a0b0f06030109 78
    0xd81340305010503880017540c00e070320101040b015004208411000001e5a1040b88142e5444420250101e01506c03010110314a109200c194580740c4c40050351140013034009411a0350085803a903207406008600481e401101c0f43c010b110410052080741066011078640700780c2800e0019980e2504064070340796200750072801c000f0383d1404142c48040003d020740343d41241e000b11820941c0070310304001c1001b16291445a0405680312140b440755100c240e041003040381d00c4402c10380c3e0607451010b03200c41c02c2c411300000071801a0041e00d46040c2c81d60b04141c11850749551000108401414214801c1c4d102010100062040e030408c00002c03081c1c1d0700c0c0c030800d030501d0040180d1842c0300310001244a81e00481038031654031030000d104000c5640d04948101040304a0300030001e013518402c4c0e0300c0940040c0111300d00251b4609414096417186040200100590380c4171340d4406951082c0100b140481c860180c01d09410740c2c019034018070224400f030580c5a04022030301d10300c0301c00d611500002401400c3e148001000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 491563012 1250 491561762 491561771
    0x10c03090902070f140102090306042301050a053421090303090203100905071e030b010605040515040b1b0c0307140a05100801060c1a13060e0d0c02091009 68
    0x1042500307000c0301c420300d106140360025003180003119421f074055070040a4160b4040800500440c0300e441100a410745132700c524540300f203100e094103800c4d600121041c00002d0b0f01d4a090204428200d41900d1b40805140344255280d00c150240c200301c500104a124104240b048490000300c01d001029500005402c0c1e04104a059034036028002e8071250009900c240900340442d0b90001090144604035075000c00501801403e201003a040050000d0045127811510f800110014520072003641c00780c441600c42c2926185404200f0440107a815040038907220306000c100b00b039000280903503030244c10443c0016904441e54510070320f8000c1c48140c007549407080002c0012008900300c4024100c0a003643d00f8020542c0340c0d0117000d41e0182d503200b100000b0b42c90078010021680310f041a440c0f00f900c28840859810090000703240030b020240e68010351006514a08010410144a002544103c2c0c5000d0311441161000150161918240190207010340000080d000c02c0c1940808003c2d240c010010072 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 491564262 1250 491563012 491563027
    0x201021e0102280f030615030e01020f071a01060c0b06060304060e030307090f0801020408030912070801050c19030b0f04020706020c06010f05150408060c2503051801030207050c010c03090902 84
    0x8492200c00c2c042002150032032207415104c9104e03000303aa0540b14117413246645000300607002c82c02804561040e51840d5402e0006c0e007030094501c2c00911100380a0b0004c600710303000b50195101c0000381a4000e005000c1d441134400c1c001854000c0103a888001107910719100da4175410180007800c0b2400310807105010003c10803070442d030456220000c9e00d49044d040c2c0c08241d100d844079401c03841035014900706640b0a0140c071810707203818a4400c030b2051068007aa1490307907541c142c1c5425504c09030f8440030342c1d12001c50b1360240c1e1300200300d1480002d07a00740350510511002d00c0108900200150006024640004494007440480c3c0c044170800100c0604942e032541e950701c80074040c1030890003120302c60410f10b500ca400324840701090760150b9410a02030261a142c1c291200328a42c0014800400d040c02100848101e100c040c0c03c6a005034000c0d04d40c580c2e50b884041540d851804c2c44800e89040c14418412840807400004244207100030070700744076018882504003520341d4070b151383c0702681e560700002d030b0b01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 491565512 1250 491564262 491564317
    0xe0c15040603060501020a020f090711060103080909090309010c03081305030412061113060302160812040b07170408071a180c01050a0e1e04020c0318010c0201021e0102 74
    0x14421210307180d40400045456100490711084040d1020f940310032892401c103082c0c03070701c801c0c40380d048016030500c4246009800079950411400340d20507a18084042841035017420000c50556001802d040031310311301002c0380d0002e440f406140c90b0250811000100040812001c05000000290007804882d202c070ba0701c1c01c10502109181034122491030502c0b03105283d5540080030380320500c2141911100c11810104220000e420500b0302201c80000e1200f6080416515401042400c481d0100702e030291801d42041070708001c003d481e0030b04209860340342c0c00b0750505800140340c006034003130080c0350745109505001c484a011f2503074a503a40c490394003d000c0c08007001c8410a812054180c00d03559080c031244010b540c580160040003011407548481e110030391900c17940307210a20107403429036000c40707170f841c4c01143c226000505194400c0c0c0c4001510b0106a581c07285080c40210f0920380700d0302d042c1c601d9000070b4640000001140c1c0d0b1400030702020701e401e1070a405440c1d44004c1801124103403800150030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 491566762 1250 491565512 491565517
    0x5090d23042d0308030c070510110714160b130e010e0a0e0613020d030c05122a151008060403031e060510050c03300a1b030e0c15 57
    0x782c2400d41d804620b400d01640410008504690f0860406400e560307400f040001e656005c07000441d041e0180001c0d03200502102d00ca103410101039426216100d41841c900a070f10b80141c201001103903407040e050a0408601880c0740001c0c7d412605401d5211034545284588402c81030b04030842c11004100080742004064071024850b01e031401007405860344032240380d131711074a05a46004290f20b503602e201003d4109003194150340e910a291400507001130b91151814006a03c03a801c1d40c82c840040c4411005440300c4900e0941c0f0b1000c01c052141c6812814210358840e041c180791204e942d01000028180092200f8440082020906030b410b107280600e801801070043e202144500740c42407054881c0080c0a1080c0401c1c1d5202134002d840e4074012100a40301a0441211401c1c188001c1201e001c88003054580c180384104070b032500003051520701c14000705680d0000c009000c241d141c01002c0f45041c1441c030941003140f0305800c00141ca4070841d19200e00b0b0035050002c440d0408500120343c0d410a600000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 491568012 1250 491566762 491566799
    0xd050403030c08070f02070b0a26091005090d030e0a05100f050a0507080441070821070c08010218090105030708120306010504031a0a0f05090d2304 65
    0x54a4615684c2c5400a8174204c1038004010010303480b11005003c4030200c10014403052103d42403046d008100c01da0040c54250254010841c000d40107410b0101d40001000719400129036980d081c0400e1600c244004d41c2c0b4074102c02900100740d01d451040c00318280038403925220a403c181900c01c603a0841032054003a0204e00050031016190000044c103100480c46000d0107000a50707940030b802d0301d9640b1075042c030745c60803040c0214265000d108602c04901d40340d008600d03121450251070b020386400d000c45041c99856400004250480140021111010310024800390800300880361905c10724201b01c051000d550f007003202590320003d109000c055950840142d00340c2c04072240261030782c0724024162981d555102c2c4030301030346c030060058081c0310b400000f0755405001850502d04165880d140c200008401c00600e0358580080414002000c416004205281c4030502081c402420050b4002e81c0d1884022203600030070508052316010354aa01b0f40c241001c052400358291030701d80302c030802044a0070562 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 491569262 1250 491568012 491568017
    0x3030b01090b0901050910050c0a0f050d02031c150b1602030f1b0f0f060406051c020f16050703022d0d03022e1b0f1805010c0204020d050403030c 64
    0x8030001d00707a20340c01c2c2101c040ca10183e6500e800e0a070500240036200102c48000c0040c00b0045c881541c1402d03040110b8603400b030050031058000e040c40e081007030070181d2201c0d4101c21508100504003d02d11f2981c0041e49062801c100010596050043c00c05109030603000111100c0300017400b0310807643c1c0c1040030a5918002c0f015581c1e1040030740032132a644c50101d26200400320030030700c0303401051410b00320030403078804040c0070703805200c0b01c05000401c203030700680008020981c0840d080c1e8660b620002145070720500700508618002c00008520424020005142060107801c0b074004e041040c2408030300c0c001c3d50f0240105100c0a8080380042000d40d6003404250300000484030740b8101d10342030b41184201a0140c001d0180b205500f12002c401203405030710461003201c0c15002d420119070a1050448510300022200c17488081e45100070b2100c0d04015a180c20003940c02061080c0880c0c102c2c21004551090800241e464035504c0031030003070300425881a1115142c1400c000031302d50150000c103074480565 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 491570512 1250 491569262 491569277
    0x40b040e090d110607050d1517100c051917090715022803020a1403070c0e1608131a060325060c02210a0302060a020a05031306021603030b01 62
    0x2d801c200d9a00c4020b44403214140e1028001c91846402100208031025201c40e0100381c07030400c00c2c040b41e181b102c00e51020203c2001400710040c961400e0009a0004500702c1e81840b0000300c9001c020024051708090101c1040803030b101d030140500650000c039800d100031420200c5072034008400c81c3c031001c80d40b04050868104518a407042840800c0030f0720a4200720b54889102030446414040d50074200c0b00442c154490100c0100100e10b20a0901c2540c40741301c002156070700200e1514560422075a44102c1c406440c520078003861000c0b00c5000101000d1624001c2e0060b80c600701250840034484102910b005000c101030840c645103030081c3c504c209000da089481c1030f800301d05800440c4103011003040b850717901c410f014080544158580890700307000404d12104410108a101560f0359641f95520081d84924100fa0070182c06008941d40140f11036800c43c10302a5000020340644402443c8002c6102d404465030308001c216030540340100500d03d54201083c00314500600200040c200ea5030204010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 491571762 1250 491570512 491570533
    0x20f0f030a050d0f061a0d0f0c08040201030e1e0a0c050a0f03080c01200909010509060a06113c030f0703050a12110a03230103080708040b040e09 64
    0x10032981180c031190340b03580c506801007070a040203118000202d288642c9800001500c400075006611822007403480c1641c0d100840f18440c001c407002c02e218107190500b4030b80000c15058000300700c2c560050702800d0100d1a422080c0441d41064542c420805010580c502741b248403100000c0c014500e24400c0d030075400f42c0c0380c484040199540c80c52003140c02c03c4a50f000c081c800a03403940301130810044807030004204d8032803403030581a8040e40c0c1010040440004aa10407903072a169a0007801490213850958182c24040085030303241d0294010700040c040c04103106c920f290001c115460302c19806240742510441415030702100040041c64600f03c3c940444003104181c2c034040110380c0010304601e91107203442e040c3d0b0750030f40c0c80350442980a0188503018810051102a074003954515034070b4415801e43c0c0341036000001d022583c01c1c4018041c503440740a00c890741903440000362415079401420450301e800041c0b90442052103640c102400f161800700340040c408012040301383c018180300040d60080c0c0c54 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 491573012 1250 491571762 491571793
    0x51f0903031a0303040b0a0e0a0603270206030a0c02030706240f08070e090c04090c0915050f1c081303020f030604170a0c050f071a03010b03040b100510020f 69
    0x40b41282d03641c541c10401c410007046024100030051015a8102180762582c81c0300003400e220203503072007600400d4480d80001c450308002c03400c0c041e0000304103469030202c110700d401040c000d020050080c000c9564030300700c81c10301c94020800c3d100b20a5101905000d00f20040c0d580c1d2410424028542d600c0745502d00c3d000c078074003248080c0da00c25262017200400030145001100700c100740001d0190101e6000344000c140c41910ba5000c0d00e24542d01594101c40d805180210440880e11107078400d0001c103000346400c0c84142d903407002d00714162604540070740c0c03c041c40000041801004080c0102000d0740002c6c6400782c4540707009240b0849008403044504000840c0502d5120041101c0c021f083c003103aa1352000059010002070b11b444020b0b460b116060500303035625686414042034144540340d000c1d6030304109107a8422126880b04002007a13140c1554035158001c10306000c041c1000f0411000040020180d5061030407400007000c00409c60081940628406901c1e03140d0346260240500400300d2000c42c158 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 491574262 1250 491573012 491573051
    0xb090a0b07081204020a05031c0f02010603020a2d0e0f060f011e120e15010602010207030f03020d020904050a0e16080c0f03031219060501080103110d051f090303 71
    0x19045001d0902d480f1050042c1108000002c10403a4010403060b00402c0c251000c1203411010307601c20b4001c024201040c1005000103034180240b0f411681040c3c81803005840750050380c81250310030b8545c0031402c030030503260003c1001d41029144501a0048001817158940702115010764080c00d49180e203619a20f09102000319101075040c0420400c5284504c00b070051101c2c5042241145400c1402e145583d030703280203540c0c1e90116a56140d2180300100070400d0086045030041010340021487c1001c5540e0240ca911000031008042c0b541c041000c41400c07450703804445009800034020841881e050822800504408007008858414029010f04e00c45c000c61401c419100b10100071308482c16004101f254240d001d04e0700c1501030001740003580707400c03250f84041400742c88141d81a42d01c0c504210307024800ca0b5801d034000e0b810401e20f0700041020841c0080c441c00901d4040e030710801c9180b000e0904e245010540d2080c0c042500c11545e0014075035801794080101c0303900c603540034801104400007005140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 491575512 1250 491574262 491574277
    0x40e0109090f020f01110118021903020a0315091b090b01091404020d180c0503060708010b04090c0507050d0201271e140d02061602010c08160c0c0b090a0b 68
    0x12000c90b8000009442d005110381c0c0006814580708046080d510f030002d00303444124100c1c0d402c0d0042c55425000b1890102003101181e448549083c4c06a0300c0c44c0c0014980518034400548a100f0b61038070f18541d02910340152815941111402017030001c40041c4150310107852080c00116898180c0c0c0d00e00e40d41c801d402d00c1c811966410000c0190082c2c3c402040002d51010018808990340e8041c03220403038404d0390056095134096421200180d00d064140360404500034024030800c5019401400140044030995055611a501c000340c941e21400c0243c2e00c41c0715600b809044c80c400c840301558803da054010340c614040c1000c620b03ca65405194000d484409240010318450500c81c0c248144070b40b2003e00c098582c040c03911080c3c0340e000100311a060041840c22400140c0080d810048014512524643c80003098402008620030318140100480c4000c0c0600400500b00e12801307550301c0c481d200c003504403508180680070140c2c0e520081c0c5c200d60300c480744590084c2004000080e8505454007070b207421 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 491576762 1250 491575512 491575523
    0x30501140d121b05030a0806060a0503130305040b071b05030a050a15111c0b0901030f0f0c0b0a050301081510030b060d0803040b0603250303050c01110f040e010909 72
    0x101c40c5594840c1800300c1000b494000b0000d21090840801c0c0010f0381c04403901e07008001540d618141e82d40d008050181c0108603500071481001019421a403290842c0d60000213400105012002c0e4a422a8680700e01e40c00038444100115506c814031581089907a003010780261032400c0199100c040c50b0315070011400240c00b50700040181340201e2004191341a58101b1040002441419006401c4181c1c201c0d080402c4a00d481c148a0103c820b00e0388280b070b210340c10403070390301d00e0310742c03550340c0724041102102c000500c0c6040b100400800c004c080e00c040e401a00c108800d00342c50f03891094004060b074009100ba2080c600c2001e681d8500740c8010080c06000c3c0c2e6094007040900c82c2151100c0400e943c010300f01542194521984a01041c140c0e005075014510032540e0300c0c5d0900700b100c200b52801c1d000180791020940b80403003d6400445030301d200c2c002c40b0b5050502646071b4a40680c02401004c0c425543c18925200260b40c000d5034003858024002c0c0c03000c5480214950742c0f9901e000c0c086900d00b4600904 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 491578012 1250 491576762 491576779
    0x1a03060a0f151d040e0d0f03020f09040b040b040f1a040c050423091e16080613021611130204061b05031c0509010b040515010c022e03050114 62
    0x31050b103d814a00011403031881030718041c40944002ca4210b5900c2c4010130081d401aa0030010768545c007065a00740d54070180b40550406541c03c03242c1000307119881410388200d544401241c050788454001d06000f0b40700800400c40d90f01520701e201e01a09200349404400a500382c401a5645424440d404217441c840c0d64003403d2904033624105030504a4441000c601684040c0901507607600741c080b403040d6540e00b64a0690038403405e044c0c0c8505009000400b030602038044050700c1c43c1d813010f0401c1d80060304035561840d01c0b01c2040004024880e05007022403d080d83c280b46405d008520240d60821401625404410320f104c1c11402c00324011805090006820640c44012901d0421405641c3d280140f080e2481d240081800031400000300b5501a042d035101c0c401c00058034800e00c0b0b14410024203903400e11080c03910180803a0204030b480d0943d810b0100c40790400d001d40d103a4801070454500003821240e004012081c605906040d0480c201c0d00183c1000c1c0086880000f10010412a20001d0443caa = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 491579262 1250 491578012 491578049
    0x80118020d030c080d0c08070309120302130f09091202030304031409150a020604060e010b0f060c01020f0d09120c0b0703092d05060a2a0302041a03060a0f 68
    0x11420740304800d030200103254001c000800c100c00014044181040703400100042c00000203043d0a03002418181454034007801c80b030101d5589881032142003070300e180051b50b03040900c140360545903440c2c105240380185a040400c2c40c0c821a40201c007070501800d112922440c0f0008200e9491004860090006890b41c81d0b5948204000340a401c542d48000c000300000ea03040b4101405036004809010010390000c0e0500042c0010707445820080d0745a1002030100210460103c1d0351316031a04049802140c001030042200d00c402e5064070780644004041c96038840b41c2c01a0240606150401921140c0340078070004170007801444400d901d640d1001d403620711075954070030a8000b008501404d642d040d003c076a010840c402030403040b04426510703050701c01d0503110030b090051504800410748512140342140f0202c030325905c10071010b84040301c011322640031800c14608402901490b44117901040f00340d8040b04000c0c4e12000079612480c1c01307450340c5204651350710003840c0d60700c0d243c4518500c441c031482e03129 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 491580512 1250 491579262 491579269
    0x40f0e01030c0e07030216061b051e13031202071802121f03021f021e120f0c0105150f150a050a2003040f0605040f05060306041404050f0708011802 65
    0x1070b42c01491360500506103800300710030b115804004003040700e4403540d501c3c90070b80140801d00c1c00500e58046190440c1010030904d01c3c0413200b10007043c440c0702c00300d0100d0010f00c0d440c08040104080c40e80030b500981491000314010795514018010b039090259103070200007411072248241c450b11800700743c1050140d00d03508440004055138410f581c00182c0d9408021000d40c903544092200c222891004a20055000707000a08056083d00f20480f160802141d900c1c0360b400004100005200d200100c0d640c031480d800310036569110768142454503500709005c1040740c0216072044000c6c0b890550360446e041d5200c0082280280c258404680c21600c14820720358130a01c00c401400c4920075070f0034241c0003400b04490f4240c2240c20100100d1813640000f81c18801c4025001e06280101400d0418608007402e0080081603200c240c0076140c01200041f00003801c60b0f40d990044107105484402d150042d007000c0c202035441d01c0002d64030181c00e02c00e203500040c2c091014030420205008410322128402c11a9080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 491581762 1250 491580512 491580539
    0x61902010e1b18130204151503020c0d11150106020109030e010305060306011a090d06092102030d02070c05192108030c03040303060308030a050105040b10051b070b0a0203040f0e01030c 81
    0x149841d145040303c1113070040c0c4443c46000510350b605a1030700d4002d4a07140c0312916030a00c44074850201030050144114011000444030042845810115140013100058070b10704800782050741b42c0916820000181c0c9034043d80030248503400381d60b60140031700c8104015001e880381a20207e402d1303408440100070120101c4100b2121030f4100d1025803402c1d940d00b0018141000c100b0302501c006603106100300c200031100c0143c01c6645501a0300e28000c0d0300a9030040c0d02c0340034159a51040c2500084c9842c1081480030162000d030000030240340c041080072001e280725202c1c1b03001e0042d035107580c00c841d80152106030102440301da074069030903451561190b9030307100d540d000904210241078130742001100103010400078501c80c5101c0000054150700d031808110640c1c0c0e1a04400340100144582449410b40c004202c56002c4c3c40b500303698510201c484030003880c0c5070b02c03684080f09001d40452140e81039640403009204454030101c01b11403883c2c50f11005c0c50014000e01c0000d120b210349170002c1004400d0b40b541d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 491583012 1250 491581762 491581771
    0x110a150e0f0312070b01050a0503010501030f060b0109030f1b09051b09061306050d050c090f0418020a0605040305160b070311010908070804030210020a02090105040b061902010e1b18 80
    0x40e5449040c0c10f010709249a000754a040791120f0000c40180964241103d80318001d04080b40280907551464407001c6004c92042000f802d069102c800c50000e42c1d018000302d80040d680702ca40b03040000c1c881e040009040c880f0070f02c14440b41480c140c0004005025010311801601c0301d46075041c4001c20007002c50300d02d030300100e0019003101051000c400364910aa100308000c1046844a0366a4401091914100c560050008040010503c0640b0203502c800680e01c40150042e1000150242016046c81d0301c80042240298071548030320012402d0382d4004043e1048170721602c01c8910b0750154460303c0d05c22460381e00402100120520a5401103841201108038055a03080001650050ba07200e0005503880010162100d5500007410011824000f00100d80141140b01422042040760700040d441f40061041c248143e0f2140d603c505c05d5610300b400c58a0707441c20581102d01d500060720b00a070180c27181d1980718000317000303200301c007204482c81c000c00704500000200080c0c0340070500258141c22800c00750 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 491584262 1250 491583012 491583019
    0x815061b0102040608010303112814010e031b0a110d0c0801020a09030213050708040809031920010c03020a0b1003050318040609020408030409020702011b110a150e0f 73
    0xea1100d581038280b005002a103541c0d40d808500e0340c150f00f00a0030042a6040050311540700030396240345081e88031071185040c507003034120410b285070301d003461604083c0904040c003040d4a807460101407084004014803003d1000100e8100304082000e00c207440d41c40300c2d8005801e4050902c4402602d03d0007007040c003801442015550011515481c4003030032601f00300c01080c00301d501c0c90381c14401d40c6080101901c5c45040d03107000b4010341c03810080060200c0c101800003072410b01e002c6060303049980c0c180100302c0134045202c0c030311152459a0500000e0300003182a010030201885401620651207241d076120480e4054000701405412595030780180f01009000d0344c0f90007107090f40400058010700c001e0520018154150a0054042c1c040004803000c590144c98440c4c410002044040004030950b0221740c640d00d00142c481e4900d00050301c502c1045840c0c83e15450400d1180f1041002c05811074640700c1c4255680c00109880720030303c0d04807410031601d005c041054802d000300e1f00e203484030031481e4602018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 491585512 1250 491584262 491584297
    0x507060504050a1b080709020301060f23070c0e0703050f0712090f0f030201151202040203101d090c030d05221e1701020f070b04081608090f01081506 66
    0x54483c3d016841004804d000059115101008104030400089000e803024000c214959450304502500d41081120b000003804901014618440c01545001101c03401c040d003a155982c0c0245810b41d101820390080841c0801c059000c02d81c1d1070f00c01c5c0300c0c10784104404034421595843d00c3c01d041e207541120540701c408003500c0e60001c034000b505030900c02c05240e2040c45000e0102d900303417078040e00351064080640d02c044c2581404201002c81060b0602c05c0c250107884c0141d407504c40c4d01043c100c224042d000012070000b4400380d0180010443c100b9031051002c0415544902650b50401d40c99043d0315036410000740090000711400419454103031011001500c86a076850360701d411120f1480507820303000100307920706c40d030400407420b482103c0400c0204110085117409000480381e4581d001b0148050800840c43c030009007007110315003c50711040f6085285d550b4001c0d60b4541044240c0c00404407030b0086050b0341d5281d40550241c040c40d80134101761041c10185200c1a001e00440e600f00e0f0341c0401740003076103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 491586762 1250 491585512 491585533
    0xf0d0f0c0c0b04061119020f1516030903030912020901030b0c221d0f0106140c0129180703020d02120f07080603070308030a1e0f2a050706050405 64
    0x2040c0140014040703034031170282c00300c45550100d060184000070000410740258681300107036108907a0080d9460101c600c425400100c0707042070b03514000d4241d003213034081e1000c0420050580003807a01d02281d21a41d544040c194807010580b050408010000390031040c00350050000410880400750b000480508581c00d080e030800d400803a5050347d4103401d11341009040244480f00000107005500004101000c8190a2001107030320143d90501c280340c00c0211100420a480d0080000c8681f0192130100034400c0107104c144500074504e062000d1195100520240469402c2141c40030782c1544041c2403400da40d9a504078290040c1d0b00c4078041c40e000301d908000042c145103860700c03130038015882c2c0103c80d4003502e416080606405405041d441c030a40c0000000c000085026084952004000d81d0101c1e03245050b40008024429040c0c205900904040085c0e04d0032010342c0c031001d101c0e03084200c814690b90802e0b503800075420303c151002c00003031000c01083c0c0200b0860340240d500f29103d602210342203074a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 491588012 1250 491586762 491586779
    0xf0311011415010203120a0c02011e050106020139020c04090c0503010501050603090307060e1e1005010b090312160c080f01050705031012060618020403050f0d0f0c0c 73
    0x41c03209810325100400500c1411000542e0003581c10000f8001185420340c002034840c0a51001081600a50b40b42d00c208803c2c580700703410195041c55040a6080404201307460500a01000d014220066113021441c41c1c04454117006505541000760100020955203103480c02230107a404280b41c2540302c6c41c501210981c44074031404025a0296100d444c0590070b141c00c260035181d040e071069200707a40a009024050a0100403950035030380c0460000762460f580504a41410100828800210145015103c443d4400b10b0a60f030f01d0070340321074100400da0f02c03000c41d4400fa00408020715050340c884170102010b444050000e182c0c05894401842140007595203a01c600c0416070003000c4580c00400c240040410b090103016040340040c2010307070031440d04034174070a0046410b10a003080742c09103104890030700a4550001c8060811030800602d542c0b4000440c03c06540180300885a0340703d080c040b0500e0b001c0c040f4135400c0b5000c00f9a0361050311505d140c41250150071b000750955803050a40f0b00012500d4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 491589262 1250 491588012 491588021
    0x6030103080705010f1104091d0f0c0a080109020121060302090403110118120e060403021009051e100c020d0b0f0712111806040801020301032609150a030207020301090c1a0f070f031101 81
    0x1c1044000308860f110802c28003038800e2842e0310403403482e810050fc002c0146c0c0c011110304482d03207000d031030300703100d842c01e40c89a002408555002070340001c6408280410f0680c041c50326251100d019001f8080b42c4000c0d4104440784207400f80103408000e8107005080b4183c03003a154440d00520051089041c50b899030001245003d505c006407005c90a205000c001c1d1f0b09082e48040c441c01d108070ba0280c0c10a200c0004964160303007a0320340030204a005100001155070300c400c03100d1481c1e0032480f07541d054607240d030200c075903a24280e60400c00314a4842d00e00300f00d002c0600440c81310300d10240d8400d0400070450802168850b81011490b0300a01c207020200b6a440240302550085000d0405141c2510440c80465075021008c04004a040000c020941c4207031605030715007035400b408044140e59000c004004034000e0003080300007507041d4244101c08050141080503d020b84080c40c4000390304c44000b0b04094068481c044040b00315100038803400c40440c600c41011009903020381084101e00c200c1008590868 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 491590512 1250 491589262 491589283
    0x6010c020f2206061403040c030605040602160c0321020703060e0a140105240f01140c0d0c0506090114040b040206040f091a03060c07060203040206070206030103080705010f1104091d 80
    0x2683c0c816041107215440b101c000d928045103101e0500d9418251540e0b940400c080c00040d2945440300702180401200d80c0c12501e20301c0503000039203205151031800e54216403503884252030081c884807009104140940f035190b914202c6030010404d15140d039448030003415034504d0070003e0340140c4854401080e5074070301d09044042d09078000100c500d4521500390821001861a06001c205140f0442164a4029883c0d40c003a909003440b050070030142e41084868130442c0d045c44100c1c0580040300c28429042401103071420701c91015288641e854052143c02c0b6400d1a41c082082003e00c4041404240c1440c4100d40143c005030076145443e4844496150700c01d01c42e0302c6040ca00e503885038204885540030071200c199074421800340003036040c040780c178640c1d501034070802801c41c40d4000040b404541d1500129081035070301903e030703988070b6959040c4200650003441c810fa0781c5500b403503003900286080d031160014940b02044054202801d0441e608002e240459009951030384c052407a40f40b0079010000070070030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 491591762 1250 491590512 491590579
    0x5090d08070516080f07061d0429130b0603060d05100501060c03081803031602010e010c02010b0a0e100303050f091e12011104062a030903060b0906010c020f 69
    0x500e0300c4e207054505607920b0841001a0880c24003440681d81c0402100141076030881c209110080100001f001080c00244100d50100c141100da001031204074150360015004803914004120300c1d030740f44c0c020395403040c40243e840101080010407034903060718810130a501510460352003902c0da030800340441e5000e07000304000c03591070450711040540c841c0000d58064101c1d03008440d00b00c084030440307540707006c050118090b16850403018940c143c403d601c945400b181120082c49000c586050282c02890b02d803640601078000340402080c0b00001d50340e1540076010031100c8441191454504031801d4000800d81c1e9030102080101c0225981c44200034084100c884901d60381e51000d5108120030041d50750840c0d0500d90501c1c049502a1040d00c056904031007103401c100e0102004000c3e00580030008003c0800c003503044a42d40814150300c01888001e0713901c111000c001011000e81004400c50342141c0361380c0040c0180c2c0b080001814000d4640a00410207440300720700c402c00013902010b017001d00354200030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 491593012 1250 491591762 491591803
    0x203040c12060f0506031501170a0812150a08060708060105120702010f0c170118020417014b0f0608010e010f05060a0b070c2d0b04050105090d080705 66
    0x15107031064814139400490850040120000c0842010341c03002c2e0500c607000030100010482020302c2402c0c44204270b160703800561640d664110f8050240310007016244c0d100980107600410f0014204911140c0607685c1300300041104d9510741e40300312103228000b00220704125040c80750102d207810417003030140190b4981d000462072041c03252400741182e10f000c8110003003082c040c5040010031070102c4220b064510305481e020707a104015060710040d2007903501070f41c0c0d059004a85a00d0b8070300d041d405110401c201c0b101541d0440c503929403884195902206000d21030b084031215440d580c0400700124242002c1010205200254014203030844500d0743c40003a5a03515890188803101c401c0c41480f0100c54010780030807003814184080742c03130040c05000701c900c032460000e010030902035202402c100038014890141e1625221948045450001c100c8840354001100ba020900480b44419101690010703911981030031000300400c003200a50700015a040d82080000780042441030003011906040141c1610 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 491594262 1250 491593012 491593031
    0x60c1e0a0e0301141504090215070c14030111042705010b12100e0c030406021201060c150605010806042a0302040807080d020c10021f0518030309100203040c1206 71
    0x600b9139003c00c48542010001070200301c1c01c0c10780c6404001e4980420341d400203040c80a440819404400501003d2510b030010818100304110140c1220a5510b4011070505800d0440241420380e4050000b00b020500184028003104c0c80c40320141e14154050145031003059030080900d001c8071800c0c0c0014a01d1100062031503a0300200009150708060740760480c0d1b071104e01c0e08095102d81c030005003142804000c00004036060121b0703901030740d0a802003034829646d1541d44040240010019074000c60300312081600d0000d0303458040c800d100c201c07101030710b41c05040c0c2d44010400000b00508209600b45c01c4540320300300c1e51585841001c0c41d40c0c088585005030b8580c241241e103454141d05e07910400b5158082d81c48008241d40c040303450b0400d00d400355240c0107580740c1d042c001e0707090101082d01040d0f4900b800c01d00720030421040e0000c600a00c1c2c0c80401c101c0b020745070350280b9220711084402c1900c9a001c008034400000d000d500070350380076010fa920b00d1502a00d0361103402d841c4546034416583c06440d030b112a0b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 491595512 1250 491594262 491594269
    0x230c030601090b090906100c1704061704020f0f04091a010906150f03150e1905100305190302070812072f040e120c1b0f03060c1e0a0e 59
    0x110050822a0f10080c00c203241d1400198000302c0c020030b114000c075000004180d005003d100c6c03e46100e54040e42c07054405410300f243e92005d030450310450300000c121144042408009820f914080e503000f52503000d09561010078480d40d10382100798203030840d40e0703800c00f440450071501c0d4070b040c0810714a4030721510754076011106094510603005145403a00024110803015040405400d581110f803e000c1210f95120b21818403001e0141c3c40150440d20b1002007128800d001c05002900500c856010016503c03580403030140d13134409002c01820f83c1c1c4940369074894030760b52041070524035101c5d1044481c26a20b4815040c02e0005940b850a1800004901c1404000a1040564081d0301c1e04d203600d80c0301b280328042003407403c00403071405001d241d8800f121840080d0a0010001c21440201d2165a5030914000b0b00e64421f022841c0d04e01036810745210f4086c45c5807580d090703145401c0040c0204800d48590030440700950082d090042c0240a8410300191214a00c02a00e10f2005036105d41c410120b120050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 491596762 1250 491595512 491595527
    0xe030d020c090f0c1b0c040c17011a070206090d172d0a0f030621110402030c0712090305070e010611280303110403060207020a0803030601080a230c030601 68
    0xf0203684005040203914074042c001e40d80d45800c00c00e0801100540880003a040034002c0164540007800d101c00140d000c0d030411545c009044108001060701e0707a840080728003031a0091080c0034008402c220f4003000d4509507001d4000441d00500e00c04405406a4407078003000184240840840400300f10f100c44070040910001480c144180303005030012a10703080014900c610603e1405100040e0a2004524801c4d0300000190080c54a884002c41002210313040001d2284800c5400c9103920001c9500d0b82001d00a070303400341c2e51030031810303080009550f9600140c48040c6010700c1040b000074400004580204000c100034808080c0387d2009504000d00280721902e90140c2904582c0142c600300308082e449040803800c50801501190340b0913841c60210301604009998400c4140041000700c2409090303801480118402c543d462400c503500e5400c0c81c0c03240011500c0c680482c0c0c00b4000142c00b0246e40e0800c1030348a411004541890001d440c020001100955100040040c0882004001d5070441d01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 491598012 1250 491596762 491596771
    0x40218030f07081f1407080615090d030309080c060112111f050d020d020f0c0d0207030b041e0b041a060604030c031203021c09020310020c03030403080402010e030d020c09 75
    0xb8000c040d040040d6596903600f102046a421810038824200c142e09030b80c060640f21034450f06011320350901c4500180444026100e040c416424840180d40b00407036002201d81085010f0300c100c0200950351030540c000e001400b816a0030000c02c20521012140134000980a0310308450501d81c90380142c01d10803c81e01c3e0413280700d401342c2c00b081000d1000a0302c007121441c0111061404550719010b0402c404060302074594941c01075400490110350425401c0050048100907000f200d01a2031240c80490f40c1d1101880051725442c2c000c400714000c00e05a11110350b10074500002108400c0346685c0d6520260310840e0290b59140102e440c40c3c40c41d2003041002c83d0001b0701190014100ba0035a10f0b1101011038a200081412803515aa0440035019030140c90b0000c8180e8659100540403c400c10050960407030100e2003401001c1c601c2c0c1c040c0b0b038a4803d44040c001180c0c000c606583e40c980c3d003075070a03c4014006905001225190302400d07581040f02907a0002c291380940101d4030701da000c0c000020400780 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 491599262 1250 491598012 491598043
    0x3211003020603130606082d06070801090f0b0913020f060a02151b0301230619030f140901090501060509061f050d15083007030e04021803 61
    0x240200302590302c0c0d40940390400001103020b40000200c0c07910a000340100d81c4220302030b0142c1559990340d000c9034619080180c40c0030002c6a10107440703c5800c4c2e21044216455408610b041c0300601000c0d645038032070007181260744400242141c1c03080c0000c020100440e00f00f507072240741004403002c508099829a80384182503605608000210a010f51501040c00d80d181c0503182000c00680c28400100c80f250260700703120501340c1da958454411b551144408803004450340b80c161101903c5051a00c00c40310304100c141100403001c10b0049045002c0c000580d030050800b031326020034204040c1c488407224000c80d1501e000003400880f81c41c0c0b46003581c80303644c4402e12a24110007001283d13100d0891018502803a41c00368116203507003840036610350003a003040781d44842c602040c0c2d542141c4c400071306070161100300c0100c4100c0010401021080101e040420140c0c58a4607480700074038600e80040c1c5121403190070200d00c600e82c04008201247c000544480c0241004c100d900214201808200f90340700105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 491600512 1250 491599262 491599291
    0x1050f04060305030a0c050a02040603050c1e0a06030f1401150f0905180612030f0a1b050d030b06090411090414010b030c07020f03010c0207180921020f0321 69
    0x688502c4c1e128001c1c40110400d000290710184100901808003078412940240b0810119449062543c2d450511625142c0190846011a090200480000301807003000402144c200c41c20180d04501620b56624606513554071420300d100d13001c4c480d0766420f0207001c00021a0000440c8110000d01e03084c80390b1420810300c020320340141700e10b48860003848400c40400e90111a61344901c00070800000160861240c07600002c0303010040901554000c02400c0b480c0e81d2412441c5613484d003048940d92070607000400380d03030080c50552909802030308042c0041c40b005007181d042000210109068444440d890b0510150004114155103490704c80c3c6050f4500c2002d29056030f40c106003807000c491201500c4260600c0011405404654554103880d45040024000f0f0083c607e001c20040d5030b0365a98040c031000304840e404008000300ca00c0c4200810a9000104020104181c0e40b0403903044003030501000c11409441d0020000f60390400040144003000341c0e601d10444a03494a0002410010f440e89003040350303d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 491601762 1250 491600512 491600519
    0x20a170a030329040b030f03032802030609240307090e0106060503060604030f020f0d060c0906020c010903030c08090907090608010f03020924040f0f0e010603170a02210301050f0406 80
    0x200905008010f02a10001043d00c1184006460405503150f140d00500c0000100890400c9640580702c154110042d44007070b0034001c51070702060340401c45440c0d40bc00d141c0400a14807904612044614521010a48014008580100b4103003140da810880307080da100c0e10f91800f48075092140138000c01a80c5006400c1d414890001800f070710881c4000f41160410346000401d640e203501308401114001001d20040c0101454464098000c0700500381c040703111030100080c8240003203204803000c04140e41d043c1d040390640d40c0030703612400404416a0070400c18002c103145502e0394461540a046903845038480039281410091407135105802200c48900c0140703040005845241a003504140000f00c0e41c0280440c01128591006040c903895130f106040c48200344510703246901944081040b950305000c88104400036030300380e4031988001010714512071400c02c640c0c2e1090000d08242011881654038079034102c858070200500c0d100003280d00f906d00100400040c58801044003541a0549080c4580c614 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 491603012 1250 491601762 491601821
    0x80f060a060806131406070e0906010c0305041208070b13170a1211210907050f030a02040207080d06030b0f0708090c040209011403010e0a0b031605010c020a170a0303 73
    0x1000c0c04c103111184132051003004001002e6008040a5090012940c4c903280c11f503c000c1101c14407450182c010b04c000f00106410354030031700c9a04c00613a00350f04d07006d107010320f016913425503102c0105c0250340074403041c04000c0000b081140343c180210003140454004244d1410501180c4c2c10051144400380b0b42000000d9480750801c94006102040280009e1071051403a000c0b007207489400c4924085a1400140d011a038404181c145e000d11403d03800c0311851070b05c4c0c40c103000c21400018555503056201954a50042c0f501c3d400504c1c0c01c40c0700e40c0781c25060643c403031020003d0f10301540086841840c810100300e499895401c00b0356001c8114613261034141801807503281c4884102001a00a60300007a4108090340500d00000d400800c03081410360743e40e9201c02c092380700c2109403a0080340905009040c030407440c000428040301c2c00740c149110865444d080054941807800b08040b40c00240c1c107200000c0250260040c41c5024103c040508200c41c9240380c01812108030b218080014480031015441c0304c070 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 491604262 1250 491603012 491603023
    0x1b030f19110d020d0e074a090c04090c0905060a120804030512070b0612120c16080c0105040618030b0702010203070e0a14120106080706051809070c2406080f060a0608 73
    0xb01e0360300100034403403824103002d0f0614051f11550544d2040710318a180a1a01c4103681a00c185c020302c1c1503404a5044004002c141e50b10400040d0200c2d020361000d0004641c280d102503000039006041d030451690340c0c0d0049201035120002a190514041020000c3c020140070a0555051f40a0410314002403070743c40c8042081c01400c0c050042c0031844c1c0303902c41407008010103180d01184070a00d81d11442d0300440c3c02d994032070b265890f80102c591503600054502c00040d1008100d50140c40d03090505040607000c8540c1d00214155a0070607200d903000101181c141000f0781d0040c00c3c40d500141e9249002c2c540504a1b580c142e1865024201100e010000d52600c1c40c0c1e031030300106044544120341615400d001e409049207030455000b80c02038207400203c030b54014000b000c46c1c900100c0008000c515800030005d500303104466804c041900c03100e8100000328000d00342c12003810309002100c0c41034400340400d0102c4204c3c0d0850a52644441c00b8275000c2203080082540c000c4050703006214040c2082c00c40c2c1e0f180c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 491605512 1250 491604262 491604299
    0x10803030f13140102030c0d1812080a0207020402160b100f090903050c030d060302100203120a02030402060c07090b1309111210141b030f19110d020d0e07 68
    0x4294181c91040005543d90110240d00c000001c4d9201d04100c0b60049240d48000b400c081ca413840d0840964510b925a940349003855000f44c0e101c05890440403003030341c07040700c024007620406508200c60001680c440c40a0111641240100d081a540900d08403000c010054600c017650fa03400d820400ca08003007211100c09503a40301c80007254090440c5810f42e2180249000105240030220b06040440030f154001c0307040340d000325514030600100c07000030790300c0307104a00840e207400c83c0c401c1c00507441d00100c0c0c00a54000344081c1486d483c1516100016082002c070303400c80b201e550380701c10030520145000c6c0000c00c800449030340c04114650250792482c4404481c841f4440c000c80c5080c01d960071420307080c051412000c104940034402e044009503a111988000c40e000b8804804448039231035011062004e481c03062404480300c02c5e46483d041210b542c4a00101401c00d11103480d00c810015148407031000c3c18401c000340700d000d81c0f01c61200290200b074829a80c004140c5600c914030400c4160701d00302a84809 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 491606762 1250 491605512 491605531
    0x6110d030b0d21022a0f0a0b1206090a0b1c020f0603040309031707020f010c0c09020408030d1107081204050102130b0711100509041e180308010803030f 67
    0x280d103240403411440201801030458a910110081c011246918520701c00d6481d0382617810f240d05105401504c4011201d02000b40c40f44401d0041321410144004c40100000600003420507980c0c186d00c0515601c00c107417985a041c204000d100041c1020050310b50404042641809807200e400c01084c00407003245844040311210348082820754030707070001034004088043c5c0425079a14280c240641440060f01c800ca0b00d41610742070080c1003d1040050b26a2158000e241e100c3d400c0a030401100d40a4011400b0f44a14800c1c5000040500044c03000384020300b102d0002c1c58403008855000d00484288400c40c00800d002088540009400d0b1000c41c0d60b9a0304400d000880c584840c00c185009004103e040d000000b4040008a038210707501b400b400c481131003080400d00e000c00681c24828030300761105505012400c02e00003011a880c041d08500c004a41c0d4088a14009071251111401e9445031080005030714498602d0340207059001c034105015025280086245060452400f40701c9070000388800300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 491608012 1250 491606762 491606771
    0x9122b021c200f0a0308061207030c0e0f010e010506070516141203030c090618040c030f0b0d0b060103020c011503080319020903070302040c0201020c072c01050d0f3906110d03 77
    0x1690752030250802c11911070b501100c0a0170340343e00d0110515040d03400ce149903803600000181800901800300b60580303120104002050f46001c05020b069004504215084c0c041c1c01095040240c454080c42c2c0200020034003913400c0c0d0715210900c00c840c208008280c40750f810030400c104c002201704040700c3c0007460543d20a0b41d180c166103190070200902103c115403003410054562219a40f60704800c0c214030701d80c0f004010382c0c3c801000f04840c0c8104090001d0040c085580040e0341340d17020b83d0292040a00320f0002040e00c400f20244425100c965800890304240040240008101080800001c0000b0302c0303404c500d01141100017035580c0d001440028416030f210021551024400c0d016039100030b00f143e0803590801d03100c0480d40c41701c028441d0074504104c0700c046072040c007050045c010707030403076034060155021410b03d40c4815201004001c41590f8411140368609180c1002c6030b1403e82100281d02072410f11580311040c008140c4150f03004801b008581c900302d81800300d020520307610a80c1141400203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 491609262 1250 491608012 491608021
    0xf061407171b010c08010b070f031d03060a020c0606090405061303050706020307092412180f0f05060601140a11120f09122b021c200f0a0308 62
    0x207a507100d03000044104500c211025414898150000c400008003a12520144c0e80c9400000404d4082c141010780301791480318400380441e02500003d2000c01400300c2c50424514505c01003480c1001c2990b415034802c2c1d002480145611051040c00d4010404030303080b45807414640c980c10303035800c0c002c0c3c61025404100e09040c0201030183d002c85070303650b501c5078081d0344034a042c54010300080f049204d640e1010040d10340d505550540707442d0443c00c0c10001d40781c001c907051991003a0001854807009481d401241510260049003086811030022031150700c1c03680e00c4480500d03100c2d040440151185043c420016441c501c8a0300078400e903090009142703045040050100c1410307140484800300070305c00c4e0718002804407420748010010041404150b98114181e074504818a0350364203000da410010080c0c606021030004400d45001d00a01450b1045a0180901040100040d024002a81d010901c40c2d00401d410404c0059503200345809130005d480b0700144400d58545900c0745000040801a6220000703 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 491610512 1250 491609262 491609303
    0x40b0307091a04050424110d0518011401061106071e091a0702011e0806060d0e0601141215180a0f0b07090f03080702130f150f061407 59
    0x60720003401c000c02c01d2184d414a4240741c00104565504c411041c071402031080c1c280d01075405100c1c440500f02c006945442036294070f100003450098422503142182c0070080415190900400c0302801c0358000c4800c1c207515100340545003c0e04200c1d1080a03401c00703c10001c02030b030050820b101c0140c05442660803c0c00030300048550107850b42015003006029208031409041038409841750390b20030713280c0d90403d001c11240101d0842c010415000080d860714005182070a0072005480018001c0c000810b685166410313803418904241c20144141525410340450b920b80901a000281d0110000d4184200c202640141c256001406546e0312000c5c1c1d600d1400c0e0103c10028014040d070087d000183d6843c451800e01000d950954100700050100c0c94080351802d40b4001d10b030708582d40001c1c840d10b01910341d801d008040c1081e80d580d84400da9154a520f81c014640e004255a09034010004c440c0a030800b01c0e4007410981c560400410404148200500f45030800122131007143c100c1c030b00c0c85035041046505d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 491611762 1250 491610512 491610551
    0x40303050307032004080f0c0a140d05030309010c170412050310030c0e041202060c0306040c111e1b0d02060313170a020d050c06070f0932040b030709 66
    0x40200741e0604e0a1300c0e01d8954907100600700b518a0081a0b0b074825684a01e9965298481503981e0303404400e03145c0c1040344030700b10b0300390540041000c1c00c600300d4031066484032420b41d00100d44c4d0030002e035120408100c45681c07140c0441300140d440000e02c0d1240c00d01d5100c00e80c1c000641a000000d0080000106020b003241032444002140c1c456100701d4110745410142624070800e48003100d42e021100818402113001280e10340c4141800b2030454210b075100c0003000050040354000406101501c0b000807003014041c401c11603100d8041095408800340b5220071032902c050240248404519040d010300640d0701c00c090841c0168048030010348036100c003905441025143c40e4010141900091003c041c0c03610701010302402c074074640aa64984413900425246440381c2202255507800510000e241140103c100b07001c040d0491510701074407030320b4545000b081000300040200d00c60000b48020311111072120460384001c0e00391400e0000078082c10120769107070701c4d90040051a40e203031000e8900d1604203254 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 491613012 1250 491611762 491611781
    0x1211040f0b0607060915110f0d1b1107090b0f010e0319140106080111030403080a06050901060c0507080304050105070803070c0b10050102190b01140a0b040b13060f0504030305030703 80
    0x301c564410051070002e0007466010401c0701d0a40348401c03c055035031507034400c803450982843d0309a0b01d03000981c810445c43e0743c8101700c0c04149e96940c0d00e040141c0c8000d035440c00029a641c0d11281082d8040d0200c4c00c0c80c088140d13108641803410228a501d10380c40b03e0066182d030104c2070820341404070341d20000a003010f42400e8140b5504801404e080c00340251720300c102d2440300081c0d0081000640311100c0e94281d07a00c0c004103e14442c810030102d40028030801d291603214222100002e90180c80c0c0c03001400d001001e900c450300280c11221208103000c8140150300090860100940c40e0500d0480003900328010a200904807541c040001142c03a4014203420070a2680000d40840503e804154180c0032021402080d00500c1090006000b522420f0f0448d1880303500103d01c15441c1e0b20b0023010380782601c0044501c40e001010100300194a048201c05007002d4040c0000342501c6840c11100c462038400300342c3c0300008100a40c0070400d500e942010884003600e4040ca01503039656207109098024128460 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 491614262 1250 491613012 491613019
    0x6160921060e0d0f03050408090607110d051006060306150c140a080d050c2115040509010203070e031504150605190312052107030e0a030c0b011211040f0b 68
    0x1c8412829440100d003c1241c1c406640301c010307184440c448220201c6008031801401c1000030402001c0c1407030308401802030300c0d1240300d0f0103440f00981008140b80310400b002c11104c60b44a203442c1078140116016690140401c0d00d03082056506d0110000c90f180c207050803c00c14040c01d55a00313007d00c0841c48a6082d003140381412a240c407051454052003c3c0e015406070b4881925020104040102640840d00447c50324403101801090210138031907041c0c80a06100070104685440d4455622240149c0e44150800000107849240c1224007030181402c840c0094405d810200c080015070240900d86a00180c0141c1c3e00e9074890741c108030728001896603403c01079010721401c01608044541604078000d40c0e102e64141800c0001c4240280c900f4003030076558807001110a03003044002d903c080b268a91102c681d25010405403000b103549400c04546d82c20a5002410490f4101d09011400250364010081303030039000d460a036143c030b8070040d05031131100740351103180c1300c070b403122502051030300041407450004 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 491615512 1250 491614262 491614271
    0x260616030605090f0412050903030a0f1115060405010501020a020102060c1e0c0615040b011704020d06060312080c21040f060c02011422080d020d050103030905030616092106 76
    0x44c000c10100008550844400881401d001c202ca88104180c41010030068025800c1585500c0c06440c280f40d4805200700300300c180f25035003200034401c020400a0b1144200704901a04028041c40261841604098152f61260300d000700141d03030003c4c58a50007441002d206444a4042400d8003440c82a807044403552100840d00000b21640420064000c04203d041190b0104c1b01a05102c01e84d00c0c24000c0c2c1d404120a01d041c90200401254030551040c402441504032400a558410880345560001e031072880ba400192840d240d0401440c6801c400846201c504021242c128400c91402c03034290b6010207071194021804004c1c002031501c45941d44140184950541d03000700900170401d01d0100e0070103a05203808101c0b200c070312032408044220041c0c03d03404330300d40c43c3e140e0742c00950040d400101216400c00040414540034130030a03010f14485e030384504540303186c0700c01c01d443c108019000a003442c20007041400115003200400e021903207900c4403148a52120400301e48078543d000d501410351800e1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 491616762 1250 491615512 491615521
    0x9050115030e010903350a060e13080403080d0f0e21160320030c0c0127030b0a0b090a06030b0708010617060a030212010626061603060509 61
    0x180c4200d042166455034200812210940302c18280e804060b40540410494068107003012081c00480e0190159a88842810400b941d0000000e6208840d444e5440760313501d000307002d10b1610000d03190300110048008000310819032a42d0780244070f6440010505080003948050219090704554503400380d42104000040c07040c581603803528452101201d54078911030380201e4000369a800d44400c10829401705040005654055508202c410054100c540b035801d8040d5803500f0800080c510b00f241c950180c40c1d0341c445880090700d0044550a8820010084810707a0760b15600380b1000e00850703070000c1c2c0c020304613110020f4000040c024087e00310b0700105c081d41004100140c0c1e811000850b071141e88040c2a655842c1070803a41c03001c080c0105400900741d4283c0f0000e080c1c08284458002c48002c000c2040c942e0740c1d5000904205a8001051080c1d440f240100021444100000d9819603001c424490071050401700c96201d032001000f2000c411210f0050041891290b44140c0242c10b018140700c895041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 491618012 1250 491616762 491616779
    0x1d0c27040504060e0d020d0e060c160308130e0114040504170f0c0d080403050703030902060d0504050c0306010603020a0903200928060e061003090b100302010207090605090105060310090501 83
    0x8060444d442900c00c4000341081d040c80010781c1c25040800366101c2c0b403500d030343e1020040c550b404400340110a1040e020555001c40e00c10281500451249055a686100c1290f244c3c0c1d64510607440755840340cdc03400300104142240504200d0510804a07400195640c551134000c107510701b404200e8940200205420901c601810028200441d60b1007c490038203c400c030045030048021200140000d01c180400740001e0301a402c0144658030041055040074500003030041103400c1180c050b5610342c4510481c0c61182402e02480d0301400e0a40341c1035141442d1550007500a000701d12000704424021090807007401ca12a080750342004000b00b596845083c00f03004010b020207090022281f44c654140b0000b8191071038402c1d8001c580642941807800d0703513088108082c5100464620382455100c1c01e40c0c100280c0070b2090f4601c44c405116140000350b003940002850078401d90040d00c001480d0000c01e118503070b2804811070444000303c580039a20364441021041c00d4000d0707070140c440c1a0401d4008103a952 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 491619262 1250 491618012 491618021
    0xd0515130c0315060c05010516051903091505070806120715020c030d0f080c040e0c0a050702030115060e060414041e18140a0b040602090612101d0c2704050406 70
    0x14003481c0223002c1600c071078064150000150b103400d0003103030041100c04c6810034540d0f080b000101745414001065403440d240c2e1103421042c1841032040e940d8500c01c000c41d054114071300a8000c01c2c160392160b01e808594200300d41d603c1c214060141c03140c1c007142c29005032901c01c0241400844021b42034030b0240c40c03603180c040c00e00001c28041070040340d41d5000090462200d50251411980303c00b040b11441e403991450352000c2e40c4031002074402c004003044104090b803024003860140c40040d0203c480c0603482c1200c000c100c02c010b005014401e0f00200310400c20640004185a90440100c1d0001000d16440000c94004440c114031000c0342410010361080800500e03652100c10341c00b4001502400440c07104490b101e80351550001e094040040116000c0340040c2e02074038611002a10702460002070302d4601100b0303c803c552690140300603883c103000c885640b5003030b2060f4143c01e0302410168184203480e940030740600c02070044610030421040c481c2801d800c034030006040700030340304000508090500b40080d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 491620512 1250 491619262 491619287
    0x228030b011a0c121c14060907030b031506220c030f110a140c010e0303090f15070e0409080d0c0905010503150d050a06110d0515130c031506 62
    0x60602502e81c0722071081c04049425102c1c0d07090107407103a4000318201e08a5500b1400d41c411070700c9094280604009403030f105180003d00b2004105081e072800c84200b001d50540107084004050034056640016100001c078003050006084403601113070340f6000800c031040c0c900c86104100d0310501004400a0000d40e0201b918070005a4091020760340407500c3d241551050309407512085420428080d499124507980c802c0c044134492030304d01c1c0c100c046804034290741500b50946900d400c004248455000100085c1c42424013070350107010858042e800000510f04010120b0b8144076900e0152141a80e1300d1740900025503104950f5a215101490708400400209050801140004501190540c040c806592180c0c5420320300084000300402401320740184054115218401c95081c0c60000e110381c002d0440400161341c08540341c2c5401c65511303040d14409007000309076922044001c0800d46400d0180020b41380705080100321042c410401301c000300300e10203480c0c0702e84d200fa85c1d001c51055404980640c81 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 491621762 1250 491620512 491620529
    0x1118131404050c090c0a050d150807061b08041a0705030712022b03090503090a0b03060a0e0906010306020a1107060e1009050604030f140706050d0f0b01020a0228030b01 74
    0x890f10040c05801d0f141a10008002d05c0c0a0004100541c0f0070001407011941504011601c0b45c0340451162103000c098200c00b5158001403402c0c02030a50101c03545090401440c208400a800b9454036035181c8228003440c40c44d18081c512104c3e912040c481180c5540c1c0d4807030100c990b500c000342070414060740c200301c054005008000480c0b40e02c0d4055001e200003854504241180e0001110741500181448403007120503020038000340920f0b0352200c108030001c1c441c440e000707a41c902d046d80410030100b2180e04000c540f40c0207142404003118000a00360f054991140c00181d40324540d00044d111f0003500280b440c510b01ca00e0b1b10105a17203030310106501070f5103810346481c40550382e02c1c002550304990f10301031146c0100c414001000400c4228008100d0305d40a01c400f1070001a082001a0400c17400b0340024012500024a004058806208080491154040800ca00703c08900001e445680050300640708940e000c54000071022010300f40d21040f001c9609207403d00e542d0349010510068244184400e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 491623012 1250 491621762 491621773
    0x1e010c0f081209010c0f0e0a120c08010c02030f04030f0f06020d0b0301051302031c050c0d0504050f01080702060402090a0f0c0e040e0a0803040b0c090a03050a05070603111813140405 80
    0x585014082da200105c0035840302410341900500403524451000211503205512090000d123808200d05d0b11a201d43c01200540d0019042244140c250785001d03498200b1907008012031500f00300380800351001d82c3e0f402001d01142018500381002001d141503c00780c43c1901c00100c888064015a000c0815400140c00078007059848203080c0c03c0490046001070741607040b03442034000ca4928035220400740500b40c1842400c1407282d5070b20a15100c4410750b83e4003c2200000c00380303c0c42c50030400d600307074166091810b482e451801c403100035200c0340040c1c4000e0092000030007003583c21555404c041d0000c10a0402008040ca4a142c001d0000d485c604905001d549050016200540c0c04142010302c950010305c2c1b030b8690348a0f41d0300c04684090041c488000c0440500c014081503480c55a02c00095024600500003080303542030450a10080303520400c28940f41130060b100400351142070b214007001002100001d0300c00742000c518501c0d01c0341d001012091810400e403003644d0101e0340e0315029a002d81e08484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 491624262 1250 491623012 491623021
    0x1021f051009051003241407121109010503090a0203030c03042301140304030201090501090f02120d140c07030204051e0c0c06043009061107051e010c0f0812 69
    0x81100d5065606503104d5a01001c10b0020036030340c10b06010603001d144044402d00b1070031001ca404072465540162130000180060101c05640803100242c0c2007080c04042250b401d00c2c9c04440b22074402c0d40120750620070040b0004d04042002d000709404140c028040e613645460034a2501c2e2258002d005415060808942c1c0a460f403010f040340c2042003070107840b0664201c01d2007861301025040104214115921a030fa2580024002e0258041c2644501d0040c0d120341668810000c09014900311042c071a032180c0c3c02c0306491a84002e10100245e9545c80c1550340b01c6810120900303040b2180c00103900305007400300b403150590303401241180c0d40c140765000b4261900d401d00410b00c2803060f850120760f660300000105000c02c94000e40090804c1d480143d4484d0030291441c0301c3c2d0000d55940065011270300300d2034108134240d040603006504203054000b40c941507040c80005031960481140b0131007080780d0402946840d03400b80070a036007a1a0072001101040542c0c0c5483d0901d0741c00310f881030001c3d00c0c415000c034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 491625512 1250 491624262 491624279
    0x230d30020f1f0b06041a04090b06070309030311151f080a080301050411120406050601090f0b0d0f1e020c1b06160309090905010212010602240601021f0510 68
    0xc6200d152201c2c448100400140e0349003000d40142c0c0341c0d032507002808200000b0036000030031645182c28040495191500c0c03810340030100711a49501054003d800c00c000c3d901c0000c0d03008800340166641410140c0525420400c45490440b0180708205243c501605001c410b0111400e01000c07041c00541c540310a0b511048101e45807030880c400200b51a4040c030043c00710f407405400c1800e07004c00010a09041160000c540f826219042d10281c4100ba42d40091080b2943d112840b030f03002c2d0551503c203d400b14500655811140f1075032101d0070040e80d862501102000d9150840c0220a403034090311304008681000c524003d43c00014451000d20500f00711702c02c0000001001d82001c940105814240401c5018541d811200e10104070304100001c140421125518801c404c0c6142c094000140c48044842d0121810241a0044001e43d84040c3c90076610041d03040000e02c0c1e0b2456405900e269803640c00050b40b03444052251103210b0b0340540341c801d5504542e0303072000b8880c0c40400004c404060751000e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 491626762 1250 491625512 491625523
    0xc02031e07120f0602030a0c0809010506061c0e06160815010f030b15040b071401020403020d081b0316030e0a0602070603020913050406090c230d30020f 67
    0x10314068002550400c68814400d0110224900510400b21410040e5644100301d0384110307003903030b401c3c1c1c2d40b00124100303958040701d22170740304500c1002042241411400200d0a0240154450f8500d44800c00c6000b0500c03290044040c82c4102e0003103c0304c50a2403200d5848000da641001c6000801e010000340854184480901000a0603104c8190070780d03aa403803c401806e1004001d0b40c1180300004200b031b401d010400104003c0001c0b8101c50780354512440c0800040781e042c0307584000c41c0c1c014082480580e4078014030102c10f65200d200d1965070f0b0201408000d4101c046240112a0301020590b0400516040c0d40c540500d03100b0340d078024004010400b00041801c1f03501684005a120708010300040d4007a500070150201c0080c51404074200a441f9981551000c45045401503241c040210130481000c0c0740501804140082159030301009040d1038400e40c41c041c030305204d060005291800c0c040003400000d8104a107481c82d4809466004001468080b9507078020700601c01d0340c2030078000f503e000c1107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 491628012 1250 491626762 491626813
    0x206040309031101020114010b1e0301030c27060305010203040c06020f06160201141509011d04110a090510050108011208270a180c030603050c1516030c0203 69
    0x7185828203003180c03610300c151032021644506543d030381c90214180342903900f440c1d0700a111551003c0e44c1c42840f15412001a4040d1307184915a000034001400001e90b0845910705036040410111400106205070080050740c1c84080f03082e242c5061000300512006400852240d03009900d040c030030303954400d0300701e0703a501c48040d40410a800100101d4500381544070348140f407101a100109201c02c810807411440b0b0020350760940c07188500709100d10181040d0381c569004011101c100a24045a0054030400c04001000102070803403680f5010800e0340e500c0c0c6000040d200f4241e0800240c508810781845480d41e5000c1e00f400314006100000d0240102c0010410343c0707034880300d99420011880c0003102c4580070002100e20241480c1d412001d10f45440f030501004210340300c61484241c00102042007201c1c40780c50640c0c201403c1400c10b04c0481e00c00200b04041000695100410424080c07400030300d1300850b01050b6003002e500c1414802e266120400d04a00c900803400d0355503200c20048042003040e0440b0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 491629262 1250 491628012 491628017
    0x2090c040e13060b041503060c0906080714190c0614010503122a37080a0c0c09020c06010509040507050d030908030d0e011503260c070e070f02060403 66
    0x40000305a801c41e01040040c1e07a101d0f110100d440e010035000203007a50346009070094044c840e400c007002440600d01456141042d06c0c1050301c103023818050010490100108141d0070312490710100d0a80d41002d508682031001007100031000440da07a18001c010b040c400304140c0d580744c20301d003c56401100607200da03412144003d006101c80740f005a483c2c031a503045280c081c0402203800d40c42d07070b0222140c2004800d1a602d020050412108440c003010782c151081c078041814103074401c01014480e00464910b0000c0c5030400c1500d9102e00c52403030b084500006010000380000100100040c3c0601d640c0c0251141c6400a01030b21220b030380f15030030301800810403100504203030b12218082180c0e003003801400385c81c2070092609242c510380701ca40c0549194010407084019981d54003411208010a00c19515001f10700d200131064140366803580c0c0c045c001c1282000e248050901b011107101a00002101e01c2c80c0c1c107440c181c949195640040d841490340441c2c440e00170681802046003220320202e402841142d058 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 491630512 1250 491629262 491629289
    0x22080f120d0b0a0503060c1306020f030a080a02090a08030a12180803091e07050108090a05070b18031002030403080c031b0f0c011503051c0e0f1504090902090c04 71
    0x62050340040c1c40d02450b07441d0844101040404e141e01c05001091041c100341c4281a580c04200c010680004003650090302103420110028442040101c111500300c0d96a26140400b5251900c4881c028407614000607403155428400145051001c0040d00c1c0c203071324a80b984445110005590001e895000d048000900d444190440004194201840d000710f12281180c005023980d911281081d4510f00310b1500d10303403100b00108107035030b841101c1603402000a0094203804543e5510a5920b40d1140074104003040e000c64000b00c80040c0c15090499030342c00404545a18040d0507a15009500580d4240c0000b030b800c400103118016440704132409101100380000400d0344036186180107800409181c1414017003003004204900e802d008240e98480700c0d140340e90ba040d1451400501d4000b41807a2900441c0c0c40d0001d11110f5504056551000c0c401654000d0450000c2c5000442c9084180085001110301240106684400368404840144281c6486000d9120f03c0c4600455000320701c01c40d400d00925 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 491631762 1250 491630512 491630527
    0x711010c0e0906121f0b03010f0e0a0311010b1c06061203020304030b04170c1006090c050d0e070902070506010f0f03151d0106091e050106021e0322080f12 68
    0x144400c03c4010b150442074070301c44020102c40c901d84d83d155101e4088806d450307000320400c0386402c0c030415091341b00c0c1d82d0007042000700280c50b603a140c102d246000740c14041d0405c14410003c000b0340003408260402088000059070240188102044880c000c1e1a50341c0351207400706448500e60f184605040d010b0300110f050514640e142c100d080c40c000d004459456000170702145064003a0007610100e0070010142c54000f80c100e0007a0111805907000e504c441d8100340324100440c0d00901143c150750003030400420b49203c109140c6182c0483d9502105540780f001a10340c0c00d00c84040745c024140c402c4034015011860780c0c1d20b10118210414003001e80b0211000c619045041c14070340c089e80300900014a0150200c0c1400c1d041801c40700c035079003c4401c0720b40b52038000204c0c244528081008a80e10f8104109a50501000070740c0c0c3c0381e07144400300000012128601204074200143d0300e2040300700d00c00c9020804422060014031800d4400c958041c860014400c01c25400840e42c1e2414016503072322681000300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 491633012 1250 491631762 491631769
    0xe03060601021c1b06060e0a05011a0f0405180106021c02100c02100905010606030c0306080703030e030a080406020106143709020706140906090d050703030f050711010c0e0906 77
    0x40280d00b4014001c140105004ca40d11a01002d03195070702810700002e031503142c00305510b04984020884440e0602d007070010f00440c400040b80c08103040400f1a402c0d25501e0302c8017110414451900181c1d03210070101c009800d6522010462416141d2036400c0d111000160703034107401c3d40080343ca600381c007680121030021100b002079801400c0885082c8129264180501020400ca41c1144420358060351101c4007480f150345c0502800747c03840d04038601080003515007202d907a2220118000201007000c00143c4e0f0140d580c0421156842c00d400454142e941c0b995020003074002c142e02d2080c10f00503000104010ba0340d281c00c042d1072000180c41e45208400020702000c040110f41c500070342e480c85c3c20361420007240c200300134409000c205201e0200013514070598070b0101003041c1c0c010464500b80d44101c1c00c02c607107500081580d0b1142d011606101d03803070302d1443ca003d8015041010b00c43d86010300c0c00741001a05a070041d05060800301c500020801d80c4c003480005c4480300f41a070000703500007500002140072030a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 491634262 1250 491633012 491633053
    0x30711010f031409060406050705040f031704030b1f14060d050916080312060321070804050904050607080603030c0d080405030f16060c02010c0903030c111f0e0306060102 75
    0x1c0ca1882c00046a00c045070083c584100c003507454002651140081200704280c501c2070703a405c03144600300f030740c1024508804094000d01d04e000c018116034500c0d0311001c2030002401031714041c55102d04040c0c043d14052050802c81c40074482156200701d080040019003400c2114004016800940303058038080c1c0000001001d020084c0c0021113030b21480c2d811401d0020340086400c0507000300c001943c1e940707507461803044210a010b01040d100c1d422054400d01c01c0c0ea4040e00e001608004038020a40b01c03503450502d050140200c3d44015000ba03400b00403c030400c40007040540c4160720b5034403160082e850300740501d59240500c0b402000a030317000310b4004046600910100d07034403e20410869190250307903407224056401007a03288440141200302c440c00c02400380111101d501d0588002c001108081400034104099031001030140491200d240d800e1003007440c600c6142c164040c180d40b00400c5241c103144140800014102d001401124100c401d9203804a20140030f41c00503802440361551198840344a071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 491635512 1250 491634262 491634287
    0x308030601021f090b0105090c03040b07030e030f040e070e0307050d020f100f08011d060f040f05010b0d0f02090303030703021b070807061706130b0102010b13020403060e03071101 79
    0x1480388421880007400e1000c0506103201d030030700740401c1c013aaa03460022640c10040c4c03c4188200106000c21032007611020a490b07209030040d080c000240c0760024264010000390304461143c0c0400a94280c0070801070000f0412183c0d40884100c0c56540d40381c0460b01075920102555254020007000c000700c0c9441e000b00d003001800108603445090340b0a00266a281507005140f01088402800203009504100064011f101e20914800700c1d40d643d8108525100005000501c41d8072140e10798142c64a850780400d400704207401d010406541c659154000f10b4000941c1103026a04019800c10a503607180240e40c0d441074007030019411519051030690194000e140c008204c896000d00c18141144200302d040001c0200710007900c00c0701d040030401448100ca02c4500c0702c1d490340c82c3c001c3c010380e602c071000b40700c04a640e0194006100a0400b004030701620741900c00d0780d401800b0849140d200c070001c0d4000d1003128404d11081015003121548591030340200840640221207190f1071000550150f410707420302 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 491636762 1250 491635512 491635517
    0xf030c1003020f04140a050d0308060d2f0a1221030e0a0305070203010f051519081608010b0901050a0b34050106050a12170d11130e100308030601 64
    0x400f8012550020f41d43c1103903001e101d090b80e001d1640720381410924000800b402094030426540401628040e24000019016500410484000303006000a000040715030280721009910340000303000318018190760900120344034aa400d200090424410381c244070b4525030010190801d4508004000815001d0007410400d00d600c1d070341102d16080060101006070340c444c0d21055190b1403140141030071101c2c142c041810365072a000910100a040c03e003178440c1e030f217001c6901c0102c1c0d400206d010660860241d00045442c400c50040c40e080440710130841d825983d04038000c10212503504101b0910344028410640c000344501c0040c44020349060040240d000da020b480040c1ca401d04218039151298600f14056006101d0140c1c02040070030300404005003000c4400d40e450340d050180d04041c0078180c09005100000301c903040380000403040b054800050392000100a038900342644c8003a035911900c43c159215032184030105001814944944c0500b0b20000f448560030b040da621106140e03c06000d0906 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 491638012 1250 491636762 491636767
    0x80106050327070b04151d09061c020a081b100816050f030705090117040b0a0b030c0307150216080709110c0703061a041e0203180604060204140f030c100302 69
    0x138048a41030081005006000607044100149640108002c0e1109221055903030300c06031a02081d510f8841321a0821402c81740105020b1170070b500c1c40805003407404000e4200e440d42c003000440c0034021581207240ca03541c51030b003131201c0001c1307040246007481c0148400106130080086280781200d4000000d406459050680c035202d40e068802885400c100d58542c00a0b20005841400d56800140c1d815044079903a5018103030f08050303480a004540c000c0111280da40e9410410380180c0d0204054100c607400641030b80d02180d01c3d10340c0e1480d0510aa245000544500021010030414000d0b01004942c9848060300c0041d041c403003103501a02481c00b28100c002014003045591203014400040107611400000032603114400c400e01c0c8001490040ca80309516008000424180058100c00c5001c2c07a10300040e80d90b034850b400001f80291000310b01009110711000c0004221035a0300400640740710a11900b551204841004405a0010300c0150186c005104110a50500d5140c1c201c13500400c1c00e0250 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 491639262 1250 491638012 491638019
    0x70806011b0b060a06030c0c0206130b0705060115110706080a1112090d030902011d0a080d0503100e010803091302040b0a03060302180c03010b0f0904050906040308010605032707 78
    0x1107028540724003900c000c003080c0140019481c000b03020740000d0500e414144442204410042c215610f2410040d005400c0000d1222014444503c24006003144a40c00f988500c06070a080b90764030401d006208a4050501090000038043c6405202030480c600082c0102400d00318103c8603014003524a003042511600ca88494140c1e03030700a0808141400c88283c507d1416400343c03440c0c514010000410325190007918000760340d01011100210100501c0c00b0240004940840c41c80d801590195225010303641c1d002c4201640400218010f00f0100000d0402603118070840c0800315080c0b00b24185540300300078019907401c02010580c810488040014145aa5500ca40d90543d10400c5200c0000350360311000d03c11890b21200c55281c110348508070780107500d4800c8414220744418000ca241035140489e11500700a1020110341c2e5622003d4024020342c00c00083c0d01c0e658aa081d1812408640b0090000c80c25610a5060f40d120b5a0a50784841c0c054211809115026031050702c4018903014402000c0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 491640512 1250 491639262 491639297
    0x302090616060b210c060c031201120c0e010f170c04051005120304122303040303050322030503060409111002030c0f01060803070b2208090a1a0307080601 68
    0x5000aa002e0103000c00d4002140d4200000074994080d40c00c0c09a4001c020400d1040e030006440f00034100559103e951351103c032100030700d03500030002d20502c58005e61002113502c5441c40c2d03030400c03400d2007204d0307000300162030300b6294840700c81c01d0191080c628074156082041420600e410740d1048429800e4450751016500030405541c02142c030280315008030001040035041c1508040c42d20324100002d1424141844008240342074441d40c0a0205076900111000c80c134812184480610030b604126031383c85640c4d00c2e01a00642045034058208000e821241030420300062004410300d0780741d9949442c550f00c041c200300040610140035910100406548401512104c0e800110a4004d400035501d4000f2035821a18041310407000d090f803641020820040c0c00400400e0f924034503401341c0401099550b11040818442d200b41e06000c80e8035500700d4200a0015040080c04540700940d25511810385502c2118000d41212000211044040002400203481072800c6a0410070500d0a02c0305912503800c1d1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 491641762 1250 491640512 491640547
    0x60c0703030b120c030c01022107150509010b0a0b070b04060f020d0e030d0b1c0303050c270a090603020d0f0303020403021e0f0a0503030a030b21010b0405010501030e0303040303020906 81
    0x840c6030503130182094158518040002d52451802480182080010190b4400903100307408611402c2800100346442040101c100701403102154410801103403070503aa86e140a4926002c103107000780d8407842c010071435018110071184d2041d048501e11881d9203940c0c0e00e000060014a0440b007526609008132070030351103540105503419440e100210345514100f094081144c0f136401540d8402e0b00704000d01c070a00d080352130703100b00f12580608000949544100d0ba5280c148110b5102020b5240031020301e102041d004490380b602181c3c02e88065203801e03281c2c1901e0048422a00010f580404040780020005000811549005200b4500981050360300e0703002c80c001d60319021112000031510801c003903007800c200c886456000030403202013030304525000200307440307209480b000e07410962a4541030005444160501c151000c00c41000d155190030003070305038001e0480d486078520a50901c40009850340c801d0107026072480340b00026601e9915150350a9000303600060b03030590448024000d0100890740120b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 491643012 1250 491641762 491641789
    0xd2003010204090c1d1206010e25050703080106360803030f09101b0c1703010f09050c03040305040e100b0f070203150408220302040504062903060c0703030b 69
    0xb600d80c1041e05c0001d0885070821191200c40c041ca100d90181c0b4440c1d0b8001500c94110741c04000c0780c56054540e0b00c9a2001c10042d0a03000e0403d0b117084205420035544a4014100c1600958501110780d803100411076408183c004602c00e2511948201505000c4090104481c00c40d0b94100152095503185541d0039a0800c981005840350303200e003003080e031440c2800002002c1003485030030000c0402500741e036240c46400a8140317040108502c0000c01300312000410303da22074445690607403030f9a599a0210010030450040502d89401c000c082020110100c064a00540d490744502d400c050401e552000b90507401010385454000c07102d00082c50295540c0202101846a041c0342d54510090062502d4092500051000c00090340208004100d071242520384031078504201010007105110036069100d8541c0004c0e5200e4900303001c1c40100291548074040310345240c00361190b1034969400002482c04109405034046d00303e01e0000700c05071400001044410300c2400d00280700c51041d00071400c074040082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 491644262 1250 491643012 491643017
    0x3f011e030515160507030f08180a14010c020c06040501140f0301060201151e050906210c030724080711010906050103051e0a062a020a02010e0d2003010204090c 70
    0xb0a00012202c07104000e044403900c0e040c8249090f0346a40d004040d83d40c600c0d15001008031003000706074100d410003074806000c1c81580c1221b18a480e0303401c00880c0002c000781450511341c41e08444017400d40c0042903440624000500700d030b0810346840300660318120340d05030014801904020795906003807020081c44c00307001d0701d40c0002411810301b00f02e0340b2071842c02d8001e044040d40c40e111390407030801c0c817604080039500f05890b03617a01ea1703e0303850115003d01500704820749401c40e140c00c0900310840005000e01190012401c584007030359141041d611180d40c000074240da0101e032001c07805c140c0e0700410f4590381201443c90718070002d11900010a007100d2852030200c0d5070644440040003400343c100000c240c00c0e60000d290614090141c014255518440036000b000d05450340700130864852120040904241c0903100a002c005040e04c0c000c0d25080c100a040b07000c030700720740c02c3d0322018108028544a61a4444e9080150920711304407c44030290001c01658159002c10005c1903104c5075004410110302540c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 491645512 1250 491644262 491644303
    0x1060509210d03110c1912030c17040f0803040f0605010b04080304210813031a060a030303090203070312030c02071d041e083f011e0305 60
    0x400304804501e03580101040d451071001165000c1c4004030301d281c080c0816050008819141d030081144500a1051002480c0103c0300e0000b0101842d015405403a8484d0601120b2503a02644c03d0b0f00300c6220404640c0001c05400500320744912a110050b0014000e130442c3c140041c0c0c5070b6038955160301c200c40895440c5410500a03080140500400340513000404009042c05d00300300d17880e6643d0085200700710b48400241d03111507100c0301704a00344003101d0704040e600d6a1001c2c010401e4114101900c01103490b400c419641100000d102802c0d030380148030050400308002d2940d00c0c224090b00328002e05aa0601a0080000002e51030340152019840309440100f0b640c60740340c00290038041540e0206d0840901e4145206804040c000400d034040c1e030003001074207000c40006038512880007010300103003040700000d094401c20001003500c102c01541e036402c03000c0040511455094000902001c641c241a0201c018071940510f00200300c100c00607059001d030320715a240c684510b0700c0d01c000d100751a0032900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 491646762 1250 491645512 491645527
    0x3080f120103060f201e0405040207050106051201090b01031101051603030c0f1707080712091104060618090f11040e060102190c06300c1101090c05040c05090306010605 74
    0x13107004600c03900c04408010345800c00300c0d0100001a1003a940107031070b141e00e4140d2050114000c481621f001c0e1101601c215100c10107490618001c154a01420307104030722805030300701550701c14010324030f4059005502d8049039103140c3e1680b42c03401c800e030b006074103010301805251088440702c440c0329000d0380250b80209080b0141d4101901038800b840d000820003501002080c000c080c03070300303030795400c2042c40c60302c4000c5039a144001c50720003900341c0a01014909005642080c0024901802d40c0d101046404200e442d54904044d031f581000d500590300e00301c113040c6041100c801130768070500403111031400c00300e80c0401d0841c000c4050b0340180c02c01c41c1c544902105008055031b040044039113007200411201009001500c0380e001c06281c521511080203900e440b050860001400244035421004100e034154074144141c03000540783d186c65420000d0855152800d96040500131096039a802c4502404928140414040501802c0c00003400340030082250110588080103160f00070001c9556044d1070341c02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 491648012 1250 491646762 491646791
    0x403090504051501020615030a1406010905060d050d030504032f100e07090c02120703050901030b06091806061306080405060901150b031f090f060b040f03080f12010306 74
    0x30050945026180c0788070070107007940d80000301b503900100c00c407880644507111040020704d05484801c008042d04a492180c0041d010000b0b03c0701d050740c074090414030042e966902440b60810a442021b4055030290341074560035070185d8440b6410078000d05c0d1807603c02100c103d01041001800c007069115034402e081c880c101180500072030380312201c00c480521191400c2c1307181d1aa12001c03400740405460756212007032109402004a00d100107100c44665031500c800f41801751a580121541901180c2006505411840c000c0100e504040c0e00074034460342c102d5006122050382000819460300400d042114116800d550b8420000520b0300e80d4500603281717041e1404505002024104000980c1869207520ba004054950074043d1002d00c40340c507449a0b074010781c0b091411500e801a250003202060045803441d003c1e0081500012108801d1168580e41d00329072501e48241e101d0506c0380314482c01c080c00054241801404801300c80a442da0408643c4502200508000c3c0d104844442e074941d4420300010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 491649262 1250 491648012 491648021
    0x10020c0a02010e04050c031929040c022b091a0a02070b070f06050c09120706092301050a17090d030b0306070e100302070f080706050f1006050a0908060403090504 71
    0x80c0c0942d014001c9081a241d0422203010140c0359100d412340700304922446024a501481c142402100b08203801a011003101e04110154210f140c00780b17091905401c01c05000040b0304021030b034810002449243c1e112403061551340700b032480d4002c2008050340002c805401e0800b440f045490741c68004e5403071004000103490003400e64444002c9003c20b02c048000b00340b020501c0500c007078002401080d596074081070100c00d8032410b2440da910031604482d03c0a8054000f40c190250340c5191100e500b0592035000e2110300040d01000c0c1780c00340040380540c15480d441b1382c016017103203801c03820141c00421340519111702400b011142650f8035030200408000d8985d142c040c40d459804154064003007410b00700340040c010149501710350b000300a0b481c011481d0b64441d90440e178580360000c0c991020802c1e01c0ca4600c900d540720000c00e4480b1401d01e030205000c040308800440c01603800b10303054650302d482c2030019909604030540240a00c5159080050150000d01082e841036210780da4503e403280c10728013000101e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 491650512 1250 491649262 491649287
    0x4090509060c07061e05040605010305011a03030d1a0d11130b0108061909020d050103120207150c0213110304050111090a05040b0f10020d090602010c050a050c10020c0a0201 76
    0x250701c11018081940d4000381114000b64202d800465240c68910742115218111030091031210b1070401040148405076000d24107032440342c0001d0041c1a401e184401c06034000e2100710343d054104100c140912022a070040d801c0220912100d2501103000000407581034540c0c0c400d564100a4002c01c00f21480c040540700c103100c03040700301001103d1101000a040810041525010381205a0440e8010384018090320040160000c299981c11200c5102805808207201c221482c01444c1c0d04080ac460010851000b603c540401e44880001c681904840c140c0b10b901c403d0b60420740100b4400302049581c003400000e81184812180c4d81d060910304503003196138403d191141d41e4030901c43e800d00b56540014a80440d40c0403100855450b009000040030840c07580c1c00c42c6c5d0f1210440b40c04844294000c00c12000c1813465482e201d850907503c14003642603402d101b0500c40001c00401c15400d00300e001d13001501c800c044000c00c4440f800010040602240d00a268580495000455020842d070b4000e0840403403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 491651762 1250 491650512 491650531
    0x15020607031113060302090d050313231503070c0b13050c0d082208010515150c0304030f030513060206180724050c070909020a080c130c021e03040905 66
    0x814103140e580506071443d0b4083c1204042d00013a1103131507a9a0320070000011508801540d907a212840e0081105610f0b03480b59501031001e0404158424110100e0800c0342030000e0800c811190500641e11003a90004210105111220b0084804560700385070a522902400a40341e4000c4401e0400701e00d08510101054032820748986210000f036070350400d85820019541ca0416118910390362101070300d1041e000906e50350306c1d042c1000340c48014141560420901a82c400da40e4244d1040300501a1041b0035051358558000c000c01c200060884408482c0035000745000e40c01c1019800d03003482d182103030798041801071384144c0074054850720b058501d15402c2c00b404000d0001034a40f074060090b045a400c8095210400c0e0045042e020b0300410484951848840503940815102ca10b007000424020700c050303004d00603e40c000b00780040d0000b15032245203402841d00281d5803899040b04060309911144104600458005032001d4110b807002c2c1c682a2180c40c0a981c0700c6060000b0641255002000e0a14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 491653012 1250 491651762 491651767
    0x50f0109051e130512030a0c091a070f021806011b031b0501022101090f06080a02090c0f0f03061206270c090106120506030309011d0a150206070311 65
    0x4100c2c00001960800e600c002000241d59a55001401207108144000d80240039504140d021000003c00035403150482050030003059208000840c0c0003042406804036400d804900036903010460006800d80c41d1188080c040e1108d01c9034042002d249036009842040b00c1c401d010f00c0314541c1c2001340d40100340314094159a8401c080c0c1c80c020102921441c0b90303001d10400e0400442400f0703003901101c0305840c40802410b0b485400c42d214003005203003403161240c018035041c07410b15071400380d008090480c0ca100e002400b041c10103400f00300403088080e01c503400e446070801c4200c180c81c20100c0642801d48020f0105034884c074000d400c1c402d20507604108000d40c1e8221034108020344030540072400b09400d081c414030601240b00e0314550302e803002e082c4800b603100762040000200c1e00d51040410940303102500c03062100752580c8050603521300803445c0e01e0340842c80f109084d03010360010840740d1914500c010002c1c0d0781d170ba99808030845941d24515083c801038200800700903203c0c1d0540580c030082e0040fa1a42031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 491654262 1250 491653012 491653021
    0xa0203060a0506220303022b0509010f0e030f030d0b04021e0d020721020f0705060405060f0d020721020c030a061a1003150501030203101521050f010905 67
    0x4410390507500402e480f620000c11504225a440109807100d4003a02100b1600981c890402075600c0c2c1820b142c0f07201d042621480f58001d143c0d522a41110700005850390f9040265110040d5900070001d102c00b0104803481c134042285960070881032078100d03a4500515a640c1011100720196030000f0000390043c1c1c01000000c1d00310110300901c031251a903809a0a458854050320440079101d43c0c0d2019240440c54003200a004030103006a044010064085803c40888e0030003644c0c540522f84200f030307401202032004001f14209000100010442500e04a15044001013044102c0e0009031055842c1c00c400382c0c6140740c4c12480310070202018030600051022044220000381d5a062070740c0018a000c4d21040c21443e91003881801200c0c411000f000f0815612441100400a0018800b0b909203448894400581540284200e90090b41d1f0509045036090412100c665401c1002e131f0302d002085540c100c800c0c074480b41c005040b4141101481d011030315040c081d202e100d4001041c4c110554041c074046c01e01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 491655512 1250 491654262 491654269
    0xc0d260316091202220c0e0108060d0b06060d060905012309010806011a070f060b0901150c02040518060103060902010807050f0d0902060c0102070507030204110a09090e1603060e060a020306 83
    0x10b03004540c3c12a00100c3c01508020280105c880da5550100490309003116601c80d0343d003050740020414420380c0e8010442d80ca00c800c100d4200092100034100c1c07000400482c0032800c00c14014410040364a8020036200da490110b10308a9409901070001c4800c018052503e4240859800100e0041110b200580d5411b09060649403503042c4030780305d00c42c0c2045080c2e40682084406562200c1c0d08a00c03000c21242090a01070054602d04c00304e584075122071400440e80314000802486035507a940e071980d04040c02c40d42444018040a480450403000c1e080c000500c141d02001100e0181d44101800700e5a0407c070700c009402014040c0040050200070b100c0600c031004102c0648691080c40c0002040041075400410010702c1075141d80142540001000d00500200144280446c0e200b03031010000250512038417241402044512400100341200400c000f18081d0806000e01000c2015240210004076044240c1006a8411940182c41d401c2c481c0d400a000d201c041e074015a2044194914581600003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 491656762 1250 491655512 491655539
    0xf06190917030703061703030604060e0717090c0918101a0f130203070905030c0609030c1002010621050c030106080d050c07170303010e0c0901020c0d26031609 70
    0x442500701000182e200da20a03000310006220410703606075412900c00025469902c1101c07818000e5040420000350b00001c0081a03100d901c0581d10034005000e0380d000440281d8015060075000d00c030341c0001c58801c2e40c0302c0002500819135a8201180f0017240391003542002d402000304103455117001d010b52000020100e43d45d681c08421a40300301910403400000c0d105189c2e01c601010160300c0481001502034115003d00b00740d520441c2101d46401681007004090f201b14800550150400300044c0d98906201c804000c1c4014103000104040d0707152000c03d10a43c104045107501d06c01c1c0d1121074014407806202a50701c03814164000c0c07042505010300161341d07202d190302440c100100040c407103a0200c4180841006410388002d42c03e517028078803403802d950790802c2c090702d1003000c480c002003a900c449260444600301010380150903458507410812120024040c003c1d120010008205017204000b492804004c440d040045600c1c0d080c411028801346407400c00c0030080c0401054144542010b4044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 491658012 1250 491656762 491656793
    0x608090610060e0613140a08070b0412020a0314160801091106030702031e0a020607050a12110403140109030801050f0d06110c150609060a031e11030f061909 69
    0x4000f034200102d9408070309944201022142c1e2000c65580c040b40141c0380e4142c0c905000000c855020080c0d4803207a03a035441d10003a00c20100118400c000070008025401400b10486000070215074246540b6220041c403403100ea40c160040b500928407075a944030002c0c03910000f421078030008001483c0b5070354074882820400c600c05482404040b001039081d40c42001110f00d0720140c00321408507030401000942d01a0841007030f004c007500915000412052107071060f070790080f0071507a401c81c0c0000798403002d00040c010f0210004040d1001c01012010076030301d0704a00d01d1760100c6000001d00000c00e0030010868141a0489403052002440f00c1c0d504d40d88610800d85541c0c0c000b24006101c10781900800b00900c03520004e22064050149440710308401088028032800c415a01007005503101c600b04140041d0500005103150008800215603100c2071103031484c441d100f20805241902d1020009180c040c0d60395141055070303c01030400210a03c00340c280302801103507080900c00d84243d65108460780032840d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 491659262 1250 491658012 491658017
    0x6050c07050309131b11120906030112060b30011b050903190c031703060d03050a17160e061206010c050705090a2c070528060801060809061006 63
    0xc13402444481540424940001507090300c003842459400a0440810101c00350310a00501c001040d000c80746c281180d240e0740d0020501460b40c1c2c00c0c40347c034130b00d088000401595050b540308440801610f880071201035800f0807000354010800084242c0701100840c42480c22980d041044107408a2006001d036543e01e009400c0550f110311701040030902c6c0245d0310b0200d0540c540d1101e04481445403c200c0401541d0243c80e00c0c6036885458807050342644000d450503500600781e00e45c5000440d00c29001f070446100c071898400d0006680360384084160b03c2c141c1e954030907240b10120098526030016030200c20600b0940b002c038141601c502640d007507101c0c01011075040c8407000b10030500700581881840041c0c08000c080000c0c80c02c00760780307060090914000d1440d130302e034040716240e42400750100941014401d0038014440c80c0d044c4010310010032a01e003294142036503201004080300c0e0390201914042c0019070b44581044d8906a0018070402c0c3c0544282102c0e0060310a00440700c00300c28507071003510713034a0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 491660512 1250 491659262 491659279
    0x50c040603022119060506031c050a050c0f0a06020c012414030a0605070e1206090a060f0608014106010c030c0501020a23040602061f1e0306050c07050309 68
    0x4a0480d8100104404052040c2c0104d003440c60400c1040d5100b940540d600350100d03000441e1244c054031640122441c018007040060220700035451044008101001c1c0c08030540d18042c2c0102812403416151b408111100d42d0040f80c42c1026250910601c07405100d1400d0050200c0c2007100c12041c003210602944002c0c4030300200359500c584040005004a55128000708010f1500360401400690940741441c07003030b5904e4005600380700700040c1d414010802d220207044151035959402008001d104440e14146031181070019000344c00780701c2c07480d500b0081026017140d4a040401204541030200f0100b0701c8a25224202c1100f0000e4103526600100c2030a10030b00c0c24029040507034a150284c0c20060032076000060511b011644104207840d0310140c88a6019044001a10290030303004034000d610040e4401c00020709059900d404001d5008040400d401700310340c03150191011a40141c0d10b100e030b0050440c8040003001614814070350700c2070a241c01c140c2000c005030340780350b101d1180d18007042c881d1520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 491661762 1250 491660512 491660569
    0x30f020a0e190f030821070e0f0118080604140106030f0b06131a040506030d0f0813050a05210403030903030c0c171e01090209010e07051306080103050c04060302 71
    0x10807101101410966401c4225195613140445d0f0a80c0000300017120001001000c0b280c0c9481720810314012841a1108410020358000384000803c405030058100100c400211040c00c0c2e5140781440036184e84000380c00e0500e03090034001401105c0c00000c0c034503070385030640401c003050340f0b817001d1288260711508106031500c4400013301b0f149243e0300c1c03114107a480c0c0a1900c001480665a47c0502c2009a600340b1446e030f45c400c205900c82c900407081c071000c0350010750307055800f2740b10301c00059010f41200000f4030401680e0310b42d28034003400703c04211040d90208404c4801c5000c6c19010550f418044080c02e8901400d45d9401084414503200050a11112a41000030004400c000b04080c0c244090400240c1550301c44c0300303aa1300c1228070070407001500460003051a50040c02048190364019000c601d1a900c0c210302040400c6c00202070800304a01404400d64000000c1140c034018500c0741d481d21040d5055062a50a000610280302d20881c034080303007040140c46034030606100c0206241c1001e4103080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 491663012 1250 491661762 491661799
    0xf0f04090204090614091b0c030403050d0512010b0703020307140c10020102031e040507052707020c130c0f0f051209010c032405090601090801090f03030f020a0e 71
    0x4941000ca6803a0012a022036449500d60040044680e0084131090711a914020f01c01405015285041c40018028441810070700f10700083c01041c0145041b00d103070903a0380d16942e091a070b4101250b00000c0c0c0004d54413801c12081e45205025000c800c40c134914003c040d0380c0c041e41c0d80c8200b0310018460a150182c043c500314040c003c1ea6241a00a0311a945140142000038001d510455104114480300942174406400014a1612541e80000100219420f02d410861101c0c0481500c0b24400411102c41c3c4008042d002c00901405441d001485440e1410717080200501c015a1100c140d1841c002001d0020356200d500c07140c180307005051580348a01403010803a85441118110480604180e00b030080500d015805410350100a55081220503100c5005400a600e00c08000388101d003441d8081c06149082090b254000505046c689803050740c940ca81803d481013510251100f41194008100389074050180745075000402400710300e45800108003500c80b40c000d0b103242d070054074030b011060481741 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 491664262 1250 491663012 491663017
    0x152206090207051e15101206090b070c0c050f30010f021204030320130915050105071b03020d030c060b01020303070c0807020d0605240108010509010504091a070f0e0d03050f0f 77
    0x2d43c01c0d4111f0110f111500700040923016513801223598260b401e00054000b4418202c1040659000c220544007038034080400c03070f525540004443d808000140d10075a42124181180028400441c6442010840507005401c50380d1b00840030b04000e004221144413651203507405648940d06090004240c075820307242035040c0304002840c4882000009110250b0301c4c840c203c3c00c00b120f200f2101885800c800c920326010811540c0301c3d8030f010440600c10307080001d051b0688054114a00103001038681d5070707500029560222044194080b51f100f12114085c000d05000d0103008010038001140745003012a002440e24034544406841c3d000e0124182c021565942c0200c03000c1900400d040c412400d041001c1201840310ba01c2040a0241c451115401540101240c40c104d0b80020320841c40e50b882c0106002c0502200c0b00205c0b8280f0300501411080e40d11184c02d680240d40750303134900d030503410720752409440000314060a91280b4119202000000d80c0002144c0b0820084142d10f0b80f5070030881d180c0251070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 491665512 1250 491664262 491664269
    0x307030609150e1003050d120b0a120501230a0c0509091e090a030f050322051605190b07050a060608060a050a05152206090207051e1510 60
    0x724203101c0380b045001c010514510a440c058003446203e03845545003001c0c0c4040c01d10000b0300c00c3c2c10034007034001114054601100d5082809001003039240160001650705a000c0d0400f042c5e43c0b1140c1598414020244110182d9022000074450241124944008070082c003c007a101c81c05c0c0c8800314004107600c2001558008400a04050224100928000c803006107482c989030542500e0320000311b038448009004c003c45030b0561125900401c1e55a01112141e000500665607407a184c601b209001d003d0103820400c040c000c101030b20000d0310001008080e20b4035a8001480785110b115060025580c0d03902c0b5800300c2d514840300550714102c038034140d4241320460502a141b0b40c605800001c4d800340c0410b03a58400d148052003081113079105d804c0042114400c2e10041165030a134200c8543c0d40c102090a1a4040c09050030283d07071100c480d80700011744201d6080040e4254021448804104080002801645c050212291251103014070580e03180441001c3c030130040001000b08905204888106002c2d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 491666762 1250 491665512 491665529
    0xe04020a0203130e0403353d0f03030516030e09070309031b03020613020a082508060c0703031107080c0f0f0706090b1b0d02100b03030a05090603070306 67
    0x9650791609581810f13048030240c010607401c1c808409148008410710b01104107a03050700000107800c9161941c0741c04c000f08074251001c070101506807844610f1442e40080d00f0090f030092600c1100c80d0100c001d4843d564003403911a83c6e0710310180f00082d00312045d00c81c0703104140141c0e240c465241c141141d0501442c44500c0d0000f00c040d081c45074959058014001803402a15450940c282004481500f6140e4032000b5006030001c0300031403010700c1442c0c2d5644d100b070300003842d4044060b214041e0a0810103000c0f00711840c1c401c80044103483e4481c00002400510350507000e00000e240c80b51501d24584202d5a00800b059034680124a00305103601c103450351580c0248a080c3c0700e06803400d1441e41d5100c1c01034501903d00c2510b484030f0302e8580c00104031081d2042d5680344030350743d0b1a08280c045070703800c8032500e1a6180d49440000e20b401408100d1903001240701d50050805a42c1008440c1c03c0305c0c1113001c3c6502a800800002c00c01a030801d04441003c00240c640541e26034500307504500805854011030031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 491668012 1250 491666762 491666797
    0x1f060b0a0215060d0b07080a0e030309010c080105030d0806010f0c12091412030f070201031803210c0c030f03180b060f0609280f030b07120506010e04020a0203 70
    0x2803031603000500898945089103001060f0b1030340000c00c0120701d49140c00600e10b41c03000700001c0156100e0804139400c401d80880121b210030f91035841c0e6003190002c03103040c0903683d9a010155252030b840700c90b09005110960103020b40400703540e401000d820004014038103021241d2071186031144a0130504903c0c6400c00030f044070b09c2d4414a070091001c880e5114090144403101c40380c0c0301c00d10b0902c00410f0200b4161000354904029007031500c09942183d00705038145556003040358074142d40c040c02003c502d0321aa8520110b02e07907024803064150320a01d181c0b00003a280135002d81c0781c00e400610f40410550107040c046912110608110003070132013110314020b1a10342c620240c0c1007042c01c10040d400380303004a690509220455080c0f1145008484000da030010040e100c144d4140010f0790103800f0b205050032800e1005803581403000786168a58422281040404200700c80301d44e005c0b909240c000c51000d0b00b800f0700e04044000810380e041ca01340c0da600c21680000c0300303107086001f0000c403502c1c00c5102c200e05c43c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 491669262 1250 491668012 491668027
    0xd11060c1b040515010e0f010c0f0602040608070914093414090f040b03030702120303090615100807031e06030c0603090c14030a060f0509150106021f060b 68
    0x800d10014104200c2c099410300021401c030540449020542d6038041c1c0d60804810784400030408a020841040703414400c40c18003003008609800d0750001410702400b00580d0740c901e0154000d184180081003182008025141404000361808003030041030340451740030145886050b15528880f6407000004400400784160040005900c011245998500e4403416101005401e0508a0384184a5140d62049220030000780c0c5103003941c0100c02c01280074084a0401c0c190780c0c089002c00c0c0c42444040c18613403004c030070040950010840d459001c80321906030f44241c1460301c0071540829422024030b0900494800003a1410310990000c0c0c405071405c002c01c1c4218900f07640c040000d00460101303484080b031705400403c0c2c0e107009029140c0d455038401d000d0904036150240d48814040d4840081c0e5041c017070b4141c90030116415000f50321100c0346075070380060b20b4140b4500075442c120790000c0e10907918643e10010000c06401140c01084400048401000308880ca0001c00c01004642c10400316090f011a984 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 491670512 1250 491669262 491669293
    0x6042d03051605090c040612060807080a0b06030109030507030e040b0301230c0f030103020d03020c04020d05090d030902060315010207030210030c120209060906090103090606080309030c0f0d11060c 87
    0x280c0001c10a500103548403500d840c01d11a000c0c00480e014017200a041204000c26845143d05240100169000003046926040d0041c10701085034000d1041c1e07448118000180080b09501c0ca0b0002c600b01c00030440ba1000360f03000790144c0240d038005420322004d100c3c190700310344980d0043c00340401c0050080103207110840390700011f840501c038141043c0609130000ba6000d0340c85412115100c130f00540044c01c6a107103500300041e41c00900d508070700314040c03040149160386544c000303001c00c0060710802054030320300780046030320b00a002c0383e884d01050300b00a0804090307100e205c00c980d080342c09002ca1b201e100344110010303490140107902c025000111400075941482d4158403501c90b01550b91f540040d03110f1a80d01100a0340980303560164407203410001502186170400050440010604010070036a10703079180c03041185c0d16035006918035080010309409610f0280541c6020500407510800d034141d00c080451807148015038010083c0d41b41d480c000c01c1c243e035040191240c924411003180d42c0c503600d50406 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 491671762 1250 491670512 491670523
    0x405010f0b09060a03020d0221062d01050103021303080d02030601090e0c0a08040632010605130905090708031b1501054b030c0105070206042d0305 65
    0x409009840d101001c012880d18108690003050014100c416190541c0c08200c0303620403c031030481c0e0200b03110401d0322120034254140031180842601504180ca01298164a0f00351600c0c00100c40040b00100101003003a03980c000c3e4152a0f00f071900681302c542d40c5d850103620b40950741014000280104010500b20100d4005520654080c4e032070450480d5514003100d140c0d041603ca083c401c1005111040d0700502c04c03100d8691203401100081500d160b900404c808681c0640d0901d2003600750a400f4021058603031400340c2c01001c0524000f46000b0079683d5200083c102ca0245650315501c8202042c00320f10100106000b404076041580c0c2d0314009a80113041400801103001c034a0f0140168034080e0324005140e8038100c030700c0507019190111140200491a2844c03550240311251510301d1280e0088102c01a182d15680d402c40303141c0e8500da01020186040c43d11506130f410440c04014190060300c031042a6000c0380c404084121845102801000d41032403241c0240443d1026002c0000500c00001344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 491673012 1250 491671762 491671781
    0x903240b03010608071805070207030b070203120412080705161106041e030b07140d0207031e020a060506090403020a032313090e06101a0c16050319030801090b060909040501 76
    0x7081c0c0601b0f0041585001612411519007015070400201003005c5a10841c805030303c14240e205880c07900d03a44606040c03080350180d03000d40714020804000d481c00c0d074015118541002d00d41c2405818607001ca2402642400c03412070091410360040c41007803054031402e066a01801c1d2204500c1558100e505441500c2e80c0240302c00d0b241450140040f81e011340c01140301c650243c0011120b41c4c58150013540c800c0180d0f2140008600f00064600003034070003c13400e18940301e80820740e4003411410580e402c040c2c050b41c40c060400f52050182c1c2c2e062100081c1c00062261090380e040c1886203000c00007415210640041810b03d895000703000401b20b07148024900480140d850018080000343d00b00c3c22084d94602c0112a6a00c0c0e014039100d090020141c0020b005807040300c041c0c1c44c42c1c541001e410465007080c0c0084031602548109100500032440c00740308440d420350306d1043c1a00c6194841e100180301e0501032098140c02d603540c262150320307034075100202c035180b20020b04408120704080c50418003e044120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 491674262 1250 491673012 491673029
    0x2040b13060512060603060607050109080a090e1603090507080f0a06050112240b030f1006050d03053f070207060507020f1309121706010903240b0301060807 69
    0x4800706034940180180e82c00d001c8140103d0980c1e54032030741400025403028280c140d00507024401000016801d002d0890150712401540d500d0b0a103040024040c0030359604404120701401040040400329610509564513162034046030450f038508005080555607000a581e0b4054010006a880340020b00c1c0d110151113400c0c2000300303070390b070304201c22050850040007040c0c0214564241010b203000b0310340743d1840b4081c18001070400d209000027403038420b040440c1c0c1144d801076102c00e21620b45512810000742801c0c0c1d882c10000b949035500825910505d0301d5a0701c610041c0480c40d50181440460000203500a0f41e015220301c41c0307040c41500d85404440700300c01031007080c40100c0c804e441842547e0302c0c2c40d40989411160b588420800c1445032605420b400241c1e52440c8070804200700c0300b6a103e540c2c003a0348809620300078001040d010484000c25079030511411000400009800320b20403488018002c0304440184070a82c10000a4610304ca00c40d5030640c204034001c246844003003412011500b0b0f02 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 491675512 1250 491674262 491674297
    0x3060317040f090501060503040204270f1203050408070305161e050c01090506070809060f040b030f0112031b0c0e0a02090405100b3a0212090c030c0f01090902040b 72
    0x20101c10081c0c4d075090291078001380c0e051000c9001400d203600008045591520808043c0d684441c41c0707902c0d01c0c01154156010005520110f0601111910300c403130b1800c66203400d000300e02e01611120204d2003140d10040c10081d00050050320104c883c4080000d0f5a8021940c242d4501c400300241010f040140081d9903e0007424403828181d03006114181c200d03100035143d00e040c880380e51074001c416007040318056003298041010031900c0d82c00c075004102070102d45207142e44a0620501501c100031058106910040340d850611300402d800601541480d41800c00140c03200809281c08003d4002c1d50b480210a40c500b03806100c004405500030f4090810240c03420812a90784a8241310071032034612a00400b11420002410030f81003040780401a00f11a4403440304401c014105079040381d05c02c3d6182002c0302c4d80031030340642c20611102019040b062080c010303c008000300000035150100684c900e4807865202e00745c1c91899000314402030007080c413040308544590740ca004209159201c41600200901403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 491676762 1250 491675512 491675519
    0xa0e010506010305060307290a11160b0712050910030b01020d080c0304080f1603030207022d011d0a080a05060c030702070b0708090603240604030b040605040303060317040f 76
    0x3c0d2090070b2051000070000c0031103034a031201c3c81e900141500c3c0c0c8035003c01d40c41d5401c403248505100c0140700000c1517603a040500d4440002590801c4429110502c807800558401c04c60700030580182c480568101c00f001d03044e00302e02d91042e42c041c0b1402d81401d8001d2040d928010240c0c0d05540100e203826420f800780c0e440e08480702d00440d03c0350400c5500c64050841400480c01043e085000380203982c0c008401c0300d1903c4000841c4200710480c10074102c00081e000603186086080c40301907010312002c85c1c0004d402040c4a003205101949458000c0da040125a841c4002914100200c010340c050006c0d02c6007811544820301503856032171000301035549109840c00b14040c04000c2d000c0342d11a02d10366014003a1a8140980c111043c0d10440c0c09032410b03002070000c9110782c0d485200943c0146042c25040e2a0342d03070083c090884025441324800d116950920040011403009111a54401c0e44150300064587e0b4a160640007401d1507040600025162420014490f440c00001d00a0700e100070540089544d8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 491678012 1250 491676762 491676767
    0x130605120d080c0c0f100c02010605010e011e031d06040c0b0f03070f1e0e1e0112050a02120108070603110405011b020d05060c220e040f0c0506030a0e01050601 70
    0x10301609100107010140010001d5044801404c0d41015132826651301c0d10030b40c54810f00d001b03400c1050042035692080f26841c0141c0910690000b03001c01c1c20a03500300260b09001a007901c0384603030781c001c001107500a030089041c4a54050000c1851780c81240740c1c102482100d480d41d50004a408450191288901180c920b0740c03130b402e44a01e0310704039a1480c03859035130010403035080d036401c400d2006102407280c1d8003011840420380a00d0805450381c0d240124043c00341040181e100a0a4822862860510b000341c640d0f0311014116150740c0982010803182c6070b90040200910071000005d008480080c0041aa40c00c0428031034220344440e40d00740400e460900f02c2d40198816442035902181070351046e03204071901c40502c464400c0c00101011038203401038444034201002200c00380d8081400084c2d4502c04034249440c1c1c0070aa07100b520a0441c01e00382005901c01c40300c06400139107a4240003201e40b0411017000d20080103010058101600c07420304061400203800c2d0151250459420080007865951 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 491679262 1250 491678012 491678023
    0xb01120204120f060f090b04020910081e1c02010501081b0306011701020702130b1005041a0c0712080414030a0b06010302090616050708011d0a02010e06040513060512 73
    0xc8400714007451945040d0ba80c0418081c201c0c1d404c0390055180d07140010301e0301c0980f0959516600402c003034010780c5042e10401421000040025040c5441c4001c01e0140301d03000a540c0700140e17a80c41098801282c6c0648051514150483d9004202d403a0f0805400e210b6040d040b1a04840b5590102c528245010558266100c6c4c420000d41d015800312004005c122001c10709903080a180100041c038260090300828010302c204021220096110110769004e420302c2000480080070500d00a41002c2c20246110b40c51080030045d51607a1201080140d5401010700004005100c48101401084d41510389500941c01500c52500e1440100313103201a58200411349000791381d8444244a226503030b020064009401100d1420341001052180707080c03054100006520842c000c000030a101c610b0050445d09544078019503450280c031001860201c1d1900040400c2503603824200071442400101c04035103540955849650301002070541142c2d5100994045016280c056035601400b1004a15103680c95 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 491680512 1250 491679262 491679269
    0x20f22020a2f1c0c11130e0601050307080f061f08060117070501211d0f0615041517120d05040501060f051302030603030405120319080f0402040f0b130b01120204 71
    0x98800741070400015145c20f00c80884c04030040c151034001d5100c00b465811510410b184000962101d070062040c0c2c0b03404c1040800074a0f13018002e20650025040c1140c6401000d0168041c0d180101d10850980c5c0310900050302801140c401c0794603643e554034807a2655942032640c1140d50064003c0402c09511800c0b2a2400b41a0380407103d191800c0d0303541020003001c080c403406080d0440540145421682440104807429640f4020026801c10342e40c1c4241c1d40c0700c103481e024412440c202c0b00f41c921418a45030407088a400c040342e109000c5001007058100031219000044100000900d4018205030b64012400703940244020041107482c0c00702c648610340c55002d0b0300d5100d070f2811710010403100e16800a69209901509890419642e90301003501541d00300c503260701c02d030004500c132910b0001c920700c510380e8003109142c104820706148100a02c00d02010700007a000d1501e0b1041031007456001d0300038500d0640090124480c00049112200040500c0010342c0e00064460068050001c2d640c001d60b0242c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 491681762 1250 491680512 491680517
    0x10911090a1e091e060902090f0105280804051606051815070f1e0206030609040f0c141801051c050a05030d09020f22020a2f1c 56
    0x5082c106100c060580704103600d0261100c92001000c14044124050426034214001c00c403102c01018001e00c1080c0c41d000d40011400510601c50f401003955013401030b404144007030820541e0303141400398400704403120107164240001c00f400c00e089032590142c0d0103031241380210143c9820001814074402044d5162049500081c030900070303042c1c00d14030060111007a110003004004080c61021050740341d504900029078080715074944110600030380445140b1580c6200750202c80212143d40007980c0303400050720184c09402050f00041c1086100381900345030f903420004440c01940e59008401403010440215030080d0310309590840921141201c0c0c0341079407002417400c41d2107020180c8201206d0a040400e1b546486000403d2001c508140001c00003645050300c0861419030034014401101c0c080a0300d1402000401c0b001c0c800c0d480d8600204d20040c0c1042405652880215000c032070300500c860320140120750300c14882280f1110340d221141e5001c00c15041d2401403071381c0f9400c0031840480382c488802 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 491683012 1250 491681762 491681779
    0x90b0d0b010317090a0e0f060d0308160c061505040f0212040f052103071d030309040b0a050a06080406180201020a12032703170c040b09031009080301091109 69
    0x703040c102c0420110f502d2010001e04140440c000101003800d9684502c0c149400030043c0145072148a46a5a0100040d19541d443c40c910340c0c0c004141e648010000000514640413a1a000c1d1040c0000002daa07009881405080a038007103c43c0c010a00e0b01c2414411840c0850048091055000355200b140388003500d441260f0b5185c4904000c4400030500300c03000e006048200141410401d00b0765082203c5034000ba03200d10b4907200140905000c603500b900d40000384241904959000800c981202c0070035103000c5076000080c3c0109415444070342080e40c0c000c1c110180401d90079030195625101701c2c001c68091149981c158150518111040d0019005030003c46e140d0300460f64924034040040003506e80000d100f0300e007040c8071102080c148664600b901801c451071090541c00003a02e802c05000488091450410b080b50828620641c49240104140405c4103c1159418441548100440401440000f00341e16010001d60320900400600b14903200c5002ca10409640075101c22200213021100e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 491684262 1250 491683012 491683019
    0x130501151d061b0c06030123010e1c03080609010308120702030405040603080c0f0606100c0609020306040f050f01020306060a08060f150d0c0804050709050c0d15090b0d0b01 76
    0x4822039818040a8615005a650504262a440003c001041aa0300b00310070078034101d140d5a0030001061400c501c01c91050005000d407815240103540c170b842e03040425121180741000140e80a2301c0005e03a25a02801c01020141e091911035000c0c01c52901c071769a8014540e86002c03c0180c204001c0c000900201c1051041c040844005580b15402c1825030041324205555800040c06030340154108540c101030102c1c070420300c2c03c010003a010100d00540c01411003071800314041141c41d001826402e08001d010ba104900740a19548440320054000d825030b1054640303824501d4111096032012952480780030340c603000c211810301c00d407801008002d20040c600426168100da020402801c25607100d040c4003840c1e91583e65100490a20364144641c00f9184c420061f000c600301c0303100903110310074005188104070000d0004070700c00040d074000c2c50780090551606400880c2314004c62811011451a140500038108183d06090084030081801841400c0c6a00c050140c224070030003008150303072103210051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 491685512 1250 491684262 491684267
    0xa0f03020f150c01140a05150105030a060801061509080f0a0201210203090a02010905030a0b0402060721050706060906180504061b0905030f07060f03020d1107080913050115 76
    0x149488010184010b56095001407856a40a0814400750b41e40d503a0300c920700342014003030581d40940c1d948800c2219180c400e11030b884800c7c1c0307640643d04114000002500400705544034501401c060802000890346540c0010f9030840c60f0b0f85204007050400f0b200050600d400140d903c01c11440304050012050654010349801c9000c540301c28855540040c01c104000f03251002d1485504428024003d40c201400098042480c0381c0129019401c00e14009000c250718010700c4d50400d6040e0f441c0d40d550714182c1408118a160b60100c80e140e020008000c01d20190b2180c00b80581c580240f00400103c0d0b56a02d2020442d0014441c041561030f44141d0045010125442980c2c068080d10002c1480d66810441d0003e240300004454042810101c090206090801c5241032600129008125640c00d051000d0040e010310820203041507000a00020300c05910341140070030100550401c0d889031501e19200030541c0010400e140035901d07442682074848034034010f042c12a21b02603041840248951000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 491686762 1250 491685512 491685529
    0x914070e04150f1107030f090803271c12020f0304050f010c060f0c2609251208071e0c0515070b0901060501110109020105300708060a050a0f0302 64
    0x5103008070b50388070140b01c1c460311300300000c20000380700f84d1343c8003000390581e103014005825940015403694000c0c440c10038014100c10340f0110414500c07100b0b45180f81c400c000110800b0300b02c0c5031150201001031015040041e1803550501c204115001e0750300e00440c0e9048155280031f107101c0d2950141050507150b07490f50103000e0020103640036a1010410041030058003041e03c40c642c400200269a80c08500c1c0700302044080515400c1069444040e83d00b072040103155280070504195600b9a4080c60701c07000e441501c81e014005060b221255418507005c1d00700700100b60040101540c0c11124002c620040c68241080410741d039500169481866041030144038403406001c41c0e081c588081040400f0201c1c640c000128841d03823024002080c0340d400c12000401c56407207988a20916030405070040c005030303000400c3d5244655242815040e06175445510032440c1e00700004aa10f002c50803050000c95948079002178072078403090b40d4844a1907514000e10620a81d00c0c45200380c1d0342d1951009100520b00000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 491688012 1250 491686762 491686781
    0xd0503040320030c150a290f0303041a0703030c0e0a06200a080702040b0a0b0706051012050109020915010203040b0a03060308120403030b0904150e010f0914070e0415 73
    0x40380d00f1309092015051030502d01c508400d140060b004200009420075014440c500103e4079000c40e1055405a010041541051070503845840d005074195000c1e1420803d8030300400d64000050b18102980c18030400a0340309903815000a410001000700a9010381001c0000890241c01a8040351818100b00c0d00f100364a030b016800a2000b20034060b840c0410003d850090b406004043d40c0c3c1e65243c41003004076440755007464015030f0420000c00800c0000b00540b401283c00410220b156610850b100c400800c650300014001040e411007102403102c154400080e0310301c00d481104040d1150800340d00e04140e074652890059000300b005001b46040a80070741940d02c910b04002c5001c0d0f489a850900769088020441744a41e8200c0801c0140355140c01560315542055a480c40e03142060f440304100c014001564501c4986c44003c070301e58600007544202480401c0003410071481c00507140c0b501c40d840d0300301d600000c240300d98080402c80351341c2c4609850159a2140c5402e4a000115800002800c41c122 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 491689262 1250 491688012 491688077
    0x40f05040e21161b0e0c1605100504030c020406090b101803120203030f010e060607030809070302041107110405062d060406030c1b050601120f050a0c05030d05030403 73
    0x80180200c1c0300c0840458414807690306002409882d000302c04111352207030321444038039a2180074081384003c1c01c012100008251107035251901c1307250074074503d01107103445001052890001000141a40181c411040300d2081360248081075444d107144007551f80954220358042c9000f03011004450290450b254640b500d0030003030100a650740c0392001d40360b0300010104c0240c5c00010810518010b44031806003d0451400c140b0641d08060b00818500e000744400201440312070004141612030030005480110360052060004044408200c0950340000c40b045030700d4030740040e0401042c98130b07008080c41504040e206064804456641e8000c1e44003254844507514441e04415010307490b40300c001d0000d000c0b10340700460b0300224800010503500c0d0454502d02002101c0c4400d000107980800c040341100d403040341d54100c001c01d504000c00c01e40f04003034004140c1d22907a90f025081250030461041110310031002d8a1803800401415640b0b8401140d006000812080e400246064181c00002c100c10a09 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 491690512 1250 491689262 491689267
    0x30c0603131502040e0603070e07051b0f0f010c03060605030402090c030c070b070221090a0b0c030903010f24030803070305150d03110c0d082d03010308040f05040e21 73
    0x20300202c400c991084d0410980c4959400c1004254101006980d0080c896054051a20710300890b00034401d00030b612484825800d1001d4010500908100c0560b00c1050202030350301e00e10352844894000d10300b918a40000c642000c60000342c550080050300c1c4a55009805144290f69090050040f070b40010034039180154180072000c00b1074200761030580b1035400c41d002003108030584409402026558507804c02c400c68100120805a2140d000c000300703d5a480084581b52000f5451036030660007504135407a0590b207050307400900700d10b1641000c00001e00000600c141c880300c5106001203c0f06034080036101b0700c000c00106400750310030780c040d5a00c01c2c1c2590303025003003216071000503015880a800035000140e1a0140d00076075081440308130b01d00d03103049415150900880e684d030241401400214901906148005034823401003040f10030034031011404860341c3c2e68580c0752127045034006003c1c2d4004950880c84c04039150130b1a200b14070034120000000c200300010110154082c02c40c41c1400c840e4141d00307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 491691762 1250 491690512 491690543
    0x1020f0f1b0307080d060b090d140c120102071103010b010f0509010c02060c0616110c0d050708060c04090c090f090216080a0905030c04020306100c0c0806070f020c030c060313 77
    0x2407014250051003880302d99078505181d40c1d41002d51b0140d030080300c10b581e020049005965186800425400d41c012080705094030615421420031410304480740e0440007000500003806019401084d0a074402c02036004200a0b290070301d801c80e22402c0c44c02e40400d5a4400c0542801e0088010340208501490044000b0080b0790214480d600080700602c2d06a00c00002e0064000f070028404590700c0f024580a24044861060b80b55244130907100c80d0b001d15036100510003405004c0c4040c00180040c04103c0700c043c1004103942c01160701c60b2103545102c500d040c50100340c4522401801085a074200c44149885040c0451000250310400400d02d02c01c004801100c0050300840103041c8038411911502d055a00c0d1505250810808106c02c512032403042042040a603203c2c01d10a01480540c40e00710310300310407440c1c03440300c2038100c1d00300c01401c0c4120820000040c0d0301211010700e00340303940c0c2a5042004420b040c15a110769030500c007a48040700384005041c8424804a0718180c5000d00040c3c61050700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 491693012 1250 491691762 491691817
    0x71403090604230102010b1516050a080c070e27010207060c090f061b0803060303130f050a0e0709060f0c020402040801051b03010311100e1002100c0201020f0f 70
    0xc41c2d8000000d10f82030306403490411500000107079116400780002e20083c006240021925080c2e0410501846004a210411702800d0340d45440711070341c042c04651241a850901044a800c4516154900e204428000c03908d1815022400c0c091034421004405407882002d10410042000038550240e650910808020441901a0100c802090348804031401c0c14a5400660310842d03400c90000c0c4460f0b0300c00c86d908211680c02c100b00d8142c000174566140d0700d403100020306501c15058025000c403050100411020109501c800440d00200e0720212142d607603602c030b4a901c000840311800032406c084000c020700e5000b20051074440ca00792801d005085090707400503007240c01503002030000c1da64650070040b90600c1c1c400c416680d92090308095003198915940c4500601d0000712079070042c2220031040075518000c401041d400786004100518002d50100c0c000d41e262207040c444403003a4106080900484e006108944610039a01d0440340780484007110307007141d0380c000c190a1b00b903800b200e080030f110b03900d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 491694262 1250 491693012 491693017
    0xc010608210d0b060a0908070b0c0304050f061c0209040507081e0403140705030408060c1201060c030c0c03063e0702060f04060207080c09011d06120d2706050714030906 74
    0x40751b620f940044505242c0702520f8511640c000390715804003008059000400082135400b00c13a0b08075649102c091443c03010500794006c146290400b2003c0d1012484403021a030090030508000340ca04202d280c0e22413078222442c100650b00c15411b0460040c0c0080d0161094808d650b0190190524003103080c60745208402a600c1620143c54503000400c0a200140f0300348051034224401c0f20132941041103111005440740e030103118000501c894a1418403c03d4040ca1202c8001904840d080215641c4c5e8100750024040300c000c08601001c141a0032010010904080441e501c4049071184842c102d2411540441d80300354803c1e0f23806601805818061403041001b80b000c3c20300ca0b03010b400142d141000b0300b8980b004e440016449294400c005000c0741c1c0c0e0540a03541c00042c1001041682d40340c110104242d42d8440c481400710b8010090040c4a40e0781044a443e020004040d40c0000f2022001103015680494011400014010440b090100d00901948100364032002c056900c1d202c010000555181e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 491695512 1250 491694262 491694277
    0x60a0302040503010b030f070b180312031f0b030705070f0f0f0b0108072301211d0102090307050d0312050f010303080a0527150c0c010608210d0b06 65
    0xa80000c1c0901c1203041c2802980340010040d0b0082a2a140c5000c41300d86646c02e5004030b028600740070986c2d1950013020344600040480107425608400040c00b44031030760394022a403810000703844107021300a001100160004403040700291074295254840103c0c0c007644400406c0d1880191302c07840001042c174000a548420b880707402c20020300c100a140100440380160710007607258010744000c2103079860848440c881c800e045080500300b1440c1e4001680d41e20300e0758601510040720503280168000d0340d64440303040005801c440462142500c0d12190907031058191554154101c04404c2000b400e1240099100c54440d04001815241003d465030844d10212002541c10310b100004100b4150400f02403500201898010f00c16440c040e1602c0102650034801d22a1204a68a0141055200303000400c1d6080310407090480303d04240380d00b0017007600601394142c0b25518251000907507000011b82104010a1101c51000341c003c004e0f6200943d40080e4448440f0549400703c00c0000c0c0c0d01c0c08001c0608 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 491696762 1250 491695512 491695517
    0x20705090a0204030201021213091808030708090105010f03050a1502071703070810030308130201180f031713030311030702040606020d110f03040e1503010c0c060e0c15030601030b060a 81
    0x16513107180002442c045480491200d1070b5020803046850402030b80b003110940e02d0081010071450203a1010010040346010007070480f203c04010320440300c1e40070401e2409004c4010007070145ea40c0b59400340074079003914400100a81c1c0b1807000d620015407074600c01841c8186440d00103040ca45641c49078255000284d40c3e0000031107002080241c2d461300940d03c150081035000c01100b805082da07030040e007101c0000d00740c2c2c0203902000480004681c0314249000b01408000c6c15501001d5450b811806c64900c903000c100da14584994120801c80306000030b48040383e2494038111034a91642d103068907001c84107191050540010041070700562154021007000340103d50061044949000009189110025011000da080010440514000002507030300f541d4116840006035180d030416100b038007002800007505542010521201c480d0001200e80d01c882c0524414082e207864046910b8a5903120626282e10444001104100344101c401443d44104107043c005000d00004001950740e8200c038052100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 491698012 1250 491696762 491696767
    0x305100f0b0a0906030216140a02030f01061403011a0d05010f060308121605041707050a170d0806010807030905150a02180d080a0804020d0816060c0206040507060f020705090a02 78
    0x9602d40d002001c40000c00742850110304120740da0800840100c803800018142c0080309075035418500701400805100e5900030115165107508001581c081e01503449805880810084682060b080600500c0c3c1d0f1683d600103410140c030384450070040e41e1a10098190342a40d0380b01d550013800c0d02c00340b2030040a18040c0d5445030701c43c3c000360204505032100401d19000fa0704100040707c811504881a1400e54509018407981140c1110019180c03100c2a800f00b58402d0344402c00148810040e000b02840181407016602281e40c40c1c0c1d01070710740358810b50301e0b10700155010300010701e513510a41c00780300c2007071080f4140d80c61201c0d442c1440c14503440988000c15420b038001020070400058505140403990161441004084151618045809035942ca81c0a102d019000a800c42d40c40391400082203600c50213064442c44000e03543c5142041e24502141e03042c1c80d00c00c0c0382901600000c3c0d07140c461988130b070051204905200003124205891038040040d44644c08001c5401c0d0f5542901d03d01c00c0102610041c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 491699262 1250 491698012 491698027
    0x140705100609020a0822050a080309011d06060d060f0218130c020c061806030f07080f0613090311120c12032a090d060e0606060f0a0305100f0b 63
    0x401c0350855400a0310309841000601e00c0c1c160000701443c0d000400e10038a108166000c10400c0c0c0070448000010810b000e0705081c0b02c1080620700c0554050710001008000d00c0000b24529099140480041c0310b19602810000b003203071800052210003180b16000118000040c640140d0507a0054003690160116440d4214050309184802101d000b0380c3c001c080c802100c0c0000080d440e07030030b0f00c00079131300985002801440c000480c01c000004040050302041d52803a04001018403000300751140c03000915080080b07114000c0e840103550089500400c5101c3c210130041c0d000740146050707281201841003d1600900080060118219a66016001c0e6a4900100d2012030414405107024140100180240588103c1200303600b0007031070040704411400c1ca80310340c81d20f420b4024495041d5001074404403076810010365801c045000e1070f003234040390070075210102004814084d2640d000c803454000e214a180461103600f1194100f10340f80d48031002651a00aa1001e03000d1607000707000728060000300003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 491700512 1250 491699262 491699293
    0x20a0e040212121806041212110123190c0c0606090c141b0706090302100201060b03070c030c0c1d0705030402060406030e0312090f0d03050c070b07140705 68
    0x68004112002c0502940d80d483c641008450040e041c1c2c0d292482180c0702c0d521030319150b0030111806400005880703403e0000ca85072000643c0c1509401c0c1c00050000c129000c171a0205018115079104217a40c0100c142440a00c038071340901000741201c8220000000840d48080a071103511214156580d90702e0038403030107041c60001d5502d0355101e01911442e105540d81c40540c0103256032a04d4590314a281e90b1121044540e18014141440c400120701462000282007030f003241806c001c4920984507004066800002a42200d00d684a810082c100400010720594400c040b0504402d00c2414804401010794543c11100703141500310503440016420781881444502205940c41461460120310314501075000c1040c901441c0300301c0f41819194591080b100b002402914420071074544203044900d8040c008680e140c0b40d4404081180c007451404d404203070b01c40c1c05054400c800e4132500616043e43d90380d41104040340141000200542c840b20076003007810000c0100a054020b9000b44005201003510 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 491701762 1250 491700512 491700529
    0x4050f010602012a0804030923011413090506030a080c01090201020708060415020721030b010905030c0139060204050a0e090a15020f0a05030a15032409020a0e0402 72
    0x20403440e081c6030140c0c444c00007080c0030144642d1150b40f070810050f407103601e002d0302c11050783c0d0000054003c48404582da803216031b484031000302c00300741c0c0e640300c1038132010044c0b0303095100d04c45030900001d00c144000c0c03109403010b811141d0010005004c032036185c40a40c0f514000e640000003035240c5070b5180d9040d2815580c0c100450800343c008040500b4542c1041d0b561180850846d006a8803131540124490042c4200c0070300c1c841c8440a8584001c58540440710300400803c041c060307040c00708098000210f00360038000b64122240070181c440d141c003104480b4105149151114015001050503000c020100345440403869905101c0e010140c1c450b4100810400c1c441e8558004175507400312507007000a0008002101180c903500318181d100381d203c40342c0380d41d0040e00c00c1c00700c100b9203120001801181c0d40e80c010006c610540c1c61000821038084c45400700707119800030b44009807501040700c0e80c0554401603220700401d20751108900150500b92940440c00c2071a5a030301c107804200e0010104820350038120031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 491703012 1250 491701762 491701781
    0xf0f02160b1e04050102070e0910110a02160501020a1e02030114091507080c03040c050a06020706030e060411060c0c09010b04060318050303160504050a17070b1606090f0204050f01060201 82
    0xb0b1242c2040e050000003075981030203204521f400042074002c50300d21032003406501c0e60f172a5604000c1c059140010198002070744800000030041c0324481c024440031a002141c002550740590107000383c4901074566401340084124030381e202c0d401d41409540140e80074407070340d580c003095559460ba051a190000030b00741030386d004103e4031550601d400c002c6d540382d108005950125401c1c15864482e1145e003040c07410391429812164009855103408203100d43c0005140c802c42e440d6560070b00503000441003e60700c0311420f4800070101c030080c402240c00c505e4001c01801001c02c08008880000e80100f00040c510030302a8002c1949950006d418424a0740c10301a000d00c9580082039100382915035a41c00365603100040491009080f40707500d151a0398800c904a074000c00c4002c01d0308100b00e8503031200218440e85079900761428030a140c40000e030000158240d0b602c1c0040d030f0100c2c201c01c180c0d80d04d0ba00042e0141080490381440c1c1c82c440e44005a840c0e1280070300a02d1081c800c420150305005000c3d003115145007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 491704262 1250 491703012 491703067
    0xc020f0a030e0616020307030308091905030706111c061a120105040509070509040804060207081606140d090f030f1817330a0504030f0f02160b 63
    0x200400440d8110881101e205401e682c440c4d6101a50f802040e5440e244201c000c0d030600890500106242c0d000720a980034119a2080c2c6103101072807011004800d8048000a04035001440740302c000c2081136002c9400b84c4540800c1504d0007c0b0405948510710314041d001040b560340b0f034418060248090880c0180081e50f024a9182540c00c42043d4407110051180724480c503203460005000d080b00740b05500c024078014094807001d05051800160a0300107004180c0144500d0300d0000c2d000c0b4000400c502c03051014450061020304118046804c8a0001e0840075444400c118842620120384250001580125000044840103140040803401c1c51402078003041402010034a42c18029100c2d4821550000040003c1c40a2900030a00701800b1031a00c152401c1c074000c05030b58008142c80c20031001c2d111441b05a019544001000d170488505460203400910304001e0600784c18003a03485c03008005540e00494070ba0329921004403ca44056070041d180480001c14100c126000d2200b2040c00449041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 491705512 1250 491704262 491704273
    0x6030b010608191404020d02040227190b0f0904140412140306030709050a0b0604030c03031b08070210111c030e07051005130824060123090102011e0c020f 68
    0x1440c603100e013140c0684040d106d11400e01c120710465440703074100c41c04005583d0b100c1c13030003485a40c03002c41c2d150016802c0b00c0c0203051a1240c600700011003c0c400b030a6640c1140c039941801c00640403015150803188000e84c2240d80d4520511020554000c0c4030f1085102d43e210142d00541d400004145c0043c050440e4041403003442400181c2e0b030081500b0055822400340003c1543c0e444a007880a07150096805030000c000180110620500f260f0300300035203020303484506045541340030f84c4d882c1c104601d0015000b80014440c050051074100b900300b40f03400d81c9182a82a2001d40c00d01e0a0909002d024a9043da00120308020b88403905801840045c0300e018000d02641442c0c140405c811404441102d030402c20300041c85000c0801d00c0641c100501000c8040b140040c024064021002c075a052000c506003201c1e80c0000c000750b00c200750300d03021400c0554220003d072a11000000f00c5030407010000c2e066549440d51015580c1071500c15030008010031201060890b05090003a04100d0768000041031900034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 491706762 1250 491705512 491705531
    0x70b09040b0d2102010204090c0e1905060301210b07110f060c0328110306011b020310050c0d02030405060103120203040b0906161a040605100f0b09010306030b01060819 74
    0x112018603c02400b0300c102810465600324020b102c1d903000f100c0540e00c1c100011400765031040c240d4060000a075454181c1c0b514080d140984c004852286070785c0408208010b1045e1003100c0c0500300202c40042c001c9605880c0c96442002520080320f803031000880d5900c0402c80d0b95010003600c2240002c0c100908258182030410060354480200300c00e401c0e090421100320140900b101031011503604010030020b03030000c00003800c401d5105039405800103180701d44503180c0c8180d19408001c0150f00400809144c0e20f8615107001400004094a80b601400d008441280340ca900003148220f200d42c004c0d12030b641c150b01e040031a80350300c000c409003194000c1c44240b258480680440c2c20b01d82013160310f00c0e103450b016904654406c80740700d001810b114240210f001001d01490506000d40d02c80c4c0c0052056a0710000400f5032024148503004120320500400c0041d04500b00050811200c103143c0411140e0701c0c1c0d22100110030b02030388a440018628804c2243c0c2d202400a611045802a401400006c1c2d1 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 491708012 1250 491706762 491706773
    0x4020a151202031302060d0c0e090610030b0102010b18010f06080c0307111009110f01020111040905040f0b070804120504060e01080709030b150a05090609010b030c040305070b09040b0d 81
    0x400c034881d109141c0c0000071680301380341a0503100d40303e5802400b441da03409034078039894042e180d20074460000c92820700b03030341c401850003035240d501c0340101806040c0000c003000c6080380178003044480103056560368801105903441c0ca0003c07807044884a000a10729501d0404c00600c14141c60303000104002051042c8111070380315004a80c0c00000380d00d000701480ca84a420f02d800c003010003e22054541c80c5c481d0101c2080580500d1454000c811a25003151842000040e8266a022070418038244c0341080203000c44202030f84070300c0d0000e000e0842c800e80f641103640c0d04d40846100351440c02c0418460320400081110640d821104001685007a41c103040c60b202d00a40035449200c1c4050511a600c1d0001b02d005100e801c4d10f00c0112f0f041041c80d030305070030529801025001e4600c041801544800d201040c103007007016885000725000740043d14103a00c0d1a61100013500082c00314a1160407c1100101068042001d000a8103c412b99555662100c030100001c96104030003042c040c03000c070162034003c01c5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 491709262 1250 491708012 491708027
    0xf1805070c0f0c27050609040c09181202010603020a140603061005132c010b1e0708031014040c021e0114100303180b0910030b040903030504020a15 65
    0x280c0c0001000441002490000140071035138103e010741e0700b01e03404101d0100140744000311440e40402001c00550701e0340c1d81445051070702110050030400203040c080044402540c841c072400390340224031750f040744019956110904541e020703040050791910018420f52070002c50300380050003d00201c40c102c0c1d00100100e01035002c0185014403601c409039007040342a010b5001c4039800c4030747c0d086000301692a22003014a02c80d9825100854818603841042e2a21080c04070350b050b100304101d050f00b000d001020081d1007500c0800a83c03d010010301c8021b001469035009940507141010003c106182803080d10f6842820b44d0011038441e40c20000c29802d1070743c01003541c0078071901041000c101d9201c1140106d014102c0d8001e8415400c104c0020440740c44000303550b01099a1281c0d0715065030100301503401d009590389000c6d9050300c138020419040140b9100f0f08050a0190074180455606e65440000d41141c000c52015408245c07210100030031858a6150400603001c0400c481ca580000740c0d800501c1107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 491710512 1250 491709262 491709287
    0x3021806130b032e1208130e04052d060a0e03090303030c04090c0302250606050a0306020903060906010f2705091c0201020a09090509032a0d020d0c02060d06080102040f180507 77
    0x61b0000105004101c0d0210108805403070f818002404a052a191203036407521a10503e000c1e0420011031102012003512150144060b20380003014a511150258401449040d05150451200304200c0d44a07480c00c0c005184a600420580c9449600d403000d140144e0346040d013000c040620411164240420b1205108510300e00c52440f842109407515200000f001d040e000079a2140c0c11620020401100e60003c050a110a40907244103840d40c07050319540350428066042d120035403413010301c20520385d50300c14200b404620a401d114030384080b0b240003c8071800c2d00c1810590704100403031208603002c0b60400464522a20086252040d6200010030140a80c001c082065468601050150004205550028000540002c0e20b40051b00d240446002232091055040c05200c1c040c2400900201c0c9031200ca1910351240706420600d81d0030440c2a501c40000c42ca003c3d070343ea041c0802c400b10244068009040c2e4418052100ba05004030141201000ca160582c00c07802c0400b04500d0f1a030105000151 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 491711762 1250 491710512 491710523
    0xc0304080f09030f0709090c050a050d0201050c120d09031e050d0e07030204110913020a35010e06040e12040b070c0317030a0c03021806130b032e12 65
    0x82c0c01c0c1900000f810311072188840c010301e10070404007007020603856005104451042c002032019568903070501101078650322034594083d0035895100055401072005007003094005007900c2c2c0b40c48080c0e0000142d5005020b00c1c0c014140da5410305000c05422034040000000801500301020241601c010503034496048103400d03494075640030700911041000190041e6038024018404030548040918164200d03c01c50ba104003954403140d00c2c540d805108840a101103a503403491030440f5031200e005143c0010348903084ae4003115600030003142290480a003c1d0260300000081c90810394204810b450440b549400d0740e4000601e015400b14a5408032021241c80f400070765250010380c02e05030881140c40d4400360200110b924180040301008006600c00e044a8104000d09000d50004508074006c0200c0d182641c0d985203c03640f4540381c0a000b80caa104080b041c0800e01c44c3e11401c91450729041550540c0e40b940884400414060b0000c0800c924440c550818880030341c90852800134000592801500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 491713012 1250 491711762 491711767
    0x506070f020a08030a0510120305160305040302030d2007050d0b060301060317040305010f092015041202030601080114012903190f050c220306090b040b0c0304080f 72
    0x9000d00a002e04030900750060003054481c030b0145032a201820040380c0520090001d01c0740440c01c11400e6682d00380d01501552045c1c1020038440700313800f00d800700304001e0301032000038400000143d40412480c0c020795810b981c3c051550045404601a04182e50314111803030b0031004040c0219101c503151958180c0e08226022025259000801d00400359500054000e107502841400c0d00708510b8001c2084038400c1d40208507001a003003a01003100c0400000511a07242c0d046c103840100e0200702c1010f8503640040c44112410709000c48445290300c00d42c8882c49140c05a50402c065107400d100f01401400032a00138080310141000a840c0f00c181405451007400210100395004140070201c2000e0540c2c00720540d56034140041d030108500c0728030054000d040d0509001d6500d412132401070074058000b00070310340d041c031400d4031140700815102c3c042588402c1030170900002007160340c02010341e0035002e50b80d4030701a824203041c07031254060000d14002c00030108005020000d1000c104903911241c06529198 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 491714262 1250 491713012 491713037
    0x1012080904180b0411030a1203090c09020309150a020c030307120905060408190e0f10020a2012070b0f03040f21090602060411060304082502041107050607 68
    0xc00a0240345072105010b00141d800741d08100c08110824051406244c1c005a80c40d44042019a140d00481008040ca0004540c2446030ba0081e00400e02e558407610341403a406803203419417001c90300100c40f401e401d940a00988862004e030006000e42005950b1819071804060451b210f944e448007030400303410045a01000c2010700c1032076201241d00769020054580324103042c10b041c965504889240c100d6003110354003421446010b0300300d0383e05107103018060b144c82c503a102d003c01c0780305100050144107601410307440c20002152550281341d0320519a02ca030300f2100044003032085440281500501c00d503c0140c003440750102c2e4800351403880c200304041580d2a40d0360310f05528403108000d0000c042d41e006215100c1c0f54400c940f101d15540c1a155a074600c2d241d03403204102d0f901c52050740c0180400240c46040d20345030500a00940d4414046c3d02c2003450070a58151034a24204050300181c140100912290210300e054061800c0d04d040300340b04241032820649449848840c050882014001d8595121 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 491715512 1250 491714262 491714269
    0x61b08071212020304060506040e06060102070312020f0f010f060b120406020702040e030c0607020606100905090408040b04030309080c04021c05040507150507050606060309060f060f1f020610120809 87
    0x420782c2140c045041d900e81c1420b1400d440540010b0341c10310702c01c6003040b40d603841030840054401d1103040d050b8010150940b41d51242c0c100702c855a01400110700500800d0513a800b41004030845001d10100001031a03071030440d40c007080381c00d1600402190b640c00c01c900111422000000c03508140c00c4800140d135503005100060007881d42201102c0d00d40004150204000c0000c641d40e4441c20f0759400344c804581e81c03c8104a04c4503a040080000314071031711800c0c000d46c02c1020a00c1d0388644900303000c13842c2a484040c812001d80007644128002060060203100b1800d0902c0610407008041d00c00f9400c2c0310a11500000400400c20103102c42540e9a000078184501000034400414001e50b0398000d090030a10000c006a0084038152074074452080031030b10070f0134040d0460380300b151410301800041c1c86101c0d1004041da006040d49500c1510300a8042d5250b0f9404070a020200d5100340500070140c2004010342001c200500011000000c848100550003205440e41c81c01da90180300300c2c2c0e42c0c84001000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 491716762 1250 491715512 491715527
    0x90902030717042f13020306121c0908070e0a020d06051909050108061e0a09080d020304050d032d060b0c150f070906110a0b090601061b080712 63
    0x1000b40c0e40c2c00e11000c0c00b0a1000416802e034011808050541c0114095100b56030040c02c855260303500545031400c6003901126a9001d1074002400520a07c040310000e502c2514040d444c020b0040610442c0311098000342d040100000109403400c090b0851038601201c9074900f180080c03022007082d40018275000741c2c005a0b4018000340230010140406a800c0c0d01c0340c515039102c6806a0314841c1c2c905000883c02000c0090711a100b404100e020b00000e04030741c143c1450040025081641058030b520702d00c000030b01031801615041c0300c00701c8010307201c0c54941407642c40c051104030800181842c0c0107810748920a6a441c0c000102003800030401c2031074484003010001c060f20b0788140800c510110b038603023803d14080342254400f502e02100d1501c1b9201e0741180000040d050700c0d102d0200f46891020030405025000907541d00c1e0005054544211a40c0c03240f644145c0125082142030300700c5401030000c43d030855a41c0d000007844410b0841510351907600c5201505c00c5403800b41c01e004001aa0941c1c00c0d00c10b420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 491718012 1250 491716762 491716787
    0x18060306070c0f1a0601030c111015080a0b06100c11040c091a07170310140a150f110f120d0b03030a05090301060902180d02040e0a051c09060909020307 67
    0x28444c000c1c04d900d525490250f820f03e0010342800301c0440034502c5088050003c08140016100040c0c0400100c40140007006c4d088600c41510440092424010b105d0300880034000d038508041c0307140100410480c12440355142c41131080c0c078035840003c20241d203c98800110152000928102d14000580700f0180b545d001c11103800042c08958072486c186400350241d1803140000f030602c46101000704070700d4001221407071341b49030704910100000d80ea4480f6a40ca080c0c000f9000d04030168460704401980b234506007002003c15607c480151080351300200c00e0301800340c02000741c03800f00300018000303488000844101300701d8030b404500350140e88c01d158012401100700908480d41d5035a81d25002d005500040307142c0d0b00c2035181c8140010007010b20700031200300d010018001d0251b161000c08000e800450241d0583e00700b651800748081100f003c0040300f160b03c1c01000140120302da842e26540714090080708090801454031401c010349030b0010000c60a440c492500541c407565800c10450b0381420294 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 491719262 1250 491718012 491718023
    0x6090b1c032d0c0b070305090d0c0c0e01230102010e0c0909011803080702160f030b1b04120b010915171011031504090b011214150618060306070c0f 65
    0x980d00524541003c81948068807500301030700c01e5030310905c00b0340c12180111075680554110044296140b48600140b06129100d035180000150b00c840401042c09426000460110035943d000c904000120000d0184810244001d1004444031504182c403990540410740c003440b91800030646251082d00903420141038000c20300c9000c440ba09000300030140c00d990590240c080e00c4482140c0751104c40f04c04050b0ba1500224441e03251030741d0f80c0c0015040c0010020b8a43c1000041e01140c405d101000401c000d01020341c0705800504141080311a06d030040e1f008403103152400a550304003041030903448048130f41d00030f80401c9140803d02c1c02420041c0024107184070506e0904181190122400070314040c00385043c0916a070459401032000711500000d014004c6500800104002c500840202010a120304440b030740a0b0030010365685020314032040011400c107400200445030a004044081e4111855521403440c02c122002c69110b0300c029240c1e90400071003034103510600c400c0c1b1144241940d07001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 491720512 1250 491719262 491719337
    0x90c060d0b04020d02071203050f07081f080d0e01170f070c0503120a06080f120d060305100629070b0705120708100501170a23090106090b1c03 63
    0x22040310300251b1090008035002500d4100d418a210b20078414144a009090304036001600c4410301a01c501400401c508580a4024800d804150b40034202d10020216840200410154200d01a040000302418281009035a01580c2ca066600c0641d1a400001c490003d450136180c10744126180300303114401400d54440054840a01e014203840144600603070302041003095201c0340520348a002e032080f000e00c2603221518094501e680741c8024034802c0c0a510000440651b0780c0e6600381401948e00d1b214002d15a0f0b010104502c1d800c0d06c1c0400060395039171a5007900c20100030280d01c0503015100313000d80100301c9040000e07010b90090084421149000c132003000149080c000040c101101250055000070000b000048c0d00d5010b4002c1100711040da00074103045070f440c0034458000700014446d1040e0254041108a14011901752060188440b203002051142c1011048000c0e0780500380024014080b4094402d503210069940c105042d506103000035000d074007070204610300d0b911807074a903940820f40f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 491721762 1250 491720512 491720527
    0x2090d020a0e1f05013c050315010201060b0403061e0f1d0f03160203251a0909010504050a09080f09040e030a020a030c0317130218090c060d0b0402 65
    0x40524107885004599114000d8882140310340912800c1846068041180c070b00d0100c521003101842210b013a2040b04088046005522044404946c00c81c4240b010031030001c18414090641e058a840c42c0380700380000c0c403049243c0116072000d48074030311000c0c2001742e583c80b0000c5180d00d10400d8482ca0307000c0c04418041100c00c032035420b0003808017400205201814480310721030380c1c0c00450300c181d1402c100c0002d10304045194203869121800a24200da142c054180c403542c010350030070740c00388585da418101050001d0038019102101d0036900c0548502c85070601c03414030995101202581518020344010a558650a418101800413400c2c020425030000c20f004001458400103003002107001c55081c400c404500c86150344034803034070b010640140c12103220003021a0160701802c03503440c8203140c403848e440c02d0009400780d100350948205910f6003486960600350318122145c00003c1d0302003400c2c3d070094100b00b8013a42d07580ba1503d5036103000d16030100303050f561f6013810f500c840703426540a4000d5686408 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 491723012 1250 491721762 491721779
    0x90d1403041503050f0709140102190506070f050c0703060b0607020a060f0f090315020a02120a181d070f11011103010f0e070806010c02060409090f0201091e0902090d020a 75
    0x1880b2450900107403518000075500012041d1081c02881c01d40c94104500f420001c110b01c1c541c80341d01d0314505600c00d007000500b2862104014071011801400506902c3c101140000d2100c3d030b01c540d86404100050007401c0b0344050220303a10301203c0d400340000510840080210b1468064007402a41c02803031201c000801c603411a80c4510392000e55500c0c40951b00001d1340c203580042450101500110000c00c8500008400340d005201492042c0100d5101503085501c04416030b215444031400154040318242c4200b12983c0010094408002ca0303e2080300c240c07105007010704000f0038001c10028041414174081d80200f0511000c0c2c54040c0007440f1801b0179952060041d8028031036406140924803000540c090a0101b0714010321095941540da5201c0100441e031506030104107a0380a0030802c03002400d882d1504c920b40c0001c0c807030101c84d0b0b0725055500025040380c01e2540081d0031140000e440307041a446084c03100d17003610381e01309005131281001008942907617088800250880c0d403a2501040030b81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 491724262 1250 491723012 491723039
    0x15060703031e0516050414090c04120c0929040c090f030b091b03060a020304020103140118050702030c0703020d0f06060b0315011707081302130c170606090d140304 72
    0x1240c24500e640c0360744e40740c221120710841c4102c610400d18111549107e24040050941041e8442c3d0071500385525044000c00070503410700c085514a0245c0020000074040d40140302050740b9403034410068440191802101c01c0d29041c000c2c1c4210344e0340c403d07000964055003110000e01410070b2601205500c038944000003250980e5002401d1060b00d401e52581c60074400302810505c0081d0240030b041e1115a50b20000c2e4101401c200d05050316042e041c0614521400150700900c081c540d48000b44010780904811641e015244008541041000d1000c0320300016680040b43d0f03040d83c043e400302400d824081d240e00040f2000818450420704001003030b41705407000c0c50080c403403896020b240d051840010764011016440e00040e41464000081310b90740100c0360580c2c410b04010042e0f414110782d03400200c04281c4d810007866810b554030030844045502126244000071a0807041040d410b0840008800d070154014240c070139046d5520810800c43c56034000a0032401000441762265110b1001d85c5940703 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 491725512 1250 491724262 491724271
    0xe371803080610030615021e06071e0507020d030903030806040e1e0a08031006020d02010e0705040b0102010f09032001060506040302040207081603090914160e0303040305071403010c020615060703031e05 89
    0x6600001080e20240c08034058ac0250015154151640150b41c00f986011001030060400d0100502030300d4056211302d04e00c01d807502d00c250b0302c01c1d0803d400c62034040c1c50008041c019502031890201080000c0b000004c4c1c0991200700c41d030301010701c180981c241c0c42c640707107007000c00801c1c951010042c0803403c0501c40300c00381580c5c42c6409880401034001012800c0360b0a80035120015802944100641e0415922a40300d001061002241c400803650b20a402e0fa1a458802c0340026200c41c02000000c3d0740b920b45103440d101000080c04564901400034525000d64000a407255500040c41c1c1c0800410030308a610410086810310072408050401820301d001174812890f071541440c01e0302007000c4202026500c2103000c6185111040c0c00e0031000c482e00706d9508008c40d0517100420001c4042141009040010031001e8114054501c06406050030750307189080b860259400f1200348004400c04c1c02c101219840107440b0941c8407009800c080700503002e10b080e4441400c4400028103291112904010301c80d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 491726618 1106 491725512 491725543
    0x6010303140c01090c0503010f110706050c090901080703050616020615040204211703060a0b071a0406020306030616090e37180308061003061502 64
    0x2180c010060940b0117038100c800821061909009214070356640c0c48040c012a12107418640c1d01c0d009110006010742e8480c00003c58044c035040c02c1d2180307168020044403855070b40d00082d0740c9540311808183c03554010a0009400900080b900443c0040c07070f40d0081040d80d90714001d204640303190303501040d440313502000001084803841c0701d2502512110040703c81110301519000c0d42c10444400724100b648020b004001c41c2e9078900c920032041b900d07a10107950b40c40d1494544241c0700900081d00b034041c3d00d201c0c0103100034000d041d0302a510515041c0c0482da426101c10b00c0e00b000640e071048400c0d00042d1362140038000c0c2150560b08507000311b10588134619030300c1c01124035444d45040941c00140c0a000d104e0a88000400740540020070f2240801103003108150b40300101180c0e0020044e41c041d6201c040860800b07031082d8805d030020000e00e4030f2078007a6500c198000307443d10082001d40c1d00 = true := by decide +kernel

theorem cover : BRFrame.Cov 491546762 491726618 := by
  have h0 := BRFrame.cov_init 491546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 491546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 491546762 ≤ n) (h2 : n < 491726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
